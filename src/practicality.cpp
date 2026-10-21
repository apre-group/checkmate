#include "property_checks.hpp"

// milliseconds to spend on deciding whether a candidate's constraint is satisfiable: undecided candidates are kept,
// which is sound, as pruning a candidate only saves work
static const unsigned PRUNE_TIMEOUT = 1000;

// Check(context ∧ formula) = sat, or undecided in time
static bool maybe_satisfiable(const z3::Bool &context, const z3::Bool &formula) {
	if (formula.is(z3::Bool(false))) {
		return false;
	}
	return holds_somewhere(context, formula, PRUNE_TIMEOUT).value_or(true);
}

// the constants still unknown at a node: unknown at the root and not revealed on the way
static std::vector<z3::Real> still_unknown(const Input &input, const std::unordered_set<std::string> &known_unknowns) {
	std::vector<z3::Real> unknown;
	for (const std::string &name : input.unknowns) {
		if (!known_unknowns.count(name)) {
			unknown.push_back(z3::Real::constant(name));
		}
	}
	return unknown;
}

// premise → conclusion and ¬formula, leaving out true and false, to keep the results readable
static z3::Bool implies(const z3::Bool &premise, const z3::Bool &conclusion) {
	if (premise.is(z3::Bool(true))) {
		return conclusion;
	}
	if (premise.is(z3::Bool(false)) || conclusion.is(z3::Bool(true))) {
		return z3::Bool(true);
	}
	if (conclusion.is(z3::Bool(false))) {
		return !premise;
	}
	return premise.implies(conclusion);
}

static z3::Bool negate(const z3::Bool &formula) {
	if (formula.is(z3::Bool(true))) {
		return z3::Bool(false);
	}
	if (formula.is(z3::Bool(false))) {
		return z3::Bool(true);
	}
	return !formula;
}

// `formula`, or true (false) if it holds for all (no) values satisfying `context`, as far as decided in time:
// it is only used under `context`, and this keeps the results readable and the later checks cheap
static z3::Bool normalise(const z3::Bool &context, const z3::Bool &formula) {
	if (formula.is(z3::Bool(true)) || formula.is(z3::Bool(false))) {
		return formula;
	}
	if (!maybe_satisfiable(context, formula)) {
		return z3::Bool(false);
	}
	if (!maybe_satisfiable(context, negate(formula))) {
		return z3::Bool(true);
	}
	return formula;
}

// ∀ variables. body, leaving out quantifiers over true and false (the domain is never empty)
static z3::Bool forall(const std::vector<z3::Real> &variables, const z3::Bool &body) {
	if (body.is(z3::Bool(true)) || body.is(z3::Bool(false))) {
		return body;
	}
	return z3::Bool::forall(variables, body);
}

// ∃ variables. body, as ¬∀ variables. ¬body (only universal quantifiers are printed and parsed)
static z3::Bool exists(const std::vector<z3::Real> &variables, const z3::Bool &body) {
	if (variables.empty() || body.is(z3::Bool(true)) || body.is(z3::Bool(false))) {
		return body;
	}
	return !z3::Bool::forall(variables, negate(body));
}

// Geq_p(U, V) (`strict`: Gt_p(U, V)): some live utility of U is at least as good (strictly better) for `player`
// than every live utility of V
static z3::Bool compare(const std::vector<LiveUtility> &U, const std::vector<LiveUtility> &V, unsigned player, bool strict) {
	std::vector<z3::Bool> disjuncts;
	for (const LiveUtility &u : U) {
		std::vector<z3::Bool> conjuncts = {u.live};
		for (const LiveUtility &v : V) {
			const Utility &left = (*u.utility)[player], &right = (*v.utility)[player];
			// simplified, so that comparisons of numbers become true or false and drop out
			z3::Bool comparison = (strict ? left > right : left >= right).simplify();
			conjuncts.push_back(implies(v.live, comparison));
		}
		disjuncts.push_back(all_of(conjuncts));
		if (disjuncts.back().is(z3::Bool(true))) {
			break;
		}
	}
	return any_of(disjuncts);
}

// add `candidate` to `candidates`, merged with a candidate with the same utility set (the same utilities with the same
// liveness conditions, in the same order) if there is one: the set is rationalizable wherever one of their constraints holds,
// and fewer candidates mean fewer combinations above
static void add_candidate(std::vector<DomCandidate> &candidates, DomCandidate candidate) {
	auto same_utilities = [&](const DomCandidate &existing) {
		if (existing.utilities.size() != candidate.utilities.size()) {
			return false;
		}
		for (size_t i = 0; i < existing.utilities.size(); i++) {
			if (existing.utilities[i].utility != candidate.utilities[i].utility || !existing.utilities[i].live.is(candidate.utilities[i].live)) {
				return false;
			}
		}
		return true;
	};
	for (DomCandidate &existing : candidates) {
		if (same_utilities(existing)) {
			existing.constraint = any_of({existing.constraint, candidate.constraint});
			return;
		}
	}
	candidates.push_back(std::move(candidate));
}

// GetDomCases: the rationalizable utility sets of `subtree` off the honest history, as computed in subtree mode,
// taken from the entry without honest history
static std::vector<DomCandidate> get_dom_cases(const Subtree &subtree) {
	for (const SubtreeEntry &entry : subtree.entries) {
		if (!std::holds_alternative<std::monostate>(entry.key)) {
			continue;
		}
		if (entry.results.practicality.empty()) {
			std::cerr << "checkmate: subtree off the honest history has no practicality results without honest history" << std::endl;
			std::exit(EXIT_FAILURE);
		}
		std::vector<DomCandidate> candidates;
		for (const PracticalitySubtreeResult &result : entry.results.practicality) {
			DomCandidate candidate {all_of(result._case), {}};
			for (const Cond_Utility &utility : result.utilities) {
				candidate.utilities.push_back({&utility.utility_tuple, utility.condition});
			}
			candidates.push_back(std::move(candidate));
		}
		return candidates;
	}
	std::cerr << "checkmate: subtree off the honest history has no results without honest history" << std::endl;
	std::exit(EXIT_FAILURE);
}

// GetPrCase: the constraints under which `subtree` along the honest history is practical, as computed in subtree mode,
// taken from the entry of the honest history inside the subtree considered in the current run
static z3::Bool get_pr_case(const Subtree &subtree) {
	if (!subtree.honest_entry) {
		std::cerr << "checkmate: subtree along the honest history has no results for the current honest history in it" << std::endl;
		std::exit(EXIT_FAILURE);
	}
	// no result: never practical
	std::vector<z3::Bool> cases;
	for (const PracticalitySubtreeResult &result : subtree.honest_entry->results.practicality) {
		cases.push_back(all_of(result._case));
	}
	return any_of(cases);
}

// ComputeDom at a branch node: for every choice of a candidate per action and every non-empty set B of actions,
// B has to contain a best choice for every value of the unknowns (hit) and be minimal with this (min, Lemma 5.1)
static std::vector<DomCandidate> branch_dom(const Input &input, const Branch &branch, const z3::Bool &ic, const z3::Bool &cond,
		const std::unordered_set<std::string> &known_unknowns) {
	const unsigned player = branch.player;
	const size_t actions = branch.choices.size();
	const std::vector<z3::Real> unknown = still_unknown(input, known_unknowns);
	const z3::Bool context = all_of({ic, cond});

	std::vector<std::vector<DomCandidate>> lists;
	for (const Choice &choice : branch.choices) {
		lists.push_back(computeDom(input, choice.node.get(), ic, cond, known_unknowns));
		if (lists.back().empty()) {
			return {};
		}
	}

	// Geq_p / Gt_p of candidate i of action a against candidate j of action b, computed once
	std::map<std::array<size_t, 5>, z3::Bool> comparisons;
	auto compare_candidates = [&](size_t a, size_t i, size_t b, size_t j, bool strict) {
		std::array<size_t, 5> key = {a, i, b, j, strict};
		auto cached = comparisons.find(key);
		if (cached != comparisons.end()) {
			return cached->second;
		}
		z3::Bool result = compare(lists[a][i].utilities, lists[b][j].utilities, player, strict);
		comparisons.emplace(key, result);
		return result;
	};

	std::vector<DomCandidate> result;
	// the candidate picked for every action, enumerated like an odometer
	std::vector<size_t> picked(actions, 0);
	while (true) {
		std::vector<z3::Bool> constraints;
		for (size_t a = 0; a < actions; a++) {
			constraints.push_back(lists[a][picked[a]].constraint);
		}
		z3::Bool picked_constraint = all_of(constraints);

		if (!picked_constraint.is(z3::Bool(false))) {
			// a is a best choice: at least as good as every other action (Geq_p(U_a, U_a) holds anyway)
			std::vector<z3::Bool> best(actions);
			for (size_t a = 0; a < actions; a++) {
				std::vector<z3::Bool> conjuncts;
				for (size_t b = 0; b < actions; b++) {
					if (b != a) {
						conjuncts.push_back(compare_candidates(a, picked[a], b, picked[b], false));
					}
				}
				best[a] = normalise(context, all_of(conjuncts));
			}

			auto add = [&](uint64_t set, const z3::Bool &formula) {
				z3::Bool constraint = normalise(context, formula);
				if (constraint.is(z3::Bool(false))) {
					return;
				}
				DomCandidate candidate {constraint, {}};
				for (size_t a = 0; a < actions; a++) {
					if (set >> a & 1) {
						const std::vector<LiveUtility> &utilities = lists[a][picked[a]].utilities;
						candidate.utilities.insert(candidate.utilities.end(), utilities.begin(), utilities.end());
					}
				}
				add_candidate(result, std::move(candidate));
			};

			if (unknown.empty()) {
				// everything known: B = {a, b} would need a strictly better than b and b strictly better than a
				// at the same values, so only singletons can be minimal; results are only used under IC ∧ cond
				for (size_t a = 0; a < actions; a++) {
					add(1ull << a, all_of({picked_constraint, best[a]}));
				}
			} else {
				for (uint64_t set = 1; set < (1ull << actions); set++) {
					std::vector<z3::Bool> some_best;
					for (size_t a = 0; a < actions; a++) {
						if (set >> a & 1) {
							some_best.push_back(best[a]);
						}
					}
					z3::Bool hit = normalise(context, forall(unknown, implies(context, any_of(some_best))));
					if (hit.is(z3::Bool(false))) {
						continue;
					}

					// minimal: every a in B is the only best choice in B for some values of the unknowns
					std::vector<z3::Bool> minimal;
					if (some_best.size() > 1) {
						for (size_t a = 0; a < actions && !(minimal.size() && minimal.back().is(z3::Bool(false))); a++) {
							if (!(set >> a & 1)) {
								continue;
							}
							std::vector<z3::Bool> conjuncts = {context, best[a]};
							for (size_t b = 0; b < actions; b++) {
								if (b != a && (set >> b & 1)) {
									conjuncts.push_back(compare_candidates(a, picked[a], b, picked[b], true));
								}
							}
							minimal.push_back(normalise(context, exists(unknown, all_of(conjuncts))));
						}
					}
					add(set, all_of({picked_constraint, hit, all_of(minimal)}));
				}
			}
		}

		size_t a = 0;
		while (a < actions && ++picked[a] == lists[a].size()) {
			picked[a++] = 0;
		}
		if (a == actions) {
			break;
		}
	}
	return result;
}

// a sequence of candidates of a condition edge c (ComputeDom at a condition node), read as a priority list:
// for values of the revealed constants, the first candidate whose constraint holds is selected;
// `covered` is ∀ revealed (IC ∧ cond ∧ c → some candidate holds), `utilities` the utilities of the candidates
// with liveness condition c ∧ φ_k ∧ ¬φ_j (j < k) ∧ c_u
struct CandidateSequence {
	z3::Bool covered;
	std::vector<LiveUtility> utilities;
};

// the sequences of pairwise distinct candidates in `list` for condition edge `condition` whose `covered` is satisfiable,
// leaving out sequences equivalent to one that is kept: with a candidate that is never selected,
// or with adjacent candidates whose constraints never hold at once in decreasing order (swapping them changes nothing)
static std::vector<CandidateSequence> condition_sequences(const std::vector<DomCandidate> &list, const z3::Bool &ic, const z3::Bool &cond,
		const z3::Bool &condition, const std::vector<z3::Real> &revealed) {
	const z3::Bool context = all_of({ic, cond});
	const z3::Bool edge_context = all_of({ic, cond, condition});
	// as in ComputeCWI: results are only used under IC ∧ cond, so they are only needed in the premise if something is quantified
	const z3::Bool premise = revealed.empty() ? condition : edge_context;

	// whether the constraints of candidates i and j can hold at once, computed once
	std::map<std::pair<size_t, size_t>, bool> overlapping;
	auto overlap = [&](size_t i, size_t j) {
		auto key = std::make_pair(std::min(i, j), std::max(i, j));
		auto cached = overlapping.find(key);
		if (cached != overlapping.end()) {
			return cached->second;
		}
		bool result = maybe_satisfiable(edge_context, all_of({list[i].constraint, list[j].constraint}));
		overlapping.emplace(key, result);
		return result;
	};

	std::vector<CandidateSequence> sequences;
	std::vector<size_t> sequence;
	std::vector<bool> used(list.size(), false);
	// the constraints of the candidates in `sequence` and the utilities with their liveness conditions so far
	std::vector<z3::Bool> earlier;
	std::vector<LiveUtility> utilities;

	auto extend = [&](auto &extend) -> void {
		z3::Bool covered = normalise(context, forall(revealed, implies(premise, any_of(earlier))));
		if (!covered.is(z3::Bool(false))) {
			sequences.push_back({covered, utilities});
		}
		z3::Bool none_earlier = negate(any_of(earlier));
		for (size_t next = 0; next < list.size(); next++) {
			if (used[next] || (!sequence.empty() && sequence.back() > next && !overlap(sequence.back(), next))) {
				continue;
			}
			// under the edge's context, as it is only used together with the condition of the edge
			z3::Bool selected = normalise(edge_context, all_of({list[next].constraint, none_earlier}));
			// never selected after the candidates so far: the sequence without it is the same
			if (selected.is(z3::Bool(false))) {
				continue;
			}
			size_t utilities_before = utilities.size();
			for (const LiveUtility &utility : list[next].utilities) {
				z3::Bool live = normalise(edge_context, all_of({selected, utility.live}));
				if (!live.is(z3::Bool(false))) {
					utilities.push_back({utility.utility, all_of({condition, live})});
				}
			}
			used[next] = true;
			sequence.push_back(next);
			earlier.push_back(list[next].constraint);
			extend(extend);
			earlier.pop_back();
			sequence.pop_back();
			used[next] = false;
			utilities.erase(utilities.begin() + utilities_before, utilities.end());
		}
	};
	extend(extend);
	return sequences;
}

// ComputeDom at a condition node: a sequence of candidates for every condition edge, which together have to cover
// all values of the revealed constants
static std::vector<DomCandidate> condition_dom(const Input &input, const ConditionNode &condition_node, const z3::Bool &ic,
		const z3::Bool &cond, const std::unordered_set<std::string> &known_unknowns) {
	// below, the unknowns revealed here are known
	std::unordered_set<std::string> known_below = known_unknowns;
	std::vector<z3::Real> revealed_here;
	for (const std::string &name : condition_node.revealed) {
		known_below.insert(name);
		revealed_here.push_back(z3::Real::constant(name));
	}

	std::vector<std::vector<CandidateSequence>> sequences;
	for (const ConditionChoice &choice : condition_node.conditions) {
		z3::Bool child_cond = all_of({cond, choice.condition});
		std::vector<DomCandidate> list = computeDom(input, choice.node.get(), ic, child_cond, known_below);
		sequences.push_back(condition_sequences(list, ic, cond, choice.condition, revealed_here));
		if (sequences.back().empty()) {
			return {};
		}
	}

	const z3::Bool context = all_of({ic, cond});
	std::vector<DomCandidate> result;
	// the sequence picked for every condition edge, enumerated like an odometer
	std::vector<size_t> picked(sequences.size(), 0);
	while (true) {
		std::vector<z3::Bool> covered;
		DomCandidate candidate;
		for (size_t c = 0; c < sequences.size(); c++) {
			const CandidateSequence &sequence = sequences[c][picked[c]];
			covered.push_back(sequence.covered);
			candidate.utilities.insert(candidate.utilities.end(), sequence.utilities.begin(), sequence.utilities.end());
		}
		candidate.constraint = normalise(context, all_of(covered));
		if (!candidate.constraint.is(z3::Bool(false))) {
			add_candidate(result, std::move(candidate));
		}

		size_t c = 0;
		while (c < sequences.size() && ++picked[c] == sequences[c].size()) {
			picked[c++] = 0;
		}
		if (c == sequences.size()) {
			break;
		}
	}
	return result;
}

std::vector<DomCandidate> computeDom(const Input &input, const Node *node, const z3::Bool &ic, const z3::Bool &cond,
		const std::unordered_set<std::string> &known_unknowns) {
	if (node->is_leaf()) {
		return {{z3::Bool(true), {{&node->leaf().utilities, z3::Bool(true)}}}};
	}
	if (node->is_subtree()) {
		return get_dom_cases(node->subtree());
	}
	if (node->is_condition_node()) {
		return condition_dom(input, node->condition_node(), ic, cond, known_unknowns);
	}
	return branch_dom(input, node->branch(), ic, cond, known_unknowns);
}

z3::Bool computeCPR(const Input &input, const Node *node, const UtilityTuplesSet &ustar, const z3::Bool &ic, const z3::Bool &cond,
		const std::unordered_set<std::string> &known_unknowns) {
	if (node->is_leaf()) {
		return z3::Bool(true);
	}

	if (node->is_subtree()) {
		return get_pr_case(node->subtree());
	}

	if (node->is_condition_node()) {
		// whichever condition holds, for all values of the unknowns revealed here
		const ConditionNode &condition_node = node->condition_node();
		std::unordered_set<std::string> known_below = known_unknowns;
		std::vector<z3::Real> revealed_here;
		for (const std::string &name : condition_node.revealed) {
			known_below.insert(name);
			revealed_here.push_back(z3::Real::constant(name));
		}
		std::vector<z3::Bool> conjuncts;
		for (const ConditionChoice &choice : condition_node.conditions) {
			z3::Bool child = computeCPR(input, choice.node.get(), ustar, ic, all_of({cond, choice.condition}), known_below);
			if (child.is(z3::Bool(true))) {
				continue;
			}
			// as in ComputeCWI: `ic` and `cond` are only needed in the premise if something is quantified
			z3::Bool premise = revealed_here.empty() ? choice.condition : all_of({ic, cond, choice.condition});
			conjuncts.push_back(z3::Bool::forall(revealed_here, implies(premise, child)));
		}
		return all_of(conjuncts);
	}

	// along the honest history: the honest child is practical, and for every deviation,
	// some rationalizable utility set is never better for the current player than the honest utility
	const Branch &branch = node->branch();
	const unsigned player = branch.player;
	const std::vector<z3::Real> unknown = still_unknown(input, known_unknowns);
	const z3::Bool context = all_of({ic, cond});
	const z3::Bool premise = unknown.empty() ? z3::Bool(true) : context;
	const Choice &honest_choice = branch.get_honest_child();

	std::vector<z3::Bool> conjuncts = {computeCPR(input, honest_choice.node.get(), ustar, ic, cond, known_unknowns)};
	for (const Choice &choice : branch.choices) {
		// as soon as one deviation is profitable, the result is false
		if (conjuncts.back().is(z3::Bool(false))) {
			break;
		}
		if (&choice == &honest_choice) {
			continue;
		}
		std::vector<z3::Bool> disjuncts;
		for (const DomCandidate &candidate : computeDom(input, choice.node.get(), ic, cond, known_unknowns)) {
			std::vector<z3::Bool> not_better;
			for (const LiveUtility &utility : candidate.utilities) {
				for (const UtilityTuple &honest : ustar) {
					z3::Bool comparison = (honest[player] >= (*utility.utility)[player]).simplify();
					not_better.push_back(implies(all_of({utility.live, honest.condition}), comparison));
				}
			}
			z3::Bool unprofitable = forall(unknown, implies(premise, all_of(not_better)));
			disjuncts.push_back(normalise(context, all_of({candidate.constraint, unprofitable})));
			if (disjuncts.back().is(z3::Bool(true))) {
				break;
			}
		}
		conjuncts.push_back(any_of(disjuncts));
	}
	return all_of(conjuncts);
}
