#include <algorithm>

#include "property_checks.hpp"

// the group of all players: collusion resilience is not considered against it
static uint64_t all_players(const Input &input) {
	return input.players.size() == 64 ? -1ull : (1ull << input.players.size()) - 1;
}

// the sum of the utilities of the players in `group` (bitset over the players)
static Utility group_utility(const std::vector<Utility> &utilities, uint64_t group) {
	Utility total {z3::Real::ZERO, z3::Real::ZERO};
	for (size_t player = 0; player < utilities.size(); player++) {
		if (group >> player & 1) {
			total = total + utilities[player];
		}
	}
	return total;
}

// are the honest utilities `ustar` and `other` the same: the same number of utility tuples, each with a partner
// with equal utilities and an equivalent condition (under `ic`), as the same formula may be written differently
static bool same_honest_utilities(const UtilityTuplesSet &ustar, const UtilityTuplesSet &other, const z3::Bool &ic) {
	if (ustar.size() != other.size()) {
		return false;
	}
	z3::Solver solver;
	solver.assert_(ic);
	for (const UtilityTuple &tuple : ustar) {
		bool found = false;
		for (const UtilityTuple &candidate : other) {
			if (tuple.size() != candidate.size()) {
				continue;
			}
			std::vector<z3::Bool> equal;
			for (size_t player = 0; player < tuple.size(); player++) {
				equal.push_back(tuple[player] == candidate[player]);
			}
			equal.push_back(tuple.condition.implies(candidate.condition));
			equal.push_back(candidate.condition.implies(tuple.condition));
			if (solver.solve({!z3::conjunction(equal)}) == z3::Result::UNSAT) {
				found = true;
				break;
			}
		}
		if (!found) {
			return false;
		}
	}
	return true;
}

// the entry of `subtree` to take the collusion resilience results from: if the subtree is along the honest history,
// the one of the honest history inside it considered in the current run, otherwise the one for the honest utilities `ustar`
static const SubtreeEntry &subtree_entry(const Subtree &subtree, const UtilityTuplesSet &ustar, const z3::Bool &ic, CrCache &cache) {
	if (subtree.honest) {
		if (!subtree.honest_entry) {
			std::cerr << "checkmate: subtree along the honest history has no results for the current honest history in it" << std::endl;
			std::exit(EXIT_FAILURE);
		}
		return *subtree.honest_entry;
	}

	auto cached = cache.subtree_entries.find(&subtree);
	if (cached != cache.subtree_entries.end()) {
		return *cached->second;
	}
	for (const SubtreeEntry &entry : subtree.entries) {
		if (std::holds_alternative<HonestUtilityElement>(entry.key)
				&& same_honest_utilities(ustar, compute_ustar(std::get<HonestUtilityElement>(entry.key)), ic)) {
			cache.subtree_entries[&subtree] = &entry;
			return entry;
		}
	}
	std::cerr << "checkmate: subtree off the honest history has no collusion resilience results for the current honest utilities" << std::endl;
	std::exit(EXIT_FAILURE);
}

// GetCrCase: the constraints under which `subtree` is collusion resilient against all supergroups of `group`,
// as computed in subtree mode (a disjunction of cases, each a conjunction)
static z3::Bool get_cr_case(const Input &input, const Subtree &subtree, const UtilityTuplesSet &ustar, const z3::Bool &ic, uint64_t group, CrCache &cache) {
	std::vector<std::string> names;
	for (size_t player = 0; player < input.players.size(); player++) {
		if (group >> player & 1) {
			names.push_back(input.players[player]);
		}
	}
	for (const SubtreeResult &result : subtree_entry(subtree, ustar, ic, cache).results.collusion_resilience) {
		std::vector<std::string> result_names = result.player_group;
		std::sort(result_names.begin(), result_names.end());
		if (result_names == names) {
			std::vector<z3::Bool> cases;
			for (const std::vector<z3::Bool> &satisfied_case : result.satisfied_in_case) {
				cases.push_back(all_of(satisfied_case));
			}
			return any_of(cases);
		}
	}
	std::cerr << "checkmate: subtree has no collusion resilience result for group " << names << std::endl;
	std::exit(EXIT_FAILURE);
}

// Algorithm 2 (ComputeCCR) at a leaf: for every honest utility u* compatible with the conditions,
// for all values of the constants still unknown here, every supergroup S of `group` (non-empty, not all players)
// gets at most its honest utility
static z3::Bool leaf_ccr(const Input &input, const Leaf &leaf, const UtilityTuplesSet &ustar, const z3::Bool &ic, const z3::Bool &cond,
		uint64_t group, const std::unordered_set<std::string> &known_unknowns) {
	// the constants still unknown here: unknown at the root and not revealed on the way
	std::vector<z3::Real> unknown;
	for (const std::string &name : input.unknowns) {
		if (!known_unknowns.count(name)) {
			unknown.push_back(z3::Real::constant(name));
		}
	}

	// the supergroups S of `group`: `group` together with every subset of the players outside of it, except all players
	const uint64_t all = all_players(input);
	const uint64_t outside = all & ~group;
	std::vector<z3::Bool> conjuncts;
	for (const UtilityTuple &honest : ustar) {
		std::vector<z3::Bool> comparisons;
		for (uint64_t extra = 0; ; extra = (extra - outside) & outside) {
			uint64_t supergroup = group | extra;
			if (supergroup != 0 && supergroup != all) {
				// simplified, so that comparisons of numbers become true or false and drop out
				comparisons.push_back((group_utility(leaf.utilities, supergroup) <= group_utility(honest.leaf, supergroup)).simplify());
			}
			if (extra == outside) {
				break;
			}
		}
		z3::Bool comparison = all_of(comparisons);
		if (comparison.is(z3::Bool(true))) {
			continue;
		}
		// as in ComputeCWI: results are only used under `ic`, so it is only needed in the premise if something is quantified
		z3::Bool premise = unknown.empty() ? all_of({cond, honest.condition}) : all_of({ic, cond, honest.condition});
		conjuncts.push_back(z3::Bool::forall(unknown, premise.implies(comparison)));
	}
	return all_of(conjuncts);
}

z3::Bool computeCCR(const Input &input, const Node *node, const UtilityTuplesSet &ustar, const z3::Bool &ic, const z3::Bool &cond,
		uint64_t group, CrCache &cache, const std::unordered_set<std::string> &known_unknowns) {
	// no supergroup of all players is a strict subgroup: nothing to check
	if (group == all_players(input)) {
		return z3::Bool(true);
	}

	auto key = std::make_pair(node, group);
	auto cached = cache.results.find(key);
	if (cached != cache.results.end()) {
		return cached->second;
	}

	z3::Bool result;
	if (node->is_leaf()) {
		result = leaf_ccr(input, node->leaf(), ustar, ic, cond, group, known_unknowns);
	} else if (node->is_subtree()) {
		result = get_cr_case(input, node->subtree(), ustar, ic, group, cache);
	} else if (node->is_condition_node()) {
		// whichever condition holds, for all values of the unknowns revealed here (quantified only here);
		// below, they are known: the leaves only quantify over the unknowns that are still unknown there
		const ConditionNode &condition_node = node->condition_node();
		std::unordered_set<std::string> known_below = known_unknowns;
		std::vector<z3::Real> revealed_here;
		for (const std::string &name : condition_node.revealed) {
			known_below.insert(name);
			revealed_here.push_back(z3::Real::constant(name));
		}
		std::vector<z3::Bool> conjuncts;
		for (const ConditionChoice &choice : condition_node.conditions) {
			z3::Bool child = computeCCR(input, choice.node.get(), ustar, ic, all_of({cond, choice.condition}), group, cache, known_below);
			if (child.is(z3::Bool(true))) {
				continue;
			}
			// as in ComputeCWI: `ic` is only needed in the premise if something is quantified
			z3::Bool premise = revealed_here.empty() ? choice.condition : all_of({ic, choice.condition});
			conjuncts.push_back(z3::Bool::forall(revealed_here, premise.implies(child)));
		}
		result = all_of(conjuncts);
	} else {
		const Branch &branch = node->branch();
		const uint64_t with_player = group | (1ull << branch.player);
		auto child_ccr = [&](const Choice &choice, uint64_t child_group) {
			return computeCCR(input, choice.node.get(), ustar, ic, cond, child_group, cache, known_unknowns);
		};

		// note: collusion resilience against all supergroups of `group` implies it against all supergroups of
		// `with_player` (they are a subset), so the result for `group` implies the one for `with_player`
		if (branch.honest) {
			// the honest choice for `group`, every deviation for `group` together with the current player;
			// as soon as one of them is false, so is the result
			const Choice &honest_choice = branch.get_honest_child();
			std::vector<z3::Bool> conjuncts = {child_ccr(honest_choice, group)};
			for (const Choice &choice : branch.choices) {
				if (conjuncts.back().is(z3::Bool(false))) {
					break;
				}
				if (&choice != &honest_choice) {
					conjuncts.push_back(child_ccr(choice, with_player));
				}
			}
			result = all_of(conjuncts);
		} else if (with_player == group) {
			// the current player deviates already: every choice for `group`
			std::vector<z3::Bool> conjuncts;
			for (const Choice &choice : branch.choices) {
				conjuncts.push_back(child_ccr(choice, group));
				if (conjuncts.back().is(z3::Bool(false))) {
					break;
				}
			}
			result = all_of(conjuncts);
		} else {
			// some choice for `group`, every other one for `group` together with the current player:
			// OR_a (R_a AND AND_{a' != a} T_a'), with R the results for `group` and T those for `with_player`;
			// as R_a implies T_a, this is (OR_a R_a) AND (AND_a T_a), and T_a need not be computed if R_a is true;
			// once some R_a is true, so is OR_a R_a, and the remaining R_a are not needed
			std::vector<z3::Bool> for_group;
			for (const Choice &choice : branch.choices) {
				for_group.push_back(child_ccr(choice, group));
				if (for_group.back().is(z3::Bool(true))) {
					break;
				}
			}
			z3::Bool some_choice = any_of(for_group);
			std::vector<z3::Bool> conjuncts = {some_choice};
			// T_a for every choice whose R_a is not true (or not computed), as soon as one of them is false, so is the result
			for (size_t i = 0; i < branch.choices.size() && !some_choice.is(z3::Bool(false)); i++) {
				if (i < for_group.size() && for_group[i].is(z3::Bool(true))) {
					continue;
				}
				conjuncts.push_back(child_ccr(branch.choices[i], with_player));
				if (conjuncts.back().is(z3::Bool(false))) {
					break;
				}
			}
			result = all_of(conjuncts);
		}
	}

	cache.results.emplace(key, result);
	return result;
}
