#include "property_checks.hpp"

// imported from the cefg branch (c9c6e6f); wrapped in namespace cefg next to the EFG engine in src/
namespace cefg {

// GetWiCase: the constraints under which `subtree` is weak(er) immune for `player`, as computed in subtree mode
// (a disjunction of cases, each a conjunction), taken from the entry of the honest history inside the subtree
// considered in the current run if the subtree is along the honest history, and from the entry without honest history otherwise
static z3::Bool get_wi_case(const Input &input, const Subtree &subtree, unsigned player, bool weaker) {
	const SubtreeEntry *entry = nullptr;
	if (subtree.honest) {
		entry = subtree.honest_entry;
	} else {
		for (const SubtreeEntry &candidate : subtree.entries) {
			// off honest, there has to be an entry without honest history or utility
			if (std::holds_alternative<std::monostate>(candidate.key)) {
				entry = &candidate;
				break;
			}
		}
	}
	if (!entry) {
		std::cerr << "checkmate: subtree " << (subtree.honest ? "along" : "off") << " the honest history has no results "
			<< (subtree.honest ? "for the current honest history it" : "without honest history") << std::endl;
		std::exit(EXIT_FAILURE);
	}

	const std::vector<SubtreeResult> &results = weaker ? entry->results.weaker_immunity : entry->results.weak_immunity;
	for (const SubtreeResult &result : results) {
		if (result.player_group.size() == 1 && result.player_group[0] == input.players[player]) {
			std::vector<z3::Bool> cases;
			for (const std::vector<z3::Bool> &satisfied_case : result.satisfied_in_case) {
				cases.push_back(all_of(satisfied_case));
			}
			return any_of(cases);
		}
	}
	std::cerr << "checkmate: subtree has no " << (weaker ? "weaker" : "weak") << " immunity result for player "
		<< input.players[player] << std::endl;
	std::exit(EXIT_FAILURE);
}

// Algorithm 1 (ComputeCWI) on the subtree rooted at `node`, with the honest history currently marked in the tree
// and `ic` the initial constraints
z3::Bool computeCWI(const Input &input, const Node *node, const z3::Bool &ic, unsigned player, bool weaker,
		const std::unordered_set<std::string> &known_unknowns) {
	if (node->is_leaf()) {
		const Utility &utility = node->leaf().utilities[player];
		return weaker ? utility.real >= z3::Real::ZERO : utility >= Utility {z3::Real::ZERO, z3::Real::ZERO};
	}

	if (node->is_subtree()) {
		return get_wi_case(input, node->subtree(), player, weaker);
	}

	if (node->is_condition_node()) {
		// whichever condition holds, for all values of the constants unknown here: the ones revealed here, and also
		// the ones that stay unknown, as `ic` may relate them to the revealed ones; quantifying only the revealed ones
		// would leave the others free in the result, so that a choice above could depend on them
		const ConditionNode &condition_node = node->condition_node();
		// if nothing is revealed here, the constants still unknown occur neither in the conditions nor in the results
		// below (leaves only use known constants), so quantifying them would not change anything
		const std::vector<z3::Real> unknown = condition_node.revealed.empty()
			? std::vector<z3::Real>() : still_unknown(input, known_unknowns);
		// below, the unknowns revealed here are known
		std::unordered_set<std::string> known_below = known_unknowns;
		for (const std::string &name : condition_node.revealed) {
			known_below.insert(name);
		}
		std::vector<z3::Bool> conjuncts;
		for (const ConditionChoice &choice : condition_node.conditions) {
			z3::Bool child = computeCWI(input, choice.node.get(), ic, player, weaker, known_below);
			if (child.is(z3::Bool(true))) {
				continue;
			}
			// results are only ever used under `ic`, so without unknowns `ic` can be left out of the premise
			z3::Bool premise = unknown.empty() ? choice.condition : ic && choice.condition;
			conjuncts.push_back(z3::Bool::forall(unknown, premise.implies(child)));
		}
		return all_of(conjuncts);
	}

	const Branch &branch = node->branch();
	// another player's choice: weak immune whatever they choose
	if (branch.player != player) {
		std::vector<z3::Bool> conjuncts;
		for (const Choice &choice : branch.choices) {
			conjuncts.push_back(computeCWI(input, choice.node.get(), ic, player, weaker, known_unknowns));
		}
		return all_of(conjuncts);
	}
	// our choice along the honest history: we follow it
	if (branch.honest) {
		return computeCWI(input, branch.get_honest_child().node.get(), ic, player, weaker, known_unknowns);
	}
	// our choice off the honest history: we may pick any action that keeps us weak immune
	std::vector<z3::Bool> disjuncts;
	for (const Choice &choice : branch.choices) {
		disjuncts.push_back(computeCWI(input, choice.node.get(), ic, player, weaker, known_unknowns));
	}
	return any_of(disjuncts);
}

} // namespace cefg
