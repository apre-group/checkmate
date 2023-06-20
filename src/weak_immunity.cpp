#include <iostream>

#include "weak_immunity.hpp"

template<bool weaker>
static void collect_constraints(
	Labels &labels,
	std::vector<z3::Bool> &conjuncts,
	const std::unique_ptr<Node> &input,
	const Player &player,
	z3::Bool *previous_player_decisions
) {
	if(input->is_leaf()) {
		const Leaf &leaf = input->leaf();
		const PlayerUtility &player_utility = leaf.get_player_utility(player.name);
		z3::Bool comparison = weaker
			? player_utility.utility.real >= z3::Real::ZERO
			: player_utility.utility >= Utility {z3::Real::ZERO, z3::Real::ZERO};
		z3::Bool label = labels.label(comparison);
		z3::Bool labelled = label.implies(comparison);
		conjuncts.push_back(previous_player_decisions ? previous_player_decisions->implies(labelled) : labelled);
		return;
	}

	const Branch &branch = input->branch();
	bool player_turn = branch.player == player;
	for(const Choice &choice : branch.choices) {
		z3::Bool player_decision;
		z3::Bool *with_player_decisions = previous_player_decisions;
		if(player_turn) {
			player_decision = previous_player_decisions
				? (choice.action.variable && *previous_player_decisions)
				: choice.action.variable;
			with_player_decisions = &player_decision;
		}
		collect_constraints<weaker>(labels, conjuncts, choice.tree, player, with_player_decisions);
	}
}

template<bool weaker>
z3::Bool weak_immunity(const Input &input, Labels &labels) {
	std::vector<z3::Bool> conjuncts;
	for(const Player &player : input.players)
		collect_constraints<weaker>(labels, conjuncts, input.root, player, nullptr);
	return input.weak_immunity_constraint.implies(z3::Bool::conjunction(conjuncts));
}

template
z3::Bool weak_immunity<false>(const Input &input, Labels &labels);

template
z3::Bool weak_immunity<true>(const Input &input, Labels &labels);
