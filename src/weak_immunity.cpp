#include <iostream>

#include "weak_immunity.hpp"

WeakImmunity::WeakImmunity(const Input &input) {
	std::vector<z3::Bool> conjuncts;
	for(const Player &player : input.players)
		collect_constraints(conjuncts, input.root, player, nullptr);
	computed = input.weak_immunity_constraint.implies(z3::Bool::conjunction(conjuncts));
}

void WeakImmunity::collect_constraints(std::vector<z3::Bool> &conjuncts, const std::unique_ptr<Node> &input, const Player &player, z3::Bool *previous_player_decisions) {
	if(input->is_leaf()) {
		const Leaf &leaf = input->leaf();
		const PlayerUtility &player_utility = leaf.get_player_utility(player.name);
		z3::Bool comparison = player_utility.utility >= Utility {z3::Real::ZERO, z3::Real::ZERO};
		// weaker immunity would be
		//z3::Bool comparison = player_utility.utility.real >= z3::Real::ZERO;
		conjuncts.push_back(previous_player_decisions ? previous_player_decisions->implies(comparison) : comparison);
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
		collect_constraints(conjuncts, choice.tree, player, with_player_decisions);
	}
}
