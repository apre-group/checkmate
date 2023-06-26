#include <iostream>

#include "solver.hpp"

Solver::Solver(const Input &input) : input(input) {
	add_action_constraints();
}

void Solver::add_action_constraints() {
	struct State {};
	std::vector<z3::Bool> actions;
	input.root->visit<State>(
		[](State &, const Leaf &) {},
		[&](State &, const Branch &branch) {
			for(const Choice &choice : branch.choices)
				actions.push_back(choice.action.variable);
			solver.assert_(z3::Bool::exactly_one(actions));
			actions.clear();
		},
		[&](State &, const Choice &) {}
	);
}

void Solver::solve(z3::Bool quantified_property) {
	solver.assert_(quantified_property);
	std::cout << solver.solve() << std::endl;
}

template<bool weaker>
void Solver::weak_immunity() {
	struct State {
		State() : player_turn(false) {}
		bool player_turn;
		z3::Bool player_decisions;
	};

	std::vector<z3::Bool> conjuncts;
	for(const Player &player : input.players) {
		input.root->visit<State>(
			[&](State &state, const Leaf &leaf) {
				const PlayerUtility &player_utility = leaf.get_player_utility(player.name);
				z3::Bool comparison = weaker
					? player_utility.utility.real >= z3::Real::ZERO
					: player_utility.utility >= Utility {z3::Real::ZERO, z3::Real::ZERO};
				z3::Bool labelled = label(comparison);
				conjuncts.push_back(state.player_decisions.null() ? labelled : state.player_decisions.implies(labelled));
			},
			[&](State &state, const Branch &branch) {
				state.player_turn = branch.player == player;
			},
			[](State &state, const Choice &choice) {
				if(state.player_turn)
					state.player_decisions = state.player_decisions.null()
						? choice.action.variable
						: (choice.action.variable && state.player_decisions);
			}
		);
	}

	z3::Bool constraint = input.initial_constraint && input.weak_immunity_constraint;
	z3::Bool computed = constraint.implies(z3::Bool::conjunction(conjuncts));
	z3::Bool quantified = z3::Bool::forall(input.quantify, computed);
	for(unsigned i = 0; i < input.honest_histories.size(); i++) {
		std::cout << "honest history #" << i + 1 << std::endl;
		auto pop_honest_history = defer([&] { solver.pop(); });
		solver.push();
		solver.assert_(input.honest_histories[i]);
		solve(quantified);
	}
}

template void Solver::weak_immunity<false>();
template void Solver::weak_immunity<true>();

z3::Bool Solver::label(z3::Bool expr) {
	z3::Bool &cached_label = expr2label[expr.id()];
	if(!cached_label.null())
		return cached_label.implies(expr);

	z3::Bool label = z3::Bool::fresh();
	solver.assert_(label);
	label2expr[label.id()] = expr;
	cached_label = label;
	return label.implies(expr);
}
