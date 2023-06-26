#include <bitset>
#include <iostream>

#include "solver.hpp"

const size_t MAX_PLAYERS = 64;

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

void Solver::solve(z3::Bool property) {
	z3::Bool quantified = z3::Bool::forall(input.quantify, property);
	solver.assert_(quantified);
	std::cout << solver.solve() << std::endl;
}

template<bool weaker>
void Solver::weak_immunity() {
	struct State {
		bool player_turn;
		z3::Bool player_decisions;
	};

	std::vector<z3::Bool> conjuncts;
	for(unsigned player = 0; player < input.players.size(); player++)
		input.root->visit<State>(
			[&](State &state, const Leaf &leaf) {
				Utility utility = leaf.utilities[player];
				z3::Bool comparison = weaker
					? utility.real >= z3::Real::ZERO
					: utility >= Utility {z3::Real::ZERO, z3::Real::ZERO};
				z3::Bool labelled = label(comparison);
				conjuncts.push_back(state.player_decisions.null() ? labelled : state.player_decisions.implies(labelled));
			},
			[&](State &state, const Branch &branch) { state.player_turn = branch.player == player; },
			[](State &state, const Choice &choice) {
				if(state.player_turn)
					state.player_decisions = state.player_decisions.null()
						? choice.action.variable
						: (choice.action.variable && state.player_decisions);
			}
		);

	z3::Bool property_constraint = weaker
		? input.weak_immunity_constraint
		: input.weaker_immunity_constraint;
	z3::Bool constraint = input.initial_constraint && property_constraint;
	z3::Bool property = constraint.implies(z3::Bool::conjunction(conjuncts));
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		auto pop = solver.push();
		solver.assert_(input.honest_histories[history]);
		solve(property);
	}
}

template void Solver::weak_immunity<false>();
template void Solver::weak_immunity<true>();

void Solver::collusion_resilience() {
	if(input.players.size() > MAX_PLAYERS)
		throw std::runtime_error("more than 64 players means a very large powerset");

	z3::Bool constraint = input.initial_constraint && input.collusion_resilience_constraint;
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		auto pop = solver.push();
		solver.assert_(input.honest_histories[history]);

		struct State {
			bool group_turn;
			z3::Bool nongroup_decisions;
		};
		const Leaf &honest_leaf = input.honest_history_leaves[history];
		std::vector<z3::Bool> conjuncts;
		// C++ standard mandates that `long long` has at least 64 bits
		for(unsigned long long binary_counter = 1; binary_counter < (1ull << input.players.size()) - 1; binary_counter++) {
			std::bitset<MAX_PLAYERS> group(binary_counter);
			Utility honest_total {z3::Real::ZERO, z3::Real::ZERO};
			for(size_t player = 0; player < input.players.size(); player++)
				if(group[player])
					honest_total = honest_total + honest_leaf.utilities[player];

			input.root->visit<State>(
				[&](State &state, const Leaf &leaf) {
					Utility total {z3::Real::ZERO, z3::Real::ZERO};
					for(size_t player = 0; player < input.players.size(); player++)
						if(group[player])
							total = total + leaf.utilities[player];
					z3::Bool comparison = honest_total >= total;
					z3::Bool labelled = label(comparison);
					conjuncts.push_back(state.nongroup_decisions.null() ? labelled : state.nongroup_decisions.implies(labelled));
				},
				[&](State &state, const Branch &branch) { state.group_turn = group[branch.player]; },
				[](State &state, const Choice &choice) {
					if(!state.group_turn)
						state.nongroup_decisions = state.nongroup_decisions.null()
							? choice.action.variable
							: (choice.action.variable && state.nongroup_decisions);
				}
			);
		}

		z3::Bool property = constraint.implies(z3::Bool::conjunction(conjuncts));
		solve(property);
	}
}

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
