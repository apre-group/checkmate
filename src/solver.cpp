#include <bitset>
#include <iostream>

#include "solver.hpp"

template<typename T>
struct Frame {
	template<typename... Args>
	Frame(const Branch &branch, Args &&...args) :
		branch(branch),
		choices(branch.choices.begin()),
		data(args...)
	{}
	const Branch &branch;
	std::vector<Choice>::const_iterator choices;
	T data;
};

Solver::Solver(const Input &input) : input(input) {
	add_action_constraints();
}

void Solver::add_action_constraints() {
	struct Unit {};
	std::vector<Frame<Unit>> stack;
	stack.emplace_back(*input.root);
	while(!stack.empty()) {
		Frame<Unit> &current = stack.back();
		if(current.choices == current.branch.choices.end()) {
			std::vector<z3::Bool> actions;
			for(const Choice &choice : current.branch.choices)
				actions.push_back(choice.action.variable);
			solver.assert_(z3::Bool::exactly_one(actions));
			stack.pop_back();
			continue;
		}
		const Choice &choice = *current.choices++;
		if(choice.node->is_leaf())
			continue;
		stack.emplace_back(choice.node->branch());
	}
}

void Solver::solve(z3::Bool property) {
	z3::Bool quantified = z3::Bool::forall(input.quantify, property);
	solver.assert_(quantified);
	std::cout << solver.solve() << std::endl;
}

template<bool weaker>
void Solver::weak_immunity() {
	std::vector<z3::Bool> conjuncts;

	for(unsigned player = 0; player < input.players.size(); player++) {
		std::vector<Frame<z3::Bool>> stack;
		stack.emplace_back(*input.root);
		while(!stack.empty()) {
			Frame<z3::Bool> &current = stack.back();
			if(current.choices == current.branch.choices.end()) {
				stack.pop_back();
				continue;
			}

			const Choice &choice = *current.choices++;
			z3::Bool player_decisions = current.data;
			if(current.branch.player == player)
				player_decisions = player_decisions.null()
					? choice.action.variable
					: (choice.action.variable && player_decisions);

			if(choice.node->is_leaf()) {
				const Leaf &leaf = choice.node->leaf();
				Utility utility = leaf.utilities[player];
				z3::Bool comparison = weaker
					? utility.real >= z3::Real::ZERO
					: utility >= Utility {z3::Real::ZERO, z3::Real::ZERO};
				z3::Bool labelled = label(comparison);
				conjuncts.push_back(player_decisions.null() ? labelled : player_decisions.implies(labelled));
				continue;
			}

			stack.emplace_back(choice.node->branch(), player_decisions);
		}
	}

	z3::Bool property_constraint = weaker
		? input.weak_immunity_constraint
		: input.weaker_immunity_constraint;
	z3::Bool constraint = input.initial_constraint && property_constraint;
	z3::Bool property = constraint.implies(z3::Bool::conjunction(conjuncts));
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		z3::Solver::Frame pop = solver.push();
		solver.assert_(input.honest_histories[history]);
		solve(property);
	}
}

template void Solver::weak_immunity<false>();
template void Solver::weak_immunity<true>();

void Solver::collusion_resilience() {
	assert(input.players.size() < Input::MAX_PLAYERS);

	z3::Bool constraint = input.initial_constraint && input.collusion_resilience_constraint;
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		const Leaf &honest_leaf = input.honest_history_leaves[history];
		std::vector<z3::Bool> conjuncts;
		// C++ standard mandates that `long long` has at least 64 bits
		for(unsigned long long binary_counter = 1; binary_counter < -1ull >> (64 - input.players.size()); binary_counter++) {
			std::bitset<Input::MAX_PLAYERS> group(binary_counter);
			Utility honest_total {z3::Real::ZERO, z3::Real::ZERO};
			for(size_t player = 0; player < input.players.size(); player++)
				if(group[player])
					honest_total = honest_total + honest_leaf.utilities[player];

			std::vector<Frame<z3::Bool>> stack;
			stack.emplace_back(*input.root);
			while(!stack.empty()) {
				Frame<z3::Bool> &current = stack.back();
				if(current.choices == current.branch.choices.end()) {
					stack.pop_back();
					continue;
				}

				const Choice &choice = *current.choices++;
				z3::Bool nongroup_decisions = current.data;
				if(!group[current.branch.player])
					nongroup_decisions = nongroup_decisions.null()
						? choice.action.variable
						: (choice.action.variable && nongroup_decisions);

				if(choice.node->is_leaf()) {
					const Leaf &leaf = choice.node->leaf();
					Utility total {z3::Real::ZERO, z3::Real::ZERO};
					for(size_t player = 0; player < input.players.size(); player++)
						if(group[player])
							total = total + leaf.utilities[player];
					z3::Bool comparison = honest_total >= total;
					z3::Bool labelled = label(comparison);
					conjuncts.push_back(nongroup_decisions.null() ? labelled : nongroup_decisions.implies(labelled));
					continue;
				}

				stack.emplace_back(choice.node->branch(), nongroup_decisions);
			}
		}
		z3::Bool property = constraint.implies(z3::Bool::conjunction(conjuncts));
		z3::Solver::Frame pop = solver.push();
		solver.assert_(input.honest_histories[history]);
		solve(property);
	}
}

void Solver::practicality() {
	using UtilityMap = std::unordered_map<Utility, std::vector<z3::Bool>>;
	using PlayerUtilities = std::vector<UtilityMap>;
	using PlayerUtilitiesByAction = std::vector<PlayerUtilities>;
	std::vector<Frame<PlayerUtilitiesByAction>> stack;
	stack.emplace_back(*input.root);
	std::vector<z3::Bool> conjuncts;
	while(true) {
		Frame<PlayerUtilitiesByAction> &current = stack.back();
		if(current.choices == current.branch.choices.end()) {
			PlayerUtilitiesByAction player_utilities_by_action = std::move(current.data);
			const Branch &current_branch = current.branch;
			for(PlayerUtilities &player_utilities : player_utilities_by_action)
				for(UtilityMap &map : player_utilities)
					for(auto &pair : map) {
						std::vector<z3::Bool> &disjuncts = pair.second;
						z3::Bool disjunction = z3::Bool::disjunction(disjuncts);
						disjuncts.clear();
						disjuncts.push_back(disjunction);
					}

			for(unsigned choice = 0; choice < current_branch.choices.size(); choice++) {
				const UtilityMap &utilities_action = player_utilities_by_action[choice][current_branch.player];
				z3::Bool action = current_branch.choices[choice].action.variable;
				for(unsigned other = 0; other < current_branch.choices.size(); other++) {
					if(choice == other)
						continue;

					const UtilityMap &utilities_other = player_utilities_by_action[other][current_branch.player];
					for(const auto &choice_pair : utilities_action) {
						Utility choice_utility = choice_pair.first;
						z3::Bool choice_condition = choice_pair.second[0];
						for(const auto &other_pair: utilities_other) {
							Utility other_utility = other_pair.first;
							z3::Bool other_condition = other_pair.second[0];
							z3::Bool conjunction = action && choice_condition && other_condition;
							z3::Bool comparison = choice_utility >= other_utility;
							z3::Bool labelled = label(comparison);
							conjuncts.push_back(conjunction.implies(labelled));
						}
					}
				}
			}

			// `current` invalidated here
			stack.pop_back();
			if(stack.empty())
				break;

			Frame<PlayerUtilitiesByAction> &parent = stack.back();
			PlayerUtilitiesByAction &parent_player_utilities_by_action = parent.data;
			parent_player_utilities_by_action.emplace_back(input.players.size());
			PlayerUtilities &parent_player_utilities = parent_player_utilities_by_action.back();
			for(unsigned choice = 0; choice < current_branch.choices.size(); choice++) {
				const PlayerUtilities &player_utilities = player_utilities_by_action[choice];
				z3::Bool action = current_branch.choices[choice].action.variable;
				for(unsigned player = 0; player < player_utilities.size(); player++) {
					const UtilityMap &utility_map = player_utilities[player];
					UtilityMap &parent_utility_map = parent_player_utilities[player];
					for(const auto &pair : utility_map) {
						Utility utility = pair.first;
						z3::Bool condition = pair.second[0];
						parent_utility_map[utility].push_back(action && condition);
					}
				}
			}
			continue;
		}

		PlayerUtilitiesByAction &player_utilities_by_action = current.data;
		const Choice &choice = *current.choices++;
		if(choice.node->is_leaf()) {
			const Leaf &leaf = choice.node->leaf();
			player_utilities_by_action.emplace_back(leaf.utilities.size());
			PlayerUtilities &player_utilities = player_utilities_by_action.back();
			for(unsigned player = 0; player < leaf.utilities.size(); player++)
				player_utilities[player][leaf.utilities[player]].push_back(z3::Bool::conjunction(std::vector<z3::Bool>()));
			continue;
		}
		stack.emplace_back(choice.node->branch());
	}

	z3::Bool constraint = input.initial_constraint && input.practicality_constraint;
	z3::Bool property = constraint.implies(z3::Bool::conjunction(conjuncts));
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		z3::Solver::Frame pop = solver.push();
		solver.assert_(input.honest_histories[history]);
		solve(property);
	}
}

z3::Bool Solver::label(z3::Bool expr) {
	z3::Bool &cached_label = expr2label[expr];
	if(!cached_label.null())
		return cached_label.implies(expr);

	z3::Bool label = z3::Bool::fresh();
	solver.assert_(label);
	label2expr[label] = expr;
	cached_label = label;
	return label.implies(expr);
}
