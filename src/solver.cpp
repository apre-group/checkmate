#include <algorithm>
#include <bitset>
#include <iostream>

#include "solver.hpp"
#include "utils.hpp"

// stack frame in simulated recursion over a tree
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

void Solver::solve(z3::Bool property, z3::Bool honest_history) {
	z3::Solver::Frame pop_history = solver.push();
	solver.assert_(honest_history);

	std::vector<z3::Bool> case_;
	std::vector<bool> finished;
	while(true) {
		z3::Solver::Frame pop_property = solver.push();
		z3::Bool with_split = z3::Bool::conjunction(case_).implies(property);
		z3::Bool quantified = z3::Bool::forall(input.quantify, with_split);
		solver.assert_(quantified);

		std::cout << "case: " << case_ << std::endl;
		if(solver.solve(assumptions) == z3::Result::SAT) {
			std::cout << "solved" << std::endl;
			while(!finished.empty()) {
				std::vector<bool>::reference top = finished.back();
				if(top) {
					case_.pop_back();
					finished.pop_back();
					continue;
				}
				top = true;
				z3::Bool &last_split = case_.back();
				last_split = !last_split;
				break;
			}
			if(finished.empty()) {
				std::cout << "done" << std::endl;
				return;
			}
			continue;
		}

		std::vector<z3::Bool> core = solver.unsat_core();
		z3::Bool split;
		for(auto label : core) {
			z3::Bool expr = label2expr[label];
			if(std::find_if(
				case_.begin(),
				case_.end(),
				[expr](z3::Bool split) { return split.is(expr) || split.is(!expr); }
			) != case_.end())
				continue;
			split = expr;
			break;
		}
		if(split.null()) {
			std::cout << "no more splits" << std::endl;
			return;
		}
		std::cout << "split: " << split << std::endl;
		case_.push_back(split);
		finished.push_back(false);
	}
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
					? label(utility.real >= z3::Real::ZERO)
					: label_geq(utility, {z3::Real::ZERO, z3::Real::ZERO});
				conjuncts.push_back(player_decisions.null() ? comparison : player_decisions.implies(comparison));
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
		solve(property, input.honest_histories[history]);
	}
}

template void Solver::weak_immunity<false>();
template void Solver::weak_immunity<true>();

void Solver::collusion_resilience() {
	assert(input.players.size() < Input::MAX_PLAYERS);

	z3::Bool constraint = input.initial_constraint && input.collusion_resilience_constraint;
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
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
					z3::Bool comparison = label_geq(honest_total, total);
					conjuncts.push_back(nongroup_decisions.null() ? comparison : nongroup_decisions.implies(comparison));
					continue;
				}

				stack.emplace_back(choice.node->branch(), nongroup_decisions);
			}
		}

		z3::Bool property = constraint.implies(z3::Bool::conjunction(conjuncts));
		std::cout << "honest history #" << history + 1 << std::endl;
		solve(property, input.honest_histories[history]);
	}
}

void Solver::practicality() {
	// possible routes from an _action_ to a leaf
	struct Routes {
		// possibilities after the action
		std::vector<z3::Bool> disjuncts;
		// if not null, the disjunction of `disjuncts` or "true" for leaves
		z3::Bool combined;
	};

	// routes that yield a certain utility
	using UtilityMap = std::unordered_map<Utility, Routes>;
	// utility map per-player
	using PlayerUtilities = std::vector<UtilityMap>;
	// utility map per-player per-action
	using PlayerUtilitiesByAction = std::vector<PlayerUtilities>;

	std::vector<Frame<PlayerUtilitiesByAction>> stack;
	stack.emplace_back(*input.root);
	std::vector<z3::Bool> conjuncts;
	while(true) {
		Frame<PlayerUtilitiesByAction> &current = stack.back();

		// finish processing a branch after all choices have been recursed into
		if(current.choices == current.branch.choices.end()) {
			// `current` will be invalidated shortly, move stuff out of the call stack
			PlayerUtilitiesByAction player_utilities_by_action = std::move(current.data);
			const Branch &current_branch = current.branch;

			// fill in the `combined` field of `Routes`
			for(PlayerUtilities &player_utilities : player_utilities_by_action)
				for(UtilityMap &map : player_utilities)
					for(auto &pair : map) {
						Routes &routes = pair.second;
						if(routes.combined.null())
							routes.combined = z3::Bool::disjunction(routes.disjuncts);
					}

			// for each possible action a in a branch...
			for(unsigned action = 0; action < current_branch.choices.size(); action++) {
				const UtilityMap &utilities_action = player_utilities_by_action[action][current_branch.player];
				z3::Bool action_variable = current_branch.choices[action].action.variable;
				// for other possible actions a' in a branch...
				for(unsigned other = 0; other < current_branch.choices.size(); other++) {
					if(action == other)
						continue;

					const UtilityMap &utilities_other = player_utilities_by_action[other][current_branch.player];
					// for each utility u reachable from a under condition c...
					for(const auto &action_pair : utilities_action) {
						Utility action_utility = action_pair.first;
						z3::Bool action_condition = action_pair.second.combined;
						// for each utility u' reachable from a' under condition c'...
						for(const auto &other_pair: utilities_other) {
							Utility other_utility = other_pair.first;
							z3::Bool other_condition = other_pair.second.combined;
							// if a and c and c'...
							z3::Bool conjunction = action_variable && action_condition && other_condition;
							// ...then u is at least as good as u', otherwise we'd switch
							z3::Bool comparison = label_geq(action_utility, other_utility);
							conjuncts.push_back(conjunction.implies(comparison));
						}
					}
				}
			}

			// `current` invalidated here
			stack.pop_back();
			if(stack.empty())
				break;

			// put all of our routes into the parent
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
						z3::Bool condition = pair.second.combined;
						parent_utility_map[utility].disjuncts.push_back(action && condition);
					}
				}
			}
			continue;
		}

		PlayerUtilitiesByAction &player_utilities_by_action = current.data;
		const Choice &choice = *current.choices++;
		// the next choice is a leaf, do all the usual logic
		if(choice.node->is_leaf()) {
			const Leaf &leaf = choice.node->leaf();
			player_utilities_by_action.emplace_back(leaf.utilities.size());
			PlayerUtilities &player_utilities = player_utilities_by_action.back();
			for(unsigned player = 0; player < leaf.utilities.size(); player++)
				player_utilities[player][leaf.utilities[player]].combined = z3::Bool::TRUE;
			continue;
		}
		stack.emplace_back(choice.node->branch());
	}

	z3::Bool constraint = input.initial_constraint && input.practicality_constraint;
	z3::Bool property = constraint.implies(z3::Bool::conjunction(conjuncts));
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		solve(property, input.honest_histories[history]);
	}
}

z3::Bool Solver::label(z3::Bool expr) {
	z3::Bool &cached_label = expr2label[expr];
	if(!cached_label.null())
		return cached_label.implies(expr);

	z3::Bool label = z3::Bool::fresh();
	assumptions.push_back(label);
	label2expr[label] = expr;
	cached_label = label;
	return label.implies(expr);
}

z3::Bool Solver::label_geq(Utility left, Utility right) {
	if(left.real.is(right.real))
		return label(left.infinitesimal >= right.infinitesimal);
	if(left.infinitesimal.is(right.infinitesimal))
		return label(left.real >= right.real);
	return label(left.real > right.real) ||
		(label(left.real == right.real) && label(left.infinitesimal >= right.infinitesimal));

}
