#include <algorithm>
#include <bitset>
#include <iostream>

#include "property.hpp"
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

// common behaviour between properties
struct Helper {
	Helper(const Input &input) : input(input) {
		solver.assert_(input.action_constraint);
	}

	void solve(z3::Bool property, z3::Bool property_constraint, z3::Bool honest_history) {
		property = (
			z3::Bool::conjunction(trigger_implications) &&
			input.initial_constraint &&
			property_constraint
		).implies(property);
		property = z3::Bool::forall(input.quantify, property);
		solver.assert_(property);

		z3::Solver::Pop pop_history(solver);
		solver.assert_(honest_history);

		z3::Solver minimize_solver;
		minimize_solver.assert_(input.initial_constraint);
		minimize_solver.assert_(property_constraint);

		std::vector<bool> triggered(triggers.size());
		std::vector<z3::Bool> case_;
		std::vector<bool> finished;
		while(true) {
			z3::Solver::Pop pop_triggers(solver);
			for(unsigned i = 0; i < triggered.size(); i++)
				solver.assert_(triggered[i] ? triggers[i] : !triggers[i]);

			std::cout << "case: " << case_ << std::endl;
			std::vector<z3::Bool> dummy;
			if(solver.solve(dummy) == z3::Result::SAT) {
				std::cout << "solved" << std::endl;
				while(!finished.empty()) {
					std::vector<bool>::reference top = finished.back();
					z3::Bool &last_split = case_.back();
					unsigned trigger_index = expr2trigger[last_split];
					if(top) {
						case_.pop_back();
						finished.pop_back();
						triggered[trigger_index] = false;
						continue;
					}
					top = true;
					triggered[trigger_index] = false;
					triggered[trigger_index + 1] = true;
					last_split = !last_split;
					break;
				}
				if(finished.empty()) {
					std::cout << "done" << std::endl;
					return;
				}
				continue;
			}
			std::cout << "failed, trying split" << std::endl;

			std::vector<z3::Bool> core = solver.unsat_core();
			z3::Bool split;
			for(auto label : core) {
				decltype(label2expr)::iterator found(label2expr.find(label));
				if(found == label2expr.end())
					continue;
				z3::Bool expr = found->second;

				if(minimize_solver.solve(case_, expr) == z3::Result::UNSAT || minimize_solver.solve(case_, !expr) == z3::Result::UNSAT)
					continue;

				split = expr;
				break;
			}

			if(split.null()) {
				std::cout << "no more splits, failed" << std::endl;
				return;
			}

			std::cout << "split: " << split << std::endl;
			case_.push_back(split);
			triggered[expr2trigger[split]] = true;
			finished.push_back(false);
		}
	}

	// produce a fresh (or cached) label for `expr` and return `label => expr`
	z3::Bool label(z3::Bool expr) {
		z3::Bool &cached_label = expr2label[expr];
		if(!cached_label.null())
			return cached_label.implies(expr);

		z3::Bool label = z3::Bool::fresh();
		solver.assert_and_track(label);
		label2expr[label] = expr;
		cached_label = label;
		expr2trigger[expr] = triggers.size();
		expr2trigger[!expr] = triggers.size() + 1;
		z3::Bool positive = z3::Bool::fresh();
		z3::Bool negative = z3::Bool::fresh();
		triggers.push_back(positive);
		triggers.push_back(negative);
		trigger_implications.push_back(positive.implies(expr));
		trigger_implications.push_back(negative.implies(!expr));
		return label.implies(expr);
	}

	// produce a labelled version of `left >= right`
	z3::Bool label_geq(Utility left, Utility right) {
		if(left.real.is(right.real))
			return label(left.infinitesimal >= right.infinitesimal);
		if(left.infinitesimal.is(right.infinitesimal))
			return label(left.real >= right.real);
		return label(left.real > right.real) ||
			(label(left.real == right.real) && label(left.infinitesimal >= right.infinitesimal));
	}

	// parsed input
	const Input &input;

	// underlying Z3 solver
	z3::Solver solver;

	// label-to-expression map
	std::unordered_map<z3::Bool, z3::Bool> label2expr;
	// expression-to-label map
	std::unordered_map<z3::Bool, z3::Bool> expr2label;

	// expr-to-trigger map
	std::unordered_map<z3::Bool, unsigned> expr2trigger;
	// list of trigger booleans
	std::vector<z3::Bool> triggers;
	// trigger implications
	std::vector<z3::Bool> trigger_implications;
};

template<bool weaker>
void weak_immunity(const Input &input) {
	Helper helper(input);
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
					? helper.label(utility.real >= z3::Real::ZERO)
					: helper.label_geq(utility, {z3::Real::ZERO, z3::Real::ZERO});
				conjuncts.push_back(player_decisions.null() ? comparison : player_decisions.implies(comparison));
				continue;
			}

			stack.emplace_back(choice.node->branch(), player_decisions);
		}
	}

	z3::Bool property_constraint = weaker
		? input.weak_immunity_constraint
		: input.weaker_immunity_constraint;
	z3::Bool property = z3::Bool::conjunction(conjuncts);
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		helper.solve(property, property_constraint, input.honest_histories[history]);
	}
}

template void weak_immunity<false>(const Input &);
template void weak_immunity<true>(const Input &);

void collusion_resilience(const Input &input) {
	assert(input.players.size() < Input::MAX_PLAYERS);

	Helper helper(input);
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
					z3::Bool comparison = helper.label_geq(honest_total, total);
					conjuncts.push_back(nongroup_decisions.null() ? comparison : nongroup_decisions.implies(comparison));
					continue;
				}

				stack.emplace_back(choice.node->branch(), nongroup_decisions);
			}
		}

		z3::Bool property = z3::Bool::conjunction(conjuncts);
		std::cout << "honest history #" << history + 1 << std::endl;
		helper.solve(property, input.collusion_resilience_constraint, input.honest_histories[history]);
	}
}

void practicality(const Input &input) {
	Helper helper(input);

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
							z3::Bool comparison = helper.label_geq(action_utility, other_utility);
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

	z3::Bool property = z3::Bool::conjunction(conjuncts);
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		helper.solve(property, input.practicality_constraint, input.honest_histories[history]);
	}
}
