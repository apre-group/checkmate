#include <algorithm>
#include <bitset>
#include <iostream>
#include <random>

#include "property.hpp"
#include "utils.hpp"
#include "z3++.hpp"

using z3::Bool;
using z3::Solver;

// data for labelling expressions
struct Labels {
public:
	// produce a fresh (or cached) label for `expr` and return `label => expr`
	Bool label(Bool expr) {
		auto &cached_label = expr2label[expr];
		if(!cached_label.null())
			return cached_label.implies(expr);

		auto label = Bool::fresh();
		label2expr[label] = expr;
		cached_label = label;
		expr2trigger[expr] = triggers.size();
		expr2trigger[!expr] = triggers.size() + 1;
		auto positive = Bool::fresh();
		auto negative = Bool::fresh();
		triggers.push_back(positive);
		triggers.push_back(negative);
		trigger_implications.push_back(positive.implies(expr));
		trigger_implications.push_back(negative.implies(!expr));
		return label.implies(expr);
	}

	// produce a labelled version of `left >= right`
	Bool label_geq(Utility left, Utility right) {
		if(left.real.is(right.real))
			return label(left.infinitesimal >= right.infinitesimal);
		if(left.infinitesimal.is(right.infinitesimal))
			return label(left.real >= right.real);
		return label(left.real > right.real) ||
			(label(left.real == right.real) && label(left.infinitesimal >= right.infinitesimal));
	}

	// label-to-expression map
	std::unordered_map<Bool, Bool> label2expr;
	// expression-to-label map
	std::unordered_map<Bool, Bool> expr2label;

	// expr-to-trigger map
	std::unordered_map<Bool, unsigned> expr2trigger;
	// list of trigger booleans
	std::vector<Bool> triggers;
	// trigger implications
	std::vector<Bool> trigger_implications;
};

void solve(const Input &input, const Labels &labels, Bool property, Bool property_constraint, Bool honest_history) {
	property = forall(input.quantify, (
		conjunction(labels.trigger_implications) &&
		input.initial_constraint &&
		property_constraint
	).implies(property));

	Solver solver;
	solver.assert_(input.action_constraint);
	solver.assert_(property);
	solver.assert_(honest_history);
	for(const auto &label : labels.label2expr)
		solver.assert_and_track(label.first);

	Solver minimize_solver;
	minimize_solver.assert_(input.initial_constraint);
	minimize_solver.assert_(property_constraint);

	std::vector<bool> triggered(labels.triggers.size());
	std::vector<Bool> case_;
	std::vector<bool> finished;
	std::minstd_rand prng;
	while(true) {
		Solver::Pop pop_triggers(solver);
		for(unsigned i = 0; i < triggered.size(); i++)
			solver.assert_(triggered[i] ? labels.triggers[i] : !labels.triggers[i]);

		std::cout << "case: " << case_ << std::endl;
		if(solver.solve() == z3::Result::SAT) {
			std::cout << "solved" << std::endl;
			while(!finished.empty()) {
				auto top = finished.back();
				auto &last_split = case_.back();
				auto trigger_index = labels.expr2trigger.at(last_split);
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

		auto core = solver.unsat_core();
		// don't get "stuck" too often
		std::shuffle(core.begin(), core.end(), prng);
		Bool split;
		for(auto label : core) {
			auto expr = labels.label2expr.at(label);
			if(
				minimize_solver.solve(case_, expr) == z3::Result::UNSAT ||
				minimize_solver.solve(case_, !expr) == z3::Result::UNSAT
			)
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
		triggered[labels.expr2trigger.at(split)] = true;
		finished.push_back(false);
	}
}

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

template<bool weaker>
void weak_immunity(const Input &input) {
	Labels labels;
	std::vector<Bool> conjuncts;
	for(unsigned player = 0; player < input.players.size(); player++) {
		std::vector<Frame<Bool>> stack;
		stack.emplace_back(*input.root);
		while(!stack.empty()) {
			auto &current = stack.back();
			if(current.choices == current.branch.choices.end()) {
				stack.pop_back();
				continue;
			}

			const auto &choice = *current.choices++;
			auto player_decisions = current.data;
			if(current.branch.player == player)
				player_decisions = player_decisions.null()
					? choice.action.variable
					: (choice.action.variable && player_decisions);

			if(choice.node->is_leaf()) {
				const auto &leaf = choice.node->leaf();
				auto utility = leaf.utilities[player];
				auto comparison = weaker
					? labels.label(utility.real >= z3::Real::ZERO)
					: labels.label_geq(utility, {z3::Real::ZERO, z3::Real::ZERO});
				conjuncts.push_back(player_decisions.null() ? comparison : player_decisions.implies(comparison));
				continue;
			}

			stack.emplace_back(choice.node->branch(), player_decisions);
		}
	}

	auto property_constraint = weaker
		? input.weak_immunity_constraint
		: input.weaker_immunity_constraint;
	auto property = conjunction(conjuncts);
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		solve(input, labels, property, property_constraint, input.honest_histories[history]);
	}
}

template void weak_immunity<false>(const Input &);
template void weak_immunity<true>(const Input &);

void collusion_resilience(const Input &input) {
	assert(input.players.size() < Input::MAX_PLAYERS);

	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		Labels labels;
		const Leaf &honest_leaf = input.honest_history_leaves[history];
		std::vector<Bool> conjuncts;
		// C++ standard mandates that `long long` has at least 64 bits
		for(unsigned long long binary_counter = 1; binary_counter < -1ull >> (64 - input.players.size()); binary_counter++) {
			std::bitset<Input::MAX_PLAYERS> group(binary_counter);
			Utility honest_total {z3::Real::ZERO, z3::Real::ZERO};
			for(size_t player = 0; player < input.players.size(); player++)
				if(group[player])
					honest_total = honest_total + honest_leaf.utilities[player];

			std::vector<Frame<Bool>> stack;
			stack.emplace_back(*input.root);
			while(!stack.empty()) {
				auto &current = stack.back();
				if(current.choices == current.branch.choices.end()) {
					stack.pop_back();
					continue;
				}

				const auto &choice = *current.choices++;
				auto nongroup_decisions = current.data;
				if(!group[current.branch.player])
					nongroup_decisions = nongroup_decisions.null()
						? choice.action.variable
						: (choice.action.variable && nongroup_decisions);

				if(choice.node->is_leaf()) {
					const auto &leaf = choice.node->leaf();
					Utility total {z3::Real::ZERO, z3::Real::ZERO};
					for(size_t player = 0; player < input.players.size(); player++)
						if(group[player])
							total = total + leaf.utilities[player];
					auto comparison = labels.label_geq(honest_total, total);
					conjuncts.push_back(nongroup_decisions.null() ? comparison : nongroup_decisions.implies(comparison));
					continue;
				}

				stack.emplace_back(choice.node->branch(), nongroup_decisions);
			}
		}

		auto property = conjunction(conjuncts);
		std::cout << "honest history #" << history + 1 << std::endl;
		solve(input, labels, property, input.collusion_resilience_constraint, input.honest_histories[history]);
	}
}

void practicality(const Input &input) {
	// possible routes from an _action_ to a leaf
	struct Routes {
		// possibilities after the action
		std::vector<Bool> disjuncts;
		// if not null, the disjunction of `disjuncts` or "true" for leaves
		Bool combined;
	};

	// routes that yield a certain utility
	using UtilityMap = std::unordered_map<Utility, Routes>;
	// utility map per-player
	using PlayerUtilities = std::vector<UtilityMap>;
	// utility map per-player per-action
	using PlayerUtilitiesByAction = std::vector<PlayerUtilities>;

	std::vector<Frame<PlayerUtilitiesByAction>> stack;
	stack.emplace_back(*input.root);
	std::vector<Bool> conjuncts;
	Labels labels;
	while(true) {
		auto &current = stack.back();

		// finish processing a branch after all choices have been recursed into
		if(current.choices == current.branch.choices.end()) {
			// `current` will be invalidated shortly, move stuff out of the call stack
			auto player_utilities_by_action = std::move(current.data);
			const auto &current_branch = current.branch;

			// fill in the `combined` field of `Routes`
			for(auto &player_utilities : player_utilities_by_action)
				for(auto &map : player_utilities)
					for(auto &pair : map) {
						auto &routes = pair.second;
						if(routes.combined.null())
							routes.combined = disjunction(routes.disjuncts);
					}

			// for each possible action a in a branch...
			for(unsigned action = 0; action < current_branch.choices.size(); action++) {
				const auto &utilities_action = player_utilities_by_action[action][current_branch.player];
				auto action_variable = current_branch.choices[action].action.variable;
				// for other possible actions a' in a branch...
				for(unsigned other = 0; other < current_branch.choices.size(); other++) {
					if(action == other)
						continue;

					const auto &utilities_other = player_utilities_by_action[other][current_branch.player];
					// for each utility u reachable from a under condition c...
					for(const auto &action_pair : utilities_action) {
						auto action_utility = action_pair.first;
						auto action_condition = action_pair.second.combined;
						// for each utility u' reachable from a' under condition c'...
						for(const auto &other_pair: utilities_other) {
							auto other_utility = other_pair.first;
							auto other_condition = other_pair.second.combined;
							// if a and c and c'...
							auto conjunction = action_variable && action_condition && other_condition;
							// ...then u is at least as good as u', otherwise we'd switch
							auto comparison = labels.label_geq(action_utility, other_utility);
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
			auto &parent = stack.back();
			auto &parent_player_utilities_by_action = parent.data;
			parent_player_utilities_by_action.emplace_back(input.players.size());
			auto &parent_player_utilities = parent_player_utilities_by_action.back();
			for(unsigned choice = 0; choice < current_branch.choices.size(); choice++) {
				const auto &player_utilities = player_utilities_by_action[choice];
				auto action = current_branch.choices[choice].action.variable;
				for(unsigned player = 0; player < player_utilities.size(); player++) {
					const auto &utility_map = player_utilities[player];
					auto &parent_utility_map = parent_player_utilities[player];
					for(const auto &pair : utility_map) {
						auto utility = pair.first;
						auto condition = pair.second.combined;
						parent_utility_map[utility].disjuncts.push_back(action && condition);
					}
				}
			}
			continue;
		}

		auto &player_utilities_by_action = current.data;
		const auto &choice = *current.choices++;
		// the next choice is a leaf, do all the usual logic
		if(choice.node->is_leaf()) {
			const auto &leaf = choice.node->leaf();
			player_utilities_by_action.emplace_back(leaf.utilities.size());
			auto &player_utilities = player_utilities_by_action.back();
			for(unsigned player = 0; player < leaf.utilities.size(); player++)
				player_utilities[player][leaf.utilities[player]].combined = Bool::TRUE;
			continue;
		}
		stack.emplace_back(choice.node->branch());
	}

	auto property = conjunction(conjuncts);
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		solve(input, labels, property, input.practicality_constraint, input.honest_histories[history]);
	}
}
