#include <algorithm>
#include <bitset>
#include <iostream>
#include <random>

#include "property.hpp"
#include "utils.hpp"
#include "z3++.hpp"

using z3::Bool;
using z3::Solver;

// helpers for labelling expressions
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
		unsigned index = triggers.size();
		expr2trigger[expr] = index;
		expr2trigger[!expr] = index;
		auto positive = Bool::fresh();
		auto negative = Bool::fresh();
		triggers.emplace_back(positive, negative);
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

	/**
	 * labels:
	 *
	 * we label comparison expressions in properties with a fresh label
	 * if the label shows up in an unsat core later, we can perform a case split
	 **/
	// label-to-expression map
	std::unordered_map<Bool, Bool> label2expr;
	// expression-to-label map, used for caching
	std::unordered_map<Bool, Bool> expr2label;

	/**
	 * split triggers:
	 *
	 * to perform a case split on a certain expression, we set a Boolean "trigger" variable true
	 * usually, triggers are forced false, which has no effect on the overall property formula
	 * when set true, they add a precondition to the property
	 * there is a separate trigger for positive and negative versions of a split,
	 * which should never both be assigned true simultaneously
	 **/
	// expr-to-trigger map: maps a comparison expression to an index into `triggers`
	std::unordered_map<Bool, unsigned> expr2trigger;
	// positive/negative pairs of trigger booleans
	std::vector<std::pair<Bool, Bool>> triggers;
	// trigger implications to be inserted into the property
	std::vector<Bool> trigger_implications;
};

// common solving behaviour for all properties
static void solve(
	// the input game
	const Input &input,
	// labels we made earlier for expressions
	const Labels &labels,
	// the property we want a solution for, without quantification or precondition
	Bool property,
	// the initial constraint for said property
	Bool property_constraint,
	// the honest history
	Bool honest_history
) {
	// wrap up property:
	// forall <variables> (triggers && initial constraints) => property
	property = forall(input.quantify, (
		conjunction(labels.trigger_implications) &&
		input.initial_constraint &&
		property_constraint
	).implies(property));

	// the main solver
	Solver solver;
	// it should know about action constraints, the wrapped property, the honest history, and labels
	solver.assert_(input.action_constraint);
	solver.assert_(property);
	solver.assert_(honest_history);
	for(const auto &label : labels.label2expr)
		solver.assert_and_track(label.first);

	// the solver used to minimise splits
	Solver minimize_solver;
	minimize_solver.assert_(input.initial_constraint);
	minimize_solver.assert_(property_constraint);

	// is a certain split trigger currently active?
	std::vector<std::pair<bool, bool>> active_splits(labels.triggers.size());
	// the current case as a series of expressions
	std::vector<Bool> case_;
	// are we solving the split for the first time, or negated for the last time?
	std::vector<bool> finished;

	// source of pseudo-random noise to shuffle unsat cores with
	std::minstd_rand prng;

	// process one case each trip around the loop
	while(true) {
		// new frame for active splits
		Solver::Pop pop_triggers(solver);
		for(unsigned i = 0; i < active_splits.size(); i++) {
			solver.assert_(active_splits[i].first ? labels.triggers[i].first : !labels.triggers[i].first);
			solver.assert_(active_splits[i].second ? labels.triggers[i].second : !labels.triggers[i].second);
		}

		std::cout << "case: " << case_ << std::endl;
		// solved the case
		if(solver.solve() == z3::Result::SAT) {
			std::cout << "solved" << std::endl;
			while(!finished.empty()) {
				auto top = finished.back();
				auto &last_split = case_.back();
				auto trigger_index = labels.expr2trigger.at(last_split);
				// finished with the top split, keep popping until we hit one we're not done with
				if(top) {
					case_.pop_back();
					finished.pop_back();
					active_splits[trigger_index].second = false;
					continue;
				}
				// flip the split and continue
				top = true;
				// disable positive trigger
				active_splits[trigger_index].first = false;
				// enable negative trigger
				active_splits[trigger_index].second = true;
				// flip the split
				last_split = !last_split;
				break;
			}
			// finished all splits, done
			if(finished.empty()) {
				std::cout << "done" << std::endl;
				return;
			}
			continue;
		}
		std::cout << "failed, trying split" << std::endl;

		auto core = solver.unsat_core();
		// don't get "stuck" in an unproductive area: shuffle the unsat core
		shuffle(core.begin(), core.end(), prng);

		// assigned if we find a suitable split
		Bool split;
		for(auto label : core) {
			// there should be nothing except labels in the unsat core, throws otherwise
			auto expr = labels.label2expr.at(label);
			// if either the split or its negation tells us nothing new, it's pointless to split on it
			if(
				minimize_solver.solve(case_, expr) == z3::Result::UNSAT ||
				minimize_solver.solve(case_, !expr) == z3::Result::UNSAT
			)
				continue;
			// otherwise, it'll do
			split = expr;
			break;
		}

		// didn't find anything worth splitting on
		if(split.null()) {
			std::cout << "no more splits, failed" << std::endl;
			return;
		}

		std::cout << "split: " << split << std::endl;
		case_.push_back(split);
		// enable positive trigger
		active_splits[labels.expr2trigger.at(split)].first = true;
		finished.push_back(false);
	}
}

/**
 * all properties are recursive in nature
 *
 * we have to simulate this: I hope you like stacks!
 **/

// stack frame in simulated recursion over a tree
template<typename T>
struct Frame {
	template<typename... Args>
	Frame(const Branch &branch, Args &&...args) :
		branch(branch),
		choices(branch.choices.begin()),
		data(args...)
	{}
	// the branch passed to the simulated function call
	const Branch &branch;
	// how far through the branch's choices we are
	std::vector<Choice>::const_iterator choices;
	// the property's stuff
	T data;
};

// logic is very similar for weak/weaker immunity, so we template it
template<bool weaker>
void weak_immunity(const Input &input) {
	std::cout << (weaker ? "weaker immunity" : "weak immunity") << std::endl;
	Labels labels;
	std::vector<Bool> conjuncts;

	// for each player...
	for(unsigned player = 0; player < input.players.size(); player++) {
		// our stack only contains the player's decisions to reach a branch
		std::vector<Frame<Bool>> stack;
		stack.emplace_back(*input.root);
		while(!stack.empty()) {
			auto &current = stack.back();
			if(current.choices == current.branch.choices.end()) {
				stack.pop_back();
				continue;
			}

			const auto &choice = *current.choices++;
			// retrieve the player's decisions to reach here
			auto player_decisions = current.data;
			// if it's the player's turn at a branch, set the current decision
			if(current.branch.player == player)
				player_decisions = player_decisions.null()
					? choice.action.variable
					: (choice.action.variable && player_decisions);

			if(choice.node->is_leaf()) {
				// ...and we reached a leaf ...
				const auto &leaf = choice.node->leaf();
				// ...with known utility for us...
				auto utility = leaf.utilities[player];
				// ...then (the real part of) the utility should be greater than zero.
				auto comparison = weaker
					? labels.label(utility.real >= z3::Real::ZERO)
					: labels.label_geq(utility, {z3::Real::ZERO, z3::Real::ZERO});
				conjuncts.push_back(player_decisions.null() ? comparison : player_decisions.implies(comparison));
				continue;
			}

			// branch: recurse
			stack.emplace_back(choice.node->branch(), player_decisions);
		}
	}

	auto property_constraint = weaker
		? input.weak_immunity_constraint
		: input.weaker_immunity_constraint;
	auto property = conjunction(conjuncts);
	// property is the same for all honest histories
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		solve(input, labels, property, property_constraint, input.honest_histories[history]);
	}
}

// instantiate for true/false, prevents linker errors
template void weak_immunity<false>(const Input &);
template void weak_immunity<true>(const Input &);

void collusion_resilience(const Input &input) {
	std::cout << "collusion resilience" << std::endl;
	assert(input.players.size() < Input::MAX_PLAYERS);

	// property is different for each honest history
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		Labels labels;
		// lookup the leaf for this history
		const Leaf &honest_leaf = input.honest_history_leaves[history];
		std::vector<Bool> conjuncts;

		// sneaky hack follows: all possible subgroups of n players can be implemented by counting through from 1 to (2^n - 2)
		// C++ standard mandates that `long long` has at least 64 bits, so we can have up to 64 players - this should be enough
		// done this way more for concision than efficiency
		for(unsigned long long binary_counter = 1; binary_counter < -1ull >> (64 - input.players.size()); binary_counter++) {
			// convert to a std::bitset to get some nice operators for free
			std::bitset<Input::MAX_PLAYERS> group(binary_counter);

			// the total honest utility for players in this subgroup
			Utility honest_total {z3::Real::ZERO, z3::Real::ZERO};
			for(size_t player = 0; player < input.players.size(); player++)
				if(group[player])
					honest_total = honest_total + honest_leaf.utilities[player];

			// our stack only contains the decisions _not_ made by the group to reach a branch
			std::vector<Frame<Bool>> stack;
			stack.emplace_back(*input.root);
			while(!stack.empty()) {
				auto &current = stack.back();
				if(current.choices == current.branch.choices.end()) {
					stack.pop_back();
					continue;
				}

				// if it's _not_ the players' turn at a branch, set the current decision
				const auto &choice = *current.choices++;
				auto nongroup_decisions = current.data;
				if(!group[current.branch.player])
					nongroup_decisions = nongroup_decisions.null()
						? choice.action.variable
						: (choice.action.variable && nongroup_decisions);

				if(choice.node->is_leaf()) {
					// we reached a leaf
					const auto &leaf = choice.node->leaf();
					// compute the total utility for the player group here...
					Utility total {z3::Real::ZERO, z3::Real::ZERO};
					for(size_t player = 0; player < input.players.size(); player++)
						if(group[player])
							total = total + leaf.utilities[player];
					// ..and compare it to the honest total
					auto comparison = labels.label_geq(honest_total, total);
					conjuncts.push_back(nongroup_decisions.null() ? comparison : nongroup_decisions.implies(comparison));
					continue;
				}

				// branch: recurse
				stack.emplace_back(choice.node->branch(), nongroup_decisions);
			}
		}

		auto property = conjunction(conjuncts);
		std::cout << "honest history #" << history + 1 << std::endl;
		solve(input, labels, property, input.collusion_resilience_constraint, input.honest_histories[history]);
	}
}

void practicality(const Input &input) {
	std::cout << "practicality" << std::endl;
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

	std::vector<Bool> conjuncts;
	Labels labels;
	// our stack contains the utility map for each player and each action at each branch
	std::vector<Frame<PlayerUtilitiesByAction>> stack;
	stack.emplace_back(*input.root);
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

		// branch: recurse
		stack.emplace_back(choice.node->branch());
	}

	auto property = conjunction(conjuncts);
	// property is the same for all honest histories
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		solve(input, labels, property, input.practicality_constraint, input.honest_histories[history]);
	}
}
