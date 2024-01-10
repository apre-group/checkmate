#include <algorithm>
#include <bitset>
#include <iostream>
#include <random>

#include "property.hpp"
#include "utils.hpp"
#include "z3++.hpp"

using z3::Bool;
using z3::Solver;

// source of pseudo-random noise to shuffle unsat cores with
std::minstd_rand PRNG;

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
		size_t index = triggers.size();
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
	std::unordered_map<Bool, size_t> expr2trigger;
	// positive/negative pairs of trigger booleans
	std::vector<std::pair<Bool, Bool>> triggers;
	// trigger implications to be inserted into the property
	std::vector<Bool> trigger_implications;
};

static bool solve_rec(
	// precomputed labels
	const Labels &labels,
	// the solver with which we solve cases
	Solver &solver,
	// the solver to minimize splits with
	Solver &minimize_solver,
	// current case
	std::vector<Bool> case_,
	// currently-active triggers
	std::vector<std::pair<bool, bool>> &active_splits
) {
	std::cout << "case: " << case_ << std::endl;

	// make a fresh frame for current case
	solver.push();

	// assert all the case's triggers
	// NB must include also those that are *not* active
	for(size_t i = 0; i < active_splits.size(); i++) {
		solver.assert_(active_splits[i].first ? labels.triggers[i].first : !labels.triggers[i].first);
		solver.assert_(active_splits[i].second ? labels.triggers[i].second : !labels.triggers[i].second);
	}

	// actually do the work
	z3::Result result = solver.solve();
	// ...and remove the case triggers to keep everything clean
	solver.pop();

	// solved the case immediately
	if(result == z3::Result::SAT) {
		std::cout << "solved" << std::endl;
		return true;
	}

	// didn't solve it, need to consider case splits

	auto core = solver.unsat_core();
	// don't get "stuck" in an unproductive area: shuffle the unsat core
	shuffle(core.begin(), core.end(), PRNG);

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
		return false;
	}

	std::cout << "split: " << split << std::endl;
	size_t trigger = labels.expr2trigger.at(split);

	// positive split
	case_.push_back(split);
	active_splits[trigger].first = true;
	bool positive = solve_rec(labels, solver, minimize_solver, case_, active_splits);
	active_splits[trigger].first = false;
	case_.pop_back();
	if(!positive)
		return false;

	// negative split
	case_.push_back(split);
	active_splits[trigger].second = true;
	bool negative = solve_rec(labels, solver, minimize_solver, case_, active_splits);
	active_splits[trigger].second = false;
	case_.pop_back();
	if(!negative)
		return false;

	return true;
}

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
	// reinitialise PRNG so it's not affected by presence of other runs
	new (&PRNG) std::minstd_rand;

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

	// the current case as a series of expressions
	std::vector<Bool> case_;
	// active triggers for the current case
	std::vector<std::pair<bool, bool>> active_splits(labels.triggers.size());
	solve_rec(labels, solver, minimize_solver, case_, active_splits);
}

// helper struct for computing the weak immunity property
template<bool weaker>
struct WeakImmunity {
	WeakImmunity(size_t player, Labels &labels) : player(player), labels(labels) {}

	z3::Bool compute(const Node &node) const {
		if(node.is_leaf()) {
			const auto &leaf = node.leaf();
			// known utility for us
			auto utility = leaf.utilities[player];
			// so (the real part of) the utility should be greater than zero
			return weaker
				? labels.label(utility.real >= z3::Real::ZERO)
				: labels.label_geq(utility, {z3::Real::ZERO, z3::Real::ZERO});
		}

		std::vector<z3::Bool> conjuncts;
		const auto &branch = node.branch();
		bool player_choice  = branch.player == player;
		for(const auto &choice : branch.choices) {
			auto choice_property = compute(*choice.node);
			// we only care about the current player's choices
			if(player_choice)
				choice_property = choice.action.variable.implies(choice_property);
			conjuncts.push_back(choice_property);
		}
		return conjunction(conjuncts);
	}

	// current player
	size_t player;
	Labels &labels;
};

// logic is very similar for weak/weaker immunity, so we template it
template<bool weaker>
void weak_immunity(const Input &input) {
	std::cout << (weaker ? "weaker immunity" : "weak immunity") << std::endl;

	Labels labels;
	std::vector<Bool> conjuncts;
	for(size_t player = 0; player < input.players.size(); player++)
		conjuncts.push_back(WeakImmunity<weaker>(player, labels).compute(*input.root));
	auto property = conjunction(conjuncts);

	auto property_constraint = weaker
		? input.weak_immunity_constraint
		: input.weaker_immunity_constraint;
	// property is the same for all honest histories
	for(size_t history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		solve(input, labels, property, property_constraint, input.honest_histories[history]);
	}
}

// instantiate for true/false, prevents linker errors
template void weak_immunity<false>(const Input &);
template void weak_immunity<true>(const Input &);

// helper struct for computing the collusion resilience property
struct CollusionResilience {
	CollusionResilience(size_t players, const Leaf &honest_leaf, Labels &labels, uint64_t binary) :
		players(players),
		labels(labels),
		group(binary),
		honest_total { z3::Real::ZERO, z3::Real::ZERO }
	{
		// compute the honest total for the current group
		for(size_t player = 0; player < players; player++)
			if(group[player])
				honest_total = honest_total + honest_leaf.utilities[player];
	}

	z3::Bool compute(const Node &node) const {
		if(node.is_leaf()) {
			const auto &leaf = node.leaf();

			// compute the total utility for the player group...
			Utility total {z3::Real::ZERO, z3::Real::ZERO};
			for(size_t player = 0; player < players; player++)
				if(group[player])
					total = total + leaf.utilities[player];

			// ..and compare it to the honest total
			return labels.label_geq(honest_total, total);
		}

		std::vector<z3::Bool> conjuncts;
		const auto &branch = node.branch();
		bool nongroup_decision = !group[branch.player];
		for(const auto &choice : branch.choices) {
			auto choice_property = compute(*choice.node);
			// we only care about decisions the group _doesn't_ make
			if(nongroup_decision)
				choice_property = choice.action.variable.implies(choice_property);
			conjuncts.push_back(choice_property);
		}
		return conjunction(conjuncts);
	}

	// the total number of players
	size_t players;
	Labels &labels;
	// the current group of players
	std::bitset<Input::MAX_PLAYERS> group;
	// their honest total
	Utility honest_total;
};

void collusion_resilience(const Input &input) {
	std::cout << "collusion resilience" << std::endl;
	assert(input.players.size() < Input::MAX_PLAYERS);

	// property is different for each honest history
	for(size_t history = 0; history < input.honest_histories.size(); history++) {
		Labels labels;
		// lookup the leaf for this history
		const Leaf &honest_leaf = input.honest_history_leaves[history];
		std::vector<Bool> conjuncts;

		// sneaky hack follows: all possible subgroups of n players can be implemented by counting through from 1 to (2^n - 2)
		// C++ standard mandates that `long long` has at least 64 bits, so we can have up to 64 players - this should be enough
		// done this way more for concision than efficiency
		for(unsigned long long binary_counter = 1; binary_counter < -1ull >> (64 - input.players.size()); binary_counter++)
			conjuncts.push_back(CollusionResilience(input.players.size(), honest_leaf, labels, binary_counter).compute(*input.root));

		auto property = conjunction(conjuncts);
		std::cout << "honest history #" << history + 1 << std::endl;
		solve(input, labels, property, input.collusion_resilience_constraint, input.honest_histories[history]);
	}
}

// helper struct for computing the practicality property
struct Practicality {
	// routes that yield a certain utility
	using UtilityMap = std::unordered_map<Utility, Bool>;
	// utility map per-player
	using PlayerUtilities = std::vector<UtilityMap>;

	Practicality(size_t players, Labels &labels) : players(players), labels(labels) {}

	// build the utility map players->utility->condition
	// the map gives a single boolean condition for "player p gets utility u starting from this subtree"
	// also, add constraints to `conjuncts` as we go
	PlayerUtilities utilities(const Node &node) {
		PlayerUtilities result(players);
		if(node.is_leaf()) {
			const auto &leaf = node.leaf();
			for(size_t player = 0; player < players; player++)
				result[player][leaf.utilities[player]] = Bool::TRUE;
			return result;
		}

		// compute player utility maps for each child recursively
		const auto &branch = node.branch();
		std::vector<PlayerUtilities> player_utilities_by_choice;
		for(const auto &choice : branch.choices)
			player_utilities_by_choice.push_back(utilities(*choice.node));

		// for each possible action a in a branch...
		for(size_t choice = 0; choice < branch.choices.size(); choice++) {
			const auto &utilities_action = player_utilities_by_choice[choice][branch.player];
			auto action_variable = branch.choices[choice].action.variable;
			// for other possible actions a' in a branch...
			for(size_t other = 0; other < branch.choices.size(); other++) {
				if(choice == other)
					continue;

				const auto &utilities_other = player_utilities_by_choice[other][branch.player];
				// for each utility u reachable from a under condition c...
				for(const auto &action_pair : utilities_action) {
					auto action_utility = action_pair.first;
					auto action_condition = action_pair.second;
					// for each utility u' reachable from a' under condition c'...
					for(const auto &other_pair: utilities_other) {
						auto other_utility = other_pair.first;
						auto other_condition = other_pair.second;
						// if a and c and c'...
						auto conjunction = action_variable && action_condition && other_condition;
						// ...then u is at least as good as u', otherwise we'd switch
						auto comparison = labels.label_geq(action_utility, other_utility);
						conjuncts.push_back(conjunction.implies(comparison));
					}
				}
			}
		}

		// combine child maps into a larger map for this node
		for(size_t choice = 0; choice < branch.choices.size(); choice++) {
			auto action = branch.choices[choice].action.variable;
			const auto &player_utilities = player_utilities_by_choice[choice];
			for(size_t player = 0; player < players; player++) {
				auto &player_result = result[player];
				const auto &utility_map = player_utilities[player];
				for(const auto &pair : utility_map) {
					auto utility = pair.first;
					auto condition = action && pair.second;
					auto &resulting_condition = player_result[utility];
					resulting_condition = resulting_condition.null()
						? condition
						: (resulting_condition || condition);
				}
			}
		}

		return result;
	}

	z3::Bool compute(const Node &node) {
		conjuncts.clear();
		utilities(node);
		return conjunction(conjuncts);
	}

	size_t players;
	Labels &labels;
	std::vector<z3::Bool> conjuncts;
};

void practicality(const Input &input) {
	std::cout << "practicality" << std::endl;
	Labels labels;
	auto property = Practicality(input.players.size(), labels).compute(*input.root);

	// property is the same for all honest histories
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << "honest history #" << history + 1 << std::endl;
		solve(input, labels, property, input.practicality_constraint, input.honest_histories[history]);
	}
}
