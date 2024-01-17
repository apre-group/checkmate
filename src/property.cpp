#include <algorithm>
#include <bitset>
#include <iostream>
#include <random>

#include "property.hpp"
#include "options.hpp"
#include "utils.hpp"
#include "z3++.hpp"

using z3::Bool;
using z3::Solver;

// helpers for labelling expressions
template<typename Property>
struct Labels {
public:
	// produce a fresh (or cached) label for `expr` and return `label => expr`
	Bool label_comparison(Bool expr) {
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
			return label_comparison(left.infinitesimal >= right.infinitesimal);
		if(left.infinitesimal.is(right.infinitesimal))
			return label_comparison(left.real >= right.real);
		return label_comparison(left.real > right.real) ||
			(label_comparison(left.real == right.real) && label_comparison(left.infinitesimal >= right.infinitesimal));
	}

	// make a fresh label, associate it with `info` and return `label => expr`
	Bool label_counterexample(typename Property::CounterExamplePart info) {
		auto label = Bool::fresh();
		node_labels.insert({label, std::move(info)});
		return label;
	}

	/**
	 * labels:
	 *
	 * we label comparison expressions in properties with a fresh label
	 * if the label shows up in an unsat core later, we can perform a case split
	 *
	 * we also label branches similarly, so we can detect counterexamples
	 **/
	// label-to-expression map
	std::unordered_map<Bool, Bool> label2expr;
	// expression-to-label map, used for caching
	std::unordered_map<Bool, Bool> expr2label;
	// which branch does this label mark for counterexamples?
	std::unordered_map<z3::Bool, typename Property::CounterExamplePart> node_labels;

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

template<typename Property>
struct SolvingHelper {
	SolvingHelper(
		const Input &input,
		const Labels<Property> &labels,
		Bool raw_property,
		Bool property_constraint,
		Bool honest_history
	) : input(input), labels(labels), active_splits(labels.triggers.size()) {
		// wrap up property:
		// forall <variables> (triggers && initial constraints) => property
		property = forall(input.quantify, (
			conjunction(labels.trigger_implications) &&
			input.initial_constraint &&
			property_constraint
		).implies(raw_property));

		// should know about action constraints, the wrapped property, the honest history, and labels
		solver.assert_(input.action_constraint);
		solver.assert_(property);
		solver.assert_(honest_history);
		for(const auto &label : labels.label2expr)
			solver.assert_and_track(label.first);
		for(const auto &label : labels.node_labels)
			solver.assert_and_track(label.first);

		// should know only about the initial constraints
		minimize_solver.assert_(input.initial_constraint);
		minimize_solver.assert_(property_constraint);
	}

	bool solve() {
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
			std::cout << "\tCase " << case_ << " satisfies property." << std::endl;
			return true;
		}

		// didn't solve it, need to consider case splits

		auto core = solver.unsat_core();
		// don't get "stuck" in an unproductive area: shuffle the unsat core
		shuffle(core.begin(), core.end(), prng);

		// assigned if we find a suitable split
		Bool split;
		std::vector<typename Property::CounterExamplePart> counterexample;
		for(auto label : core) {
			// ignore other non-comparison labels
			auto location = labels.label2expr.find(label);
			// if it's not a comparison, should be a counterexample label
			if(location == labels.label2expr.end()) {
				auto node_info = labels.node_labels.at(label);
				counterexample.push_back(node_info);
				continue;
			}

			auto expr = location->second;
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
			std::cout << "\tNO, case " << case_ << " violates property." << std::endl;
			if(!counterexample.empty()) {
				counterexamples.push_back({
					case_,
					std::move(counterexample)
				});
			}
			return false;
		}

		std::cout << "\tFurther case split required." << std::endl;
		std::cout << "\tSplit on: " << split << std::endl;
		size_t trigger = labels.expr2trigger.at(split);

		// positive split
		case_.push_back(split);
		active_splits[trigger].first = true;
		bool positive = solve();
		active_splits[trigger].first = false;
		case_.pop_back();
		if(!positive)
			return false;

		// negative split
		case_.push_back(!split);
		active_splits[trigger].second = true;
		bool negative = solve();
		active_splits[trigger].second = false;
		case_.pop_back();
		if(!negative)
			return false;

		return true;
	}

	const Input &input;
	// labels we need
	const Labels<Property> &labels;
	// the property we're testing
	Bool property;
	// the main solver
	Solver solver;
	// the solver used to minimise splits
	Solver minimize_solver;
	// source of pseudo-random noise to shuffle unsat cores with
	std::minstd_rand prng;
	// the current case as a series of expressions
	std::vector<Bool> case_;
	// active triggers for the current case
	std::vector<std::pair<bool, bool>> active_splits;

	struct CounterExample {
		std::vector<z3::Bool> case_;
		std::vector<typename Property::CounterExamplePart> parts;
	};

	std::vector<CounterExample> counterexamples;
};

// helper struct for computing the weak immunity property
template<bool weaker>
struct WeakImmunity {
	struct CounterExamplePart {
		const Leaf &leaf;
		size_t player;
	};

	WeakImmunity(
		const Options &options,
		Labels<WeakImmunity<weaker>> &labels,
		size_t player
	) : options(options), labels(labels), player(player) {}

	z3::Bool compute(const Node &node) const {
		if(node.is_leaf()) {
			const auto &leaf = node.leaf();
			// known utility for us
			auto utility = leaf.utilities[player];
			// so (the real part of) the utility should be greater than zero
			auto comparison = weaker
				? labels.label_comparison(utility.real >= z3::Real::ZERO)
				: labels.label_geq(utility, {z3::Real::ZERO, z3::Real::ZERO});

			if(options.counterexamples)
				comparison = labels.label_counterexample({leaf, player})
					.implies(comparison);
			return comparison;
		}

		std::vector<z3::Bool> conjuncts;
		const auto &branch = node.branch();
		bool player_choice = branch.player == player;
		for(const auto &choice : branch.choices) {
			auto choice_property = compute(*choice.node);
			// we only care about the current player's choices
			if(player_choice)
				choice_property = choice.action.variable.implies(choice_property);
			conjuncts.push_back(choice_property);
		}
		return conjunction(conjuncts);
	}

	const Options &options;
	Labels<WeakImmunity<weaker>> &labels;
	// current player
	size_t player;
};

// logic is very similar for weak/weaker immunity, so we template it
template<bool weaker>
void weak_immunity(const Options &options, const Input &input) {
	std::cout << std::endl;
	std::cout << std::endl;
	std::cout << (weaker ? "WEAKER IMMUNITY" : "WEAK IMMUNITY") << std::endl;

	Labels<WeakImmunity<weaker>> labels;
	std::vector<Bool> conjuncts;
	for(size_t player = 0; player < input.players.size(); player++)
		conjuncts.push_back(
			WeakImmunity<weaker>(options, labels, player)
				.compute(*input.root)
		);
	auto property = conjunction(conjuncts);

	auto property_constraint = weaker
		? input.weaker_immunity_constraint
		: input.weak_immunity_constraint;
	// property is the same for all honest histories
	for(size_t history = 0; history < input.honest_histories.size(); history++) {
		std::cout << std::endl;
		std::cout << "Is history " << input.readable_honest_histories[history] << (weaker ? " weaker immune?" : " weak immune?") << std::endl;
		SolvingHelper<WeakImmunity<weaker>> helper(
			input,
			labels,
			property,
			property_constraint,
			input.honest_histories[history]
		);
		const bool is_sat = helper.solve();
		if(is_sat) {
			std::cout << "YES, it is" << (weaker ? " weaker immune." : " weak immune.") << std::endl;
		}

		for(const auto &counterexample : helper.counterexamples) {
			std::cout << "Counterexample for " << counterexample.case_ << std::endl;
			// the following is just 1 counterexample
			for(const auto &part : counterexample.parts)
				std::cout
					<< "\tPlayer "
					<< input.players[part.player]
					<< " can be harmed at "
					<< part.leaf.compute_history()
					<< std::endl;
		}
	}
}

// instantiate for true/false, prevents linker errors
template void weak_immunity<false>(const Options &, const Input &);
template void weak_immunity<true>(const Options &, const Input &);

// helper struct for computing the collusion resilience property
struct CollusionResilience {
	using ColludingGroup = std::bitset<Input::MAX_PLAYERS>;

	struct CounterExamplePart {
		const Leaf &leaf;
		ColludingGroup group;
	};

	CollusionResilience(
		const Options &options,
		Labels<CollusionResilience> &labels,
		size_t players,
		const Leaf &honest_leaf,
		uint64_t binary
	) :
		options(options),
		labels(labels),
		players(players),
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
			auto comparison = labels.label_geq(honest_total, total);
			if(options.counterexamples)
				comparison = labels.label_counterexample({leaf, group})
					.implies(comparison);
			return comparison;
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

	const Options &options;
	Labels<CollusionResilience> &labels;
	// the total number of players
	size_t players;
	// the current group of players
	std::bitset<Input::MAX_PLAYERS> group;
	// their honest total
	Utility honest_total;
};

void collusion_resilience(const Options &options, const Input &input) {
	std::cout << std::endl;
	std::cout << std::endl;
	std::cout << "COLLUSION RESILIENCE" << std::endl;
	assert(input.players.size() < Input::MAX_PLAYERS);

	// property is different for each honest history
	for(size_t history = 0; history < input.honest_histories.size(); history++) {
		Labels<CollusionResilience> labels;
		// lookup the leaf for this history
		const Leaf &honest_leaf = input.honest_history_leaves[history];
		std::vector<Bool> conjuncts;

		// sneaky hack follows: all possible subgroups of n players can be implemented by counting through from 1 to (2^n - 2)
		// done this way more for concision than efficiency
		for(uint64_t binary_counter = 1; binary_counter < -1ull >> (64 - input.players.size()); binary_counter++)
			conjuncts.push_back(CollusionResilience(
				options,
				labels,
				input.players.size(),
				honest_leaf,
				binary_counter
			).compute(*input.root));

		auto property = conjunction(conjuncts);
		std::cout << std::endl;
		std::cout << "Is history " << input.readable_honest_histories[history] << " collusion resilient?" << std::endl;
		SolvingHelper<CollusionResilience> helper(
			input,
			labels,
			property,
			input.collusion_resilience_constraint,
			input.honest_histories[history]
		);
		const bool is_sat = helper.solve();
		if(is_sat) {
			std::cout << "YES, it is collusion resilient." << std::endl;
		}


		for(const auto &counterexample : helper.counterexamples) {
			std::cout << "Counterexample for " << counterexample.case_ << std::endl;
			for(const auto &part : counterexample.parts) {
				std::cout << "\tGroup";
				for(size_t player = 0; player < input.players.size(); player++)
					if(part.group[player])
						std::cout << " " << input.players[player];
				std::cout
					<< " profits from deviation at "
					<< part.leaf.compute_history()
					<< std::endl;
			}
		}
	}
}

// helper struct for computing the practicality property
struct Practicality {
	struct CounterExamplePart {
		const Branch &branch;
		size_t choice;
	};

	// routes that yield a certain utility
	using UtilityMap = std::unordered_map<Utility, Bool>;
	// utility map per-player
	using PlayerUtilities = std::vector<UtilityMap>;

	Practicality(
		const Options &options,
		Labels<Practicality> &labels,
		size_t players
	) : options(options), labels(labels), players(players) {}

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

				Bool counterexample_label;
				if(options.counterexamples)
					counterexample_label = labels.label_counterexample({
						branch,
						other
					});

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
						if(options.counterexamples)
							comparison = counterexample_label.implies(comparison);
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

	const Options &options;
	Labels<Practicality> &labels;
	size_t players;
	std::vector<z3::Bool> conjuncts;
};

void practicality(const Options &options, const Input &input) {
	std::cout << std::endl;
	std::cout << std::endl;
	std::cout << "PRACTICALITY" << std::endl;
	Labels<Practicality> labels;
	auto property = Practicality(options, labels, input.players.size()).compute(*input.root);

	// property is the same for all honest histories
	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << std::endl;
		std::cout << "Is history " << input.readable_honest_histories[history] << " practical?" << std::endl;
		SolvingHelper<Practicality> helper(
			input,
			labels,
			property,
			input.practicality_constraint,
			input.honest_histories[history]
		);
		const bool is_sat = helper.solve();
		if(is_sat) {
			std::cout << "YES, it is practical." << std::endl;
		}

		for(const auto &counterexample : helper.counterexamples) {
			std::cout << "Counterexample for " << counterexample.case_ << std::endl;
			size_t root_index;
			auto root_length = std::numeric_limits<size_t>::max();
			for(size_t i = 0; i < counterexample.parts.size(); i++) {
				auto length = counterexample.parts[i].branch.history_length();
				if(length < root_length) {
					root_index = i;
					root_length = length;
				}
			}
			const auto &root_part = counterexample.parts[root_index];
			std::cout
				<< "\tPlayer "
				<< input.players[root_part.branch.player]
				<< " obtains maximal utility at "
				<< root_part.branch.compute_history()
				<< " by taking action "
				<< root_part.branch.choices[root_part.choice].action.name
				<< std::endl;
		}
	}
}
