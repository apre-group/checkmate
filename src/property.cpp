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
		label2part.insert({label, std::move(info)});
		counterexample_labels.push_back(label);
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
	// what information does this label mark for counterexamples?
	std::unordered_map<z3::Bool, typename Property::CounterExamplePart> label2part;
	// all counterexample labels
	std::vector<z3::Bool> counterexample_labels;

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
		const Options &options,
		const Input &input,
		const Labels<Property> &labels,
		Bool raw_property,
		Bool property_constraint,
		Bool honest_history
	) : options(options), input(input), labels(labels), active_splits(labels.triggers.size()) {
		// wrap up property:
		// forall <variables> (triggers && initial constraints) => property
		property = forall(input.quantify, (
			conjunction(labels.trigger_implications) &&
			input.initial_constraint &&
			property_constraint
		).implies(raw_property));

		// should know about action constraints, the wrapped property, 
		// the honest history, and labels
		solver.assert_(input.action_constraint);
		solver.assert_(property);
		solver.assert_(honest_history);
		for(const auto &label : labels.label2expr)
			solver.assert_and_track(label.first);

		// should know only about the initial constraints
		minimize_solver.assert_(input.initial_constraint);
		minimize_solver.assert_(property_constraint);
	}

	Bool find_split() {
		auto core = solver.unsat_core();
		// don't get "stuck" in an unproductive area: shuffle the unsat core
		shuffle(core.begin(), core.end(), prng);

		Bool split;
		for(auto label : core) {
			// ignore other non-comparison labels
			auto location = labels.label2expr.find(label);
			// ignore if it's not a comparison, could be a counterexample label
			if(location == labels.label2expr.end())
				continue;

			auto expr = location->second;
			// if either the split or its negation tells us nothing new, it's 
			// pointless to split on it
			if(
				minimize_solver.solve(case_, expr) == z3::Result::UNSAT ||
				minimize_solver.solve(case_, !expr) == z3::Result::UNSAT
			)
				continue;
			// otherwise, it'll do
			split = expr;
			break;
		}

		return split;
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
		auto result = solver.solve(labels.counterexample_labels);

		// solved the case immediately
		if(result == z3::Result::SAT) {
			std::cout << "\tCase " << case_ << " satisfies property." << std::endl;
			if(options.strategies) {
				z3::Model model = solver.model();

				case_models.push_back({
							case_,
							std::move(model)
						});
 			}
			// remove the case triggers
			solver.pop();
			return true;
		}

		// didn't solve it, need to consider case splits
		auto split = find_split();
		// didn't find anything worth splitting on
		if(split.null()) {
			if (!failed || options.all_cases){
				std::cout << "\tCase " << case_ << " violates property." << std::endl;

				if(options.counterexamples) {
					std::vector<typename Property::CounterExamplePart> counterexample;
					if(Property::EXTERNAL_COUNTEREXAMPLES){
						counterexamples.push_back({
							case_,
							std::move(counterexample)
						});
					}
					else {
						z3::MinimalCores cores(solver, labels.counterexample_labels);
						while(cores.next_core()) {
							std::vector<typename Property::CounterExamplePart> counterexample;
							for(auto label : cores.core){
								counterexample.push_back(labels.label2part.at(label));
								}
							counterexamples.push_back({
								case_,
								std::move(counterexample)
							});
							// std::cout << "\tFound counterexample." << std::endl;
							if(!options.all_counterexamples)
								break;
						}
					}
				}
			}
			failed = true;

			if(options.preconditions){
				unsat_cases.push_back(case_);
			}
			
			// remove the case triggers
			solver.pop();
			return options.all_cases || options.preconditions;
		}

		// remove the case triggers
		solver.pop();
		if (!failed || options.all_cases){
		std::cout << "\tRequire case split on " << split << std::endl;
		}
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
		case_.push_back(split.invert());
		active_splits[trigger].second = true;
		bool negative = solve();
		active_splits[trigger].second = false;
		case_.pop_back();
		if(!negative)
			return false;

		return true;
	}

	std::vector<std::vector<z3::Bool>> precondition_simplify() const {

		std::vector<std::vector<z3::Bool>> simp;
		for (const std::vector<z3::Bool> &case_ : unsat_cases){
			std::vector<z3::Bool> copy;
			for (const z3::Bool &atom : case_){
				copy.push_back(atom);
			}
			simp.push_back(copy);
		}
		bool any_rule1 = true;
		bool any_rule2 = true;
		while(any_rule1 || any_rule2){
			any_rule1 = false;
			any_rule2 = false;
			for(long unsigned int j = 0; j < simp.size(); j++){
				auto case_ = simp[j];
				for(long unsigned int k = j +1; k < simp.size(); k++){
					auto other_case = simp[k];
					bool rule1 = true;
					bool rule2 = false;
					if (case_.size() == other_case.size()) {
						bool one_inverse = false;
						long unsigned int inverse;
						for (long unsigned int i = 0 ; i < case_.size(); i++){
							if (case_[i].is_equal(other_case[i].invert()) && not one_inverse){
								one_inverse = true;
								inverse = i;
							}
							else if (case_[i].is_equal(other_case[i].invert()) && one_inverse) {
								rule1 = false;
								break;
							}
							else if ( not case_[i].is_equal(other_case[i])) {
								rule1 = false;
								break;
							}
						}
						rule1 = rule1 && one_inverse;
						if (rule1) {
							// remove other_case
							std::swap(simp[k], simp.back());
							simp.pop_back();
							// remove case_[i] from case_
							std::swap(case_[inverse], case_.back());
							case_.pop_back();
							simp[j] = case_;
							any_rule1 = true;
							break;
						} 
					}
					else {
						rule1 = false;
					}
					if ((case_.size() == 1) | (other_case.size() == 1)){
						// continue
						std::vector<z3::Bool> singleton;
						std::vector<z3::Bool> other; 
						int which_singleton;
						if (case_.size() == 1) {
							singleton = case_;
							other = other_case;
							which_singleton = 0;
						}
						else {
							singleton = other_case;
							other = case_;
							which_singleton = 1;
						}
						int inverse;
						for (long unsigned int l = 0; l < other.size(); l++) {
							if (singleton[0].is_equal(other[l].invert())){
								rule2 = true;
								inverse = l;
							}
						}
						if (rule2){
							std::swap(other[inverse], other.back());
							other.pop_back();
							if (which_singleton == 0){
								simp[k] = other;
							}
							else {
								simp[j] = other;
							}
							any_rule2 = true;
						}

					}
					else {
						rule2 = false;
					}

				}
			} 
		}

		return simp;
	}


	z3::Model solve_for_counterexample() {
		// assert all the case's triggers
		// NB must include also those that are *not* active
		for(size_t i = 0; i < active_splits.size(); i++) {
			solver.assert_(!labels.triggers[i].first);
			solver.assert_(!labels.triggers[i].second);
		}

		// actually do the work
		return solver.solve() == z3::Result::SAT ? solver.model() : z3::Model();
	}

	const Options &options;
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
	// did we fail at any point?
	bool failed = false;

	struct CounterExample {
		std::vector<z3::Bool> case_;
		std::vector<typename Property::CounterExamplePart> parts;
	};

	struct CaseModel {
		std::vector<z3::Bool> case_;
		z3::Model model; 
	};

	std::vector<CounterExample> counterexamples;
	std::vector<std::vector<z3::Bool>> unsat_cases;
	std::vector<CaseModel> case_models;
};

// helper struct for computing the weak immunity property
template<bool weaker>
struct WeakImmunity {
	static const bool EXTERNAL_COUNTEREXAMPLES = false;
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


void print_strategy(Node *next, std::vector<std::reference_wrapper<const std::string>> history, const z3::Model &model) {

	if (next->is_leaf()){
		return;
	}

	const Branch &current = next->branch();
	for(const auto &choice : current.choices) {
		// TBC
		std::vector<std::reference_wrapper<const std::string>> new_history = {choice.action.name};
		for (const auto elem : history){
			new_history.push_back(elem);
		}

		print_strategy(choice.node.get(), new_history, model);

		if(model.assigns<true>(choice.action.variable)) {
			std::cout << "\t Choose " << choice.action.name << " after history " << history << std::endl;
		}
	}
	return;			
}


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
			options,
			input,
			labels,
			property,
			property_constraint,
			input.honest_histories[history]
		);
		helper.solve();
		if(!helper.failed) {
			std::cout << "YES, it is" << (weaker ? " weaker immune." : " weak immune.") << std::endl;
			if(options.strategies){
				std::cout << std::endl;
				for (const auto &casemodel : helper.case_models){
					std::cout << "Strategy for case: " << casemodel.case_ << std::endl;
					const z3::Model &model = casemodel.model;

					// do model-to-strategy stuff
					Node *next = input.root.get();
					std::vector<std::reference_wrapper<const std::string>> history;
					print_strategy(next, history, model);
				}
			}
		}
		else {
			std::cout << "NO, it is not" << (weaker ? " weaker immune." : " weak immune.") << std::endl;
			if (options.counterexamples) {
				std::cout << std::endl;
			}
			for(const auto &counterexample : helper.counterexamples) {
				std::cout << "Counterexample for " << counterexample.case_ << ":" << std::endl;
				// the following is just 1 counterexample
				const auto &part = counterexample.parts[0];
				std::cout
					<< "\tPlayer "
					<< input.players[part.player]
					<< " can be harmed if:"
					<< std::endl;

				std::vector<std::vector<std::string>> histories_of_counterexample;
				for(const auto &part : counterexample.parts) {
					
					auto history = part.leaf.compute_history();
					auto branch = input.root.get();
					std::vector<std::string> actions_so_far;
					
					for(auto choice : part.leaf.compute_history()) {
						std::string action = choice.get().action.name;
						bool already_printed = false;
						for (auto const &printed_history : histories_of_counterexample){
							if (printed_history == actions_so_far){
								already_printed = true;
							}
						}
						if((branch->player != part.player) and !already_printed){
							std::cout
								<< "\tPlayer "
								<< input.players[branch->player]
								<< " takes action "
								<< action
								<< " after history "
								<< actions_so_far
								<< std::endl;
							histories_of_counterexample.push_back(actions_so_far);
						}
						actions_so_far.push_back(action);
						auto next = choice.get().node.get();
						if(!next->is_leaf())
							branch = static_cast<Branch *>(next);
					}
				}
			}

			if (options.preconditions){
				std::cout << std::endl;
				std::vector<z3::Bool> conjuncts;
				// std::vector<z3::Bool> testest;
				std::vector<std::vector<z3::Bool>> simplified = helper.precondition_simplify();

				for(const auto &unsat_case : simplified) {
					// negate each case (by disjoining the negated elements), then conjunct all - voila weakest prec to be added to the init constr
					std::vector<z3::Bool> neg_case;
					for (const auto &elem : unsat_case){
						neg_case.push_back(elem.invert());
					}
					z3::Bool disj = disjunction(neg_case);
					conjuncts.push_back(disj);
				}
				z3::Bool raw_prec = conjunction(conjuncts);
				z3::Bool simpl_prec = raw_prec.simplify();
				std::cout << "Weakest Precondition: " << std::endl << "\t" << simpl_prec << std::endl;
			}
		}
	}
}

// instantiate for true/false, prevents linker errors
template void weak_immunity<false>(const Options &, const Input &);
template void weak_immunity<true>(const Options &, const Input &);

// helper struct for computing the collusion resilience property
struct CollusionResilience {
	using ColludingGroup = std::bitset<Input::MAX_PLAYERS>;

	static const bool EXTERNAL_COUNTEREXAMPLES = false;
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
			options,
			input,
			labels,
			property,
			input.collusion_resilience_constraint,
			input.honest_histories[history]
		);
		helper.solve();
		if(!helper.failed){
			std::cout << "YES, it is collusion resilient." << std::endl;
			if(options.strategies){
				std::cout << std::endl;
				for (const auto &casemodel : helper.case_models){
					std::cout << "Strategy for case: " << casemodel.case_ << std::endl;
					const z3::Model &model = casemodel.model;

					// do model-to-strategy stuff
					Node *next = input.root.get();
					std::vector<std::reference_wrapper<const std::string>> history;
					print_strategy(next, history, model);
				}
			}
		}
		else{

			std::cout << "NO, it is not collusion resilient." << std::endl;
			if (options.counterexamples) {
				std::cout << std::endl;
			}
			for(const auto &counterexample : helper.counterexamples) {
				std::cout << "Counterexample for " << counterexample.case_ << ":" << std::endl;

				const auto &part = counterexample.parts[0];
				std::cout << "\tGroup";
				for(size_t player = 0; player < input.players.size(); player++)
					if(part.group[player])
						std::cout << " " << input.players[player];
				std::cout << " profits from deviation if:" << std::endl;


				std::vector<std::vector<std::string>> histories_of_counterexample;
				for(const auto &part : counterexample.parts) {

					auto history = part.leaf.compute_history();
					auto branch = input.root.get();
					std::vector<std::string> actions_so_far;
					for(auto choice : part.leaf.compute_history()) {
						std::string action = choice.get().action.name;
						bool already_printed = false;
						for (auto const &printed_history : histories_of_counterexample){
							if (printed_history == actions_so_far){
								already_printed = true;
							}
						}
						if(part.group[branch->player] and !already_printed){
							std::cout
								<< "\tPlayer "
								<< input.players[branch->player]
								<< " takes action "
								<< action
								<< " after history "
								<< actions_so_far
								<< std::endl;
							histories_of_counterexample.push_back(actions_so_far);
						}
						actions_so_far.push_back(action);
						auto next = choice.get().node.get();
						if(!next->is_leaf())
							branch = static_cast<Branch *>(next);
					}
				}
			}

			if (options.preconditions){
				std::cout << std::endl;
				std::vector<z3::Bool> conjuncts;
				std::vector<std::vector<z3::Bool>> simplified = helper.precondition_simplify();
				for(const auto &unsat_case : simplified) {
					// negate each case (by disjoining the negated elements), then conjunct all - voila weakest prec to be added to the init constr
					std::vector<z3::Bool> neg_case;
					for (const auto &elem : unsat_case){
						neg_case.push_back(elem.invert());
					}
					z3::Bool disj = disjunction(neg_case);
					conjuncts.push_back(disj);
				}
				z3::Bool raw_prec = conjunction(conjuncts);
				z3::Bool simpl_prec = raw_prec.simplify();
				std::cout << "Weakest Precondition: " << std::endl << "\t" << simpl_prec << std::endl;
			}

		}

		
	}
}

// helper struct for computing the practicality property
struct Practicality {
	static const bool EXTERNAL_COUNTEREXAMPLES = true;
	struct CounterExamplePart {};

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

		// loops exchanged below in order to reduce number of counterexample labels
		// for other possible actions a' in a branch...
		for(size_t other = 0; other < branch.choices.size(); other++) {
			Bool counterexample_label;
			const auto &utilities_other = player_utilities_by_choice[other][branch.player];

			// for each possible action a in a branch...
			for(size_t choice = 0; choice < branch.choices.size(); choice++) {
				if(choice == other)
					continue;

				auto action_variable = branch.choices[choice].action.variable;
				const auto &utilities_action = player_utilities_by_choice[choice][branch.player];

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
						auto complete = conjunction.implies(comparison);
						conjuncts.push_back(complete);
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

	// property is the same for all honest histories
	Labels<Practicality> labels;
	auto property = Practicality(options, labels, input.players.size()).compute(*input.root);

	for(unsigned history = 0; history < input.honest_histories.size(); history++) {
		std::cout << std::endl;
		std::cout << "Is history " << input.readable_honest_histories[history] << " practical?" << std::endl;
		SolvingHelper<Practicality> helper(
			options,
			input,
			labels,
			property,
			input.practicality_constraint,
			input.honest_histories[history]
		);
		helper.solve();
		if(!helper.failed) {
			std::cout << "YES, it is practical." << std::endl;
			if(options.strategies){
				std::cout << std::endl;
				for (const auto &casemodel : helper.case_models){
					std::cout << "Strategy for case: " << casemodel.case_ << std::endl;
					const z3::Model &model = casemodel.model;

					// do model-to-strategy stuff
					Node *next = input.root.get();
					std::vector<std::reference_wrapper<const std::string>> history;
					print_strategy(next, history, model);
				}
			}
			}
		else{
			std::cout << "NO, it is not practical." << std::endl;
			if (options.counterexamples) {
				std::cout << std::endl;
			}
			bool stop_gen = false;
			for(size_t i = 0; i < helper.counterexamples.size(); i++) {
				if (stop_gen) {
					break;
				}
				const auto &counterexample = helper.counterexamples[i];
				SolvingHelper<Practicality> ce_helper(
					options,
					input,
					labels,
					property,
					input.practicality_constraint && conjunction(counterexample.case_),
					z3::Bool::TRUE
				);
				z3::Model model;
				Node *next; 
				// if there is no counterexample in the current case, we have to split further
				if (!(model = ce_helper.solve_for_counterexample())){
					// case split necessary to get a counterexample
					auto split = ce_helper.find_split();
					assert(!split.null());
					// append positive and negative case splits
					std::vector<z3::Bool> pos_case;
					std::vector<z3::Bool> neg_case;
					for(const z3::Bool exp: counterexample.case_){
						pos_case.push_back(exp);
						neg_case.push_back(exp);
					}
					pos_case.push_back(split);
					neg_case.push_back(split.invert());
					// positive case
					helper.counterexamples.push_back({
							pos_case,
							std::move(counterexample.parts)
						});
					// negative case
					helper.counterexamples.push_back({
							neg_case,
							std::move(counterexample.parts)
						});
				}
				while((model = ce_helper.solve_for_counterexample())) {
					std::cout << "Counterexample for " << counterexample.case_ << ":" << std::endl;
					next = input.root.get();
					std::vector<std::string> dev_history;
					std::vector<Bool> conflict;
					const auto hon_history = input.readable_honest_histories[history];
					int i = 0;
					bool already_deviated = false;
					unsigned int dev_player;
					unsigned int deviation_point;
					while(!next->is_leaf()) {
						const Branch &current = next->branch();
						for(const auto &choice : current.choices) {
							if(model.assigns<true>(choice.action.variable)) {
								dev_history.push_back(choice.action.name);
								conflict.push_back(choice.action.variable);
								next = choice.node.get();
								if (hon_history[i] == choice.action.name and !already_deviated){
									i++;
								}
								else if (hon_history[i] != choice.action.name and !already_deviated)
								{
									already_deviated = true;
									dev_player = current.player;
									deviation_point = i;
								}
								
							}
						}
					}

					Utility dev_utility = static_cast<Leaf*>(next)->utilities[dev_player];
					const Leaf &honest_leaf = input.honest_history_leaves[history];
					Utility hon_utility = honest_leaf.utilities[dev_player];

					// check if deviation actually better
					Solver actual_ce_solver;
					z3::Bool conj_case = z3::conjunction(counterexample.case_);
					z3::Bool conj_pr = input.practicality_constraint;
					z3::Bool conj_prec = input.initial_constraint;
					z3::Bool conj = z3::conjunction({conj_case, conj_pr, conj_prec});
					z3::Bool ineq = dev_utility > hon_utility;
					z3::Bool impl = z3::conjunction({conj, !ineq});
					actual_ce_solver.assert_(impl);
					auto result = actual_ce_solver.solve();
					// only a deviation with better utility is an actual counterexample
					if(result == z3::Result::UNSAT) {
						std::vector<std::string> dev_subhist;
						for (unsigned int i = deviation_point; i < dev_history.size(); i++){
							dev_subhist.push_back(dev_history[i]);
						}
						std::vector<std::string> hon_subhist;
						for (unsigned int i = 0; i < deviation_point; i++){
							hon_subhist.push_back(dev_history[i]);
						}
						std::cout << "\tPlayer " << input.players[dev_player] << " profits from deviating to " << dev_subhist << " after " << hon_subhist << std::endl;
						ce_helper.solver.assert_(!conjunction(conflict));
						if(!options.all_counterexamples) {
							stop_gen = true;
							break;
						}
					}
				}
			}

			if (options.preconditions){
				std::cout << std::endl;
				std::vector<z3::Bool> conjuncts;
				std::vector<std::vector<z3::Bool>> simplified = helper.precondition_simplify();
				for(const auto &unsat_case : simplified) {
					// negate each case (by disjoining the negated elements), then conjunct all - voila weakest prec to be added to the init constr
					std::vector<z3::Bool> neg_case;
					for (const auto &elem : unsat_case){
						neg_case.push_back(elem.invert());
					}
					z3::Bool disj = disjunction(neg_case);
					conjuncts.push_back(disj);
				}
				z3::Bool raw_prec = conjunction(conjuncts);
				z3::Bool simpl_prec = raw_prec.simplify();
				std::cout << "Weakest Precondition: " << std::endl << "\t" << simpl_prec << std::endl;
			}

		}
	}
}


