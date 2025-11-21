#include <iostream>
#include <bitset>
#include <cassert>
#include <unordered_set>
#include <string>
#include <sstream>
#include <cmath>
#include <fstream>
#include <algorithm>

#include "input.hpp"
#include "options.hpp"
#include "z3++.hpp"
#include "utils.hpp"
#include "property.hpp"
#include "json.hpp"
#include "z3.h"

using z3::Bool;
using z3::Solver;

int count_wi = 0;
int count_weri = 0;
int count_cr = 0;
int count_pr = 0;

int count_wi_repetitions = 0;
int count_weri_repetitions = 0;
int count_cr_repetitions = 0;
int count_pr_repetitions = 0;

int calls_wi = 0;
int calls_weri = 0;
int calls_cr = 0;
int calls_pr = 0;

void reset_global_counters(bool wi, bool weri, bool cr, bool pr) {
	if(wi) {
		count_wi = 0;
		count_wi_repetitions = 0;
	}

	if(weri){
		count_weri = 0;
		count_weri_repetitions = 0;
	}
	
	if(cr){
		count_cr = 0;
		count_cr_repetitions = 0;
	}

	if(pr){
		count_pr = 0;
		count_pr_repetitions = 0;
	}
}

void reset_calls(bool wi, bool weri, bool cr, bool pr) {
	if(wi) {
		calls_wi = 0;
	}

	if(weri){
		calls_weri = 0;
	}
	
	if(cr){
		calls_cr = 0;
	}

	if(pr){
		calls_pr = 0;
	}
}

void print_global_counters(bool wi, bool weri, bool cr, bool pr) {
	std::cout << "\t  Without repetitions:" << std::endl;
	if(wi)
		std::cout << "\t\t  WI:" << count_wi << std::endl;

	if(weri)
		std::cout << "\t\tWERI:" << count_weri << std::endl;

	if(cr)
		std::cout << "\t\t  CR:" << count_cr << std::endl;

	if(pr)
		std::cout << "\t\t  PR:" << count_pr << std::endl;
	
	std::cout << std::endl;
	std::cout << "\t  With repetitions:" << std::endl;
	if(wi)
		std::cout << "\t\t  WI:" << count_wi_repetitions << std::endl;

	if(weri)
		std::cout << "\t\tWERI:" << count_weri_repetitions << std::endl;

	if(cr)
		std::cout << "\t\t  CR:" << count_cr_repetitions << std::endl;

	if(pr)
		std::cout << "\t\t  PR:" << count_pr_repetitions << std::endl;
}

void print_calls_counters(bool wi, bool weri, bool cr, bool pr) {
	if(wi)
		std::cout << "\t\t  WI:" << calls_wi << std::endl;

	if(weri)
		std::cout << "\t\tWERI:" << calls_weri << std::endl;

	if(cr)
		std::cout << "\t\t  CR:" << calls_cr << std::endl;

	if(pr)
		std::cout << "\t\t  PR:" << calls_pr << std::endl;

}

// Need global copy due to issue with dangling references in load_tree
// Alternatively, we can wrap UtilityTuple s.t. it creates a copy and does not just use the reference
extern std::vector<std::vector<std::vector<Utility>>> utilities_storage;


static std::string print_history(const HonestNode *history)
{

	std::string history_representation = history->action + " [ ";
	for (size_t i = 0; i < history->children.size(); i++)
	{
		if (i != 0)
		{
			history_representation = history_representation + ", ";
		}
		history_representation = history_representation + print_history(history->children[i]);
	}

	history_representation = history_representation + " ]";
	return history_representation;
}

// third-party library for parsing JSON
using json = nlohmann::json;

json parse_sat_case(std::vector<z3::Bool> sat_case) {
    json arr_case = json::array();
    if(sat_case.size() == 0) {
        arr_case.push_back("true");
    } else {
        for(auto &case_entry: sat_case) {
            std::stringstream ss;
            ss << case_entry;
            arr_case.push_back(ss.str());
        }
    }
	return arr_case;
}

json parse_utility(const Input &input, std::vector<Utility> utility_to_parse) {
    json utility = json::array();
    unsigned player_index = 0;
    for(auto &u : utility_to_parse) {
        json obj = {{"player", input.players[player_index]}};
        std::stringstream ss;
        ss << u;
        std::string utility_string = ss.str();
        obj["value"] = utility_string;
        utility.push_back(obj);
        player_index++;
    }
    return utility;
}

json parse_property_to_json(std::vector<SubtreeResult> property_result, bool preconditions) {

    json arr_res = json::array();

    for(auto &subtree_result : property_result) {
        // parse satisfied_in_case
        json arr_cases = json::array();
        for(auto &sat_case: subtree_result.satisfied_in_case) {
            json arr_case = parse_sat_case(sat_case);
            arr_cases.push_back(arr_case);
        }

		// parse cases_for_preconditions
        json arr_cases_preconditions = json::array();
        for(auto &sat_case: subtree_result.cases_for_preconditions) {
            json arr_case_precond = parse_sat_case(sat_case);
            arr_cases_preconditions.push_back(arr_case_precond);
        }

		// parse preconditions
        json arr_preconditions = json::array(); // vec vec vec bool
		if(preconditions) {
			for(auto &precond_case: subtree_result.preconditions_for_player_group) { // precond is vec vec
				json arr_preconditions_case = json::array();
				for(auto &precond: precond_case) {
					json arr_precond = parse_sat_case(precond);
					arr_preconditions_case.push_back(arr_precond);
				}
				arr_preconditions.push_back(arr_preconditions_case);
        	}
		}

        json obj = {{"player_group", subtree_result.player_group}, {"satisfied_in_case", arr_cases}, {"cases_for_preconditions", arr_cases_preconditions}, {"preconditions_for_player_group", arr_preconditions}};
        arr_res.push_back(obj);
    }
    return arr_res;
}

json parse_practicality_property_to_json(const Input &input, std::vector<PracticalitySubtreeResult> property_result, bool preconditions) {
    json arr_pr = json::array();
    for(auto &subtree_result : property_result) {
        // parse case
        json arr_case = parse_sat_case(subtree_result._case);
        // parse utilities
        json utilities = json::array();

		for(size_t i = 0; i < subtree_result.utilities.condition.size(); i++) {
			// parse condition

			json condition;

			// optimization for benchmarks with no conditional actions
			// if condition is "true & true & true" just print "true"
			// TODO optimize this by passing the solver as parameter and not instantiating it with every call
			// TODO do this in practicality_rec_old instead of here
			z3::Solver solver_check_validity;
			if(solver_check_validity.solve({!subtree_result.utilities.condition[i]}) == z3::Result::UNSAT) {
				condition = "true";
			}

			else {
				json condition_res = parse_sat_case({subtree_result.utilities.condition[i]});
				assert(condition_res.size() == 1);
				condition = condition_res[0];
			}

			json arr_cond_utils = json::array();

			for(const auto &util_tuple : subtree_result.utilities.utilities[i]) {
				json parsed_utility = parse_utility(input, util_tuple.leaf);
				arr_cond_utils.push_back(parsed_utility);
			}

			json cond_util_obj = {{"conditional_actions", condition}, {"utilities", arr_cond_utils}};
			utilities.push_back(cond_util_obj);
		}

        // for(auto &utility_list : subtree_result.utilities) {
        //     // parse utility
        //     json utility = parse_utility(input, utility_list);
        //     utilities.push_back(utility);
        // }

		// parse preconditions
        json arr_preconditions = json::array();
		if(preconditions) {
			for(auto &precond: subtree_result.preconditions_for_current_case) {
				json arr_precond = parse_sat_case(precond);
				arr_preconditions.push_back(arr_precond);
        	}
		}

        json obj = {{"case", arr_case}, {"conditional_utilities", utilities}, {"preconditions_for_current_case", arr_preconditions}};

		arr_pr.push_back(obj);
    }
    return arr_pr;
}

void print_subtree_result_to_file(const Input &input, std::string file_name, Subtree &subtree, bool preconditions) {
    std::ofstream outputFile(file_name);
    if (outputFile.is_open()) {
        // Convert the subtree object to JSON
        json subtree_json;

        json arr_wi = parse_property_to_json(subtree.weak_immunity, preconditions);
        json arr_weri = parse_property_to_json(subtree.weaker_immunity, preconditions);
        json arr_cr = parse_property_to_json(subtree.collusion_resilience, preconditions);
        json arr_pr = parse_practicality_property_to_json(input, subtree.practicality, preconditions);
        json arr_honest_utility = json::array();


		for(auto pair: subtree.honest_utility) {
			json condition = parse_sat_case(pair.conditional_actions);
			json utility = parse_utility(input, pair.utility);
			json obj = {{"conditional_actions", condition}, {"utility", utility}};
			arr_honest_utility.push_back(obj);
		}

        subtree_json["subtree"]["weak_immunity"] = arr_wi;
        subtree_json["subtree"]["weaker_immunity"] = arr_weri;
        subtree_json["subtree"]["collusion_resilience"] = arr_cr;
        subtree_json["subtree"]["practicality"] = arr_pr;
        subtree_json["subtree"]["honest_utility"] = arr_honest_utility;
		subtree_json["subtree"]["solved_for_weak_conditional_actions"] = subtree.solved_weak_cond_actions;
		subtree_json["subtree"]["solved_for_preconditions"] = subtree.solved_for_preconditions;

        // Print the JSON representation
        outputFile << subtree_json.dump(4); // Pretty print with 4 spaces
        outputFile.close();

    } else {
        std::cerr << "Failed to create the file." << std::endl;
    }
}

z3::Bool get_split_approx(z3::Solver &solver, Options options, Utility a, Utility b, bool wi, bool weri, bool cr, bool pr)
{
	if(options.count_calls) {
		if (wi)
			calls_wi++;
		else if (weri)
			calls_weri++;
		else if (cr)
			calls_cr++;
		else if (pr)
			calls_pr++;
	}
	// split on a>=b
	if (solver.solve({a.real < b.real}) == z3::Result::UNSAT)
	{
		if(options.count_calls) {
			if (wi)
				calls_wi++;
			else if (weri)
				calls_weri++;
			else if (cr)
				calls_cr++;
			else if (pr)
				calls_pr++;
		}
		if (solver.solve({a.infinitesimal >= b.infinitesimal}) == z3::Result::UNSAT)
		{
			return a.real > b.real;
		}
		else
		{
			return a.infinitesimal >= b.infinitesimal;
		}
	}
	// we don't know whether their real parts are >=, assert it
	else
	{
		return a.real >= b.real;
	}
}

// const Node& get_honest_leaf(Node *node, const std::vector<std::string> &history, unsigned index) {
// 	switch(node->type()) {
//     case NodeType::LEAF:
// 		return node->leaf();
//     case NodeType::SUBTREE:
//         return node->subtree();
// 	case NodeType::BRANCH:
// 		break;
//     // no need for default
//     }

// 	unsigned next_index = index + 1;
// 	return get_honest_leaf(node->branch().get_choice(history[index]).node.get(), history, next_index);
// }

bool utility_tuples_eq(UtilityTuple tuple1, UtilityTuple tuple2)
{
	if (tuple1.size() != tuple2.size())
	{
		return false;
	}
	else
	{
		bool all_same = true;
		for (size_t i = 0; i < tuple1.size(); i++)
		{
			if (!tuple1[i].is(tuple2[i]))
			{
				all_same = false;
			}
		}
		return all_same;
	}
	return false;
}

std::vector<std::string> index2player(const Input &input, PropertyType property, unsigned index) {

	if(property==PropertyType::WeakImmunity || property==PropertyType::WeakerImmunity) {
		return {input.players[index]};
	}

	std::bitset<Input::MAX_PLAYERS> group = index;
	std::vector<std::string> players;

	for (size_t player = 0; player < input.players.size(); player++) {
		if (group[player]) {
			players.push_back(input.players[player]);
		}
	}

	return players;
}

bool weak_immunity_rec(const Input &input, z3::Solver &solver, const Options &options, Node *node, unsigned player, bool weaker, bool consider_prob_groups)
{
	if(weaker) {
		count_weri_repetitions++;
		if(!node->checked_weri) {
			count_weri++;
			node->checked_weri = true;
		}
	} else {
		count_wi_repetitions++;
		if(!node->checked_wi) {
			count_wi++;
			node->checked_wi = true;
		}
	}

	if (node->is_leaf())
	{
		const auto &leaf = node->leaf();

		// if ((player < leaf.problematic_group) && consider_prob_groups){
		// 	return true;
		// }

		// NEW: Allow conditions in leaves
		bool at_least_one_non_contradictory_condition = false;

		bool result = true;

		for (size_t i = 0; i < leaf.conditions.size(); i++) {

			z3::Frame leafFrame(solver);
			solver.assert_(leaf.conditions[i]);

			if (solver.solve() != z3::Result::UNSAT)
			{
				at_least_one_non_contradictory_condition = true;
				bool for_sure_secure = false;

				// known utility for us
				auto utility = leaf.utilities[i].leaf[player];

				z3::Bool condition = weaker ? utility.real >= z3::Real::ZERO : utility >= Utility{z3::Real::ZERO, z3::Real::ZERO};

				if(options.count_calls) {
					weaker ? calls_weri++ : calls_wi++;
				}
				if (solver.solve({!condition}) == z3::Result::UNSAT)
				{
					for_sure_secure = true;
					if (consider_prob_groups)
					{
						leaf.problematic_group = player + 1;
					}

					if(options.weak_conditional_actions) {
						return true;
					}
				}

				if(options.count_calls) {
					weaker ? calls_weri++ : calls_wi++;
				}
				bool for_sure_insecure = false;
				if (solver.solve({condition}) == z3::Result::UNSAT)
				{
					for_sure_insecure = true;
					if(options.strong_conditional_actions) {
						leaf.reset_reason();

						if(options.preconditions) {
							result = false;
							leaf.violated_conditions.push_back({leaf.conditions[i]});
						} else {
							return false;
						}
					}
				}

				// if (consider_prob_groups) {
				// 	leaf.problematic_group = player;
				// }

				// for weak conditional actions
				if (options.weak_conditional_actions && leaf.reason.null() && !for_sure_insecure) {
					leaf.reason = weaker ? utility.real >= z3::Real::ZERO : get_split_approx(solver, options, utility, Utility{z3::Real::ZERO, z3::Real::ZERO}, !weaker, weaker, false, false);
				} else if (options.strong_conditional_actions && !for_sure_secure) {
					if(!for_sure_insecure && leaf.reason.null() ) {
						leaf.reason = weaker ? utility.real >= z3::Real::ZERO : get_split_approx(solver, options, utility, Utility{z3::Real::ZERO, z3::Real::ZERO}, !weaker, weaker, false, false);
					}
					
					
					if(options.preconditions) {
						result = false;
						leaf.violated_conditions.push_back({leaf.conditions[i]});
					} else {
						return false;
					}
				}
				
				//input.set_reset_point(leaf);

			}
		}

		if(options.strong_conditional_actions && options.preconditions) {
			return result;
		}

		// weak_conditional actions -> return false
		// we've been through all conditions and never found 
		// a condition for which the property is satisfied

		// strong_conditional actions -> return true
		// we've been through all conditions and did not found
		// a condition for which the property is violated
		return options.weak_conditional_actions ? at_least_one_non_contradictory_condition ? false : true : true;
		
	}

	else if (node->is_subtree()){

		const auto &subtree = node->subtree();
		
		/*if ((player < subtree.problematic_group) && consider_prob_groups){
			return true;
		}*/

		if(subtree.solved_weak_cond_actions && options.strong_conditional_actions) {
			std::cerr << "checkmate: subtree is solved for weak conditional actions. Thus, supertree cannot be solved for strong conditional actions... " << std::endl;
			std::exit(EXIT_FAILURE);
		}

		if(!subtree.solved_weak_cond_actions && options.weak_conditional_actions) {
			std::cerr << "checkmate: subtree is solved for strong conditional actions. Thus, supertree cannot be solved for weak conditional actions... " << std::endl;
			std::exit(EXIT_FAILURE);
		}

		if(subtree.solved_for_preconditions & !options.preconditions) {
			std::cerr << "checkmate: subtree is solved with preconditions. Thus, supertree cannot be solved without preconditions... " << std::endl;
			std::exit(EXIT_FAILURE);
		}

		if(!subtree.solved_for_preconditions & options.preconditions) {
			std::cerr << "checkmate: subtree is solved without preconditions. Thus, supertree cannot be solved with preconditions... " << std::endl;
			std::exit(EXIT_FAILURE);
		}

		// look up current player:
		// 		if disj_of_cases (in satisfied_for_case) is equivalent to current case or weaker we return true
		//			e.g. satisfied for case [a+1>b, b>a+1], current_case is a>b;
		//				 since a>b => a+1>b, we conclude satisfied for a>b (i.e. return true)
		// 		else if disj_of_cases not disjoint from current case --> need case split (set the first of these not disjoint ones to be reason)
		//			e.g. satisfied for case [a>b], current_case is a>0;
		//  			hence whether satisfied or not depends on b, so we add a>b as the reason
		// 		else return false
		//			e.g. satisfied for case [a>b], current case a < b, then for sure not satisfied, make sure reason is empty and return false

		// search for SubtreeResult in weak(er)_immunity that corresponds to the current player

		const std::vector<SubtreeResult> &subtree_results = weaker ? subtree.weaker_immunity : subtree.weak_immunity;

		std::string player_name = input.players[player];

		for (const SubtreeResult &subtree_result : subtree_results) {

			assert(subtree_result.player_group.size() == 1);
			if (subtree_result.player_group[0] == player_name) {

				// (init_cons && wi_cons && curent_case) => disj_of_cases VALID
				// ! (init_cons && wi_cons && current_case) || disj_of_cases VALID
				// (init_cons && wi_cons && current_case) && !disj_of_cases UNSAT
				// init_cons && wi_cons && current_case    && !disj_of_cased UNSAT

				std::vector<z3::Bool> cases_as_conjunctions = {};

				for (auto _case: subtree_result.satisfied_in_case) {
					// try to optimize: if only 1 -> no need for conjunction
					if(_case.size() == 1) {
						cases_as_conjunctions.push_back(_case[0]);
					} else {
						cases_as_conjunctions.push_back(z3::conjunction(_case));
					}
				}

				z3::Bool disj_of_cases = z3::disjunction(cases_as_conjunctions);

				if(cases_as_conjunctions.size() == 1) {
					disj_of_cases = cases_as_conjunctions[0];
				} else {
					disj_of_cases = z3::disjunction(cases_as_conjunctions);
				}

				if(options.count_calls) {
					weaker ? calls_weri++ : calls_wi++;
				}
				z3::Result z3_result_implied = solver.solve({!disj_of_cases});

				if (z3_result_implied == z3::Result::UNSAT) {
					/*if (consider_prob_groups) {
						subtree.problematic_group = player + 1;
					}*/
					return true;
				} else {

					// compute if current_case and case are disjoint:
					// is it sat that init && wi && case && current_case?
					// if no, then disjoint

					if(options.count_calls) {
						weaker ? calls_weri++ : calls_wi++;
					}
					z3::Result z3_result_disjoint = solver.solve({disj_of_cases});

					if (z3_result_disjoint == z3::Result::SAT) {
						// set reason
						subtree.reason = disj_of_cases;
						return false;
					}

					// if (consider_prob_groups) {
					// 	subtree.problematic_group = player;
					// }
					//input.set_reset_point(subtree);

					if(options.preconditions) {
						// we now look at subtree.cases_for_preconditions and subtree.preconditions_for_player_group
						// cases_for_preconditions[i] is a case and preconditions_for_player_group[i] specifies which conditions 
						// are violated for this case that is, what needs to be propagated to be later (negated and) used for preconditions

						// we proceed as follows:
						// go through each case from cases_for_preconditions
						// if not case and current unsat
						// add case && preconditions_for_player_group[i] to subtree.violated_conditions

						// examples
						// 1) case a<b and c<=d ; precond p>=0 ; current a < b
						// 		add (a<b and c<=d and p>= 0) to subtree violated
						// 2) case a<b ; precond p>=0 ; current a < b and c <= d
						// 		add (a<b and p>= 0) to subtree violated
						// 3) case a<b ; precond p>=0 ; current a >= b 
						// 		do nothing
						// 4) case e<f ; precond p>=0 ; current a<b 
						// 		add (e<f and p>= 0) to subtree violated

						for(size_t i = 0; i < subtree_result.cases_for_preconditions.size(); i++) {

							auto case_violated = subtree_result.cases_for_preconditions[i];
							
							if(solver.solve(case_violated) != z3::Result::UNSAT) {

								auto violated_for_case = subtree_result.preconditions_for_player_group[i];

								std::vector<z3::Bool> vec_to_add = {};

								auto case_conj = z3::conjunction(case_violated);

								for(auto violated_case : violated_for_case) {

									std::vector<z3::Bool> entries = {case_conj};
									entries.insert(entries.end(), violated_case.begin(), violated_case.end());
									auto conj = z3::conjunction(entries);
									vec_to_add.push_back(conj);
								}

								subtree.violated_conditions.push_back(vec_to_add);
							}	
						}
					}
					
					return false;
				}
			}
		}
	}

	const auto &branch = node->branch();

	// if ((player < branch.problematic_group) && consider_prob_groups){
	// 	return true;
	// }

	// else we deal with a branch
	if (player == branch.player)
	{
		// player behaves honestly
		if (branch.honest)
		{
			// if we are along the honest history, we want to take an honest strategy

			bool at_least_one_non_contradictory_condition = false;
			bool result = true;

			for (size_t i = 0; i < branch.conditions.size(); i++)
			{

				z3::Frame f1(solver);
				solver.assert_(branch.conditions[i].condition);

				// while we refine the case by adding a case split, we may have to prune
				// the tree of contradictory actions. In practice, we can ignore the
				// branches belonging to contradictory actions "on the fly"; see next line
				if(options.count_calls) {
					weaker ? calls_weri++ : calls_wi++;
				}
				if (solver.solve() != z3::Result::UNSAT)
				{
					at_least_one_non_contradictory_condition = true;

					auto &honest_choice = branch.get_honest_child(i);
					auto *subtree = honest_choice.node;

					if(options.strategies) {
						// set chosen action, needed for printing strategy
						branch.strategy[i] = honest_choice.action;
					}

					// the honest choice must be weak immune
					if (weak_immunity_rec(input, solver, options, subtree, player, weaker, consider_prob_groups))
					{
						// if (consider_prob_groups) {
						// 	branch.problematic_group = player + 1;
						// }

						if (options.weak_conditional_actions)
						{
							return true;
						}
					}
					else
					{
						if (branch.reason.null())
						{
							branch.reason = subtree->reason;
						}
						input.set_reset_point(branch);

						if(options.counterexamples && subtree->reason.null()) {
							branch.use_cond_for_strong_ce[i] = true;
						}

						if (options.strong_conditional_actions)
						{
							if(options.preconditions) {
								result = false;
								for(auto &violated_cond : subtree->violated_conditions) {
									std::vector<z3::Bool> updated_conds = {branch.conditions[i].condition};
									updated_conds.insert(updated_conds.end(), violated_cond.begin(), violated_cond.end());
									branch.violated_conditions.push_back(updated_conds);
								}
							} else if (options.all_counterexamples) {
								result = false;
							}
							else {
								return false;
							}
							
						}
					}
				}

				// solver.pop(); , done implicitly because the frame dies
			}
			// in the loop above
			// mode weak_conditional_actions: we return as soon as we find one which is ok
			// mode strong_conditional_actions: we return as soon as we find one which is not ok
			// so if we reach the code after the loop, only one the following cases is possible
			// mode weak_conditional_actions and no condition is secure -> return false
			// mode strong_conditional_actions and all conditions are secure -> return true

			if(options.strong_conditional_actions && (options.preconditions || options.all_counterexamples)) {
				return result;
			}
			return options.weak_conditional_actions ? at_least_one_non_contradictory_condition ? false : true : true;
		}

		// otherwise we can take any strategy we please as long as it's weak immune
		// weak version of conditional actions: we need to have one such option for one condition
		// strong version of conditional actions: we need to have one such option for each condition
		bool at_least_one_non_contradictory_condition = false;
		bool result = true;
		for (size_t j = 0; j < branch.conditions.size(); j++)
		{
			std::vector<z3::Bool> disjunctions;
			z3::Frame f2(solver);
			solver.assert_(branch.conditions[j].condition);

			// while we refine the case by adding a case split, we may have to prune
			// the tree of contradictory actions. In practice, we can ignore the
			// branches belonging to contradictory actions "on the fly"; see next line
			if(options.count_calls) {
				weaker ? calls_weri++ : calls_wi++;
			}
			if (solver.solve() != z3::Result::UNSAT)
			{
				at_least_one_non_contradictory_condition = true;
				bool secure_choice_found = false;
				z3::Bool reason;
				unsigned reset_index;
				unsigned i = 0;
				for (const Choice &choice : branch.conditions[j].children)
				{
					if (weak_immunity_rec(input, solver, options, choice.node, player, weaker, consider_prob_groups))
					{
						if(options.strategies) {
							// set chosen action, needed for printing strategy
							branch.strategy[j] = choice.action;
						}
						
						// if (consider_prob_groups) {
						// 		branch.problematic_group = player + 1;
						// }

						secure_choice_found = true;
						if (options.weak_conditional_actions) {
							return true;
						} else if (options.strong_conditional_actions && !options.preconditions) {
							break; // go to next condition
						}

					} else {
						std::vector<z3::Bool> disjuncts;
						for(auto &cond:choice.node->violated_conditions) {
							disjuncts.push_back(z3::conjunction(cond));
						}
						disjunctions.push_back(z3::disjunction(disjuncts));
					}
					
					if ((!choice.node->reason.null()) && (reason.null()))
					{
						reason = choice.node->reason;
						// reset_index = i;
					}
					i++;
				}
				if (!reason.null())
				{
					branch.reason = reason;
					// input.set_reset_point(*branch.choices[reset_index].node);
				}

				if(options.counterexamples && reason.null()) {
					branch.use_cond_for_strong_ce[j] = true;
				}

				if (options.strong_conditional_actions && !secure_choice_found)
				{
					if(options.preconditions) {
						result = false;
						std::vector<z3::Bool> precond = {branch.conditions[j].condition};
						precond.insert(precond.end(), disjunctions.begin(), disjunctions.end());
						branch.violated_conditions.push_back(precond);
					} else if (options.all_counterexamples) {
						result = false;
					}
					else {
						return false;
					}
				}
			}

			// solver.pop(); , done implicitly because the frame dies
		}

		if(options.strong_conditional_actions && (options.preconditions || options.all_counterexamples)) {
			return result;
		}

		return options.weak_conditional_actions ? at_least_one_non_contradictory_condition ? false : true : true;
	}
	else
	{
		// if we are not the honest player, we could do anything,
		// so all branches should be weak immune for the player
		// weak version of conditional actions: we need to ensure this for one condition
		// strong version of conditional actions: we need to ensure this for each condition
		bool at_least_one_non_contradictory_condition = false;
		bool result_top_level = true;
		for (size_t j = 0; j < branch.conditions.size(); j++)
		{
			z3::Frame f3(solver);
			solver.assert_(branch.conditions[j].condition);

			// while we refine the case by adding a case split, we may have to prune
			// the tree of contradictory actions. In practice, we can ignore the
			// branches belonging to contradictory actions "on the fly"; see next line
			if(options.count_calls) {
				weaker ? calls_weri++ : calls_wi++;
			}
			if (solver.solve() != z3::Result::UNSAT)
			{
				at_least_one_non_contradictory_condition = true;
				bool not_secure_choice_found = false;
				bool result = true;
				z3::Bool reason;
				unsigned reset_index;
				//unsigned i = 0;
				
				for (const Choice &choice : branch.conditions[j].children)
				{
					if (!weak_immunity_rec(input, solver, options, choice.node, player, weaker, consider_prob_groups))
					{
						if (choice.node->reason.null()){
							if (options.counterexamples) {
								branch.counterexample_choices[j].push_back(choice.action);
								branch.use_cond_for_strong_ce[j] = true;
							}
							// if (!options.all_counterexamples){
							//  	return false;
							// } else {
								result = false;
							// }
						} else {
							if (result && reason.null()){
								reason = choice.node->reason;
								// reset_index = i;
							}
							result = false;
						}
						not_secure_choice_found = true;

						// we have found one condition where not all choices are secure
						if (options.strong_conditional_actions)
						{
							if (!reason.null())
							{
								branch.reason = reason;
								// input.set_reset_point(*branch.choices[reset_index].node);
							}

							if(options.preconditions) {
								result_top_level = false;
								for(auto &cond: choice.node->violated_conditions) {
									std::vector<z3::Bool> precond = {branch.conditions[j].condition};
									precond.insert(precond.end(), cond.begin(), cond.end());
									branch.violated_conditions.push_back(precond);
								}
							} else if (options.all_counterexamples) {
								result_top_level = false;
							} else {
								return false;
							}
							
						}
					
						if(!options.all_counterexamples && reason.null()) {
							break; // go to next condition
						}
					}
					//i++;
				}
				if (!reason.null())
				{
					branch.reason = reason;
					// input.set_reset_point(*branch.choices[reset_index].node);
				}
				// if (result && consider_prob_groups) {
				// 	branch.problematic_group = player + 1;
				// }
				// return result;

				// we have one condition where all choices are secure
				if (options.weak_conditional_actions && !not_secure_choice_found)
				{
					return true;
				}
			}

			// solver.pop(); , done implicitly because the frame dies
		}

		if(options.strong_conditional_actions && (options.preconditions || options.all_counterexamples)) {
			return result_top_level;
		}

		return options.weak_conditional_actions ? at_least_one_non_contradictory_condition ? false : true : true;
	}
}

bool collusion_resilience_rec(const Input &input, z3::Solver &solver, const Options &options, Node *node, std::bitset<Input::MAX_PLAYERS> group, unsigned players, uint64_t group_nr, bool consider_prob_groups)
{
	count_cr_repetitions++;
	if(!node->checked_cr) {
		count_cr++;
		node->checked_cr = true;
	}

	// case branch: just copy paste parts from weak immunity
	// case leaf:
	// 	- we do not pass "Utility honest_total" as an argument to this function
	//	- instead before calling this function we traverse the tree and in the root we save a vector of
	//   ({cond_action && ... && cond_action}, honest_utility) pairs
	//  - now when we need to check whether a leaf is cr we iterate over all elements from the vector and check for each pair
	//  	- if UNSAT when 1st element of the pair added to current solver -> continue (incompatible, no need to check anything)
	// 		- else make sure that 2nd element of pair i.e. honest utility is >= current utility in the leaf
	//		- if  !honest_total >= group_utility UNSAT continue with next element of vector
	// 		- if honest_total >= group_utility UNSAT return false immediately, set reason to null before returning
	// 		- else return false

	if (node->is_leaf())
	{
		const auto &leaf = node->leaf();

		// if  ((group_nr < leaf.problematic_group) && consider_prob_groups){
		// 	return true;
		// }

		// NEW: Allow conditions in leaves
		bool at_least_one_non_contradictory_condition = false;

		bool result = true;

		for (size_t i = 0; i < leaf.conditions.size(); i++) {

			z3::Frame leafFrame(solver);
			solver.assert_(leaf.conditions[i]);

			if (solver.solve() != z3::Result::UNSAT)
			{
				at_least_one_non_contradictory_condition = true;
				bool for_sure_secure = false;

				// compute the total utility for the player group...
				Utility group_utility{z3::Real::ZERO, z3::Real::ZERO};

				for (size_t player = 0; player < players; player++)
					if (group[player])
						group_utility = group_utility + leaf.utilities[i].leaf[player];

				bool can_decide_for_all = true;
				bool insecure_for_sure_found = false;
				
				// ..and compare it to all honest utilities that are "compatible"
				for (auto pair : input.cond_actions_honest_utility_pairs)
				{

					if(options.count_calls) {
						calls_cr++;
					}
					if (solver.solve({pair.conditional_actions}) == z3::Result::UNSAT)
					{
						// incompatible, no need to check anything
						continue;
					}

					// compute honest_total for this pair
					Utility honest_total{z3::Real::ZERO, z3::Real::ZERO};
					for (size_t player = 0; player < players; player++)
						if (group[player])
							honest_total = honest_total + pair.utility[player];

					auto condition = honest_total >= group_utility;

					if(options.count_calls) {
						calls_cr++;
					}
					if (solver.solve({!condition}) == z3::Result::UNSAT)
					{
						// nothing to do in this case
						//  we can continue
						//  this "if" can be completely removed in future
						continue;
					}

					if(options.count_calls) {
						calls_cr++;
					}

					bool for_sure_insecure = false;
					if (solver.solve({condition}) == z3::Result::UNSAT)
					{
						if(options.strategies) {
							node->violates_cr[group_nr - 1] = true;
						}

						for_sure_insecure = true;
						insecure_for_sure_found = true;

						if(options.strong_conditional_actions) {
							// we need to reset the reason because it can be the case that the reason is set from
							// a previous pair, and we want to return false with no reason (because we know that
							// honest < group_utility so we do not want to split unnecessarily)
							leaf.reset_reason(); 
							//leaf.reason = ::new (&leaf.reason) z3::Bool();
							
							if(options.preconditions) {
								result = false;
								leaf.violated_conditions.push_back({leaf.conditions[i]});
							} else {
								return false;
							}
						}

						if(!(options.strong_conditional_actions && options.preconditions)) {
							break; // go to next condition
						}
						
					}
					
					can_decide_for_all = false;
					if (options.weak_conditional_actions && leaf.reason.null() && !for_sure_insecure) {
						leaf.reason = get_split_approx(solver, options, honest_total, group_utility, false, false, true, true);
					} else if (options.strong_conditional_actions) {
						if(!for_sure_insecure && leaf.reason.null()) {
							leaf.reason = get_split_approx(solver, options, honest_total, group_utility, false, false, true, true);
						}

						if(options.preconditions) {
							result = false;
							leaf.violated_conditions.push_back({leaf.conditions[i]});
						} else {
							return false;
						}
					}
				}

				if(options.weak_conditional_actions && can_decide_for_all && !insecure_for_sure_found) {
					return true;
				}				

				// in the future we need to add a boolean which ensures that we only enter the
				// first "if". If this is the case we can increment "solved_for_group".

				// if (consider_prob_groups) {
				// 	leaf.problematic_group = group_nr;
				// }

				// input.set_reset_point(leaf);

			}

		}

		if(options.strong_conditional_actions && options.preconditions) {
			return result;
		}

		return options.weak_conditional_actions ? at_least_one_non_contradictory_condition ? false : true : true;

	}

	else if (node->is_subtree()){

		const auto &subtree = node->subtree();

		// if  ((group_nr < subtree.problematic_group) && consider_prob_groups){
		// 	return true;
		// }

		if(subtree.solved_weak_cond_actions && options.strong_conditional_actions) {
			std::cerr << "checkmate: subtree is solved for weak conditional actions. Thus, supertree cannot be solved for strong conditional actions... " << std::endl;
			std::exit(EXIT_FAILURE);
		}

		if(!subtree.solved_weak_cond_actions && options.weak_conditional_actions) {
			std::cerr << "checkmate: subtree is solved for strong conditional actions. Thus, supertree cannot be solved for weak conditional actions... " << std::endl;
			std::exit(EXIT_FAILURE);
		}

		if(subtree.solved_for_preconditions & !options.preconditions) {
			std::cerr << "checkmate: subtree is solved with preconditions. Thus, supertree cannot be solved without preconditions... " << std::endl;
			std::exit(EXIT_FAILURE);
		}

		if(!subtree.solved_for_preconditions & options.preconditions) {
			std::cerr << "checkmate: subtree is solved without preconditions. Thus, supertree cannot be solved with preconditions... " << std::endl;
			std::exit(EXIT_FAILURE);
		}

		// look up current player_group:
		// 		if disj_of_cases (in satisfied_for_case) that is equivalent to current case or weaker we return true
		//			e.g. satisfied for case [a+1>b, b>a+1], current_case is a>b;
		//				 since a>b => a+1>b, we conclude satisfied for a>b (i.e. return true)
		// 		else if disj_of_cases not disjoint from current case --> need case split (set the first of these not disjoint ones to be reason)
		//			e.g. satisfied for case [a>b], current_case is a>0;
		//  			hence whether satisfied or not depends on b, so we add a>b as the reason
		// 		else return false
		//			e.g. satisfied for case [a>b], current case a < b, then for sure not satisfied, make sure reason is empty and return false

		// search for SubtreeResult in weak(er)_immunity that corresponds to the current player

		const std::vector<SubtreeResult> &subtree_results = subtree.collusion_resilience;
		std::vector<std::string> player_names = index2player(input, PropertyType::CollusionResilience, group_nr);

		for (const SubtreeResult &subtree_result : subtree_results) {
			// find the correct subtree_result
			bool correct_subtree = true;
			if (subtree_result.player_group.size() != player_names.size()){
				correct_subtree = false;
			} else {
				for (const std::string &subtree_player : subtree_result.player_group){
					int counted = 0;
					for (const auto &name : player_names){
						if(name == subtree_player){
							counted++;
						}
					}
					if (counted == 0 ) {
						correct_subtree = false;
						break;
					}
				}
				if (correct_subtree){

					// (init_cons && wi_cons && curent_case) => disj_of_cases VALID
					// ! (init_cons && wi_cons && current_case) || disj_of_cases VALID
					// (init_cons && wi_cons && current_case) && !disj_of_cases UNSAT
					// init_cons && wi_cons && current_case    && !disj_of_cased UNSAT

					std::vector<z3::Bool> cases_as_conjunctions = {};

					for (auto _case: subtree_result.satisfied_in_case) {
						// try to optimize: if only 1 -> no need for conjunction
						if(_case.size() == 1) {
							cases_as_conjunctions.push_back(_case[0]);
						} else {
							cases_as_conjunctions.push_back(z3::conjunction(_case));
						}
					}
					z3::Bool disj_of_cases;

					if(cases_as_conjunctions.size() == 1) {
						disj_of_cases = cases_as_conjunctions[0];
					} else {
						disj_of_cases = z3::disjunction(cases_as_conjunctions);
					}

					if(options.count_calls) {
						calls_cr++;
					}
					z3::Result z3_result_implied = solver.solve({!disj_of_cases});

					if (z3_result_implied == z3::Result::UNSAT) {
						// if (consider_prob_groups) {
						// 	subtree.problematic_group = group_nr + 1;
						// }
						return true;
					} else {

						// compute if current_case and case are disjoint:
						// is it sat that init && wi && case && current_case?
						// if no, then disjoint

						if(options.count_calls) {
							calls_cr++;
						}
						z3::Result z3_result_disjoint = solver.solve({disj_of_cases});

						if (z3_result_disjoint == z3::Result::SAT) {
							// set reason
							subtree.reason = disj_of_cases;
						}

						// if (consider_prob_groups) {
						// 	subtree.problematic_group = group_nr;
						// }
						// input.set_reset_point(subtree);

						if(options.preconditions) {
							// we now look at subtree.cases_for_preconditions and subtree.preconditions_for_player_group
							// cases_for_preconditions[i] is a case and preconditions_for_player_group[i] specifies which conditions 
							// are violated for this case that is, what needs to be propagated to be later (negated and) used for preconditions

							// we proceed as follows:
							// go through each case from cases_for_preconditions
							// if not case and current unsat
							// add case && preconditions_for_player_group[i] to subtree.violated_conditions

							// examples
							// 1) case a<b and c<=d ; precond p>=0 ; current a < b
							// 		add (a<b and c<=d and p>= 0) to subtree violated
							// 2) case a<b ; precond p>=0 ; current a < b and c <= d
							// 		add (a<b and p>= 0) to subtree violated
							// 3) case a<b ; precond p>=0 ; current a >= b 
							// 		do nothing
							// 4) case e<f ; precond p>=0 ; current a<b 
							// 		add (e<f and p>= 0) to subtree violated

							for(size_t i = 0; i < subtree_result.cases_for_preconditions.size(); i++) {

								auto case_violated = subtree_result.cases_for_preconditions[i];
								
								if(solver.solve(case_violated) != z3::Result::UNSAT) {

									auto violated_for_case = subtree_result.preconditions_for_player_group[i];

									std::vector<z3::Bool> vec_to_add = {};

									auto case_conj = z3::conjunction(case_violated);

									for(auto violated_case : violated_for_case) {

										std::vector<z3::Bool> entries = {case_conj};
										entries.insert(entries.end(), violated_case.begin(), violated_case.end());
										auto conj = z3::conjunction(entries);
										vec_to_add.push_back(conj);
									}

									subtree.violated_conditions.push_back(vec_to_add);
								}	
							}
						}
						
						return false;
					}
				}
			}
		}
	}


	const auto &branch = node->branch();

	// if  ((group_nr < branch.problematic_group) && consider_prob_groups ){
	// 	return true;
	// }

	// else we deal with a branch
	if (!group[branch.player])
	{

		// player behaves honestly
		if (branch.honest)
		{
			// if we are along the honest history, we want to take an honest strategy

			bool at_least_one_non_contradictory_condition = false;
			bool result = true;

			for (size_t i = 0; i < branch.conditions.size(); i++)
			{

				z3::Frame f1(solver);
				solver.assert_(branch.conditions[i].condition);

				// while we refine the case by adding a case split, we may have to prune
				// the tree of contradictory actions. In practice, we can ignore the
				// branches belonging to contradictory actions "on the fly"; see next line
				if(options.count_calls) {
					calls_cr++;
				}
				if (solver.solve() != z3::Result::UNSAT)
				{

					at_least_one_non_contradictory_condition = true;

					auto &honest_choice = branch.get_honest_child(i);
					auto *subtree = honest_choice.node;

					if(options.strategies) {
						// set chosen action, needed for printing strategy
						branch.strategy[i] = honest_choice.action;
					}

					// the honest choice must be collusion resilient
					if (collusion_resilience_rec(input, solver, options, subtree, group, players, group_nr, consider_prob_groups))
					{
						// if (consider_prob_groups) {
						// 	branch.problematic_group = player + 1;
						// }

						if (options.weak_conditional_actions)
						{
							return true;
						}
					}
					else
					{
						if (branch.reason.null())
						{
							branch.reason = subtree->reason;
						}
						// input.set_reset_point(branch);

						if(options.counterexamples && subtree->reason.null()) {
							branch.use_cond_for_strong_ce[i] = true;
						}

						if (options.strong_conditional_actions)
						{
							if(options.preconditions) {
								result = false;
								for(auto &violated_cond : subtree->violated_conditions) {
									std::vector<z3::Bool> updated_conds = {branch.conditions[i].condition};
									updated_conds.insert(updated_conds.end(), violated_cond.begin(), violated_cond.end());
									branch.violated_conditions.push_back(updated_conds);
								}
							} else if (options.all_counterexamples) {
								result = false;
							} else {
								return false;
							}
						}
					}
				}

				// solver.pop(); , done implicitly because the frame dies
			}
			// in the loop above
			// mode weak_conditional_actions: we return as soon as we find one which is ok
			// mode strong_conditional_actions: we return as soon as we find one which is not ok
			// so if we reach the code after the loop, only one the following cases is possible
			// mode weak_conditional_actions and no condition is secure -> return false
			// mode strong_conditional_actions and all conditions are secure -> return true
			
			if(options.strong_conditional_actions && (options.preconditions || options.all_counterexamples)) {
				return result;
			}
			return options.weak_conditional_actions ? at_least_one_non_contradictory_condition ? false : true : true;
		}
		// otherwise we can take any strategy we please as long as it's collusion resilient
		// weak version of conditional actions: we need to have one such option for one condition
		// strong version of conditional actions: we need to have one such option for each condition
		bool at_least_one_non_contradictory_condition = false;
		bool result = true;
		for (size_t j = 0; j < branch.conditions.size(); j++)
		{

			std::vector<z3::Bool> disjunctions;
			z3::Frame f2(solver);
			solver.assert_(branch.conditions[j].condition);

			// while we refine the case by adding a case split, we may have to prune
			// the tree of contradictory actions. In practice, we can ignore the
			// branches belonging to contradictory actions "on the fly"; see next line
			if(options.count_calls) {
				calls_cr++;
			}
			if (solver.solve() != z3::Result::UNSAT)
			{
				at_least_one_non_contradictory_condition = true;
				bool secure_choice_found = false;
				z3::Bool reason;
				unsigned reset_index;
				unsigned i = 0;
				bool found = false;
				for (const Choice &choice : branch.conditions[j].children)
				{
					if (collusion_resilience_rec(input, solver, options, choice.node, group, players, group_nr, consider_prob_groups))
					{
						if(options.strategies) {
							// set chosen action, needed for printing strategy
							branch.strategy[j] = choice.action;
						}
						
						// if (consider_prob_groups) {
						// 		branch.problematic_group = player + 1;
						// }
						
						secure_choice_found = true;
						found = true;
						if (options.weak_conditional_actions && !options.strategies)
						{
							return true;
						}
					} else {

						std::vector<z3::Bool> disjuncts;
						for(auto &cond:choice.node->violated_conditions) {
							disjuncts.push_back(z3::conjunction(cond));
						}
						disjunctions.push_back(z3::disjunction(disjuncts));
						
						if (options.strategies && choice.node->reason.null()) {
						choice.node->violates_cr[group_nr - 1] = true;
						}
					}
					
					if ((!choice.node->reason.null()) && (reason.null()))
					{
						reason = choice.node->reason;
						// reset_index = i;
					}
					i++;
				}
				if (options.weak_conditional_actions && found)
				{
					return true;
				}
				if (!reason.null())
				{
					branch.reason = reason;
					// input.set_reset_point(*branch.choices[reset_index].node);
				}

				if(options.counterexamples && reason.null()) {
					branch.use_cond_for_strong_ce[j] = true;
				}

				if (options.strong_conditional_actions && !secure_choice_found)
				{
					if(options.preconditions) {
						result = false;
						std::vector<z3::Bool> precond = {branch.conditions[j].condition};
						precond.insert(precond.end(), disjunctions.begin(), disjunctions.end());
						branch.violated_conditions.push_back(precond);
					} else if (options.all_counterexamples) {
						result = false;
					} else {
						return false;
					}
				}
			}

			// solver.pop(); , done implicitly because the frame dies
		}

		if(options.strong_conditional_actions && (options.preconditions || options.all_counterexamples)) {
			return result;
		}

		return options.weak_conditional_actions ? at_least_one_non_contradictory_condition ? false : true : true;
	}
	else
	{
		// if we are not the honest player, we could do anything,
		// so all branches should be collusion resilient for the player
		// weak version of conditional actions: we need to ensure this for one condition
		// strong version of conditional actions: we need to ensure this for each condition
		bool at_least_one_non_contradictory_condition = false;
		bool result_top_level = true;
		for (size_t j = 0; j < branch.conditions.size(); j++)
		{
			z3::Frame f3(solver);
			solver.assert_(branch.conditions[j].condition);

			// while we refine the case by adding a case split, we may have to prune
			// the tree of contradictory actions. In practice, we can ignore the
			// branches belonging to contradictory actions "on the fly"; see next line
			if(options.count_calls) {
				calls_cr++;
			}
			if (solver.solve() != z3::Result::UNSAT)
			{
				at_least_one_non_contradictory_condition = true;
				bool not_secure_choice_found = false;
				bool result = true;
				z3::Bool reason;
				unsigned reset_index;
				unsigned i = 0;
				for (const Choice &choice : branch.conditions[j].children)
				{
					if (!collusion_resilience_rec(input, solver, options, choice.node, group, players, group_nr, consider_prob_groups))
					{
						if (choice.node->reason.null()){
							if (options.counterexamples) {
								branch.counterexample_choices[j].push_back(choice.action);
								branch.use_cond_for_strong_ce[j] = true;
							 }
							// if (!options.all_counterexamples){
							//  	return false;
							// } else {
								result = false;
							// }
						} else {
							if (result && reason.null()){
								reason = choice.node->reason;
								//reset_index = i;
							}
							result = false;
						}
						not_secure_choice_found = true;

						// we have found one condition where not all choices are secure
						if (options.strong_conditional_actions)
						{
							if (!reason.null())
							{
								branch.reason = reason;
								// input.set_reset_point(*branch.choices[reset_index].node);
							}

							if(options.preconditions) {
								result_top_level = false;
								for(auto &cond: choice.node->violated_conditions) {
									std::vector<z3::Bool> precond = {branch.conditions[j].condition};
									precond.insert(precond.end(), cond.begin(), cond.end());
									branch.violated_conditions.push_back(precond);
								}
							} else if (options.all_counterexamples) {
								result_top_level = false;
							} else {
								return false;
							}
						}

						if(!options.all_counterexamples && reason.null()) {
							break; // go to next condition
						}
					}
					i++;
				}
				if (!reason.null())
				{
					branch.reason = reason;
					// input.set_reset_point(*branch.choices[reset_index].node);
				}
				// if (result && consider_prob_groups) {
				// 	branch.problematic_group = player + 1;
				// }
				// return result;

				// we have one condition where all choices are secure
				if (options.weak_conditional_actions && !not_secure_choice_found)
				{
					return true;
				}
			}

			// solver.pop(); , done implicitly because the frame dies
		}

		// Refactor: A ? !B : true

		if(options.strong_conditional_actions && (options.preconditions || options.all_counterexamples)) {
			return result_top_level;
		}
		
		return options.weak_conditional_actions ? at_least_one_non_contradictory_condition ? false : true : true;
	}
}

bool practicality_rec_old(const Input &input, const Options &options, z3::Solver &solver, Node *node, std::vector<std::string> actions_so_far, std::vector<z3::Bool> conditions_so_far, bool consider_prob_groups)
{
	count_pr_repetitions++;
	if(!node->checked_pr) {
		count_pr++;
		node->checked_pr = true;
	}

	if (node->is_leaf())
	{
		return true;
	}
	else if (node->is_subtree()) {
		// we again have to consider how the current case relates to the PracticalitySubtreeResult cases
		// note that those cases are disjoint and span the whole universe

		// iterate over all PracticalitySubtreeResult
		// 		ask whether case and current_case is satisfiable
		//			if yes: ask whether current_case and not case is satisfiable
		//				if yes: case split on case (i.e. set reason to case, return false)
		//				if no: set practical_utilities for this node to the set of utilities in PracticalitySubtreeResult
		//						or if there are no practical utilities -> take over preconditions
		//			if no: proceed to next PracticalitySubtreeResult

		const auto &subtree = node->subtree();

		if(subtree.solved_weak_cond_actions && options.strong_conditional_actions) {
			std::cerr << "checkmate: subtree is solved for weak conditional actions. Thus, supertree cannot be solved for strong conditional actions... " << std::endl;
			std::exit(EXIT_FAILURE);
		}

		if(!subtree.solved_weak_cond_actions && options.weak_conditional_actions) {
			std::cerr << "checkmate: subtree is solved for strong conditional actions. Thus, supertree cannot be solved for weak conditional actions... " << std::endl;
			std::exit(EXIT_FAILURE);
		}

		if(subtree.solved_for_preconditions & !options.preconditions) {
			std::cerr << "checkmate: subtree is solved with preconditions. Thus, supertree cannot be solved without preconditions... " << std::endl;
			std::exit(EXIT_FAILURE);
		}

		if(!subtree.solved_for_preconditions & options.preconditions) {
			std::cerr << "checkmate: subtree is solved without preconditions. Thus, supertree cannot be solved with preconditions... " << std::endl;
			std::exit(EXIT_FAILURE);
		}

		for (size_t i = 0; i < subtree.practicality.size(); i++) {

			PracticalitySubtreeResult subtree_result = subtree.practicality[i];

			z3::Bool subtree_case;
			// try to optimize: if only 1 -> no need for conjunction
			if(subtree_result._case.size() == 1) {
				subtree_case = subtree_result._case[0];
			} else {
				subtree_case = z3::conjunction(subtree_result._case);
			}

			if(options.count_calls) {
				calls_pr++;
			}
			z3::Result overlapping = solver.solve({subtree_case});

			if (overlapping == z3::Result::SAT){
				if(options.count_calls) {
					calls_pr++;
				}
				z3::Result implied = solver.solve({!subtree_case});

				if (implied == z3::Result::SAT){
					subtree.reason = subtree_case;
					return false;
				} else {

					bool one_pr = false;
					for(auto const &subtree_res : subtree_result.utilities.utilities) {
						if(subtree_res.size() == 0 && options.strong_conditional_actions) {
							if(options.preconditions) {
								subtree.violated_conditions = subtree_result.preconditions_for_current_case;
							}
							return false;
						}
						else if (subtree_res.size() != 0){
							one_pr = true;
						}
					}
					if(options.weak_conditional_actions && !one_pr) {
						if(options.preconditions) {
							subtree.violated_conditions = subtree_result.preconditions_for_current_case;
						}
						return false;
					}

					if (subtree_result.utilities.utilities.size() == 0) {
						//we have to be along honest at this point, otw we would have had at least one pr utility

						if(options.counterexamples) {
							z3::Bool placeholder;
							input.counterexamples.push_back(input.root.get()->compute_pr_cecase(input.players, input.players.size(), actions_so_far, {}, "", placeholder, {}));
						}
						return false;
					}

					subtree.utilities = subtree_result.utilities;
					return true;
				}
			}
		}
		// in case we have listed only cases where it is practical and they do not
		// span the whole universe, return false, because no corresponding case has been found
		if(options.counterexamples) {
			z3::Bool placeholder;
			input.counterexamples.push_back(input.root.get()->compute_pr_cecase(input.players, input.players.size(), actions_so_far, {}, "", placeholder, {}));
		}

		// with the new implementation for conditional actions we should never be here
		// if we care about preconditions
		if(options.preconditions) {
			assert(false);
		}
		return false;
	}

	// else we deal with a branch
	const auto &branch = node->branch();

	// if  (branch.problematic_group == 1 && consider_prob_groups){
	// 	return true;
	// }

	// get practical strategies and corresponding utilities recursively
	// the outer vector stratifies over conditions for convenience
	std::vector<std::vector<ConditionalUtilities>> children;
	// TODO: think about how to store the actions for extracting strategies and counterexamples
	std::vector<std::vector<std::string>> children_actions;

	std::vector<ConditionalUtilities> honest_utilities;
	std::vector<unsigned> honest_index;
	std::vector<std::string> honest_choice;

	bool result = true;
	bool any_honest_practical = false;

	for (size_t j = 0; j < branch.conditions.size(); j++)
	{

		z3::Frame f1(solver);
		solver.assert_(branch.conditions[j].condition);

		unsigned int i = 0;

		// check honest branch first
		for (const Choice &choice : branch.conditions[j].children)
		{
			if (choice.node->honest)
			{
				std::vector<std::string> updated_actions;
				updated_actions.insert(updated_actions.begin(), actions_so_far.begin(), actions_so_far.end());
				updated_actions.push_back(choice.action);

				std::vector<z3::Bool> updated_conditions;
				updated_conditions.insert(updated_conditions.begin(), conditions_so_far.begin(), conditions_so_far.end());
				updated_conditions.push_back(branch.conditions[j].condition);

				if (!practicality_rec_old(input, options, solver, choice.node, updated_actions, updated_conditions, consider_prob_groups))
				{
					if (result)
					{
						branch.reason = choice.node->reason;
						// input.set_reset_point(branch);
					}

					result = false;

					// if(!options.all_counterexamples || !branch.reason.null()) {
					// 	return result;
					// }

					if(options.preconditions && options.strong_conditional_actions) {
						auto &viol_conds_hon_child = choice.node->violated_conditions;
						for(auto &cond : viol_conds_hon_child) {
							std::vector<z3::Bool> new_condition = {branch.conditions[j].condition};
							new_condition.insert(new_condition.end(), cond.begin(), cond.end());
							branch.violated_conditions.push_back(new_condition);
						}
					} else {
						if(options.strong_conditional_actions && options.all_counterexamples) {
							//don't return 
							result = false;
						}
						else if (!branch.reason.null() || options.strong_conditional_actions)
						{
							return result;
						}
					}
					
				}
				else
				{
					any_honest_practical = true;
				}

				if (choice.node->get_utilities().utilities.size() > 0 || (options.strong_conditional_actions && options.preconditions))
				{
					ConditionalUtilities honest_utilities_per_condition = choice.node->get_utilities();
					for (int k = 0; k < honest_utilities_per_condition.condition.size(); k++)
					{
						honest_utilities_per_condition.condition[k] = (z3::conjunction({honest_utilities_per_condition.condition[k], branch.conditions[j].condition}));
					}
					honest_utilities.push_back(honest_utilities_per_condition);
				}

				honest_choice.push_back(choice.action);
				// branch.strategy = choice.action; // choose the honest action along the honest history
				honest_index.push_back(i);

				break;
			}
			i++;
		}
	}
	// Important fix: add branch.honest to the condition
	// Because we can only return if this is along the honest history
	if (!any_honest_practical && options.weak_conditional_actions && branch.honest)
	{
		if(options.all_counterexamples) {
			// don't terminate yet, there might be more counterexamples upwards
			result = false;
		} else {
			return false;
		}
	}

	for (size_t j = 0; j < branch.conditions.size(); j++)
	{

		z3::Frame f2(solver);
		solver.assert_(branch.conditions[j].condition);

		std::vector<ConditionalUtilities> children_per_condition;
		std::vector<std::string> actions_per_condition;

		for (const Choice &choice : branch.conditions[j].children)
		{

			if (!choice.node->honest)
			{
				// this child has no practical strategy (propagate reason for case split, if any)
				std::vector<std::string> updated_actions;
				updated_actions.insert(updated_actions.begin(), actions_so_far.begin(), actions_so_far.end());
				updated_actions.push_back(choice.action);

				std::vector<z3::Bool> updated_conditions;
				updated_conditions.insert(updated_conditions.begin(), conditions_so_far.begin(), conditions_so_far.end());
				updated_conditions.push_back(branch.conditions[j].condition);

				if (!practicality_rec_old(input, options, solver, choice.node, updated_actions, updated_conditions, consider_prob_groups))
				{
					if (result)
					{
						branch.reason = choice.node->reason;
						// input.set_reset_point(branch);
					}

					result = false;

					// if(!options.all_counterexamples || !branch.reason.null()) {
					// 	return result;
					// }

					// We (Anja, Ivana) believe that this is always the case
					// When NOT along honest history there is always a pr unitility except when we need to spilit i.e. reason is not null
					// At least in the usual mode (no all_cases, all_counterexamples, etc.)
					// if (!branch.reason.null())
					// {
					// 	return result;
					// }

					// Branch reason can be null if we are running in mode all_counterexamples
					// and still want to gather further counterexamples
					if(!options.all_counterexamples || !branch.reason.null()) {
						return result;
					}
				}

				if (choice.node->get_utilities().utilities.size()==0){
					assert(!result);
					assert(options.all_counterexamples);
					assert(input.counterexamples.size()>0);
				}

				ConditionalUtilities conditional_utilities = choice.node->get_utilities();
				for (int k = 0; k < conditional_utilities.condition.size(); k++)
				{
					conditional_utilities.condition[k] = z3::conjunction({conditional_utilities.condition[k], branch.conditions[j].condition});
				}

				children_per_condition.push_back(conditional_utilities);
				actions_per_condition.push_back(choice.action);
			}
		}

		children.push_back(children_per_condition);
		children_actions.push_back(actions_per_condition);
	}
	
	if (branch.honest)
	{
		// if we are at an honest node, our strategy must be the honest strategy
		// honest_utilities.size() == branch.conditions.size(), that is we have
		// one ConditionalUtility in honest_utilities per condition

		assert(honest_utilities.size() == branch.conditions.size());	

		for (const auto &conditional_hon_utility : honest_utilities)
		{
			for (const auto &hon_utility : conditional_hon_utility.utilities)
				// the utility at the leaf of the honest subtree
				assert(hon_utility.size() == 1); // the size of utilityTuplesSet needs to be 1
		}

		ConditionalUtilities practical_utilities_for_branch;

		bool condition_where_honest_practical = false;

		for (size_t j = 0; j < branch.conditions.size(); j++)
		{
			z3::Frame f3(solver);
			solver.assert_(branch.conditions[j].condition);

			ConditionalUtilities honest_conditional_utility = honest_utilities[j];

			assert(honest_conditional_utility.condition.size() == honest_conditional_utility.utilities.size());

			// check for weak conditional actions, that we can return true after finding one practical condition
			bool every_honest_practical = true;

			std::vector<UtilityTuplesSet> collected_honest_utility_tuple_sets;

			for (size_t m = 0; m < honest_conditional_utility.condition.size(); m++)
			{

				z3::Bool condition_maximum_utility = honest_conditional_utility.condition[m];
				
				UtilityTuple honest_utility_storage = *honest_conditional_utility.utilities[m].begin();

				std::vector<std::string> honest_strategy; 
				std::vector<z3::Bool> honest_conditions;
				std::vector<Utility> leaf;
				UtilityTuplesSet to_clear_strategy;
				honest_strategy.insert(honest_strategy.end(), honest_utility_storage.strategy_vector.begin(), honest_utility_storage.strategy_vector.end());
				honest_conditions.insert(honest_conditions.end(), honest_utility_storage.strategy_conditions.begin(), honest_utility_storage.strategy_conditions.end());
				UtilityTuple cleared_strategy(honest_utility_storage.leaf);
				to_clear_strategy.insert(cleared_strategy);

				UtilityTuple honest_utility = *to_clear_strategy.begin(); 

				honest_utility.strategy_vector = {};
				honest_utility.strategy_conditions = {};
				// This should be done later
				//honest_utility.strategy_vector.push_back(honest_choice[j]);
				//honest_utility.strategy_conditions.push_back(branch.conditions[j].condition);
				
				// this should be maximal against other players, so...
				Utility maximum = honest_conditional_utility.utilities[m].begin()->leaf[branch.player];

				z3::Frame f4(solver);
				solver.assert_(condition_maximum_utility);

				// for all other children
				unsigned int k = 0;
				bool honest_added = false;
				
				for (const auto &utilities : children[j])
				{
		
					for (size_t n = 0; n < utilities.condition.size(); n++)
					{						
						z3::Bool child_condition = utilities.condition[n];
						UtilityTuplesSet &child_utilities_set = utilities.utilities[n];

						bool found = false;
						// does there exist a possible utility such that `maximum` is geq than it?

						if(options.count_calls) {
							calls_pr++;
						}
						if (solver.solve({child_condition}) == z3::Result::UNSAT)
						{
							continue;
						}

						z3::Frame f5(solver);
						solver.assert_(child_condition);

						for (const auto &utility : child_utilities_set)
						{
							auto comparison = maximum < utility[branch.player];
							if(options.count_calls) {
								calls_pr++;
							}
							if (solver.solve({comparison}) == z3::Result::SAT)
							{
								if(options.count_calls) {
									calls_pr++;
								}
								if (solver.solve({!comparison}) == z3::Result::SAT)
								{
									// might be maximal, just couldn't prove it
									if (result)
									{
										branch.reason = get_split_approx(solver, options, maximum, utility[branch.player], false, false, false, true);
										// input.set_reset_point(branch);
									}
								}
							}
							else
							{
								found = true;
								// need to insert strategy after honest at right point in vector
								if ((options.strategies || options.counterexamples) && k == honest_index[j] && !honest_added){

									honest_added = true;
									
									honest_utility.strategy_vector.push_back(honest_choice[j]);
									honest_utility.strategy_conditions.push_back(branch.conditions[j].condition);

									//add both once insert strategy, once conditions
									honest_utility.strategy_vector.insert(honest_utility.strategy_vector.end(), honest_strategy.begin(), honest_strategy.end());
									honest_utility.strategy_conditions.insert(honest_utility.strategy_conditions.end(), honest_conditions.begin(), honest_conditions.end());
								}
								
								if(options.strategies || options.counterexamples) {
									honest_utility.strategy_vector.insert(honest_utility.strategy_vector.end(), utility.strategy_vector.begin(), utility.strategy_vector.end());
									honest_utility.strategy_conditions.insert(honest_utility.strategy_conditions.end(), utility.strategy_conditions.begin(), utility.strategy_conditions.end());
								}

								break;
							}
						}

						if (!found && utilities.utilities.size() > 0)
						{ // !! utilities.utilities.size()>0 is always true -> discuss
							// counterexample: current child (deviating choice) is the counterexample together with all its practical histories/strategies,
							//                  additional information needed: current history (to be able to document deviation point)
							//                                                 current player
							// NOTE format of ce different from wi and cr, since all practical histories of child are needed to be a CE

							// store (push back) it in input.counterexamples; case will be added in property rec

							// all counterexamples: do not return here (store return value in variable), but check all other children for further violations --> counterexamples
							// 						then also do not return yet, but continue the reasoning up to the root to collect further CEs

							// NOTE: for not along honest history, nothing to do


							// TO DO: add counterexample here
							std::string deviating_action = children_actions[j][k];
							z3::Bool deviating_condition = branch.conditions[j].condition;
							if(options.counterexamples && branch.reason.null()) {
								input.counterexamples.push_back(input.root.get()->compute_pr_cecase(input.players, branch.player, actions_so_far, conditions_so_far, deviating_action, deviating_condition, utilities));
							}

							result = false;
							every_honest_practical = false;

							if(options.strong_conditional_actions && options.preconditions) {
								//current child (deviating choice) is the counterexample together with all its practical histories/strategies,
								std::vector<z3::Bool> new_condition = {branch.conditions[j].condition};
								new_condition.push_back(child_condition);
								branch.violated_conditions.push_back(new_condition);
							}

							// if(!options.all_counterexamples || !branch.reason.null()) {
							// 	return result; //false
							// }
							if (options.strong_conditional_actions && !options.preconditions && !options.all_counterexamples)
							{
								return result; // false
							}
							}

						//k++; -> old. not correct anymore for conditions, should be later

						// pop the child_condition, done implicitly because the frame dies
					}
					// pop the condition_maximum_utility, done implicitly because the frame dies
					
					k++;
					
				}
				
				if(k == honest_index[j] && (options.strategies || options.counterexamples)) {
					honest_utility.strategy_vector.push_back(honest_choice[j]);
					honest_utility.strategy_conditions.push_back(branch.conditions[j].condition);

					honest_utility.strategy_vector.insert(honest_utility.strategy_vector.end(), honest_strategy.begin(), honest_strategy.end());
					honest_utility.strategy_conditions.insert(honest_utility.strategy_conditions.end(), honest_conditions.begin(), honest_conditions.end());
				}

				UtilityTuplesSet honest_set;
				honest_set.insert(honest_utility);
				collected_honest_utility_tuple_sets.push_back(honest_set);

			}

			if (every_honest_practical || options.all_counterexamples)
			{
				condition_where_honest_practical = true;
				// cannot return yet, need to gather information about whether the other honest ones are pr
				// to set the practical utilities of the node
				// crucial for decisions that might come later (higher in the tree)

				// NEW!
				// the honest utilities from this condition are pr
				// take them to the result that will be saved at the node
				for (size_t i = 0; i < honest_conditional_utility.condition.size(); i++)
				{
					practical_utilities_for_branch.condition.push_back(honest_conditional_utility.condition[i]);
					//practical_utilities_for_branch.utilities.push_back(honest_conditional_utility.utilities[i]);
					practical_utilities_for_branch.utilities.push_back(collected_honest_utility_tuple_sets[i]);
				}
			}

			// if (options.weak_conditional_actions && every_honest_practical){
			// 	condition_where_honest_practical = true;
			// 	assert (false);
			// 	return true;
			// 	// what about setting practical utilities for branch??
			// }

			// pop the branch_conditions[j], done implicitly because the frame dies
		}	

		// set the honest utilities for the branch
		branch.practical_utilities = practical_utilities_for_branch;

		// we return the maximal strategy
		// honest choice is practical for current player
		// return true;

		if (options.weak_conditional_actions)
		{
			return condition_where_honest_practical;
		}

		if(options.strong_conditional_actions && (options.preconditions || options.all_counterexamples)) {
			return result;
		} else {
			assert(result);
			return true;
		}

	}
	else
	{
		// not in the honest history
		// to do: we could do this more efficiently by working out the set of utilities for the player
		// but utilities can't be put in a set easily -> fix this here in the C++ version

		// for this scenario we do not need to distinguish between weak and strong conditional actions
		// we need to figure out the set to be dropped and this is independent on weak/strong conditional actions

		// merge the conditional utilities for each condition
		std::vector<ConditionalUtilities> practical_utilities_per_condition;
		std::vector<ConditionalUtilities> practical_utilities_per_condition_storage;
		std::vector<std::vector<std::string>> preceding_actions;
		for (size_t j = 0; j < branch.conditions.size(); j++)
		{
			std::vector<std::string> preceding_actions_for_condition;
			ConditionalUtilities cu;
			unsigned int k = 0;
			for (const auto &child : children[j])
			{
				for (size_t i = 0; i < child.condition.size(); i++)
				{
					cu.condition.push_back(child.condition[i]);
					//cu.utilities.push_back(child.utilities[i]); --> removed this to add the code below, needed for strategies
					UtilityTuplesSet ut_set;
					for (auto &utility_tuple: child.utilities[i]) {
						UtilityTuple to_insert(utility_tuple.leaf);
						 
						// This is done later - here is not the correct point to do it 
						//to_insert.strategy_vector.push_back(children_actions[j][k]);
						//to_insert.strategy_conditions.push_back(branch.conditions[j].condition);
						ut_set.insert(to_insert);
					}
					cu.utilities.push_back(ut_set);
					preceding_actions_for_condition.push_back(children_actions[j][k]);
				}
				k++;
			}
			practical_utilities_per_condition.push_back(cu);
			preceding_actions.push_back(preceding_actions_for_condition);

			ConditionalUtilities cu1;
			std::vector<std::string> preceding_action;
			for (const auto &child : children[j])
			{
				for (size_t i = 0; i < child.condition.size(); i++)
				{
					cu1.condition.push_back(child.condition[i]);
					UtilityTuplesSet ut_set;
					for (auto &utility_tuple: child.utilities[i]) {
						UtilityTuple to_insert(utility_tuple.leaf);
						to_insert.strategy_vector.insert(to_insert.strategy_vector.end(), utility_tuple.strategy_vector.begin(), utility_tuple.strategy_vector.end());
						to_insert.strategy_conditions.insert(to_insert.strategy_conditions.end(), utility_tuple.strategy_conditions.begin(), utility_tuple.strategy_conditions.end());
						ut_set.insert(to_insert);
					}
					cu1.utilities.push_back(ut_set);
				}
			}
			practical_utilities_per_condition_storage.push_back(cu1);
		}

		for (size_t j = 0; j < branch.conditions.size(); j++)
		{
			z3::Frame f6(solver);
			solver.assert_(branch.conditions[j].condition);

			// we need to make sure that
			// for each conditional utility, for each set of practical utilities, for each element
			// there is one other set which contains an element <= than the one we look at

			// the set to drop
			UtilityTuplesSet remove_set;

			ConditionalUtilities &conditional_utilites_for_condition = practical_utilities_per_condition[j];

			for (size_t k = 0; k < conditional_utilites_for_condition.condition.size(); k++)
			{

				bool action_added = false;

				z3::Frame f7(solver);
				solver.assert_(conditional_utilites_for_condition.condition[k]);

				UtilityTuplesSet &practical_utilities_set = conditional_utilites_for_condition.utilities[k];
				for (const UtilityTuple &candidate : practical_utilities_set)
				{
					// work out whether to drop `candidate`
					// this player's utility
					auto dominatee = candidate[branch.player];
					// check all other children
					// if any child has the property that all its utilities are bigger than `dominatee`
					// it can be dropped

					//for (size_t m = 0; m < conditional_utilites_for_condition.condition.size(); m++)
					for (size_t m = 0; m < practical_utilities_per_condition_storage[j].condition.size(); m++)
					{
						if(options.count_calls) {
							calls_pr++;
						}
						if (solver.solve({conditional_utilites_for_condition.condition[m]}) == z3::Result::UNSAT)
						{
							// incompatible, continue
							continue;
						}

						z3::Frame f8(solver);
						solver.assert_(conditional_utilites_for_condition.condition[m]);

						UtilityTuplesSet &utilities = practical_utilities_per_condition_storage[j].utilities[m];
						// skip any where the cadidate is already contained

						// this logic can be factored out in an external function
						bool contained = false;
						for (const auto &utility : utilities)
						{
							if (utility_tuples_eq(utility, candidate))
							{
								contained = true;

								if(!action_added && (options.strategies || options.counterexamples)) {
									action_added = true;
									//candidate.strategy_vector.push_back(children_actions[j][k]);
									candidate.strategy_vector.push_back(preceding_actions[j][k]);
									candidate.strategy_conditions.push_back(branch.conditions[j].condition);
								}

								if(options.strategies || options.counterexamples) {
									candidate.strategy_vector.insert(candidate.strategy_vector.end(), utility.strategy_vector.begin(), utility.strategy_vector.end());
									candidate.strategy_conditions.insert(candidate.strategy_conditions.end(), utility.strategy_conditions.begin(), utility.strategy_conditions.end());
								}
								break;
							}
						}

						if (contained)
						{
							continue;
						}

						// *all* utilities have to be bigger
						bool dominated = true;

						for (const auto &utility : utilities)
						{
							auto dominator = utility[branch.player];
							auto condition = dominator <= dominatee;
							if(options.count_calls) {
								calls_pr++;
							}
							if (solver.solve({condition}) == z3::Result::SAT)
							{
								if (dominated && (options.strategies|| options.counterexamples)){
									candidate.strategy_vector.insert(candidate.strategy_vector.end(), utility.strategy_vector.begin(), utility.strategy_vector.end());
									candidate.strategy_conditions.insert(candidate.strategy_conditions.end(), utility.strategy_conditions.begin(), utility.strategy_conditions.end());
								}
								dominated = false;

								if(options.count_calls) {
									calls_pr++;
								}
								if (solver.solve({!condition}) == z3::Result::SAT)
								{
									branch.reason = get_split_approx(solver, options, dominatee, dominator, false, false, false, true);
									// input.set_reset_point(branch);
									return false;
								}
							}
						}

						if (dominated)
						{
							remove_set.insert(candidate);
							break;
						}

						// pop conditional_utilites_for_condition.condition[m], done implicitly because the frame dies
					}
				}
				// pop conditional_utilites_for_condition.condition[k], done implicitly because the frame dies
			}

			
			// iterate over practical_utilities_per_condition[j] and drop remove set
			for (auto &utilities_set : practical_utilities_per_condition[j].utilities)
			{
				for (const auto &elem : remove_set)
				{
					utilities_set.erase(elem);
				}
			}

			// pop branch.conditions[j].condition, done implicitly because the frame dies
		}

		// set branch practical utilities
		ConditionalUtilities practical_utilities;
		for (size_t j = 0; j < branch.conditions.size(); j++)
		{
			// iterate over all conditions and utilities of the conditional utilities
			// object corresponding to the current condition
			ConditionalUtilities &cond_util = practical_utilities_per_condition[j];
			for (size_t m = 0; m < cond_util.condition.size(); m++)
			{
				// take only condition, utility pairs where the utility pair is not empty
				// it can be empty if we dropped/removed all of its elements previously
				if (cond_util.utilities[m].size() > 0)
				{
					auto &condition_to_add = cond_util.condition[m];
					auto &utilities_to_add = cond_util.utilities[m];

					bool equivalent_condition_exists = false;

					for(size_t ii=0; ii < practical_utilities.condition.size(); ii++) {
						bool existing_implies_new = false;
						bool new_implies_existing = false;

						if(solver.solve({z3::conjunction({practical_utilities.condition[ii], !condition_to_add})}) == z3::Result::UNSAT)
							existing_implies_new = true;

						if(solver.solve({z3::conjunction({!practical_utilities.condition[ii], condition_to_add})}) == z3::Result::UNSAT)
							new_implies_existing = true;

						if(existing_implies_new && new_implies_existing) {
							equivalent_condition_exists = true;
							for(auto &util : utilities_to_add) {
								practical_utilities.utilities[ii].insert(util);
							}
							break;
						}
					}

					if(!equivalent_condition_exists) {
						practical_utilities.condition.push_back(cond_util.condition[m]);
						practical_utilities.utilities.push_back(cond_util.utilities[m]);
					}
				}
			}
		}

		assert(practical_utilities.condition.size() > 0);
		branch.practical_utilities = practical_utilities;
		return true;
	}
}

void compute_conditional_actions_honest_utility_pairs(const Input &input, std::vector<z3::Bool> cond_actions_so_far, Node *node)
{

	if (node->is_leaf())
	{
		for (size_t i = 0; i < node->leaf().conditions.size(); i++) { 

			CondActionsUtilityPair pair;
			pair.conditional_actions.insert(pair.conditional_actions.begin(), cond_actions_so_far.begin(), cond_actions_so_far.end());
			pair.conditional_actions.push_back(node->leaf().conditions[i]);

			pair.utility.insert(pair.utility.begin(), node->leaf().utilities[i].leaf.begin(), node->leaf().utilities[i].leaf.end());
			
			input.cond_actions_honest_utility_pairs.push_back(pair);
		}
		return;
	} else if (node->is_subtree()) {

		for (auto pair : node->subtree().honest_utility)
		{
			CondActionsUtilityPair new_pair;
			new_pair.conditional_actions.insert(new_pair.conditional_actions.begin(), cond_actions_so_far.begin(), cond_actions_so_far.end());
			new_pair.conditional_actions.insert(new_pair.conditional_actions.begin(), pair.conditional_actions.begin(), pair.conditional_actions.end());
			new_pair.utility.insert(new_pair.utility.begin(), pair.utility.begin(), pair.utility.end());
			input.cond_actions_honest_utility_pairs.push_back(new_pair);
		}

	}
	else
	{

		for (auto condition : node->branch().conditions)
		{
			std::vector<z3::Bool> updated_actions;
			updated_actions.insert(updated_actions.begin(), cond_actions_so_far.begin(), cond_actions_so_far.end());
			updated_actions.push_back(condition.condition);

			for (auto child : condition.children)
			{
				if (child.node->honest)
				{
					// call recursively for honest child
					compute_conditional_actions_honest_utility_pairs(input, updated_actions, child.node);
				}
			}
		}
	}
}

bool property_under_split(z3::Solver &solver, const Input &input, const Options &options, const PropertyType property, size_t history)
{
	/* determine if the input has some property for the current honest history under the current split */

	if (property == PropertyType::WeakImmunity || property == PropertyType::WeakerImmunity)
	{
		bool result = true;

		z3::Bool reason;
		Node *current_reset_point;
		std::vector<uint64_t> problematic_group_storage;
		std::vector<z3::Bool> reason_storage;
		bool is_unsat = false;

		for (size_t player = 0; player < input.players.size(); player++)
		{
			if(options.preconditions && options.strong_conditional_actions) {
				input.root->reset_violated_conditions();
			}

			// if (!input.solved_for_group[player]) {
			// problematic groups are only considered when we haven't found a case split point yet

			bool weak_immune_for_player = weak_immunity_rec(input, solver, options, input.root.get(), player, property == PropertyType::WeakerImmunity, true);
		
			if (!weak_immune_for_player)
			{
				if(options.preconditions && options.strong_conditional_actions) {
					input.violated_conditions_current_case.insert(input.violated_conditions_current_case.end(), input.root->violated_conditions.begin(), input.root->violated_conditions.end());
				}
				if (options.counterexamples && input.root->reason.null()){
					is_unsat = true;
					std::vector<size_t> pl = {player};
					input.compute_cecase(options, pl, property);
					input.root.get()->reset_counterexample_choices();
					input.root.get()->reset_use_cond_for_strong_ce();
				}
				if (!options.all_counterexamples && input.root->reason.null() && !options.preconditions)
				{
					return false;
				}
				else if ((!options.all_counterexamples || !is_unsat) && !input.root->reason.null() && reason.null()) {
					reason = input.root->reason;
					// current_reset_point = input.reset_point;
					// problematic_group_storage = input.root->store_problematic_groups();
					reason_storage = input.root->store_reason();
				}
				result = false;
			}

			input.root.get()->reset_counterexample_choices();
			input.root.get()->reset_use_cond_for_strong_ce();
			input.root->reset_reason();
			
		}
		if (!options.all_counterexamples) {
			if (!reason.null()){
				// input.root->restore_problematic_groups(problematic_group_storage);
				// input.reset_point = current_reset_point;
				input.root->restore_reason(reason_storage);
			}
		} else {
			if ((!reason.null()) && !is_unsat){
				// input.root->restore_problematic_groups(problematic_group_storage);
				// input.reset_point = current_reset_point;
				input.root->restore_reason(reason_storage);
			}
		}
		return result;
	}

	else if (property == PropertyType::CollusionResilience)
	{

		// THE CODE BELOW NEEDS TO BE CONSIDERED WHEN IMPLEMENTING SUBTREE/SUPERTREE FUNCTIONALITY FOR CONDITIONAL ACTIONSs
		// lookup the leaf for this history
		// std::vector<Utility> utility;
		// if(history < input.honest.size()) {
		// 	const Node &honest_leaf = get_honest_leaf(input.root.get(), input.honest[history], 0);
		// 	if (honest_leaf.is_leaf()){
		// 		utility = honest_leaf.leaf().utilities;
		// 	} else {
		// 		// the case where the honest history ends in an subtree
		// 		utility = honest_leaf.subtree().honest_utility;
		// 	}
		// } else {
		// 	utility = input.honest_utilities[history - input.honest.size()].leaf;
		// }

		compute_conditional_actions_honest_utility_pairs(input, {}, input.root.get());

		// sneaky hack follows: all possible subgroups of n players can be implemented by counting through from 1 to (2^n - 2)
		// done this way more for concision than efficiency
		bool result = true;

		z3::Bool reason;
		Node *current_reset_point;
		std::vector<uint64_t> problematic_group_storage;
		std::vector<z3::Bool> reason_storage;
		bool is_unsat = false;
		for (uint64_t binary_counter = 1; binary_counter < -1ull >> (64 - input.players.size()); binary_counter++)
		{
			if(options.preconditions && options.strong_conditional_actions) {
				input.root->reset_violated_conditions();
			}

			// if (!input.solved_for_group[binary_counter]){
				if(options.strategies) {
					input.root->add_violation_cr();
				}

				std::bitset<Input::MAX_PLAYERS> group = binary_counter;

				// problematic groups are only considered when we haven't found a case split point yet
				bool collusion_resilient_for_group = collusion_resilience_rec(input, solver, options, input.root.get(), group, input.players.size(), binary_counter, true);
				if (!collusion_resilient_for_group)
				{
					if(options.preconditions && options.strong_conditional_actions) {
						input.violated_conditions_current_case.insert(input.violated_conditions_current_case.end(), input.root->violated_conditions.begin(), input.root->violated_conditions.end());
					}

					if (options.counterexamples && input.root->reason.null()){
						is_unsat = true;
						std::vector<size_t> pl;
						for (size_t player = 0; player < input.players.size(); player++) {
							if (group[player]) {
								pl.push_back(player);
							}
						}
						input.compute_cecase(options, pl, property);
						input.root.get()->reset_counterexample_choices();
						input.root.get()->reset_use_cond_for_strong_ce();
					}

					if (!options.all_counterexamples && input.root->reason.null()){
						return false;
					} else if ((!options.all_counterexamples || !is_unsat ) && !input.root->reason.null() && reason.null()) {
						reason = input.root->reason;
						// current_reset_point = input.reset_point;
						// problematic_group_storage = input.root->store_problematic_groups();
						reason_storage = input.root->store_reason();
					}
					result = false;
					// } else {
					//input.solved_for_group[binary_counter] = true;
				}

				input.root.get()->reset_counterexample_choices();
				input.root.get()->reset_use_cond_for_strong_ce();
				input.root->reset_reason();
			//}
		}
		if (!options.all_counterexamples) {
			if (!reason.null()){
				// input.root->restore_problematic_groups(problematic_group_storage);
				// input.reset_point = current_reset_point;
				input.root->restore_reason(reason_storage);
			}
		} else {
			if ((!reason.null()) && !is_unsat){
				// input.root->restore_problematic_groups(problematic_group_storage);
				// input.reset_point = current_reset_point;
				input.root->restore_reason(reason_storage);
			}
		}
		return result;
	}

	else if (property == PropertyType::Practicality)
	{
		if(options.preconditions && options.strong_conditional_actions) {
			input.root->reset_violated_conditions();
		}

		bool pr_result = practicality_rec_old(input, options, solver, input.root.get(), {}, {}, true);
		
		if(!pr_result) {
			if(options.preconditions && options.strong_conditional_actions) {
				input.violated_conditions_current_case.insert(input.violated_conditions_current_case.end(), input.root->violated_conditions.begin(), input.root->violated_conditions.end());
			}
		}
		
		if(pr_result && options.counterexamples && !input.root->branch().honest) {
			CeCase pr_ce_case;
			std::vector<CeChoice> pr_choices;

			for (size_t i = 0; i < input.root->practical_utilities.condition.size(); i++) {

				auto &condition = input.root->practical_utilities.condition[i];
				auto &practical_utilities_set = input.root->practical_utilities.utilities[i];

				for(auto &utility : practical_utilities_set) {
					CeChoice cechoice;

					cechoice.conditions = {};
					cechoice.choices = {};

					std::vector<std::string> pruned_history = {};
					std::vector<z3::Bool> pruned_conditions = {};

					bool stop_reached = false;
					input.root->strat2hist(utility.strategy_vector, utility.strategy_conditions, condition, utility, pruned_history, pruned_conditions, stop_reached);

					cechoice.choices.push_back(pruned_history);
					cechoice.conditions.insert(cechoice.conditions.end(), pruned_conditions.begin(), pruned_conditions.end());

					pr_choices.push_back(cechoice);

					// for(const auto& pr_utility : input.root->practical_utilities) {
					// 	CeChoice ce_choice;
					// 	ce_choice.choices = input.root->strat2hist(pr_utility.strategy_vector);
					// 	pr_choices.push_back(ce_choice);
					// }
					// pr_ce_case.counterexample = pr_choices;
					// input.counterexamples.push_back(pr_ce_case);
				}
			}
		}
		return pr_result;
	}

	assert(false);
	UNREACHABLE
}

bool property_rec(z3::Solver &solver, const Options &options, const Input &input, const PropertyType property, std::vector<z3::Bool> current_case, size_t history, std::vector<PracticalitySubtreeResult> &subtree_results_pr)
{
	/*
		actual case splitting engine
		determine if the input has some property for the current honest history, splitting recursively
	*/

	// property holds under current split
	bool res = property_under_split(solver, input, options, property, history);
	if (res)
	{
		if (!input.stop_log)
		{
			std::cout << "\tProperty satisfied for case: " << current_case << std::endl;
		}

		if(options.subtree) {
			PracticalitySubtreeResult subtree_result_pr;
			subtree_result_pr._case = current_case;
			// subtree_result_pr.utilities = {};
			// std::vector<Utility> honest_utility;
			// for (auto elem: input.root->branch().practical_utilities) {
			// 	honest_utility = elem.leaf;
			// }
			for (size_t i = 0; i < input.root->branch().practical_utilities.condition.size(); i++) {
				subtree_result_pr.utilities.condition.push_back(input.root->branch().practical_utilities.condition[i]);
				subtree_result_pr.utilities.utilities.push_back(input.root->branch().practical_utilities.utilities[i]);
			}
			// subtree_result_pr.utilities = {honest_utility};
			subtree_results_pr.push_back(subtree_result_pr);

		}


		//if strategies, add a "potential case" to keep track of all strategies
		if (options.strategies){
			input.compute_strategy_case(options, current_case, property);

			if(options.all_cases && property == PropertyType::CollusionResilience) {
				input.root->reset_violation_cr();
			}
		}

		if(options.counterexamples && property == PropertyType::Practicality && !input.root->honest) {
			input.add_case2ce(current_case);
		}

		return true;
	}

	// otherwise consider case split
	z3::Bool split = input.root->reason;
	// there is no case split
	if (split.null())
	{
		if (!input.stop_log)
		{
			std::cout << "\tProperty violated in case: " << current_case << std::endl;
		}
		
		if (options.preconditions)
		{
			input.stop_logging();
			
			if(options.subtree) {
				PracticalitySubtreeResult subtree_result_pr;
				subtree_result_pr._case = current_case;
				subtree_result_pr.preconditions_for_current_case = input.root->violated_conditions;
				subtree_results_pr.push_back(subtree_result_pr);
			} else {
				input.add_unsat_case(current_case);
				//auto simplified = input.condition_simplify();
				if(options.strong_conditional_actions) {
					std::vector<z3::Bool> items;
					//for(auto &cond: simplified) {
					for(auto &cond: input.violated_conditions_current_case) {
						items.push_back(z3::conjunction(cond).simplify());
					}
					input.violated_conditions.push_back(items);
				}
			}

		}

		if (options.counterexamples){
			input.add_case2ce(current_case);
		}

		if(options.all_cases && options.strategies && property == PropertyType::CollusionResilience) {
			input.root->reset_violation_cr();
		}

		return false;
	}
	if (!input.stop_log)
	{
		std::cout << "\tSplitting on: " << split << std::endl;
	}

	std::vector<std::vector<bool>> violation;
	if (property == PropertyType::CollusionResilience && options.strategies){
		violation = input.root->store_violation_cr();
	}

	std::vector<std::vector<std::vector<std::string>>> ce_storage;
	std::vector<std::vector<bool>> use_for_ce_storage;
	if (options.counterexamples && property != PropertyType::Practicality) {
		ce_storage = input.root->store_counterexample_choices();
		use_for_ce_storage= input.root->store_use_cond_for_strong_ce();
	}

	// std::vector<bool> solved_for_storage;
	// std::vector<uint64_t> problematic_groups;
	// if (property != PropertyType::Practicality) {
	// 	solved_for_storage = input.store_solved_for();
	// 	problematic_groups = input.root->store_problematic_groups();
	// }

	auto &current_reset_point = input.reset_point;
	bool result = true;

	for (const z3::Bool &condition : {split, split.invert()})
	{
		// reset reason and strategy
		// ? should be the same point of reset
		input.root->reset_reason();
		input.root->reset_strategy();
		// if(!input.reset_point->is_leaf() && !input.reset_point->is_subtree()) {
		// 	auto &current_reset_branch = current_reset_point->branch();
		// 	current_reset_branch.reset_strategy();
		// }

		if(options.preconditions && options.strong_conditional_actions) {
			input.reset_violated_conditions_current_case();
		}

		solver.push();

		solver.assert_(condition);
		assert(solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);

		bool attempt = property_rec(solver, options, input, property, new_current_case, history, subtree_results_pr);

		solver.pop();

		if (property != PropertyType::Practicality) {
		// 	// reset the branch.problematic_group for all branches to presplit state, such that the other case split starts at the same point
		// 	input.root->restore_problematic_groups(problematic_groups);
		// 	input.restore_solved_for(solved_for_storage);

			if (options.counterexamples){
				input.root->restore_counterexample_choices(ce_storage);
				input.root->restore_use_cond_for_strong_ce(use_for_ce_storage);
			}
		}

		if (property == PropertyType::CollusionResilience && options.strategies){
			std::vector<std::vector<bool>> violation_copy;
			violation_copy.insert(violation_copy.end(), violation.begin(), violation.end());
			input.root->restore_violation_cr(violation_copy);
		}

		if (!attempt)
		{
			if ((!options.preconditions) && (!options.all_cases))
			{
				return false;
			}
			else
			{
				result = false;
				if (options.preconditions)
				{
					input.stop_logging();
				}
			}
		}
	}
	return result;
}

bool property_rec_subtree(z3::Solver &solver, const Options &options, const Input &input, const PropertyType property, std::vector<z3::Bool> current_case, size_t history, unsigned group_nr, std::vector<std::vector<z3::Bool>> &satisfied_in_case,  std::vector<std::vector<z3::Bool>> &violated_in_case, std::vector<std::vector<std::vector<z3::Bool>>> &preconditions_for_player_group) {
	/*
		only called for weak(er) immunity and collusion resilience
		actual case splitting engine
		determine if the input has some property for the current honest history, splitting recursively
	*/

	bool property_result;
	std::bitset<Input::MAX_PLAYERS> group;

	if(property == PropertyType::CollusionResilience) {
		property_result = collusion_resilience_rec(input, solver, options, input.root.get(), group, input.players.size(), group_nr, false);
	} else {
		assert(property != PropertyType::Practicality);
		assert(group_nr > 0); // set to i+1 in previous fct
		property_result = weak_immunity_rec(input, solver, options, input.root.get(), group_nr-1, property == PropertyType::WeakerImmunity, false);
	}

	// property holds under current split
	if (property_result) {
		if (!input.stop_log){
			std::cout << "\tProperty satisfied for case: " << current_case << std::endl;
		}

		satisfied_in_case.push_back(current_case);
		return true;
	}

	// otherwise consider case split
	z3::Bool split = input.root->reason;
	// there is no case split
	if (split.null()) {
		if (!input.stop_log){
			std::cout << "\tProperty violated in case: " << current_case << std::endl;
			violated_in_case.push_back(current_case);
			preconditions_for_player_group.push_back(input.root->violated_conditions);
		}

		return false;
	}
	if (!input.stop_log){
		std::cout << "\tSplitting on: " << split << std::endl;
	}

	auto &current_reset_point = input.reset_point;

	bool result = true;

	// both cr and w(er)i need all cases for soundness
	for (const z3::Bool& condition : {split, split.invert()}) {
		// reset reason and strategy
		// ? should be the same point of reset
		input.root->reset_reason();
		input.root->reset_strategy();
		// if(!input.reset_point->is_leaf() && !input.reset_point->is_subtree()) {
		// 	auto &current_reset_branch = current_reset_point->branch();
		// 	current_reset_branch.reset_strategy();
		// }

		solver.push();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);

		bool attempt = property_rec_subtree(solver, options, input, property, new_current_case, history, group_nr, satisfied_in_case, violated_in_case, preconditions_for_player_group);

		solver.pop();

		if (!attempt)
		{
			if ((!options.preconditions) && (!options.all_cases))
			{
				return false;
			}
			else
			{
				result = false;
				if (options.preconditions)
				{
					input.stop_logging();
				}
			}
		}
	}
	return result;
}

bool property_rec_utility(z3::Solver &solver, const Options &options, const Input &input, const PropertyType property, std::vector<z3::Bool> current_case, std::vector<Utility> honest_utility, unsigned group_nr, std::vector<std::vector<z3::Bool>> &satisfied_in_case, std::vector<std::vector<z3::Bool>> &violated_in_case, std::vector<std::vector<std::vector<z3::Bool>>> &preconditions_for_player_group) {
	/*
		only called for collusion resilience
		actual case splitting engine
		determine if the input has some property for the current honest history, splitting recursively
	*/

	bool property_result;
	std::bitset<Input::MAX_PLAYERS> group = group_nr;
	Utility honest_total{z3::Real::ZERO, z3::Real::ZERO};

	// compute the honest total for the current group
	for (size_t player = 0; player < input.players.size(); player++) {
		if (group[player]) {
			honest_total = honest_total + honest_utility[player];
		}
	}
	property_result = collusion_resilience_rec(input, solver, options, input.root.get(), group, input.players.size(), group_nr, false);

	// property holds under current split
	if (property_result) {
		if (!input.stop_log){
			std::cout << "\tProperty satisfied for case: " << current_case << std::endl;
		}

		satisfied_in_case.push_back(current_case);
		return true;
	}

	// otherwise consider case split
	z3::Bool split = input.root->reason;
	// there is no case split
	if (split.null()) {
		if (!input.stop_log){
			std::cout << "\tProperty violated in case: " << current_case << std::endl;
			violated_in_case.push_back(current_case);
			preconditions_for_player_group.push_back(input.root->violated_conditions);
		}

		return false;
	}
	if (!input.stop_log){
		std::cout << "\tSplitting on: " << split << std::endl;
	}

	auto &current_reset_point = input.reset_point;

	bool result = true;

	for (const z3::Bool& condition : {split, split.invert()}) {
		// reset reason and strategy
		// ? should be the same point of reset
		input.root->reset_reason();
		input.root->reset_strategy();
		// if(!input.reset_point->is_leaf() && !input.reset_point->is_subtree()) {
		// 	auto &current_reset_branch = current_reset_point->branch();
		// 	current_reset_branch.reset_strategy();
		// }

		solver.push();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);

		bool attempt = property_rec_utility(solver, options, input, property, new_current_case, honest_utility, group_nr, satisfied_in_case, violated_in_case, preconditions_for_player_group);

		solver.pop();

		if (!attempt)
		{
			if ((!options.preconditions) && (!options.all_cases))
			{
				return false;
			}
			else
			{
				result = false;
				if (options.preconditions)
				{
					input.stop_logging();
				}
			}
		}
	}
	return result;
}

bool property_rec_nohistory(z3::Solver &solver, const Options &options, const Input &input, const PropertyType property, std::vector<z3::Bool> current_case, unsigned player_nr, std::vector<std::vector<z3::Bool>> &satisfied_in_case, std::vector<PracticalitySubtreeResult> &subtree_results_pr, std::vector<std::vector<z3::Bool>> &violated_in_case, std::vector<std::vector<std::vector<z3::Bool>>> &preconditions_for_player_group) {

	/*
		only called for w(er)i and practicality
		actual case splitting engine
		determine if the input has some property for the current honest history, splitting recursively
	*/

	assert(property != PropertyType::CollusionResilience);

	bool property_result;
	if(property == PropertyType::WeakImmunity) {
		property_result = weak_immunity_rec(input, solver, options, input.root.get(), player_nr, false, false);
	} else if (property == PropertyType::WeakerImmunity) {
		property_result = weak_immunity_rec(input, solver, options, input.root.get(), player_nr, true, false);
	} else if (property == PropertyType::Practicality) {
		property_result = practicality_rec_old(input, options, solver, input.root.get(),{}, {}, false);
	}

	// property holds under current split
	if (property_result) {
		if (!input.stop_log){
			std::cout << "\tProperty satisfied for case: " << current_case << std::endl;
		}

		if(options.subtree && property == PropertyType::Practicality) {
			PracticalitySubtreeResult subtree_result_pr;
			subtree_result_pr._case = current_case;
			// subtree_result_pr.utilities = {};
			// for (auto elem: input.root->branch().practical_utilities) {
			// 	subtree_result_pr.utilities.push_back(elem.leaf);
			// }

			for (size_t i = 0; i < input.root->branch().practical_utilities.condition.size(); i++) {
				subtree_result_pr.utilities.condition.push_back(input.root->branch().practical_utilities.condition[i]);
				subtree_result_pr.utilities.utilities.push_back(input.root->branch().practical_utilities.utilities[i]);
			}
			subtree_results_pr.push_back(subtree_result_pr);
		} else if (property != PropertyType::Practicality) {
			satisfied_in_case.push_back(current_case);
		}

		if(property == PropertyType::Practicality) {
			UtilityCase utilityCase;
			utilityCase._case = current_case;
			// for(auto practical_utility : input.root.get()->practical_utilities) {
			// 	utilityCase.utilities.push_back(practical_utility.leaf);
			// }
			for (size_t i = 0; i < input.root->branch().practical_utilities.condition.size(); i++) {
				utilityCase.utilities.condition.push_back(input.root.get()->practical_utilities.condition[i]);
				utilityCase.utilities.utilities.push_back(input.root.get()->practical_utilities.utilities[i]);
			}

			input.utilities_pr_nohistory.push_back(utilityCase);
		}

		return true;
	}

	// otherwise consider case split
	z3::Bool split = input.root->reason;
	// there is no case split
	if (split.null()) {
		if (!input.stop_log){
			std::cout << "\tProperty violated in case: " << current_case << std::endl;
		}
		if(options.preconditions) {
			if(property == PropertyType::Practicality) {
				PracticalitySubtreeResult subtree_result_pr;
				subtree_result_pr._case = current_case;
				subtree_result_pr.preconditions_for_current_case = input.root->violated_conditions;
				subtree_results_pr.push_back(subtree_result_pr);
			} else {
				violated_in_case.push_back(current_case);
				preconditions_for_player_group.push_back(input.root->violated_conditions);
			}
			
		}

		return false;
	}
	if (!input.stop_log){
		std::cout << "\tSplitting on: " << split << std::endl;
	}

	auto &current_reset_point = input.reset_point;

	bool result = true;

	for (const z3::Bool& condition : {split, split.invert()}) {
		// reset reason and strategy
		// ? should be the same point of reset
		input.root->reset_reason();
		input.root->reset_strategy();
		// if(!input.reset_point->is_leaf() && !input.reset_point->is_subtree()) {
		// 	auto &current_reset_branch = current_reset_point->branch();
		// 	current_reset_branch.reset_strategy();
		// }

		solver.push();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);

		bool attempt = property_rec_nohistory(solver, options, input, property, new_current_case, player_nr, satisfied_in_case, subtree_results_pr, violated_in_case, preconditions_for_player_group);

		solver.pop();

		if (!attempt)
		{
			if ((!options.preconditions) && (!options.all_cases))
			{
				return false;
			}
			else
			{
				result = false;
				if (options.preconditions)
				{
					input.stop_logging();
				}
			}
		}
	}
	return result;
}

void property(const Options &options, const Input &input, PropertyType property, size_t history)
{

	/* determine if the input has some property for the current honest history */
	Solver solver;
	for (z3::Bool constraint : input.initial_constraints) {
		solver.assert_(constraint);
	}
	std::string prop_name;
	bool prop_holds;

	switch (property)
	{
	case PropertyType::WeakImmunity:
		solver.assert_(input.weak_immunity_constraint);
		prop_name = "weak immune";
		break;
	case PropertyType::WeakerImmunity:
		solver.assert_(input.weaker_immunity_constraint);
		prop_name = "weaker immune";
		break;
	case PropertyType::CollusionResilience:
		solver.assert_(input.collusion_resilience_constraint);
		prop_name = "collusion resilient";
		break;
	case PropertyType::Practicality:
		solver.assert_(input.practicality_constraint);
		prop_name = "practical";
		break;
	}

	std::cout << std::endl;
	std::cout << std::endl;
	if (history < input.honest.size())
	{
		std::cout << "Is history " << print_history(input.honest[history]) << " " << prop_name << "?" << std::endl;
	}
	else {
		if(property == PropertyType::Practicality) {
			std::cout << "Computing practical histories/strategies." << std::endl;
		} else if (property == PropertyType::CollusionResilience) {
			// see comment in analyze properties
			// if history >= input.honest.size() then we are running subtree in default mode
			// and are considering an honest utility, not an honest history
			std::cout << "Is the subtree " << prop_name << " for honest utility " << input.honest_utilities[history - input.honest.size()].utility << "?" << std::endl;
		} else {
			std::cout << "Is the subtree " << prop_name << "?" << std::endl;
		}
	}


	if (solver.solve() == z3::Result::UNSAT){
		// report unsat initial constraints
		std::cout << "unsat initial constraints" << std::endl;
		return;
	}

	if (property == PropertyType::Practicality)
	{
		input.reset_practical_utilities();
		std::vector<PracticalitySubtreeResult> satisfied_in_case = {};
		if (property_rec(solver, options, input, property, std::vector<z3::Bool>(), history, satisfied_in_case))
		{
			if (history < input.honest.size())
			{
				std::cout << "YES, it is " << prop_name << "." << std::endl;
			}
			prop_holds = true;
		}
		else
		{
			std::cout << "NO, it is not " << prop_name << "." << std::endl;
			prop_holds = false;
		}
	}
	else
	{
		size_t number_groups = property == PropertyType::CollusionResilience ? pow(2, input.players.size()) - 1 : input.players.size();
		input.init_solved_for_group(number_groups);
		
		std::vector<PracticalitySubtreeResult> satisfied_in_case = {};
		if (property_rec(solver, options, input, property, std::vector<z3::Bool>(), history, satisfied_in_case))
		{
			std::cout << "YES, it is " << prop_name << "." << std::endl;
			prop_holds = true;
		}
		else
		{
			std::cout << "NO, it is not " << prop_name << "." << std::endl;
			prop_holds = false;
		}
	}

	//generate preconditions
	if (options.preconditions && !prop_holds) {
		if(options.weak_conditional_actions) {
			std::cout << std::endl;
			std::vector<z3::Bool> conjuncts;
			std::vector<std::vector<z3::Bool>> simplified = input.precondition_simplify();

			for (const auto &unsat_case: simplified) {
				// negate each case (by disjoining the negated elements), then conjunct all - voila weakest prec to be added to the init constr
				std::vector<z3::Bool> neg_case;
				for (const auto &elem: unsat_case) {
					neg_case.push_back(elem.invert());
				}
				z3::Bool disj = disjunction(neg_case);
				conjuncts.push_back(disj);
			}
			z3::Bool raw_prec = conjunction(conjuncts);
			z3::Bool simpl_prec = raw_prec.simplify();
			std::cout << "Weakest Precondition: " << std::endl << "\t" << simpl_prec << std::endl;
		} else {
			std::cout << std::endl;

			// don't use simplify anymore, because afterwards the size of simplified_cases might not be the same, 
			// so it might mess up the correspondence to the conditions
			//std::vector<std::vector<z3::Bool>> simplified_cases = input.precondition_simplify();

			std::cout << "The set of weakest preconditions includes: " << std::endl;

			std::vector<z3::Bool> precondition_items;

			for(size_t i=0; i<input.unsat_cases.size(); i++) {
				// for each case we need in the precondition case => \neg conditions which is basically \neg case or \neg conditions
				z3::Bool case_conj = z3::conjunction(input.unsat_cases[i]);

				std::vector<z3::Bool> negated = {};
				for(auto &cond : input.violated_conditions[i]) {
					negated.push_back(!cond);
				}

				z3::Bool cond_conj = z3::conjunction(negated);

				std::cout << "\t (" << case_conj << ") implies (" << cond_conj << ")" << std::endl;

				precondition_items.push_back(z3::disjunction({!case_conj, cond_conj}));

			}

			z3::Bool raw_prec = z3::conjunction(precondition_items);
			z3::Bool simpl_prec = raw_prec.simplify();

			z3::Solver preconditions_solver;
			preconditions_solver.assert_(simpl_prec);
			if(preconditions_solver.solve() == z3::Result::UNSAT) {
				std::cout << "Weakest Precondition: " << std::endl << "\t" << "false" << std::endl;
			} else {
				std::cout << "Weakest Precondition: " << std::endl << "\t" << simpl_prec << std::endl;
			}
		}
		
	}

	// generate strategies
	if (options.strategies && prop_holds){
		// for each case a strategy
		bool is_wi = (property == PropertyType::WeakerImmunity) || (property == PropertyType::WeakImmunity);
		input.print_strategies(options, is_wi);
	}

	if (options.counterexamples && !prop_holds){
		bool is_wi = (property == PropertyType::WeakerImmunity) || (property == PropertyType::WeakImmunity);
		bool is_cr = (property == PropertyType::CollusionResilience);
		input.print_counterexamples(options, is_wi, is_cr);
	}

	if(options.counterexamples && prop_holds && history == input.honest.size() && property == PropertyType::Practicality) {
		input.print_counterexamples(options, false, false);
	}
}

void property_subtree(const Options &options, const Input &input, PropertyType property, size_t history, Subtree &subtree) {

	/* determine if the input has some property for the current honest history */
	Solver solver;
	for (z3::Bool constraint : input.initial_constraints) {
		solver.assert_(constraint);
	}
	std::string prop_name;

	switch (property)
	{
		case  PropertyType::WeakImmunity:
			solver.assert_(input.weak_immunity_constraint);
			prop_name = "weak immune";
			break;
		case  PropertyType::WeakerImmunity:
			solver.assert_(input.weaker_immunity_constraint);
			prop_name = "weaker immune";
			break;
		case  PropertyType::CollusionResilience:
			solver.assert_(input.collusion_resilience_constraint);
			prop_name = "collusion resilient";
			break;
		case  PropertyType::Practicality:
			solver.assert_(input.practicality_constraint);
			prop_name = "practical";
			break;
	}

	std::cout << std::endl;
	std::cout << std::endl;
	std::cout << "Is history " << print_history(input.honest[history]) << " " << prop_name << "?" << std::endl;


	if (solver.solve() == z3::Result::UNSAT){
		// report unsat initial constraints
		std::cout << "unsat initial constraints" << std::endl;
		return;
		}

	if (property == PropertyType::Practicality) {
		input.reset_practical_utilities();

		std::vector<PracticalitySubtreeResult> subtree_results_pr = {};

		bool pr_result = property_rec(solver, options, input, property, std::vector<z3::Bool>(), history, subtree_results_pr);

		if (pr_result) {
			// Removed this assertion because we do not have 1 pr utility any more,
			// see new below
			//assert(input.root->branch().practical_utilities.size() == 1);

			// New assertion - one pr utility per condition
			bool one_pr = false;
			for (size_t i = 0; i < input.root->branch().practical_utilities.condition.size(); i++) {
				if(options.strong_conditional_actions) {
					assert(input.root->branch().practical_utilities.utilities[i].size() == 1);
				} else {
					if(input.root->branch().practical_utilities.utilities[i].size() == 1) {
						one_pr = true;
					}
				}
			}
			if(options.weak_conditional_actions) {
				assert(one_pr);
			}


			// std::vector<Utility> honest_utility;
			// for (auto elem: input.root->branch().practical_utilities) {
			// 	honest_utility = elem.leaf;
			// }
			//std::cout << "YES, it is " << prop_name << ", the honest practical utility is "<<  honest_utility << "." << std::endl;

			std::cout << "YES, it is " << prop_name << ", the honest practical utility is as follows: " << std::endl;
			for (size_t i = 0; i < input.root->branch().practical_utilities.condition.size(); i++) {
				std::cout << "\tConditions: " << input.root->branch().practical_utilities.condition[i] << std::endl;
				std::cout << "\tUtilities: " << std::endl;
				for(const auto &pr_utility : input.root->branch().practical_utilities.utilities[i]) {
					std::cout << "\t\tUtility: " << pr_utility.leaf << std::endl;
				}
			}

		} else {
			//assert( input.root->branch().practical_utilities.size() == 0);
			// removed this assertion bacause it was failing
			// practical utilites is always at least once - we always set it
			// even though when it is not correct because we needed this for an
			// additional feature (it was either the counterexamples, or strategies or all cases)

			std::cout << "NO, it is not " << prop_name << ", hence there is no honest practical utility." << std::endl;
		}

		subtree.practicality.insert(subtree.practicality.end(), subtree_results_pr.begin(), subtree_results_pr.end());
	} else {

		size_t number_groups = property == PropertyType::CollusionResilience ? pow(2,input.players.size())-2 : input.players.size();

		std::string output_text = property == PropertyType::CollusionResilience ? " against group " : " for player ";

		std::vector<SubtreeResult> subtree_results;

		for (unsigned i = 0; i < number_groups; i++){
			input.reset_reset_point();
			input.root.get()->reset_reason();

			std::vector<std::string> players;

            if(property == PropertyType::CollusionResilience) {
                players = index2player(input, property, i+1);
            } else if (property == PropertyType::WeakImmunity || property == PropertyType::WeakerImmunity) {
                players = { input.players[i] };
            }

			SubtreeResult subtree_result_player;
			subtree_result_player.player_group = players;
			subtree_result_player.satisfied_in_case = {};

			if (property_rec_subtree(solver, options, input, property, std::vector<z3::Bool>(), history, i+1, subtree_result_player.satisfied_in_case, subtree_result_player.cases_for_preconditions, subtree_result_player.preconditions_for_player_group)){
				std::cout << "YES, it is " << prop_name << output_text << players << "."  << std::endl;
			} else {
				std::cout << "NO, it is not " << prop_name << output_text << players << "." << std::endl;
			}

			// check whether we already have a SubtreeResult for this player
			// if yes: append sat cases
			// if not: pushback
			bool found = false;
			for(auto &subtree_result : subtree_results) {
				if(subtree_result.player_group.size() == subtree_result_player.player_group.size()) {
					if(std::equal(subtree_result.player_group.begin(), subtree_result.player_group.end(),subtree_result_player.player_group.begin())) {
						found = true;
						subtree_result.satisfied_in_case.insert(subtree_result.satisfied_in_case.end(), subtree_result_player.satisfied_in_case.begin(), subtree_result_player.satisfied_in_case.end());
						subtree_result.cases_for_preconditions.insert(subtree_result.cases_for_preconditions.end(), subtree_result_player.cases_for_preconditions.begin(), subtree_result_player.cases_for_preconditions.end());
						subtree_result.preconditions_for_player_group.insert(subtree_result.preconditions_for_player_group.end(), subtree_result_player.preconditions_for_player_group.begin(), subtree_result_player.preconditions_for_player_group.end());
						break;
					}
				}
			}
			if(!found) {
				subtree_results.push_back(subtree_result_player);
			}
		}

		if(property == PropertyType::WeakImmunity) {
			subtree.weak_immunity.insert(subtree.weak_immunity.end(), subtree_results.begin(), subtree_results.end());
		} else if (property == PropertyType::WeakerImmunity) {
			subtree.weaker_immunity.insert(subtree.weaker_immunity.end(), subtree_results.begin(), subtree_results.end());
		} else if (property == PropertyType::CollusionResilience) {
			subtree.collusion_resilience.insert(subtree.collusion_resilience.end(), subtree_results.begin(), subtree_results.end());
		}

	}

	return;
}

void property_subtree_utility(const Options &options, const Input &input, PropertyType property, std::vector<Utility> honest_utility, Subtree &subtree) {
	/* determine if the input has some property for the current honest history */

	assert(property == PropertyType::CollusionResilience);

	Solver solver;
	for (z3::Bool constraint : input.initial_constraints) {
		solver.assert_(constraint);
	}

	solver.assert_(input.collusion_resilience_constraint);

	std::cout << std::endl;
	std::cout << std::endl;
	std::cout << "Is utility " << honest_utility << " collusion resilient?" << std::endl;

	if (solver.solve() == z3::Result::UNSAT){
		// report unsat initial constraints
		std::cout << "unsat initial constraints" << std::endl;
		return;
		}

	size_t number_groups = pow(2,input.players.size())-2;
	std::vector<SubtreeResult> subtree_results;

	for (unsigned i = 0; i < number_groups; i++){
		input.reset_reset_point();
		input.root.get()->reset_reason();
		std::vector<std::string> players = index2player(input, property, i+1);

		SubtreeResult subtree_result_player;
		subtree_result_player.player_group = players;
		subtree_result_player.satisfied_in_case = {};

		if (property_rec_utility(solver, options, input, property, std::vector<z3::Bool>(), honest_utility, i+1, subtree_result_player.satisfied_in_case, subtree_result_player.cases_for_preconditions, subtree_result_player.preconditions_for_player_group)){
			std::cout << "YES, it is collusion resilient against group " <<  players << "."  << std::endl;
		} else {
			std::cout << "NO, it is not collusion resilient against group " << players << "." << std::endl;
		}

		// check whether we already have a SubtreeResult for this player
		// if yes: append sat cases
		// if not: pushback
		bool found = false;
		for(auto &subtree_result : subtree_results) {
			if(subtree_result.player_group.size() == subtree_result_player.player_group.size()) {
				if(std::equal(subtree_result.player_group.begin(), subtree_result.player_group.end(),subtree_result_player.player_group.begin())) {
					found = true;
					subtree_result.satisfied_in_case.insert(subtree_result.satisfied_in_case.end(), subtree_result_player.satisfied_in_case.begin(), subtree_result_player.satisfied_in_case.end());
					subtree_result.cases_for_preconditions.insert(subtree_result.cases_for_preconditions.end(), subtree_result_player.cases_for_preconditions.begin(), subtree_result_player.cases_for_preconditions.end());
					subtree_result.preconditions_for_player_group.insert(subtree_result.preconditions_for_player_group.end(), subtree_result_player.preconditions_for_player_group.begin(), subtree_result_player.preconditions_for_player_group.end());
					break;
				}
			}
		}
		if(!found) {
			subtree_results.push_back(subtree_result_player);
		}

	}

	subtree.collusion_resilience.insert(subtree.collusion_resilience.end(), subtree_results.begin(), subtree_results.end());

	return;
}

void property_subtree_nohistory(const Options &options, const Input &input, PropertyType property, Subtree &subtree) {

	Solver solver;
	for (z3::Bool constraint : input.initial_constraints) {
		solver.assert_(constraint);
	}
	std::string prop_name;

	switch (property)
	{
		case  PropertyType::WeakImmunity:
			solver.assert_(input.weak_immunity_constraint);
			prop_name = "weak immune";
			break;
		case  PropertyType::WeakerImmunity:
			solver.assert_(input.weaker_immunity_constraint);
			prop_name = "weaker immune";
			break;
		case  PropertyType::Practicality:
			solver.assert_(input.practicality_constraint);
			prop_name = "practical";
			break;
		case PropertyType::CollusionResilience:
			std::cerr << "checkmate: fct property_subtree_nohistory should not be called for Collusion Resilience" << std::endl;
			std::exit(EXIT_FAILURE);
			break;
	}

	std::cout << std::endl;
	std::cout << std::endl;

	auto result = solver.solve();

    if (result == z3::Result::UNSAT){
		// Z3_solver new_solver = Z3_mk_simple_solver(z3::CONTEXT);
		// Z3_solver_inc_ref(z3::CONTEXT, new_solver);
		// auto result1 = Z3_solver_check_assumptions(z3::CONTEXT, new_solver,input.initial_constraints.size(), reinterpret_cast<Z3_ast*>(const_cast<z3::Bool*>(input.initial_constraints.data())));
		// auto core = Z3_solver_get_unsat_core(z3::CONTEXT, new_solver);
		// Z3_ast_vector_inc_ref(z3::CONTEXT,core);
		// std::cout << Z3_ast_vector_to_string (z3::CONTEXT,core) << std::endl;

		// report unsat initial constraints
		std::cout << "unsat initial constraints" << std::endl;
		return;
		}
    // std::cout << result << std::endl;
    // assert(solver.solve() == z3::Result::SAT);




	// if (result == z3::Result::UNSAT){
	// 	Z3_solver new_solver = Z3_mk_simple_solver(z3::CONTEXT);
	// 	Z3_solver_inc_ref(z3::CONTEXT, new_solver);
	// 	for (z3::Bool constraint : input.initial_constraints) {
	// 		Z3_solver_assert(z3::CONTEXT, new_solver, constraint.get_ast());
	// 	}
	// 	// auto asrts = Z3_solver_get_assertions(z3::CONTEXT, new_solver);
	// 	// std::cout << Z3_ast_vector_to_string(z3::CONTEXT, asrts) << std::endl;
	// 	auto result1 = Z3_solver_check_assumptions(z3::CONTEXT, new_solver,input.initial_constraints.size(), reinterpret_cast<Z3_ast*>(const_cast<z3::Bool*>(input.initial_constraints.data())));
	// 	std::cout << result1 << std::endl;
	// 	// Z3_ast const *foo = input.initial_constraint.ast;
	// 	// Z3_solver_check_assumptions(z3::CONTEXT, new_solver, 1, foo);
	// 	auto core = Z3_solver_get_unsat_core(z3::CONTEXT, new_solver);
	// 	Z3_ast_vector_inc_ref(z3::CONTEXT,core);
	// 	std::cout << Z3_ast_vector_size (z3::CONTEXT,core) << std::endl;
	// }
	// std::cout << result << std::endl;
	// assert(solver.solve() == z3::Result::SAT);

	if (property == PropertyType::Practicality){
		input.reset_practical_utilities();

		std::vector<std::vector<z3::Bool>> satisfied_in_case;
		std::vector<PracticalitySubtreeResult> subtree_results_pr = {};

		std::vector<std::vector<z3::Bool>> violated_in_case;
		std::vector<std::vector<std::vector<z3::Bool>>> preconditions;

		std::cout << "What are the subtree's practical utilities?" << std::endl;
		bool pr_result = property_rec_nohistory(solver, options, input, property, std::vector<z3::Bool>(), 0, satisfied_in_case, subtree_results_pr, violated_in_case, preconditions);

		assert(pr_result);

		// removed for conditional actions - new assertion below
		//assert(input.root.get()->practical_utilities.size()>0);
		for (size_t i = 0; i < input.root->branch().practical_utilities.condition.size(); i++) {
			assert(input.root->branch().practical_utilities.utilities[i].size() > 0);
		}

		// ATTENTION THINK ABOUT HOW LATER (IN SUPERTREE) CASE SPLITS MAY IMPACT THE RESULT
		// we need to print the corresponding utilities for each case
		// kind of "all cases" for practicality_subtree
		// since in property_rec_nohistory we are not along honest, we consider all cases implicitly
		// it suffices to have a new data structure where we store <case, utulities> information and print them below
		//std::cout << "print utilities" << std::endl;

		for(auto &utilityCase : input.utilities_pr_nohistory) {
			std::cout << "Case: " << utilityCase._case << std::endl;
			for(size_t i=0; i<utilityCase.utilities.condition.size(); i++) {
				std::cout << "\tConditions: " << utilityCase.utilities.condition[i] << std::endl;
				std::cout << "\tUtilities: " << std::endl;
				for(const auto &pr_utility : utilityCase.utilities.utilities[i]) {
					std::cout << "\t\tUtility: " << pr_utility.leaf << std::endl;
				}
			}
		}

		subtree.practicality.insert(subtree.practicality.end(), subtree_results_pr.begin(), subtree_results_pr.end());
	} else {
		size_t number_groups = input.players.size();

		std::cout << "Is this subtree " << prop_name << "?" << std::endl;
		std::vector<SubtreeResult> subtree_results;

		for (size_t i = 0; i < number_groups; i++){
			input.reset_reset_point();
			input.root.get()->reset_reason();

			size_t value = property == PropertyType::CollusionResilience ? i+1 : i;
			std::vector<std::string> players = index2player(input, property, value);

			SubtreeResult subtree_result_player;
			subtree_result_player.player_group = players;
			subtree_result_player.satisfied_in_case = {};

			std::vector<PracticalitySubtreeResult> subtree_results_pr = {};

			// i+1 in index2player while i in property_rec_nohistory is on purpose
			if (property_rec_nohistory(solver, options, input, property, std::vector<z3::Bool>(), i, subtree_result_player.satisfied_in_case, subtree_results_pr, subtree_result_player.cases_for_preconditions, subtree_result_player.preconditions_for_player_group)){
				std::cout << "YES, it is " << prop_name << " for player " <<  players << "."  << std::endl;
			} else {
				std::cout << "NO, it is not " << prop_name << " for player " << players << "." << std::endl;
			}

			// check whether we already have a SubtreeResult for this player
			// if yes: append sat cases
			// if not: pushback
			bool found = false;
			for(auto &subtree_result : subtree_results) {
				if(subtree_result.player_group.size() == subtree_result_player.player_group.size()) {
					if(std::equal(subtree_result.player_group.begin(), subtree_result.player_group.end(),subtree_result_player.player_group.begin())) {
						found = true;
						subtree_result.satisfied_in_case.insert(subtree_result.satisfied_in_case.end(), subtree_result_player.satisfied_in_case.begin(), subtree_result_player.satisfied_in_case.end());
						subtree_result.cases_for_preconditions.insert(subtree_result.cases_for_preconditions.end(), subtree_result_player.cases_for_preconditions.begin(), subtree_result_player.cases_for_preconditions.end());
						subtree_result.preconditions_for_player_group.insert(subtree_result.preconditions_for_player_group.end(), subtree_result_player.preconditions_for_player_group.begin(), subtree_result_player.preconditions_for_player_group.end());
						break;
					}
				}
			}
			if(!found) {
				subtree_results.push_back(subtree_result_player);
			}
		}

		if(property == PropertyType::WeakImmunity) {
			subtree.weak_immunity.insert(subtree.weak_immunity.end(), subtree_results.begin(), subtree_results.end());
		} else if (property == PropertyType::WeakerImmunity) {
			subtree.weaker_immunity.insert(subtree.weaker_immunity.end(), subtree_results.begin(), subtree_results.end());
		}

	}

	return;
}

void analyse_properties(const Options &options, const Input &input)
{

	if (input.honest_utilities.size() != 0)
	{
		std::cout << "INFO: This file is a subtree, but CheckMate is running in default mode" << std::endl;
	}

	/* iterate over all honest histories and check the properties for each of them */
	for (size_t history = 0; history < input.honest.size(); history++)
	{

		if(options.count_nodes) {
			reset_global_counters(true, true, true, true);
			input.root->reset_count_check(true, true, true, true);
		}

		if(options.count_calls) {
			reset_calls(true, true, true, true);
		}

		std::cout << std::endl;
		std::cout << std::endl;
		std::cout << "Checking history " << print_history(input.honest[history]) << std::endl;

		input.root->reset_honest();
		input.root->mark_honest(input.honest[history]);
		input.cond_actions_honest_utility_pairs = {};

		if(options.strategies) {
			input.root->reset_violation_cr();
		}

		std::vector<bool> property_chosen = {options.weak_immunity, options.weaker_immunity, options.collusion_resilience, options.practicality};
		std::vector<PropertyType> property_types = {PropertyType::WeakImmunity, PropertyType::WeakerImmunity, PropertyType::CollusionResilience, PropertyType::Practicality};

		assert(property_chosen.size() == property_types.size());

		for (size_t i = 0; i < property_chosen.size(); i++)
		{
			if (property_chosen[i])
			{
				input.reset_counterexamples();
				input.root.get()->reset_counterexample_choices();
				input.root.get()->reset_use_cond_for_strong_ce();
				input.reset_logging();

				input.reset_unsat_cases();
				input.root->reset_reason();
				input.root->reset_strategy();
				input.reset_strategies();
				// input.root->reset_problematic_group(i==2);
				// input.reset_reset_point();

				if(options.preconditions && options.strong_conditional_actions) {
					input.reset_violated_conditions();
					input.reset_violated_conditions_current_case();
					input.root->reset_violated_conditions();
				}
				property(options, input, property_types[i], history);
			}
		}

		if(options.count_nodes) {
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Number of checked nodes for history: " << print_history(input.honest[history]) << std::endl;
			print_global_counters(true, true, true, true);
		}

		if(options.count_calls) {
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Number of SMT calls for history: " << print_history(input.honest[history]) << std::endl;
			print_calls_counters(true, true, true, true);
		}
	}

	if(input.honest_utilities.size() != 0) {

		if(options.count_nodes) {
			reset_global_counters(true, true, false, true);
			input.root->reset_count_check(true, true, false, true);
		}

		if(options.count_calls) {
			reset_calls(true, true, false, true);
		}

		input.root->reset_honest();

		std::vector<bool> property_chosen = {options.weak_immunity, options.weaker_immunity, options.practicality};
		std::vector<PropertyType> property_types = {PropertyType::WeakImmunity, PropertyType::WeakerImmunity, PropertyType::Practicality};

		assert(property_chosen.size() == property_types.size());

		if(property_chosen.size() > 0) {
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Checking no honest history " << std::endl;
		}

		for (size_t i=0; i<property_chosen.size(); i++) {
			if(property_chosen[i]) {
				input.reset_counterexamples();
				input.root.get()->reset_counterexample_choices();
				input.root.get()->reset_use_cond_for_strong_ce();
				input.reset_logging();
				
				input.reset_unsat_cases();
				input.root->reset_reason();
				input.root->reset_strategy();
				input.reset_strategies();

				// input.root->reset_problematic_group(false);
				// input.reset_reset_point();

				if(options.preconditions && options.strong_conditional_actions) {
					input.reset_violated_conditions();
					input.reset_violated_conditions_current_case();
					input.root->reset_violated_conditions();
				}
				
				property(options, input, property_types[i], input.honest.size());
			}
		}

		if(options.count_nodes) {
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Number of checked nodes for no hohest history: " << std::endl;
			print_global_counters(true, true, false, true);
		}

		if(options.count_calls) {
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Number of checked nodes for no hohest history: " << std::endl;
			print_calls_counters(true, true, false, true);
		}

		if(options.collusion_resilience) {

			for(unsigned honest_utility = 0; honest_utility < input.honest_utilities.size(); honest_utility++) {
				
				if(options.count_nodes) {
					reset_global_counters(false, false, true, false);
					input.root->reset_count_check(false, false, true, false);
				}

				if(options.count_calls) {
					reset_calls(false, false, true, false);
				}

				std::cout << std::endl;
				std::cout << std::endl;
				std::cout << "Checking honest utility " << input.honest_utilities[honest_utility].utility << std::endl;

				if(options.strategies) {
					input.root->reset_violation_cr();
				}

				input.reset_counterexamples();
				input.root.get()->reset_counterexample_choices();
				input.root.get()->reset_use_cond_for_strong_ce();
				input.reset_logging();
				
				input.reset_unsat_cases();
				input.root->reset_reason();
				input.reset_strategies();

				// input.root->reset_problematic_group(true);
				// input.reset_reset_point();
				
				// input.honest.size() + honest_utility means we are running a subree in default mode
				// and we consider collusion resilience for the honest utility
				
				if(options.preconditions && options.strong_conditional_actions) {
					input.reset_violated_conditions();
					input.reset_violated_conditions_current_case();
					input.root->reset_violated_conditions();
				}
				
				property(options, input, PropertyType::CollusionResilience, input.honest.size() + honest_utility);

				if(options.count_nodes) {
					std::cout << std::endl;
					std::cout << std::endl;
					std::cout << "Number of checked nodes for honest utility: " << input.honest_utilities[honest_utility].utility << std::endl;
					print_global_counters(false, false, true, false);
				}

				if(options.count_calls) {
					std::cout << std::endl;
					std::cout << std::endl;
					std::cout << "Number of checked nodes for honest utility: " << input.honest_utilities[honest_utility].utility << std::endl;
					print_calls_counters(false, false, true, false);
				}

			}

		}

	}
}

void analyse_properties_subtree(const Options &options, const Input &input) {

	// analysis for a subtree:
	// i.e. we might be along the honest history or not
	// if we are not along honest, we need the honest utility as comparison value (for collusion resilience)--> probably an input parameter

	// in any case we want to return...
	//     ...for w(er)i: for which players the subtree is w(er)i
	//     ...for cr: against which groups of players the subtree is cr
	//     ...for pr: all practical utilities

	// input needs: honest utility vector (std::vector<UtilityTuple>)

	/* iterate over all honest histories and check the properties for each of them */
	for (size_t history = 0; history < input.honest.size(); history++) {

		if(options.count_nodes) {
			reset_global_counters(true, true, true, true);
			input.root->reset_count_check(true, true, true, true);
		}

		if(options.count_calls) {
			reset_calls(true, true, true, true);
		}

		std::cout << std::endl;
		std::cout << std::endl;
		std::cout << "Checking history " << print_history(input.honest[history]) << std::endl;

		input.root->reset_honest();
		input.root->mark_honest(input.honest[history]);
		input.root->reset_practical_utilities();
		input.cond_actions_honest_utility_pairs = {};

		if(options.collusion_resilience) {
			compute_conditional_actions_honest_utility_pairs(input, {}, input.root.get());
		}

		if(options.strategies) {
			input.root->reset_violation_cr();
		}

		std::vector<bool> property_chosen = {options.weak_immunity, options.weaker_immunity, options.collusion_resilience, options.practicality};
		std::vector<PropertyType> property_types = {PropertyType::WeakImmunity, PropertyType::WeakerImmunity, PropertyType::CollusionResilience, PropertyType::Practicality};

		assert(property_chosen.size() == property_types.size());

		Subtree st({}, {}, {}, {}, {});
		Subtree &subtree = st;
		subtree.honest_utility = input.cond_actions_honest_utility_pairs;

		for (size_t i=0; i<property_chosen.size(); i++) {
			if(property_chosen[i]) {
				input.reset_counterexamples();
				input.root.get()->reset_counterexample_choices();
				input.root.get()->reset_use_cond_for_strong_ce();
				input.reset_logging();

				input.reset_unsat_cases();
				input.root->reset_reason();
				input.reset_strategies();
				// input.root->reset_problematic_group(i==2);
				// input.reset_reset_point();

				if(options.preconditions && options.strong_conditional_actions) {
					input.reset_violated_conditions();
					input.reset_violated_conditions_current_case();
					input.root->reset_violated_conditions();
				}
				property_subtree(options, input, property_types[i], history, subtree);
			}
		}



		std::string file_name = options.input_path + std::string(".out");
		if(options.weak_conditional_actions) {
			subtree.solved_weak_cond_actions = true;
		} else {
			subtree.solved_weak_cond_actions = false;
		}

		if(options.preconditions) {
			subtree.solved_for_preconditions = true;
		} else {
			subtree.solved_for_preconditions = false;
		}

		std::cout << "Print to file..." << std::endl;
        print_subtree_result_to_file(input, file_name, subtree, options.preconditions);

	}

	// iterate over all honest utilities (only for cr) and check the properties for each of them
	// compute w(er)i and pr results
	if (input.honest_utilities.size()>0) {

		if(options.count_nodes) {
			reset_global_counters(true, true, false, true);
			input.root->reset_count_check(true, true, false, true);
		}

		if(options.count_calls) {
			reset_calls(true, true, false, true);
		}

		std::cout << std::endl;
		std::cout << std::endl;
		std::cout << "Checking no honest history " << std::endl;

		input.root->reset_honest();
		input.root->reset_practical_utilities();

		// possibly comment out
		if(options.strategies) {
			input.root->reset_violation_cr();
		}

		Subtree st({}, {}, {}, {}, {});
		Subtree &subtree = st;

		// cr handled below
		std::vector<bool> property_chosen = {options.weak_immunity, options.weaker_immunity, options.practicality};
		std::vector<PropertyType> property_types = {PropertyType::WeakImmunity, PropertyType::WeakerImmunity, PropertyType::Practicality};

		assert(property_chosen.size() == property_types.size());

		for (size_t i=0; i<property_chosen.size(); i++) {
			if(property_chosen[i]) {
				input.reset_counterexamples();
				input.root.get()->reset_counterexample_choices();
				input.root.get()->reset_use_cond_for_strong_ce();
				input.reset_logging();
				
				input.reset_unsat_cases();
				input.root->reset_reason();
				input.reset_strategies();
				// input.reset_reset_point();

				if(options.preconditions && options.strong_conditional_actions) {
					input.reset_violated_conditions();
					input.reset_violated_conditions_current_case();
					input.root->reset_violated_conditions();
				}
				property_subtree_nohistory(options, input, property_types[i], subtree);
			}
		}

		if(options.count_nodes) {
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Number of checked nodes for no hohest history: " << std::endl;
			print_global_counters(true, true, false, true);
		}

		if(options.count_calls) {
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Number of checked nodes for no hohest history: " << std::endl;
			print_calls_counters(true, true, false, true);
		}

		// for cr iterate over all honest utilities
		for (unsigned utility = 0; utility < input.honest_utilities.size(); utility++) {

			if(options.count_nodes) {
				reset_global_counters(false, false, true, false);
				input.root->reset_count_check(false, false, true, false);
			}

			if(options.count_calls) {
				reset_calls(false, false, true, false);
			}

			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Checking utility " << input.honest_utilities[utility].utility << std::endl;

			input.root->reset_honest();

			// possible comment out?
			if(options.strategies) {
				input.root->reset_violation_cr();
			}

			subtree.collusion_resilience = {};

			if(options.collusion_resilience) {
				input.reset_counterexamples();
				input.root.get()->reset_counterexample_choices();
				input.root.get()->reset_use_cond_for_strong_ce();
				input.reset_logging();
				
				input.reset_unsat_cases();
				input.root->reset_reason();
				input.reset_strategies();
				// input.root->reset_problematic_group(true);
				// input.reset_reset_point();

				if(options.preconditions && options.strong_conditional_actions) {
					input.reset_violated_conditions();
					input.reset_violated_conditions_current_case();
					input.root->reset_violated_conditions();
				}
				property_subtree_utility(options, input, PropertyType::CollusionResilience, input.honest_utilities[utility].utility, subtree);
			}

			if(options.count_nodes) {
				std::cout << std::endl;
				std::cout << std::endl;
				std::cout << "Number of checked nodes for honest utility: " << input.honest_utilities[utility].utility << std::endl;
				print_global_counters(false, false, true, false);
			}

			if(options.count_calls) {
				std::cout << std::endl;
				std::cout << std::endl;
				std::cout << "Number of checked nodes for honest utility: " << input.honest_utilities[utility].utility << std::endl;
				print_calls_counters(false, false, true, false);
			}

			// create one file for this utility
			// set honest utility to this utility
			// set wi, weri, cr, pr subtree results
			// wi, weri, pr always the same, only cr changes
			subtree.honest_utility = input.honest_utilities;



			std::string file_name = options.input_path + std::string(".out");
			if(options.weak_conditional_actions) {
				subtree.solved_weak_cond_actions = true;
			} else {
				subtree.solved_weak_cond_actions = false;
			}

			if(options.preconditions) {
				subtree.solved_for_preconditions = true;
			} else {
				subtree.solved_for_preconditions = false;
			}

			std::cout << "Print to file..." << std::endl;
        	print_subtree_result_to_file(input, file_name, subtree, options.preconditions);

		}

	}
}