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

// third-party library for parsing to JSON
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

json parse_honest_utility_element(const Input &input, const HonestUtilityElement &element) {
    if (std::holds_alternative<std::vector<Utility>>(element)) {
        // It's a utility vector
        return parse_utility(input, std::get<std::vector<Utility>>(element));
    } else {
        // It's a vector of conditions
        const auto &conditions = std::get<std::vector<HonestUtilityCondition>>(element);
        json result = json::array();
        
        for (const auto &cond : conditions) {
            json cond_obj;
            std::stringstream ss;
            ss << cond.condition;
            cond_obj["condition"] = ss.str();
            cond_obj["utility"] = parse_honest_utility_element(input, cond.utility);
            result.push_back(cond_obj);
        }
        
        return result;
    }
}

json parse_property_to_json(std::vector<SubtreeResult> property_result) {

    json arr_res = json::array();

    for(auto &subtree_result : property_result) {
        // parse satisfied_in_case
        json arr_cases = json::array();
        for(auto &sat_case: subtree_result.satisfied_in_case) {
            json arr_case = parse_sat_case(sat_case);
            arr_cases.push_back(arr_case);
        }

        json obj = {{"player_group", subtree_result.player_group}, {"satisfied_in_case", arr_cases}};
        arr_res.push_back(obj);
    }
    return arr_res;
}

json parse_practicality_property_to_json(const Input &input, std::vector<PracticalitySubtreeResult> property_result) {
    json arr_pr = json::array();
    for(auto &subtree_result : property_result) {
        // parse case				
        json arr_case = parse_sat_case(subtree_result._case);
        // parse utilitiesß
        json utilities = json::array();
        for(auto &utility_tuple : subtree_result.utilities) {
            // parse utility
            json utility = parse_utility(input, utility_tuple.utility_tuple);
            
            // parse condition
            std::stringstream ss;
            ss << utility_tuple.condition;
            std::string condition_string = ss.str();
            
            json utility_with_condition = {
                {"utility", utility},
                {"condition", condition_string}
            };
            utilities.push_back(utility_with_condition);
        }
        
        json obj = {{"case", arr_case}, {"utilities", utilities}};
        arr_pr.push_back(obj);
    }
    return arr_pr;
}

void print_subtree_result_to_file(const Input &input, std::string file_name, Subtree &subtree) {
    std::ofstream outputFile(file_name);
    if (outputFile.is_open()) {  
        // Convert the subtree object to JSON
        json subtree_json;

        json arr_wi = parse_property_to_json(subtree.weak_immunity);
        json arr_weri = parse_property_to_json(subtree.weaker_immunity);
        json arr_cr = parse_property_to_json(subtree.collusion_resilience);
        json arr_pr = parse_practicality_property_to_json(input, subtree.practicality);
        json arr_honest_utility = parse_honest_utility_element(input, subtree.honest_utility);

        subtree_json["subtree"]["weak_immunity"] = arr_wi;
        subtree_json["subtree"]["weaker_immunity"] = arr_weri;
        subtree_json["subtree"]["collusion_resilience"] = arr_cr;
        subtree_json["subtree"]["practicality"] = arr_pr;
        subtree_json["subtree"]["honest_utility"] = arr_honest_utility;

        // Print the JSON representation
        outputFile << subtree_json.dump(4); // Pretty print with 4 spaces
        outputFile.close(); 

    } else {
        std::cerr << "Failed to create the file." << std::endl; 
    }
}

z3::Bool get_split_approx(z3::Solver &solver, Utility a, Utility b) {
// split on a>=b

	if (solver.solve({a.real < b.real}) == z3::Result::UNSAT) {
		if (solver.solve({a.infinitesimal >= b.infinitesimal}) == z3::Result::UNSAT) {
			return a.real > b.real;
		} else {
			return a.infinitesimal >= b.infinitesimal;
		}
		
	}
	// we don't know whether their real parts are >=, assert it
	else {
		return a.real >= b.real;
	}	
}

std::vector<HonestLeaf> get_honest_leaves(Node *node, const HonestHistory &history, const z3::Bool &parent_condition = z3::Bool()) {
	switch(node->type()) {
    case NodeType::LEAF:
		{
			HonestLeaf leaf;
			leaf.condition = parent_condition.null() ? z3::Bool(true) : parent_condition;
			leaf.leaf = &node->leaf();
			return {leaf};
		}
    case NodeType::SUBTREE:
		{
			HonestLeaf subtree;
			subtree.condition = parent_condition.null() ? z3::Bool(true) : parent_condition;
			subtree.leaf = &node->subtree();
			return {subtree};
		}
	case NodeType::BRANCH:
		break;
	case NodeType::CONDITION_NODE:
		break;
    // no need for default
    }

	assert(!history.empty());
	if (node->is_branch()) {
		assert(std::holds_alternative<std::string>(history[0]));
		HonestHistory next_history(history.begin() + 1, history.end());
		return get_honest_leaves(node->branch().get_choice(std::get<std::string>(history[0])).node.get(), next_history, parent_condition);
	} else if (node->is_condition_node()) {
		assert(std::holds_alternative<std::vector<HonestHistoryCondition>>(history[0]));
		// For condition nodes, recursively collect leaves from all conditions
		std::vector<HonestLeaf> all_leaves;
		for (const auto &hhcondition : std::get<std::vector<HonestHistoryCondition>>(history[0])) {
			// Combine parent condition with the condition from this branch
			z3::Bool combined_condition = parent_condition.null() ? hhcondition.condition : (parent_condition && hhcondition.condition);
			std::vector<HonestLeaf> condition_leaves = get_honest_leaves(node->condition_node().get_choice(hhcondition.condition).node.get(), hhcondition.path, combined_condition);
			all_leaves.insert(all_leaves.end(), condition_leaves.begin(), condition_leaves.end());
		}
		return all_leaves;
	}
	return {}; // Should not reach here
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




bool weak_immunity_rec(const Input &input, z3::Solver &solver, const Options &options, Node *node, unsigned player, bool weaker, bool consider_prob_groups) {

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


	if (node->is_leaf()) {
		const auto &leaf = node->leaf();

		if ((player < leaf.problematic_group) && consider_prob_groups){
			return true;
		}
		// known utility for us
		auto utility = leaf.utilities[player];

		z3::Bool property = weaker ? utility.real >= z3::Real::ZERO : utility >= Utility {z3::Real::ZERO, z3::Real::ZERO};

		if(options.count_calls) {
			weaker ? calls_weri++ : calls_wi++;
		}
		if (solver.solve({!property}) == z3::Result::UNSAT) {
			if (consider_prob_groups) {
				leaf.problematic_group = player + 1;
			}
			return true;
		}
		
		if(options.count_calls) {
			weaker ? calls_weri++ : calls_wi++;
		}
		if (solver.solve({property}) == z3::Result::UNSAT) {
			leaf.weakest_preconditions = z3::Bool(false);
			return false;
		}

		if (consider_prob_groups) {
			leaf.problematic_group = player;
		}
		leaf.reason = weaker ? utility.real >= z3::Real::ZERO : get_split_approx(solver, utility, Utility {z3::Real::ZERO, z3::Real::ZERO});
		input.set_reset_point(leaf);
		return false;

	} else if (node->is_subtree()){

		const auto &subtree = node->subtree();

		if ((player < subtree.problematic_group) && consider_prob_groups){
			return true;
		}

		// look up current player:
		// 		if disj_of_cases (in satisfied_for_case) is implied by current case we return true 
		//			e.g. satisfied for case [a+1>b, b>a+1], current_case is a>b;
		//				 since a>b => a+1>b, we conclude satisfied for a>b (i.e. return true)
		// 		else if disj_of_cases not disjoint from current case --> need case split (set the first of these not disjoint ones to be reason)
		//			e.g. satisfied for case [a>b], current_case is a>0;
		//  			hence whether satisfied or not depends on b, so we add a>b as the reason 
		// 		else (satisfied in case disjoint from current case) return false
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
					} else if (_case.size() == 0) {
						cases_as_conjunctions.push_back(z3::Bool(true));
					} else {
						cases_as_conjunctions.push_back(z3::conjunction(_case));
					}
				}

				z3::Bool disj_of_cases;

				if(cases_as_conjunctions.size() == 1) {
					disj_of_cases = cases_as_conjunctions[0];
				} else if (cases_as_conjunctions.size() == 0) {
					disj_of_cases = z3::Bool(false);
				} else {
					disj_of_cases = z3::disjunction(cases_as_conjunctions);
				}

				if(options.count_calls) {
					weaker ? calls_weri++ : calls_wi++;
				}
				z3::Result z3_result_implied = solver.solve({!disj_of_cases});

				// first case in description above: disj_of_cases implied by current case, so subtree weak(er) immune for player
				if (z3_result_implied == z3::Result::UNSAT) {
					if (consider_prob_groups) {
						subtree.problematic_group = player + 1;
					}
					return true;
				} else {

					// compute if current_case and case are disjoint:
					// is it sat that init && wi && case && current_case?
					// if no, then disjoint

					if(options.count_calls) {
						weaker ? calls_weri++ : calls_wi++;
					}
					z3::Result z3_result_disjoint = solver.solve({disj_of_cases});
					
					// second case in description above: not disjoint, but also not implied, so we need to split on the case as reason
					if (z3_result_disjoint == z3::Result::SAT) {
						// set reason
						subtree.reason = disj_of_cases;
					}

					// third case in description above: disjoint, so subtree not weak(er) immune for player, make sure reason is empty and return false
					if (consider_prob_groups) {
						subtree.problematic_group = player;
					}
					input.set_reset_point(subtree);
					subtree.weakest_preconditions = z3::Bool(false);
					return false;
				}
			}
		}
	} else if (node->is_condition_node()) {

		const auto &cond_node = node->condition_node();

		if ((player < cond_node.problematic_group) && consider_prob_groups){
			return true;
		}

		// we cannot control which condition will become true, so all branches (that are possible given the current case)
		// should be weak immune for the analyzed player
		bool result = true;
		z3::Bool reason;
		unsigned reset_index;
		bool none_violated = true;
		std::vector<z3::Bool> prec_vec;
		unsigned i = 0;
		for (const ConditionChoice &choice: cond_node.conditions) {
			// only consider condition if it is compatible with the current case
			if (solver.solve({choice.condition}) == z3::Result::SAT) {
				// add condition as assumption for recursive call, and remove it afterwards (solver.pop())
				solver.push();
				solver.assert_(choice.condition);
				if (!weak_immunity_rec(input, solver, options, choice.node.get(), player, weaker, consider_prob_groups)) {
					none_violated = false;
					if (choice.node->reason.null()){
						if (options.counterexamples) {
							z3::Bool current_condition = choice.condition;
							cond_node.counterexample_choices.push_back(CondAction(current_condition.to_string()));
						}
						if (!options.all_counterexamples && !options.preconditions && !options.subtree){
							solver.pop();
							return false;
						} else {
							result = false;
							if (options.preconditions || options.subtree) {
								if (!choice.node->get_weakestpreconditions().is(z3::Bool(false))) {
									prec_vec.push_back(choice.condition && choice.node->get_weakestpreconditions());
									// cond_node.weakest_preconditions = cond_node.weakest_preconditions || (choice.condition && choice.node->get_weakestpreconditions());
								}
							}
						}
					} else {
						if (result && reason.null()){
							reason = choice.node->reason;
							reset_index = i;
						}
						result = false;
					}	
				} else {
					if (options.preconditions || options.subtree) {
						prec_vec.push_back(choice.condition);
						 // cond_node.weakest_preconditions = cond_node.weakest_preconditions || choice.condition;
					}
				}
				solver.pop();
				i++;
				
			}
		}
		if (!reason.null()) {
			cond_node.reason = reason;
			input.set_reset_point(*cond_node.conditions[reset_index].node);
		}
		if (result && consider_prob_groups) {
			cond_node.problematic_group = player + 1;
		}
		if (none_violated && ( options.preconditions || options.subtree) ) {
			cond_node.weakest_preconditions = z3::Bool(true);
		}
		else if (options.preconditions || options.subtree) {
			if (prec_vec.size() == 0 ){
				cond_node.weakest_preconditions = z3::Bool(false);
			} else if (prec_vec.size() == 1) {
				cond_node.weakest_preconditions = prec_vec[0];
			} else {
				cond_node.weakest_preconditions = z3::disjunction(prec_vec);
			}
			cond_node.weakest_preconditions = cond_node.weakest_preconditions.simplify();
		}
		return result;
	}
	else {
		assert(node->is_branch());
	
		const auto &branch = node->branch();

		if ((player < branch.problematic_group) && consider_prob_groups){
			return true;
		}


		// analyzed player is current player
		if (player == branch.player) { 	

			// we are along the honest history -> we have to take the honest action, so we only need to check that branch for weak immunity
			if (branch.honest) {
				// if we are along the honest history, we want to take the honest action
				auto &honest_choice = branch.get_honest_child();
				auto *subtree = honest_choice.node.get();

				// set chosen action, needed for printing strategy
				branch.strategy = honest_choice.action;
				

				// the honest choice must be weak immune
				if (weak_immunity_rec(input, solver, options, subtree, player, weaker, consider_prob_groups)) {
					if (consider_prob_groups) {
						branch.problematic_group = player + 1;
					}
					return true;
				} 
				branch.weakest_preconditions = honest_choice.node->get_weakestpreconditions();
				

				branch.reason = subtree->reason;
				input.set_reset_point(branch);
				return false;
			}
			// otherwise, we are not along the honest history, we can take any action we please as long as it's weak immune
			z3::Bool reason;
			unsigned reset_index;
			unsigned i = 0;
			std::vector<z3::Bool> prec_vec;
			for (const Choice &choice: branch.choices) {
				if (weak_immunity_rec(input, solver, options, choice.node.get(), player, weaker, consider_prob_groups)) {
					// set chosen action, needed for printing strategy
					branch.strategy = choice.action;
					if (consider_prob_groups) {
							branch.problematic_group = player + 1;
						}
					branch.weakest_preconditions = z3::Bool(true);
					return true;
				}
				if (choice.node->reason.null()){
					if (options.preconditions || options.subtree) {
						if (!choice.node->get_weakestpreconditions().is(z3::Bool(false))) {
							prec_vec.push_back(choice.node->get_weakestpreconditions());
							// branch.weakest_preconditions = branch.weakest_preconditions ||  choice.node->get_weakestpreconditions();
						}
					}
				}
				
				if ((!choice.node->reason.null()) && (reason.null())) {
						reason = choice.node->reason;
						reset_index = i;
				}
				i++;
			}
			if (!reason.null()) {
					branch.reason = reason;
					input.set_reset_point(*branch.choices[reset_index].node);
			}	
			if (options.preconditions || options.subtree) {
				if (prec_vec.size() == 0 ){
					branch.weakest_preconditions = z3::Bool(false);
				} else if (prec_vec.size() == 1) {
					branch.weakest_preconditions = prec_vec[0];
				} else {
					branch.weakest_preconditions = z3::disjunction(prec_vec);
				}
				branch.weakest_preconditions = branch.weakest_preconditions.simplify();
			}
			return false;

		} else {
			// if we are not the analyzed player, we could do anything,
			// so all branches should be weak immune for the analyzed player
			bool result = true;
			z3::Bool reason;
			unsigned reset_index;
			unsigned i = 0;
			branch.weakest_preconditions = z3::Bool(true);
			std::vector<z3::Bool> prec_vec;
			bool wp_is_false = false;
			for (const Choice &choice: branch.choices) {
				if (!weak_immunity_rec(input, solver, options, choice.node.get(), player, weaker, consider_prob_groups)) {
					if (choice.node->reason.null()){
						if (options.preconditions || options.subtree) {
							if (!choice.node->get_weakestpreconditions().is(z3::Bool(false))) {
								prec_vec.push_back(choice.node->get_weakestpreconditions());
								// branch.weakest_preconditions = branch.weakest_preconditions && choice.node->get_weakestpreconditions();
							} else {
								wp_is_false = true;
							}
						}
						if (options.counterexamples) {
							branch.counterexample_choices.push_back(CondAction(choice.action));
						}
						if (!options.all_counterexamples){
							if (wp_is_false) {
								branch.weakest_preconditions = z3::Bool(false);
							}
							return false;
						} else {
							result = false;
						}
					} else {
						if (result && reason.null()){
							reason = choice.node->reason;
							reset_index = i;
						}
						result = false;
					}	
				}
				i++;
			}
			if (!reason.null()) {
				branch.reason = reason;
				input.set_reset_point(*branch.choices[reset_index].node);
			} else if ((options.preconditions || options.subtree) && wp_is_false) {
				branch.weakest_preconditions = z3::Bool(false);
			}
			if (result && consider_prob_groups) {
				branch.problematic_group = player + 1;
			}
			if (options.preconditions || options.subtree) {
				if (prec_vec.size() == 0 ){
					branch.weakest_preconditions = z3::Bool(true);
				} else if (prec_vec.size() == 1) {
					branch.weakest_preconditions = prec_vec[0];
				} else {
					branch.weakest_preconditions = z3::conjunction(prec_vec);
				}
				branch.weakest_preconditions = branch.weakest_preconditions.simplify();
			}	
			return result;
		}
	}

	assert(false); // should not reach here
	return false;
} 


z3::Bool collusion_resilience_rec(const Input &input, z3::Solver &solver, const Options &options, Node *node, std::bitset<Input::MAX_PLAYERS> group, std::vector<CondHonestTotalUtility> all_honest_total, unsigned players, uint64_t group_nr, bool consider_prob_groups) {

	count_cr_repetitions++;
	if(!node->checked_cr) {
		count_cr++;
		node->checked_cr = true;
	}
	
	if (node->is_leaf()) {
		const auto &leaf = node->leaf();


		if (leaf.honest) {
			// if we are along the honest history, we want to take the honest action, so we only need "to check" that branch for collusion resilience
			if (consider_prob_groups) {
				leaf.problematic_group = group_nr + 1;
			}
			return true;
		} else { // not along honest
			if  ((group_nr < leaf.problematic_group) && consider_prob_groups){
				return true;
			}

			// compute the total utility for the player group...
			Utility group_utility{z3::Real::ZERO, z3::Real::ZERO};
			
			for (size_t player = 0; player < players; player++)
				if (group[player])
					group_utility = group_utility + leaf.utilities[player];

			z3::Bool reason;
			z3::Bool result = false;
			std::vector<z3::Bool> result_vec;
			bool fails_one_honest = false;
			std::vector<z3::Bool> violation_conditions; // conditions under which the group utility is not smaller than an honest total utility

			// ..and compare it to all honest total utilities that are possible given the current case (i.e. all honest total utilities for which the condition can be satisfied under the current case)
			for (const auto &honest_total : all_honest_total) {
				// if the condition for this honest total is satisfiable, we need to check that the group utility is smaller than this honest total
				if (solver.solve({honest_total.condition}) == z3::Result::SAT) {
					solver.push();
					solver.assert_(honest_total.condition);

					z3::Bool condition = honest_total.utility >= group_utility;	

					if(options.count_calls) {
						calls_cr++;
					}
					if (solver.solve({condition}) == z3::Result::UNSAT) {

						if(options.strategies) { 
							violation_conditions.push_back(honest_total.condition); // violates cr only in this condition
						}
						fails_one_honest = true;
					} else {

						if(options.count_calls) {
							calls_cr++;
						}
						if (solver.solve({!condition}) == z3::Result::SAT) {
							fails_one_honest = true;
							if (reason.null()){
								reason = get_split_approx(solver, honest_total.utility, group_utility);
							}
						} else {
							if (honest_total.condition.is(z3::Bool(true))) { // honest history has no condition nodes, so there is just 1 honest_total
								solver.pop();
								return true;
							}
							result_vec.push_back(honest_total.condition); 
							// result = result || honest_total.condition;
						}
					}

					solver.pop();
				}
			}

			if (result_vec.size() == 0) {
				result = z3::Bool(false);
			} else if (result_vec.size() == 1) {
				result = result_vec[0];
			} else {
				result = z3::disjunction(result_vec);
			}

			if(!fails_one_honest){
				result = true;
				if (consider_prob_groups) {
					leaf.problematic_group = group_nr + 1;
				}
			} else {
				if (options.strategies) {
					if (violation_conditions.size() == all_honest_total.size()) {
						node->violates_cr[group_nr - 1] = z3::Bool(true); // violates cr in all conditions, so just set to true
					} else if (violation_conditions.size() == 0) {
						node->violates_cr[group_nr - 1] = z3::Bool(false); // does not violate cr in any condition, so just set to false
					} else {
						node->violates_cr[group_nr - 1] = disjunction(violation_conditions); // violates cr in violation conditions
					}
				}
			}

			if (!reason.null()) {
				leaf.reason = reason;
				input.set_reset_point(leaf);
				if (consider_prob_groups) {
					leaf.problematic_group = group_nr;
				}
				return result;
			}
			leaf.weakest_preconditions = result;
			return result;
		}

	} else if (node->is_subtree()){
		const auto &subtree = node->subtree();

		if  ((group_nr < subtree.problematic_group) && consider_prob_groups){
			return true;
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
			if (subtree_result.player_group.size() == player_names.size()){
				bool correct_subtree = true;
				for (const std::string &subtree_player : subtree_result.player_group){
					bool found = false;
					for (const auto &name : player_names){
						if(name == subtree_player){
							found = true;
							break;
						}
					}
					if (!found) {
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
						} else if (_case.size() == 0) {
							cases_as_conjunctions.push_back(z3::Bool(true));
						} else {
							cases_as_conjunctions.push_back(z3::conjunction(_case));
						}
					}
					z3::Bool disj_of_cases;

					if(cases_as_conjunctions.size() == 1) {
						disj_of_cases = cases_as_conjunctions[0];
					} else if (cases_as_conjunctions.size() == 0) {
						disj_of_cases = z3::Bool(false);
					} else {
						disj_of_cases = z3::disjunction(cases_as_conjunctions);
					}
					
					if(options.count_calls) {
						calls_cr++;
					}
					z3::Result z3_result_implied = solver.solve({!disj_of_cases});

					if (z3_result_implied == z3::Result::UNSAT) {
						if (consider_prob_groups) {
							subtree.problematic_group = group_nr + 1;
						}
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
						} else {
							// this subtree not cr against group in current case
							if (options.strategies) {
								subtree.violates_cr[group_nr - 1] = z3::Bool(true); // violates cr in all conditions, so just set to true
							}
						}

						if (consider_prob_groups) {
							subtree.problematic_group = group_nr;
						}
						input.set_reset_point(subtree);
						subtree.weakest_preconditions = z3::Bool(false);
						return false;
					}
				}
			}		
		}
	} else if (node->is_condition_node()) {
		const auto &cond_node = node->condition_node();

		if  ((group_nr < cond_node.problematic_group) && consider_prob_groups){
			return true;
		}

		if (cond_node.honest) {
			// we cannot control which condition will become true, so all branches (that are possible given the current case)
			// should be collusion resilient for the analyzed player group
			bool result = true;
			z3::Bool reason;
			unsigned reset_index;
			unsigned i = 0;
			bool none_violated = true;
			std::vector<z3::Bool> prec_vec;
			for (const ConditionChoice &choice: cond_node.conditions) {
				// only consider condition if it is compatible with the current case
				if (solver.solve({choice.condition}) == z3::Result::SAT) {
					// add condition as assumption for recursive call, and remove it afterwards (solver.pop())
					solver.push();
					solver.assert_(choice.condition);
					z3::Bool child_result = collusion_resilience_rec(input, solver, options, choice.node.get(), group, all_honest_total, players, group_nr, consider_prob_groups);
					if (child_result.is(z3::Bool(false))) {
						none_violated = false;
						if (choice.node->reason.null()){
							if (options.counterexamples) { 
								z3::Bool current_condition = choice.condition;
								cond_node.counterexample_choices.push_back(CondAction(current_condition.to_string()));
							}
							if (options.strategies) {
								cond_node.violates_cr[group_nr - 1] = z3::Bool(true);
							}
							if (!options.all_counterexamples && !options.preconditions && !options.subtree){
								solver.pop();
								return false;
							} else {
								result = false;
								if (options.preconditions || options.subtree) {
									if (!choice.node->get_weakestpreconditions().is(z3::Bool(false))) {
										prec_vec.push_back(choice.condition && choice.node->get_weakestpreconditions());
										// cond_node.weakest_preconditions = cond_node.weakest_preconditions || (choice.condition && choice.node->get_weakestpreconditions());
									}
								}
							}
						} else {
							if (result && reason.null()){
								reason = choice.node->reason;
								reset_index = i;
							}
							result = false;
						}	
					} else {
						assert(child_result.is(z3::Bool(true))); // if not false, result has to be true since along honest only yes/no answers possible
						if (options.preconditions || options.subtree) {
							prec_vec.push_back(choice.condition);
							// cond_node.weakest_preconditions = cond_node.weakest_preconditions || choice.condition;
						}
					}
					solver.pop();
					i++;
				}
			}
			if (!reason.null()) {
				cond_node.reason = reason;
				input.set_reset_point(*cond_node.conditions[reset_index].node);
			}
			if (result && consider_prob_groups) {
				cond_node.problematic_group = group_nr + 1;
			}
			if (none_violated && ( options.preconditions || options.subtree) ) {
				cond_node.weakest_preconditions = z3::Bool(true);
			}
			else if (options.preconditions || options.subtree) {
				if (prec_vec.size() == 0 ){
					cond_node.weakest_preconditions = z3::Bool(false);
				} else if (prec_vec.size() == 1) {
					cond_node.weakest_preconditions = prec_vec[0];
				} else {
					cond_node.weakest_preconditions = z3::disjunction(prec_vec);
				}
				cond_node.weakest_preconditions = cond_node.weakest_preconditions.simplify();
			}
			return result;
		} else { // we are off the honest history

			// we cannot control which condition will become true, so all branches (that are possible given the current case)
			// should be collusion resilient for the analyzed player group
			z3::Bool result = false;
			bool one_not_true = false;
			z3::Bool reason;
			std::vector<z3::Bool> result_vec;
			unsigned reset_index;
			unsigned i = 0;
			std::vector<z3::Bool> violation_condition; // conditions under which the subtree rooted at this condition node is not collusion resilient
			for (const ConditionChoice &choice: cond_node.conditions) {
				// only consider condition if it is compatible with the current case
				if (solver.solve({choice.condition}) == z3::Result::SAT) {
					// add condition as assumption for recursive call, and remove it afterwards (solver.pop())
					solver.push();
					solver.assert_(choice.condition);
					z3::Bool child_result = collusion_resilience_rec(input, solver, options, choice.node.get(), group, all_honest_total, players, group_nr, consider_prob_groups);
					if (!child_result.is(z3::Bool(true))) { // for each child that is not actually true, we collect the result and reason (if not null)
						one_not_true = true;
						if (!child_result.is(z3::Bool(false))) {
							result_vec.push_back(child_result && choice.condition);
						}
						
						if (choice.node->reason.null()){
							if (options.counterexamples) {
								z3::Bool current_condition = choice.condition;
								if (child_result.is(z3::Bool(false))) {
									cond_node.counterexample_choices.push_back(CondAction(current_condition.to_string()));
								} else {
									cond_node.counterexample_choices.push_back(CondAction(current_condition.to_string(), child_result.invert()));
								}
							}
							if (options.strategies) {
								if (child_result.is(z3::Bool(false))) {
									violation_condition.push_back(choice.condition); // violates cr in this condition
								} else {
									violation_condition.push_back(choice.condition && choice.node->violates_cr[group_nr - 1]);
								}
							}
							// if (!options.all_counterexamples){
							// 	return false;
							// } else {
							// 	result = false;
							// }
						} else {
							if (reason.null()){
								reason = choice.node->reason;
								reset_index = i;
							}
						}	
					} else {
						result_vec.push_back(choice.condition); // if true, we can add just the condition to the result
					}
					solver.pop();
					i++;
				}
			}
			if (!reason.null()) {
				cond_node.reason = reason;
				input.set_reset_point(*cond_node.conditions[reset_index].node);
			}
			if (!one_not_true) { // if all children are actually true, then we are actually true as well
				result = true;
				if (consider_prob_groups) {
					cond_node.problematic_group = group_nr + 1;
				}
			} else {
				if (result_vec.size() == 0) {
					result = z3::Bool(false);
				} else if (result_vec.size() == 1) {
					result = result_vec[0];
				} else {
					result = disjunction(result_vec);
				}
				if (options.strategies) {
					if (solver.solve({!cond_node.violates_cr[group_nr - 1]}) == z3::Result::UNSAT) { // if violation condition is implied to be true, we can just set it to true
						cond_node.violates_cr[group_nr - 1] = z3::Bool(true);
					} else if (violation_condition.size() == 0) { // if no violation condition, set to false
						cond_node.violates_cr[group_nr - 1] = z3::Bool(false);
					} else {
						cond_node.violates_cr[group_nr - 1] = disjunction(violation_condition); // violates cr in violation conditions
					}
				}
			}
			cond_node.weakest_preconditions = result;
			return result;
		}
		
	
	} else { // we deal with a branch
		assert(node->is_branch());

		const auto &branch = node->branch();

		if  ((group_nr < branch.problematic_group) && consider_prob_groups ){
			return true;
		}
		
		if (branch.honest) {
			if (!group[branch.player]) { // not a deviator and along honest, foward honest result
				// if we are along the honest history, we want to take an honest strategy
				auto &honest_choice = branch.get_honest_child();
				auto *subtree = honest_choice.node.get();

				// set chosen action, needed for printing strategy
				//branch.strategy = honest_choice.action;

				// the honest choice must be collusion resilient
				z3::Bool child_result = collusion_resilience_rec(input, solver, options, subtree, group, all_honest_total, players, group_nr, consider_prob_groups);
				if (child_result.is(z3::Bool(true))) {
					if (consider_prob_groups) {
						branch.problematic_group = group_nr + 1;
					}
					return true;
				} 
				
				if (options.strategies){
					branch.violates_cr[group_nr - 1] = z3::Bool(true);
				}
				assert(child_result.is(z3::Bool(false))); // if not true, result has to be false since along honest only yes/no answers possible
				branch.reason = subtree->reason;
				branch.weakest_preconditions = subtree->get_weakestpreconditions();
				input.set_reset_point(*subtree);
				return false;
			} else { // deviator has a turn, so all children have to be actually true along honest
				
				bool result = true;
				z3::Bool reason;
				unsigned reset_index;
				unsigned i = 0;
				branch.weakest_preconditions = z3::Bool(true);
				std::vector<z3::Bool> prec_vec;
				bool wp_is_false = false;
				for (const Choice &choice: branch.choices) {
					z3::Bool child_result = collusion_resilience_rec(input, solver, options, choice.node.get(), group, all_honest_total, players, group_nr, consider_prob_groups);
					bool equiv_to_true;
					if (!child_result.is(z3::Bool(true))) { // check whether child_result is equiv to true
						if (!child_result.is(z3::Bool(false))) {
							if (options.count_calls) {
								calls_cr++;
							}
							if (solver.solve({!child_result}) == z3::Result::UNSAT) { // child_result is implied by current assumptions, so we can treat it as true for the analysis of the other branches
								equiv_to_true = true;
							} else {
								equiv_to_true = false;
							}
						} else {
							equiv_to_true = false;
						}
					} else {
						equiv_to_true = true;
					}

					if (!equiv_to_true) {
						if (choice.node->reason.null()) {
							if (options.preconditions || options.subtree) {
								if (!choice.node->get_weakestpreconditions().is(z3::Bool(false))) {
									prec_vec.push_back(choice.node->get_weakestpreconditions());
									// branch.weakest_preconditions = branch.weakest_preconditions && choice.node->get_weakestpreconditions();
								} else {
									wp_is_false = true;
								}
							}
							if (options.strategies) {
								branch.violates_cr[group_nr - 1] = z3::Bool(true);
							}
							if (options.counterexamples) {
								branch.counterexample_choices.push_back(CondAction(choice.action));
							}
							if (!options.all_counterexamples){
								if (wp_is_false) {
									branch.weakest_preconditions = z3::Bool(false);
								}
								return false;
							} else {
								result = false;
							}
						} else {
							if (result && reason.null()){
								reason = choice.node->reason;
								reset_index = i;
							}
							result = false;
						}	
					}
					i++;
				}
				if (!reason.null()) {
					branch.reason = reason;
					input.set_reset_point(*branch.choices[reset_index].node);
				}
				else if ((options.preconditions || options.subtree) && wp_is_false) {
					branch.weakest_preconditions = z3::Bool(false);
				}
				else if (options.preconditions || options.subtree) {
					if (prec_vec.size() == 0 ){
						branch.weakest_preconditions = z3::Bool(true);
					} else if (prec_vec.size() == 1) {
						branch.weakest_preconditions = prec_vec[0];
					} else {
						branch.weakest_preconditions = z3::conjunction(prec_vec);
					}
					branch.weakest_preconditions = branch.weakest_preconditions.simplify();
				}
				if (result && consider_prob_groups) {
					branch.problematic_group = group_nr + 1;
				}
				return result;
			}
		}
		else { // we are off the honest behavior

			if (!group[branch.player]) {  // not a deviator and off honest 
				// we can take any strategy we please as long as it's collusion resilient
				// if options.strategies is set, we have to consider all branches, otherwise we can stop after the first cr one
				
				
				if (options.strategies){ 
					z3::Bool result = false;
					std::vector<z3::Bool> result_vec;
					bool one_true = false;
					z3::Bool reason;
					unsigned reset_index;
					unsigned i = 0;
					std::vector<z3::Bool> violation_condition; // condition under which the subtree rooted at this branch is not collusion resilient
					for (const Choice &choice: branch.choices) {
						z3::Bool child_result = collusion_resilience_rec(input, solver, options, choice.node.get(), group, all_honest_total, players, group_nr, consider_prob_groups);
						if (child_result.is(z3::Bool(true))) {

							if (consider_prob_groups){
								branch.problematic_group = group_nr + 1;
							}
							one_true = true;
						// if not cr and reason is null, then violated
						} else if (choice.node->reason.null()) {
							if (!child_result.is(z3::Bool(false))) {
								violation_condition.push_back(choice.node->violates_cr[group_nr - 1]); // violated in this condition
							}
						}
						if (!child_result.is(z3::Bool(false))) {
							result_vec.push_back(child_result);
						}
						if ((!choice.node->reason.null()) && (reason.null())) {
							reason = choice.node->reason;
							reset_index = i;
						}
						i++;		
					}

					if (one_true){
						branch.violates_cr[group_nr - 1] = z3::Bool(false);
						return true;
					} else {
						if (solver.solve({branch.violates_cr[group_nr - 1]}) == z3::Result::UNSAT) { // if violation condition is unsat, then we are actually not violated
							branch.violates_cr[group_nr - 1] = z3::Bool(false);
						} else {
							if (violation_condition.size() == 0) {
								branch.violates_cr[group_nr - 1] = z3::Bool(true); // if no violation condition, set to true
							} else {
								branch.violates_cr[group_nr - 1] = conjunction(violation_condition); // violated if all violation conditions are satisfied
							}
						}
					}
					// only set reason if there is one
					if (!reason.null()) {
							branch.reason = reason;
							input.set_reset_point(*branch.choices[reset_index].node);
					}
					if (result_vec.size() == 0) {
						result = z3::Bool(false);
					} else if (result_vec.size() == 1) {
						result = result_vec[0];
					} else {
						result = disjunction(result_vec);
					}
					branch.weakest_preconditions = result;
					return result;

				} else {
					z3::Bool reason;
					std::vector<z3::Bool> result_vec;
					z3::Bool result = false;
					unsigned reset_index;
					unsigned i = 0;
					for (const Choice &choice: branch.choices) {
						z3::Bool child_result = collusion_resilience_rec(input, solver, options, choice.node.get(), group, all_honest_total, players, group_nr, consider_prob_groups);
						if (child_result.is(z3::Bool(true))) {
							
							if (consider_prob_groups) {
								branch.problematic_group = group_nr + 1;
							}
							return true;
						} 
						if (!child_result.is(z3::Bool(false))) {
							result_vec.push_back(child_result);
						}
						if ((!choice.node->reason.null()) && (reason.null())) {
							reason = choice.node->reason;
							reset_index = i;
						}
						i++;
					}
					if (!reason.null()) {
							branch.reason = reason;
							input.set_reset_point(*branch.choices[reset_index].node);
					}
					if (result_vec.size() == 0) {
						result = z3::Bool(false);
					} else if (result_vec.size() == 1) {
						result = result_vec[0];
					} else {
						result = disjunction(result_vec);
					}
					branch.weakest_preconditions = result;
					return result;
				}


			} else {
				// if we are not the honest player, we could do anything,
				// so all branches should be collusion resilient for the player
				z3::Bool result = true;
				std::vector<z3::Bool> result_vec;
				bool one_false = false;
				bool one_false_without_reason = false;
				z3::Bool reason;
				unsigned reset_index;
				unsigned i = 0;
				std::vector<z3::Bool> violation_condition; 
				for (const Choice &choice: branch.choices) {
					z3::Bool child_result = collusion_resilience_rec(input, solver, options, choice.node.get(), group, all_honest_total, players, group_nr, consider_prob_groups);
					if (!child_result.is(z3::Bool(true))) {
						if (child_result.is(z3::Bool(false))) {
							if (choice.node->reason.null()) {
								if (options.strategies) {
									branch.violates_cr[group_nr - 1] = z3::Bool(true);
								}
								if (options.counterexamples) { 
									branch.counterexample_choices.push_back(CondAction(choice.action));
								}
								if (!options.all_counterexamples){
									branch.weakest_preconditions = z3::Bool(false);
									return false;
								} else {
									one_false = true;
									one_false_without_reason = true;
								}
							} else {
								if (!one_false && reason.null()){ 
									reason = choice.node->reason;
									reset_index = i;
								}
								one_false = true;
							}
						}	else {
							result_vec.push_back(child_result);
							if ((!choice.node->reason.null()) && (reason.null() && !one_false)) {
								reason = choice.node->reason;
								reset_index = i;
							}
							if (choice.node->reason.null() && options.strategies) {
								violation_condition.push_back(choice.node->violates_cr[group_nr - 1]); // violated in this condition
							}
							if (options.counterexamples && choice.node->reason.null()) {
								branch.counterexample_choices.push_back(CondAction(choice.action, child_result.invert()));
							}

						}
					}
					i++;
				}
				if (one_false) { 
					result = false;
					if (one_false_without_reason) {
						branch.weakest_preconditions = z3::Bool(false);
						if (options.strategies) {
							branch.violates_cr[group_nr - 1] = z3::Bool(true);
						}
						return false;
					}
				} else {
					if (result_vec.size() == 0) {
						result = z3::Bool(true);
					} else if (result_vec.size() == 1) {
						result = result_vec[0];
					} else {
						result = conjunction(result_vec);
					}
				}

				if (!reason.null()) {
					branch.reason = reason;
					input.set_reset_point(*branch.choices[reset_index].node);
				} else {
					if (options.strategies) {
						if (solver.solve({!branch.violates_cr[group_nr - 1]}) == z3::Result::UNSAT) { 
							branch.violates_cr[group_nr - 1] = z3::Bool(true);
						} else {
							if (violation_condition.size() == 0) {
								branch.violates_cr[group_nr - 1] = z3::Bool(false); // if no violation condition, set to false
							} else {
								branch.violates_cr[group_nr - 1] = disjunction(violation_condition); // violated if one violation conditions is satisfied
							}
						}
					}
				}

				if (result.is(z3::Bool(true)) && consider_prob_groups) {
					branch.problematic_group = group_nr + 1;
				}
				branch.weakest_preconditions = result;
				return result;
			}

		}

	}

	assert(false); // should not reach here
	return false;
}

bool practicality_rec(const Input &input, const Options &options, z3::Solver &solver, Node *node, std::vector<std::string> actions_so_far, bool consider_prob_groups) {

	count_pr_repetitions++;
	if(!node->checked_pr) {
		count_pr++;
		node->checked_pr = true;
	}
	
	if (node->is_leaf()) {
		return true;
	} else if (node->is_subtree()) {
		// we again have to consider how the current case relates to the PracticalitySubtreeResult cases
		// note that those cases are disjoint and span the whole universe

		// iterate over all PracticalitySubtreeResult
		// 		ask whether case and current_case is satisfiable
		//			if yes: ask whether current_case and not case is satisfiable
		//				if yes: case split on case (i.e. set reason to case, return false)
		//				if no: set practical_utilities for this node to the set of utilities in PracticalitySubtreeResult
		//			if no: proceed to next PracticalitySubtreeResult

		const auto &subtree = node->subtree();

		for (const PracticalitySubtreeResult &subtree_result: subtree.practicality) {
			z3::Bool subtree_case;
			// try to optimize: if only 1 -> no need for conjunction
			if(subtree_result._case.size() == 1) {
				subtree_case = subtree_result._case[0];
			} else if (subtree_result._case.size() == 0) {
				subtree_case = z3::Bool(true);
			} else {
				subtree_case = z3::conjunction(subtree_result._case);
			}

			if(options.count_calls) {
				calls_pr++;
			}
			z3::Result overlapping = solver.solve({subtree_case});

			
			if (overlapping == z3::Result::SAT){
				// cases overlap, check whether current case is implying subtree case
				if(options.count_calls) {
					calls_pr++;
				}
				z3::Result implied = solver.solve({!subtree_case});

				if (implied == z3::Result::SAT){
					// current case does not imply subtree case, so we need to split on this case
					subtree.reason = subtree_case;
					return false;
				} else {
					// current case implies subtree case,
					// hence every other subtree case is disjoint from current case 
					// so we can set the practical utilities for this subtree to the ones in this practicality subtree result
					if (subtree_result.utilities.size() == 0) {
						// we have to be along honest at this point, otw we would have had at least one pr utility
						if(options.counterexamples) {
							input.counterexamples.push_back(input.root.get()->compute_pr_cecase(input.players, input.players.size(), actions_so_far, "", {}));
						}
						return false;
					}
					subtree.utilities = {};
					for (const auto &utility_tuple : subtree.utilities) {
						subtree.utilities.push_back(UtilityTuple(utility_tuple.leaf, utility_tuple.condition));
					}

					if (subtree.honest) { // check whether the honest utilties are practical in every condition (deciding whether the subtree is pr)
						std::vector<z3::Bool> disjuncts = {};
						for (const auto &utility_tuple : subtree_result.utilities) {
							disjuncts.push_back(utility_tuple.condition);
						}
						assert(disjuncts.size() > 0);
						z3::Bool joint_condition = z3::disjunction(disjuncts);
						if(solver.solve({!joint_condition}) == z3::Result::SAT) {
							if(options.counterexamples) {
								input.counterexamples.push_back(input.root.get()->compute_pr_cecase(input.players, input.players.size(), actions_so_far, "", {}));
							}
							return false;
						} else {
							return true;
						}	
					}
					return true;
				}
			} 
		}
		// in case we have listed only cases where it is practical and they do not 
		// span the whole universe, return false, because no corresponding case has been found
		if(options.counterexamples) {
			input.counterexamples.push_back(input.root.get()->compute_pr_cecase(input.players, input.players.size(), actions_so_far, "", {}));
		}
		return false;

	} else if (node->is_condition_node()) { 

		const auto &cond_node = node->condition_node();

		if ((cond_node.problematic_group == 1) && consider_prob_groups){
			return true;
		}

		// we cannot control which condition will become true, so all branches (that are possible given the current case)
		// should be practical

		// get all practical utilities recursively
		std::vector<UtilityTuplesSet> children; 
		std::vector<z3::Bool> children_conditions;

		bool result = true;

  		for (const ConditionChoice &choice: cond_node.conditions) {
			if (options.count_calls) {
				calls_pr++;
			}
			if (solver.solve({choice.condition}) == z3::Result::SAT) {	

				std::vector<std::string> updated_actions;
				updated_actions.insert(updated_actions.begin(), actions_so_far.begin(), actions_so_far.end());
				z3::Bool current_condition = choice.condition;
				updated_actions.push_back(current_condition.to_string());
				solver.push();
				solver.assert_(current_condition);
				if(!practicality_rec(input, options, solver, choice.node.get(), updated_actions, consider_prob_groups)) {
					if (result) {
						cond_node.reason = choice.node->reason;
						input.set_reset_point(cond_node);
					}

					result = false;
					
					if(!options.all_counterexamples || !cond_node.reason.null()) {
						if (!(cond_node.reason.null() && (options.preconditions || options.subtree))) {
							solver.pop();
							return false;
						}
						result = false;
					}

				}

				
				if (choice.node->get_utilities().size()==0){
					assert(!result); 
				}
			
				children.push_back(choice.node->get_utilities());
				children_conditions.push_back(current_condition);
				
				solver.pop();
			}
		}

		UtilityTuplesSet practical_utilities;
		unsigned int i = 0;
		for (const auto& utilities : children) {
			for (const auto& utility : utilities) {
				z3::Bool simp_condition = (utility.condition && children_conditions[i]).simplify();
				UtilityTuple to_add(utility.leaf, simp_condition);
				Strategy new_strategy(children_conditions[i].to_string()); 
				new_strategy.children_strategies = {utility.strategy};
				to_add.strategy = new_strategy;
				practical_utilities.insert(to_add);
			}
			i++;
		}

		cond_node.practical_utilities = practical_utilities;
		return result;

	} else {
		assert(node->is_branch());
		// else we deal with a branch
		const auto &branch = node->branch();

		if  (branch.problematic_group == 1 && consider_prob_groups){
			return true;
		}	

		// get practical utilities recursively
		std::vector<UtilityTuplesSet> children; // conditions taken care of correctly by get_utilities
		std::vector<std::string> children_actions;

		UtilityTuplesSet honest_utilities; // conditions taken care of correctly by get_utilities
		unsigned int i = 0;
		unsigned honest_index = 0;
		std::string honest_choice;

		bool result = true;

		// collecting practical utilities for all children
		// start with honest child (if along honest)
		if (branch.honest) {
			// check honest branch first
			for (const Choice &choice: branch.choices) {
				if (choice.node->honest) {
					std::vector<std::string> updated_actions;
					updated_actions.insert(updated_actions.begin(), actions_so_far.begin(), actions_so_far.end());
					updated_actions.push_back(choice.action);
					if(!practicality_rec(input, options, solver, choice.node.get(), updated_actions, consider_prob_groups)) {
						branch.reason = choice.node->reason;
						input.set_reset_point(branch);
						result = false;

						if(!options.all_counterexamples || !branch.reason.null()) {
							return false;
						}
					}
					honest_utilities = choice.node->get_utilities();
					honest_choice = choice.action;
					branch.strategy = choice.action; // choose the honest action along the honest history
					honest_index = i;
					
					break;
				}
				i++;
			}
		}

		// check other (not honest) children
		for (const Choice &choice: branch.choices) {
			if (!choice.node->honest) {
				// this child has no practical strategy (propagate reason for case split, if any) 
				std::vector<std::string> updated_actions;
				updated_actions.insert(updated_actions.begin(), actions_so_far.begin(), actions_so_far.end());
				updated_actions.push_back(choice.action);
				if(!practicality_rec(input, options, solver, choice.node.get(), updated_actions, consider_prob_groups)) {
					if (result) {
						branch.reason = choice.node->reason;
						input.set_reset_point(branch);
					}

					result = false;

					if(!options.all_counterexamples || !branch.reason.null()) {
						return false;
					}
				}

				
				if (choice.node->get_utilities().size()==0){
					assert(!result);
					assert(options.all_counterexamples);
					assert(input.counterexamples.size()>0);
				}
			
				children.push_back(choice.node->get_utilities());
				children_actions.push_back(choice.action);
				
			}
		}

		// practicality reasoning starting here
		if (branch.honest) {
			// each honest utility has to be checked for practicality
			for ( auto& honest_utility: honest_utilities) {

				z3::Bool new_condition = honest_utility.condition;

				// we need to remove the strategy of the PR utilities in a first step to be able to update it correctly later
				// so we store it temporarily in honest_strategy
				std::optional<Strategy> honest_strategy = honest_utility.strategy; 
				honest_utility.strategy = Strategy(honest_choice);

				// for all other children
				unsigned int j = 0;
				for (const auto& utilities : children) {

					// exists dominated "function"
					bool found = false;
					z3::Bool condition = z3::Bool(false);
					std::vector<ConditionStrategy> child_strategy;

					// does there exist a possible utility such that `honest_utility` is geq than it?				
					for (const auto& utility : utilities) {
						if(options.count_calls) {
							calls_pr++;
						}
						if (solver.solve({honest_utility.condition, utility.condition}) == z3::Result::SAT) {
							solver.push();
							solver.assert_(honest_utility.condition);
							solver.assert_(utility.condition);
							auto comparison =   honest_utility[branch.player] < utility[branch.player];
							if(options.count_calls) {
								calls_pr++;
							}
							z3::Result comparison_result = solver.solve({comparison});
							if (comparison_result == z3::Result::SAT) {
								if(options.count_calls) {
									calls_pr++;
								}
								if (solver.solve({!comparison}) == z3::Result::SAT) {
									// might be maximal, just couldn't prove it
									if (result){
										branch.reason =  get_split_approx(solver, honest_utility[branch.player], utility[branch.player]); 
										input.set_reset_point(branch);
									}
								}
							} 
							else {
								assert(comparison_result == z3::Result::UNSAT);
								found = true;
								ConditionStrategy dominated_strategy(utility.condition, utility.strategy);
								child_strategy.push_back(dominated_strategy);
								
								condition = condition || utility.condition;
							}
							solver.pop();
						}
					}
					if (found){
						// need to insert strategy after honest at right point in vector
						if (j == honest_index){
							honest_utility.strategy->children_strategies.push_back(honest_strategy);
						} 
						honest_utility.strategy->children_strategies.push_back(child_strategy);
					}
					
					
					// end of exists dominated "function"

					if(options.count_calls) {
						calls_pr++;
					}
					bool exists_non_pr_condition = solver.solve({!condition, honest_utility.condition}) == z3::Result::SAT;
					if ((!found || exists_non_pr_condition) && utilities.size()>0) {
						
						// counterexample: current child (deviating choice) is the counterexample together with all its practical histories/strategies, 
						//                  additional information needed: current history (to be able to document deviation point)
						//                                                 current player
						// NOTE format of ce different from wi and cr, since all practical histories of child are needed to be a CE 

						// store (push back) it in input.counterexamples; case will be added in property rec


						// all counterexamples: do not return here (store return value in variable), but check all other children for further violations --> counterexamples
						// 						then also do not return yet, but continue the reasoning up to the root to collect further CEs

						// NOTE: for not along honest history, nothing to do

						std::string deviating_action = children_actions[j];

						if(options.counterexamples && branch.reason.null()) {
							input.counterexamples.push_back(input.root.get()->compute_pr_cecase(input.players, branch.player, actions_so_far, deviating_action, utilities));
						}

						result = false;

						if(!options.all_counterexamples || !branch.reason.null()) {
							if (!(branch.reason.null() && (options.preconditions || options.subtree))) {
								return result; //false
							}
							new_condition = new_condition && condition;
							
						}
					}
					j++;
				}
				if(j == honest_index) {
					honest_utility.strategy->children_strategies.push_back(honest_strategy);
				}
				honest_utility.condition = new_condition.simplify();
			}
			
			branch.practical_utilities = honest_utilities;
			
			// honest choice is practical for current player
			// return true;

			return result;

		} else { // not along the honest history

			UtilityTuplesSet utility_result;
			
			unsigned int k = 0;
			for (const auto& utilities : children) {
				for ( const auto& utility : utilities) {
					
					Strategy new_strategy(children_actions[k]);

					// start actual practicality reasoning: check whether to drop this utility or not
					bool is_practical = true;
					z3::Bool new_condition = utility.condition;

					unsigned int m = 0;
					for (const auto& sibling_utilities : children) {
						if (k != m) {
							// exists dominated "function"
							bool found = false;
							z3::Bool condition = z3::Bool(false);
							std::vector<ConditionStrategy> child_strategy;

							// does there exist a sibling utility such that `utility` is geq than it?				
							for (const auto& other_utility : sibling_utilities) {
								if(options.count_calls) {
									calls_pr++;
								}
								if (solver.solve({utility.condition, other_utility.condition}) == z3::Result::SAT) {
									solver.push();
									solver.assert_(utility.condition);
									solver.assert_(other_utility.condition);
									auto comparison =   utility[branch.player] < other_utility[branch.player];
									if(options.count_calls) {
										calls_pr++;
									}
									z3::Result comparison_result = solver.solve({comparison});
									if (comparison_result == z3::Result::SAT) {
										if(options.count_calls) {
											calls_pr++;
										}
										if (solver.solve({!comparison}) == z3::Result::SAT) {
											// need case split
											if (result){
												branch.reason =  get_split_approx(solver, utility[branch.player], other_utility[branch.player]); 
												input.set_reset_point(branch);
											}
										}
									} 
									else {
										assert(comparison_result == z3::Result::UNSAT);
										// Insert the strategy of the dominating sibling utility
										ConditionStrategy dominated_strategy(other_utility.condition, other_utility.strategy);
										child_strategy.push_back(dominated_strategy);
										
										condition = condition || other_utility.condition;
										found = true;
									}
									solver.pop();
								}
							}

							if (found){
								// need to insert strategy at right point in vector
								new_strategy.children_strategies.push_back(child_strategy);
							}
							// end of exists dominated "function"

							if (!found) {
								assert(sibling_utilities.size()>0);
								if(!branch.reason.null()) {
									return false;
								}

								is_practical = false;
								break;
							} else {
								// this utility is dominating at least one other utility, so we need to add the condition under which it is dominating to the condition of this utility
								new_condition = new_condition && condition;
							}
						} else {
							//  insert the original child strategy at the correct place
							new_strategy.children_strategies.push_back(utility.strategy);
						
						}
						m++;
					}
					if (is_practical) {
						UtilityTuple to_insert(utility.leaf, new_condition.simplify()); 
						to_insert.strategy = new_strategy;
						utility_result.insert(to_insert);
					}

				}
				k++;
			}

			branch.practical_utilities = utility_result;
			
			assert(utility_result.size()>0);
			return true;

		} 

	}
}


// relay function to foward to property specific rec functions, also takes care of player_group and some book keeping for counterexamples and reasons for case splits
bool property_under_split(z3::Solver &solver, const Input &input, const Options &options, const PropertyType property, size_t history) {
	/* determine if the input has some property for the current honest history under the current split */
	
	if (property == PropertyType::WeakImmunity || property == PropertyType::WeakerImmunity) {
		bool result = true;

		z3::Bool reason;
		Node *current_reset_point;
		std::vector<uint64_t> problematic_group_storage;
		std::vector<z3::Bool> reason_storage;
		bool is_unsat = false;
		for (size_t player = 0 ; player < input.players.size(); player++) {
			
			if (!input.solved_for_group[player]) {
				// problematic groups are only considered when we haven't found a case split point yet
			
				bool weak_immune_for_player = weak_immunity_rec(input, solver, options, input.root.get(), player, property == PropertyType::WeakerImmunity, true);

				if (!weak_immune_for_player) {

					if (input.root->reason.null()){
						is_unsat = true;
						if (options.counterexamples) {
							std::vector<size_t> pl = {player};
							input.compute_cecase(pl, property);
							if (input.root->is_branch()) {
								input.root->branch().reset_counterexample_choices();
							} else {
								assert(input.root->is_condition_node());
								input.root->condition_node().reset_counterexample_choices();
							}
						}
					}
				
					if (!options.all_counterexamples && !options.preconditions && input.root->reason.null()){
						return false;
					} else if (((!options.all_counterexamples && !options.preconditions) || !is_unsat) && !input.root->reason.null() && reason.null()) {
						reason = input.root->reason;
						current_reset_point = input.reset_point;						
						if (input.root->is_branch()) {
							problematic_group_storage = input.root->branch().store_problematic_groups();
							reason_storage = input.root->branch().store_reason();
						} else {
							assert(input.root->is_condition_node());
							problematic_group_storage = input.root->condition_node().store_problematic_groups();
							reason_storage = input.root->condition_node().store_reason();
						}
					}

					if (options.preconditions && input.root->reason.null()) {
						input.weakest_precondition.push_back(input.root->get_weakestpreconditions()); 
					}

					result = false;
				} else {
					input.solved_for_group[player] = true;
				}

				input.root->reset_weakest_preconditions();

				if (input.root->is_branch()) {
					input.root->branch().reset_counterexample_choices();
					input.root->branch().reset_reason();
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().reset_counterexample_choices();
					input.root->condition_node().reset_reason();
				}
			}
		}
		if (!options.all_counterexamples && !options.preconditions) {
			if (!reason.null()){
				if (input.root->is_branch()) {
					input.root->branch().restore_problematic_groups(problematic_group_storage);
					input.root->branch().restore_reason(reason_storage);
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().restore_problematic_groups(problematic_group_storage);
					input.root->condition_node().restore_reason(reason_storage);
				}
				input.reset_point = current_reset_point;
			}
		} else {
			if ((!reason.null()) && !is_unsat){
				 if (input.root->is_branch()) {
					input.root->branch().restore_problematic_groups(problematic_group_storage);
					input.root->branch().restore_reason(reason_storage);
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().restore_problematic_groups(problematic_group_storage);
					input.root->condition_node().restore_reason(reason_storage);
				}
				input.reset_point = current_reset_point;
			}
		}
		return result;
	}

	else if (property == PropertyType::CollusionResilience) {
		

		std::vector<CondHonestUtility> all_honest_utilities;
		// lookup the leaves for this history
		if(history < input.honest.size()) {
			std::vector<HonestLeaf> honest_leaves = get_honest_leaves(input.root.get(), input.honest[history]);
			for (const HonestLeaf& honest_leaf : honest_leaves) {
				if (honest_leaf.leaf->is_leaf()){
					CondHonestUtility honest_utility;
					honest_utility.utility_tuple = honest_leaf.leaf->leaf().utilities;
					honest_utility.condition = honest_leaf.condition;
					all_honest_utilities.push_back(honest_utility);
				} else {
					// the case where the honest history ends in a subtree
					HonestUtilityElement honest_utility_element = honest_leaf.leaf->subtree().honest_utility;
					std::vector<CondHonestUtility> subtree_honest_utilities = get_conditional_honest_utilities(honest_utility_element, honest_leaf.condition);
					all_honest_utilities.insert(all_honest_utilities.end(), subtree_honest_utilities.begin(), subtree_honest_utilities.end());
				}
			}
		} else {
			// history is from input.honest_utilities
			const HonestUtilityTuple& honest_utility_tuple = input.honest_utilities[history - input.honest.size()];
			all_honest_utilities = get_conditional_honest_utilities(honest_utility_tuple.element);
			
		}
		
		// sneaky hack follows: all possible subgroups of n players can be implemented by counting through from 1 to (2^n - 2)
		// done this way more for concision than efficiency
		bool result = true;

		z3::Bool reason;
		Node *current_reset_point;
		std::vector<uint64_t> problematic_group_storage;
		std::vector<z3::Bool> reason_storage;
		bool is_unsat = false;
		for (uint64_t binary_counter = 1; binary_counter < -1ull >> (64 - input.players.size()); binary_counter++) {

			if (!input.solved_for_group[binary_counter]){
				if(options.strategies) {
					input.root->add_violation_cr();
				}

				// Convert CondHonestUtility to CondHonestTotalUtility for the current group
				std::bitset<Input::MAX_PLAYERS> group = binary_counter;
				std::vector<CondHonestTotalUtility> all_honest_total;
				for (const auto& cond_utility : all_honest_utilities) {
					CondHonestTotalUtility cond_total;
					cond_total.condition = cond_utility.condition;
					// Compute the total for this group
					Utility group_total{z3::Real::ZERO, z3::Real::ZERO};
					for (size_t player = 0; player < input.players.size(); player++) {
						if (group[player]) {
							group_total = group_total + cond_utility.utility_tuple[player];
						}
					}
					cond_total.utility = group_total;
					all_honest_total.push_back(cond_total);
				}
				// problematic groups are only considered when we haven't found a case split point yet
				z3::Bool cr_result = collusion_resilience_rec(input, solver, options, input.root.get(), group, all_honest_total, input.players.size(), binary_counter, false);
				bool collusion_resilient_for_group;
				if (cr_result.is(z3::Bool(true))) {
					collusion_resilient_for_group = true;
				} else {
					collusion_resilient_for_group = false;
				}
				
				if (!collusion_resilient_for_group) {

					if (input.root->reason.null()){
						is_unsat = true;
						if (options.counterexamples) {
							std::vector<size_t> pl;
							for (size_t player = 0; player < input.players.size(); player++) {
								if (group[player]) {
									pl.push_back(player);
								}
							}
							input.compute_cecase(pl, property);
							if (input.root->is_branch()) {
								input.root->branch().reset_counterexample_choices();
							} else {
								assert(input.root->is_condition_node());
								input.root->condition_node().reset_counterexample_choices();
							}
						}
					}
					
					if (!options.all_counterexamples && !options.preconditions && input.root->reason.null()){
						return false;
					} else if (((!options.all_counterexamples && !options.preconditions) || !is_unsat ) && !input.root->reason.null() && reason.null()) {
						reason = input.root->reason;
						current_reset_point = input.reset_point;
						if (input.root->is_branch()) {
							problematic_group_storage = input.root->branch().store_problematic_groups();
							reason_storage = input.root->branch().store_reason();
						} else {
							assert(input.root->is_condition_node());
							problematic_group_storage = input.root->condition_node().store_problematic_groups();
							reason_storage = input.root->condition_node().store_reason();
						}
					}

					if (options.preconditions && input.root->reason.null()) {
						input.weakest_precondition.push_back(input.root->get_weakestpreconditions()); 
					}

					result = false;
				} else {
					input.solved_for_group[binary_counter] = true;
				}

				input.root->reset_weakest_preconditions();

				if (input.root->is_branch()) {
					input.root->branch().reset_counterexample_choices();
					input.root->branch().reset_reason();
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().reset_counterexample_choices();
					input.root->condition_node().reset_reason();
				}
			}
		}
		if (!options.all_counterexamples && !options.preconditions) {
			if (!reason.null()){
				if (input.root->is_branch()) {
					input.root->branch().restore_problematic_groups(problematic_group_storage);
					input.root->branch().restore_reason(reason_storage);
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().restore_problematic_groups(problematic_group_storage);
					input.root->condition_node().restore_reason(reason_storage);
				}
				input.reset_point = current_reset_point;
			}
		} else {
			if ((!reason.null()) && !is_unsat){
				if (input.root->is_branch()) {
					input.root->branch().restore_problematic_groups(problematic_group_storage);
					input.root->branch().restore_reason(reason_storage);
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().restore_problematic_groups(problematic_group_storage);
					input.root->condition_node().restore_reason(reason_storage);
				}
				input.reset_point = current_reset_point;
			}
		}
		return result;
	}

	else if (property == PropertyType::Practicality) {
		//the consider_probs groups flag is not relevant for practicality;
		bool pr_result = practicality_rec(input, options, solver, input.root.get(), {}, true);
		if(pr_result && options.counterexamples && !input.root->honest) { // for subtree in regular mode
			CeCase pr_ce_case;
			std::vector<CeChoice> pr_choices;
			const auto& practical_utilities = input.root->is_branch() ? input.root->branch().practical_utilities : input.root->condition_node().practical_utilities;
			for(const auto& pr_utility : practical_utilities) {
				CeChoice ce_choice;
				std::vector<std::string> choices = input.root->strat2hist(pr_utility.strategy);
				for (const auto& choice : choices) {
					ce_choice.choices.push_back(CondAction(choice));
				}
				ce_choice.condition = pr_utility.condition;
				pr_choices.push_back(ce_choice);
			}
			pr_ce_case.counterexample = pr_choices;
			input.counterexamples.push_back(pr_ce_case);
		}
		if (!pr_result && input.root->reason.null() && (options.preconditions || options.subtree)) { // have to be along honest at root 
			// so collect honest utilties conditions as preconditions
			std::vector<z3::Bool> disjuncts;
			for (const auto& honest_utility : input.root->is_branch() ? input.root->branch().practical_utilities : input.root->condition_node().practical_utilities) {
				disjuncts.push_back(honest_utility.condition);
			}
			assert(disjuncts.size()>0);
			z3::Bool wp = disjunction(disjuncts);

			input.weakest_precondition = {wp}; 
		}
		input.root->reset_weakest_preconditions();
		return pr_result;
	}
	
 
	assert(false);
	UNREACHABLE
}



// recursive case splitting engine, for non subtree mode and subtree mode if pr and honest history
bool property_rec(z3::Solver &solver, const Options &options, const Input &input, const PropertyType property, std::vector<z3::Bool> current_case, size_t history, std::vector<PracticalitySubtreeResult> &subtree_results_pr) {
	/* 
		actual case splitting engine
		determine if the input has some property for the current honest history, splitting recursively
	*/

	// property holds under current split
	if (property_under_split(solver, input, options, property, history)) {
		if (!input.stop_log){
			std::cout << "\tProperty satisfied for case: " << current_case << std::endl; 
		}

		if(options.subtree) {
			PracticalitySubtreeResult subtree_result_pr;
			subtree_result_pr._case = current_case;
			subtree_result_pr.utilities = {};
			std::vector<Cond_Utility> honest_utilities;
			if (input.root->is_branch()) {
				for (auto elem: input.root->branch().practical_utilities) {
					honest_utilities.push_back(Cond_Utility(elem.leaf, elem.condition));
				}
			} else if (input.root->is_condition_node()){
				for (auto elem: input.root->condition_node().practical_utilities) {
					honest_utilities.push_back(Cond_Utility(elem.leaf, elem.condition));
				}
			}
			subtree_result_pr.utilities = honest_utilities;
			subtree_results_pr.push_back(subtree_result_pr);
		}


		// if strategies, add a "potential case" to keep track of all strategies
		if (options.strategies){
			input.compute_strategy_case(current_case, property, solver);

			if(options.all_cases && property == PropertyType::CollusionResilience) {
				input.root->reset_violation_cr();
			}
		}

		if(options.counterexamples && property == PropertyType::Practicality && !input.root->honest) {
			input.add_case2ce(current_case);
			
		}

		// add current case to the list of preconditions if option is on
		if (options.preconditions ) {
			input.add_sat_case(current_case);
			input.weakest_precondition = {};
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
		if (options.preconditions) {
			if (std::none_of(input.weakest_precondition.begin(), input.weakest_precondition.end(), [](const z3::Bool& b){ return b.is(z3::Bool(false)); })) {
				// if one element is actual false, then the case is not satisfiable, so we don't have to add it as a precondition
				std::vector<z3::Bool> new_sat_case = current_case;
				new_sat_case.insert(new_sat_case.end(), input.weakest_precondition.begin(), input.weakest_precondition.end());

				input.add_sat_case(new_sat_case);

			}
			input.weakest_precondition = {};
			input.stop_logging();
		}

		if(options.subtree) {
			PracticalitySubtreeResult subtree_result_pr;
			subtree_result_pr._case = current_case;
			subtree_result_pr.utilities = {};
			std::vector<Cond_Utility> prac_utilities;
			if (input.root->is_branch()) {
				for (auto elem: input.root->branch().practical_utilities) {
					prac_utilities.push_back(Cond_Utility(elem.leaf, elem.condition));
				}
			} else if (input.root->is_condition_node()){
				for (auto elem: input.root->condition_node().practical_utilities) {
					prac_utilities.push_back(Cond_Utility(elem.leaf, elem.condition));
				}
			}
			subtree_result_pr.utilities = prac_utilities;
			subtree_results_pr.push_back(subtree_result_pr);
		}


		if (options.counterexamples){
			input.add_case2ce(current_case);
		}

		if(options.all_cases && options.strategies && property == PropertyType::CollusionResilience) {
			input.root->reset_violation_cr();
		}

		return false;
	}
	if (!input.stop_log){
		std::cout << "\tSplitting on: " << split << std::endl;
	}

	std::vector<std::vector<z3::Bool>> violation;
	if (property == PropertyType::CollusionResilience && options.strategies){
		if (input.root->is_branch()) {
			violation = input.root->branch().store_violation_cr();
		} else {
			assert(input.root->is_condition_node());
			violation = input.root->condition_node().store_violation_cr();
		}
	}

	std::vector<std::vector<CondAction>> ce_storage;
	if (options.counterexamples && property != PropertyType::Practicality) {
		if (input.root->is_branch()) {
			ce_storage = input.root->branch().store_counterexample_choices();
		} else {
			assert(input.root->is_condition_node());
			ce_storage = input.root->condition_node().store_counterexample_choices();
		}
	}

	std::vector<bool> solved_for_storage;
	std::vector<uint64_t> problematic_groups;
	std::vector<z3::Bool> weakest_precondition_storage;
	if (property != PropertyType::Practicality) {
		solved_for_storage = input.store_solved_for();
		weakest_precondition_storage = input.weakest_precondition;
		if (input.root->is_branch()) {
			problematic_groups = input.root->branch().store_problematic_groups();
		} else {
			assert(input.root->is_condition_node());
			problematic_groups = input.root->condition_node().store_problematic_groups();
		}
	}

	auto &current_reset_point = input.reset_point;
	bool result = true;

	for (const z3::Bool& condition : {split, split.invert()}) {
		// reset reason and strategy
		// ? should be the same point of reset
		if (input.root->is_branch()) {
			input.root->branch().reset_reason();
		} else {
			assert(input.root->is_condition_node());
			input.root->condition_node().reset_reason();
		}
		if (input.reset_point->is_branch()) {
			input.reset_point->branch().reset_strategy();
		} else if (input.reset_point->is_condition_node()) {
			input.reset_point->condition_node().reset_strategy();
		}

		solver.push();
		solver.assert_(condition);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);
		assert (solver.solve() != z3::Result::UNSAT);

		bool attempt = property_rec(solver, options, input, property, new_current_case, history, subtree_results_pr);

		solver.pop();


		if (property != PropertyType::Practicality) {
			input.weakest_precondition = weakest_precondition_storage;
			// reset the branch.problematic_group for all branches to presplit state, such that the other case split starts at the same point
			if (input.root->is_branch()) {
				input.root->branch().restore_problematic_groups(problematic_groups);
			} else {
				assert(input.root->is_condition_node());
				input.root->condition_node().restore_problematic_groups(problematic_groups);
			}
			input.restore_solved_for(solved_for_storage);

			if (options.counterexamples){
				if (input.root->is_branch()) {
					input.root->branch().restore_counterexample_choices(ce_storage);
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().restore_counterexample_choices(ce_storage);
				}
			}
		}

		if (property == PropertyType::CollusionResilience && options.strategies){
			std::vector<std::vector<z3::Bool>> violation_copy;
			violation_copy.insert(violation_copy.end(), violation.begin(), violation.end());
			if (input.root->is_branch()) {
				input.root->branch().restore_violation_cr(violation_copy);
			} else {
				assert(input.root->is_condition_node());
				input.root->condition_node().restore_violation_cr(violation_copy);
			}
		}

		if (!attempt){
			if ((!options.preconditions) && (!options.all_cases)){
				return false;
			}
			else {
				result = false;
				if (options.preconditions){
					input.stop_logging();
				}
			}
		}
	}
	input.weakest_precondition = {}; // reseting for next history/property
	return result;
}

// actual case splitting engine, for subtree mode and honest history
bool property_rec_subtree(z3::Solver &solver, const Options &options, const Input &input, const PropertyType property, std::vector<z3::Bool> current_case, size_t history, unsigned group_nr, std::vector<std::vector<z3::Bool>> &satisfied_in_case) {
	/* 
		only called for weak(er) immunity and collusion resilience
		actual case splitting engine
		determine if the input has some property for the current honest history, splitting recursively
	*/

	bool property_result;
	std::bitset<Input::MAX_PLAYERS> group;

	if(property == PropertyType::CollusionResilience){
		std::vector<HonestLeaf> honest_leaves_vec = get_honest_leaves(input.root.get(), input.honest[history]);
		// For subtree mode, compute all possible honest totals from all conditional leaves
		group = group_nr;
		
		std::vector<CondHonestTotalUtility> all_honest_total;
		for (const auto& honest_leaf : honest_leaves_vec) {
			if (honest_leaf.leaf->is_leaf()) {
				const Leaf &leaf = honest_leaf.leaf->leaf();
				// Compute the honest total for the current group
				Utility group_total{z3::Real::ZERO, z3::Real::ZERO};
				for (size_t player = 0; player < input.players.size(); player++) {
					if (group[player]) {
						group_total = group_total + leaf.utilities[player];
					}
				}
				CondHonestTotalUtility cond_total;
				cond_total.condition = honest_leaf.condition;
				cond_total.utility = group_total;
				all_honest_total.push_back(cond_total);
			} else {
				assert(honest_leaf.leaf->is_subtree());
				const Subtree &subtree = honest_leaf.leaf->subtree();
				HonestUtilityElement honest_utility_element = subtree.honest_utility;
				std::vector<CondHonestUtility> subtree_honest_utilities = get_conditional_honest_utilities(honest_utility_element, honest_leaf.condition);
				for (const auto& cond_utility : subtree_honest_utilities) {
					Utility group_total{z3::Real::ZERO, z3::Real::ZERO};
					for (size_t player = 0; player < input.players.size(); player++) {
						if (group[player]) {
							group_total = group_total + cond_utility.utility_tuple[player];
						}
					}
					CondHonestTotalUtility cond_total;
					cond_total.condition = cond_utility.condition;
					cond_total.utility = group_total;
					all_honest_total.push_back(cond_total);
				}
			}
			
		}
		z3::Bool cr_result = collusion_resilience_rec(input, solver, options, input.root.get(), group, all_honest_total, input.players.size(), group_nr, false);
		if (cr_result.is(z3::Bool(true))) {
			property_result = true;
		} else {
			assert(cr_result.is(z3::Bool(false)));
			property_result = false;
		} 
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
		input.weakest_precondition = {}; // probably not necessary to reset here, since we won't use it for subtree mode, but just to be safe for now
		input.root->reset_weakest_preconditions(); // resetting the weakest preconditions in the tree such that they don't interfere with the other case split
		return true;
	}

	// otherwise consider case split
	z3::Bool split = input.root->reason;
	// there is no case split
	if (split.null()) {
		if (!input.stop_log){
			std::cout << "\tProperty violated in case: " << current_case << std::endl;
		}
		if (!input.root->get_weakestpreconditions().is(z3::Bool(false))) {
			std::vector<z3::Bool> new_sat_case = current_case;
			new_sat_case.push_back(input.root->get_weakestpreconditions());

			satisfied_in_case.push_back(new_sat_case);
		}
		input.weakest_precondition = {}; // probably not necessary to reset here, since we won't use it for subtree mode, but just to be safe for now
		input.root->reset_weakest_preconditions(); // resetting the weakest preconditions in the tree such that they don't interfere with the other case split
		return false;
	}

	input.weakest_precondition = {}; // probably not necessary to reset here, since we won't use it for subtree mode, but just to be safe for now
	input.root->reset_weakest_preconditions(); // resetting the weakest preconditions in the tree such that they don't interfere with the other case split


	if (!input.stop_log){
		std::cout << "\tSplitting on: " << split << std::endl;
	}

	auto &current_reset_point = input.reset_point;


	bool result = true;

	// both cr and w(er)i need all cases for soundness
	for (const z3::Bool& condition : {split, split.invert()}) {
		// reset reason and strategy
		// ? should be the same point of reset
		if (input.root->is_branch()) {
			input.root->branch().reset_reason();
		} else {
			assert(input.root->is_condition_node());
			input.root->condition_node().reset_reason();
			
		}
		if (input.reset_point->is_branch()) {
			input.reset_point->branch().reset_strategy();
		} else if (input.reset_point->is_condition_node()) {
			input.reset_point->condition_node().reset_strategy();
		}
		solver.push();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);

		bool attempt = property_rec_subtree(solver, options, input, property, new_current_case, history, group_nr, satisfied_in_case);

		solver.pop();

		if (!attempt){
			result = false;
		}


	}

	input.weakest_precondition = {}; // reseting for next history/property
	input.root->reset_weakest_preconditions(); // resetting the weakest preconditions in the tree 
	return result;
}

// actual case splitting enigne, for subtree mode and CR, if honest utility
bool property_rec_utility(z3::Solver &solver, const Options &options, const Input &input, const PropertyType property, std::vector<z3::Bool> current_case, const std::vector<CondHonestTotalUtility> &all_honest_total, unsigned group_nr, std::vector<std::vector<z3::Bool>> &satisfied_in_case) {
	/* 
		only called for collusion resilience
		actual case splitting engine
		determine if the input has some property for the current honest history, splitting recursively
	*/

	bool property_result;
	std::bitset<Input::MAX_PLAYERS> group = group_nr;

	z3::Bool cr_result = collusion_resilience_rec(input, solver, options, input.root.get(), group, all_honest_total, input.players.size(), group_nr, false);
	if (cr_result.is(z3::Bool(true))) {
		property_result = true;
	} else {
		if (solver.solve({!cr_result}) == z3::Result::UNSAT){
			property_result = true; // equiv to true also true
		} else {
			property_result = false;
		}
	}

	// property holds under current split
	if (property_result) {
		if (!input.stop_log){
			std::cout << "\tProperty satisfied for case: " << current_case << std::endl; 
		}
		
		satisfied_in_case.push_back(current_case);
		input.weakest_precondition = {}; // probably not necessary to reset here, since we won't use it for subtree mode, but just to be safe for now
		input.root->reset_weakest_preconditions(); // resetting the weakest preconditions in the tree such that they don't interfere with the other case split
		return true;
	}

	// otherwise consider case split
	z3::Bool split = input.root->reason;
	// there is no case split
	if (split.null()) {
		if (!input.stop_log){
			std::cout << "\tProperty violated in case: " << current_case << std::endl;
		}
		if (!input.root->get_weakestpreconditions().is(z3::Bool(false))) {
			std::vector<z3::Bool> new_sat_case = current_case;
			new_sat_case.push_back(input.root->get_weakestpreconditions());

			satisfied_in_case.push_back(new_sat_case);
		}

		input.weakest_precondition = {}; // probably not necessary to reset here, since we won't use it for subtree mode, but just to be safe for now
		input.root->reset_weakest_preconditions(); // resetting the weakest preconditions in the
		return false;
	}

	input.weakest_precondition = {}; // probably not necessary to reset here, since we won't use it for subtree mode, but just to be safe for now
	input.root->reset_weakest_preconditions(); // resetting the weakest preconditions in the tree

	if (!input.stop_log){
		std::cout << "\tSplitting on: " << split << std::endl;
	}

	auto &current_reset_point = input.reset_point;

	bool result = true;

	for (const z3::Bool& condition : {split, split.invert()}) {
		// reset reason and strategy
		// ? should be the same point of reset
		if (input.root->is_branch()) {
			input.root->branch().reset_reason();
		} else if (input.root->is_condition_node()){
			input.root->condition_node().reset_reason();
		}
		if (input.reset_point->is_branch()) {
			input.reset_point->branch().reset_strategy();
		} else if (input.reset_point->is_condition_node()) {
			input.reset_point->condition_node().reset_strategy();
		}

		solver.push();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);


		bool attempt = property_rec_utility(solver, options, input, property, new_current_case, all_honest_total, group_nr, satisfied_in_case);

		solver.pop();

		if (!attempt){
			result = false;
		}
	}

	input.weakest_precondition = {}; // reseting for next history/property
	input.root->reset_weakest_preconditions(); // resetting the weakest preconditions in the tree
	return result;
}

bool property_rec_nohistory(z3::Solver &solver, const Options &options, const Input &input, const PropertyType property, std::vector<z3::Bool> current_case, unsigned player_nr, std::vector<std::vector<z3::Bool>> &satisfied_in_case, std::vector<PracticalitySubtreeResult> &subtree_results_pr) {
	
	/* 
		only called for w(er)i and practicality
		actual case splitting engine
		determine if the input has some property for the current honest history, splitting recursively
	*/

	assert(property != PropertyType::CollusionResilience);
	
	bool property_result = false;
	if(property == PropertyType::WeakImmunity) {
		property_result = weak_immunity_rec(input, solver, options, input.root.get(), player_nr, false, false);
	} else if (property == PropertyType::WeakerImmunity) {
		property_result = weak_immunity_rec(input, solver, options, input.root.get(), player_nr, true, false);	
	} else if (property == PropertyType::Practicality) {
		property_result = practicality_rec(input, options, solver, input.root.get(),{}, false);
	}

	// property holds under current split
	if (property_result) {
		if (!input.stop_log){
			std::cout << "\tProperty satisfied for case: " << current_case << std::endl; 
		}

		if(property == PropertyType::Practicality) {
			PracticalitySubtreeResult subtree_result_pr;
			subtree_result_pr._case = current_case;
			subtree_result_pr.utilities = {};
			if (input.root->is_branch()) {
				for (auto elem: input.root->branch().practical_utilities) {
					std::vector<std::string> history_vec = input.root->strat2hist(elem.strategy);
					subtree_result_pr.utilities.push_back(Cond_Utility(elem.leaf, elem.condition, history_vec));
				}
			} else if (input.root->is_condition_node()){
				for (auto elem: input.root->condition_node().practical_utilities) {
					std::vector<std::string> history_vec = input.root->strat2hist(elem.strategy);
					subtree_result_pr.utilities.push_back(Cond_Utility(elem.leaf,elem.condition, history_vec));

				}
			}

			subtree_results_pr.push_back(subtree_result_pr);
		} else {
			satisfied_in_case.push_back(current_case);
		}


		input.weakest_precondition = {}; // probably not necessary to reset here, since we won't use it for subtree mode, but just to be safe for now
		input.root->reset_weakest_preconditions(); // resetting the weakest preconditions in the tree
		return true;
	}

	// otherwise consider case split
	z3::Bool split = input.root->reason;
	// there is no case split
	if (split.null()) {
		if (!input.stop_log){
			std::cout << "\tProperty violated in case: " << current_case << std::endl;
		}
		if (property != PropertyType::Practicality) {
			if (!input.root->get_weakestpreconditions().is(z3::Bool(false))){
				std::vector<z3::Bool> new_sat_case = current_case;
				new_sat_case.push_back(input.root->get_weakestpreconditions());

				satisfied_in_case.push_back(new_sat_case);
			}
		} else {
			assert(false); // practicality off the honest history should not reutrn false without a case split
		}
		input.weakest_precondition = {}; // probably not necessary to reset here, since we won't use it for subtree mode, but just to be safe for now
		input.root->reset_weakest_preconditions(); // resetting the weakest preconditions in the tree such that they don't interfere with the other case split


		return false;
	}

	input.weakest_precondition = {}; // probably not necessary to reset here, since we won't use it for subtree mode, but just to be safe for now
	input.root->reset_weakest_preconditions(); // resetting the weakest preconditions in the tree

	if (!input.stop_log){
		std::cout << "\tSplitting on: " << split << std::endl;
	}
	
	bool result = true;

	for (const z3::Bool& condition : {split, split.invert()}) {
		// reset reason and strategy
		// ? should be the same point of reset
		if (input.root->is_branch()) {
			input.root->branch().reset_reason();
		} else {
			assert(input.root->is_condition_node());
			input.root->condition_node().reset_reason();
		}
		if (input.reset_point->is_branch()) {
			input.reset_point->branch().reset_strategy();
		} else if (input.reset_point->is_condition_node()) {
			input.reset_point->condition_node().reset_strategy();
		}

		solver.push();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);


		bool attempt = property_rec_nohistory(solver, options, input, property, new_current_case, player_nr, satisfied_in_case, subtree_results_pr);

		solver.pop();

		if (!attempt){
			result = false;
		}
	}

	input.weakest_precondition = {}; // reseting for next history/property
	input.root->reset_weakest_preconditions(); // resetting the weakest preconditions in the tree
	return result;
}


// function for non-subtree mode, managing the overall process of checking a property, generating preconditions, strategies and counterexamples
void property(const Options &options, const Input &input, PropertyType property, size_t history) {
	/* determine if the input has some property for the current honest history */
	Solver solver;
	solver.assert_(input.initial_constraint);
	std::string prop_name;
	bool prop_holds;

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
	if(history < input.honest.size()) {
		std::cout << "Is history " << input.honest[history] << " " << prop_name << "?" << std::endl;
	} else {
		if(property == PropertyType::Practicality) {
			std::cout << "Computing practical histories." << std::endl;
		} else if (property == PropertyType::CollusionResilience) {
			// see comment in analyze properties
			// if history >= input.honest.size() then we are running subtree in default mode
			// and are considering an honest utility, not an honest history
			std::cout << "Is the subtree " << prop_name << " for honest utility " << input.honest_utilities[history - input.honest.size()].element << "?" << std::endl;
		} else {
			std::cout << "Is the subtree " << prop_name << "?" << std::endl;
		}
	}

	assert(solver.solve() == z3::Result::SAT);

	if (property == PropertyType::Practicality) {
		input.reset_practical_utilities();
		std::vector<PracticalitySubtreeResult> satisfied_in_case = {};
		if (property_rec(solver, options, input, property, std::vector<z3::Bool>(), history, satisfied_in_case)) {
			if(history < input.honest.size()) {
				std::cout << "YES, it is " << prop_name << "." << std::endl;
			} else {
				for (UtilityTuple utility : input.root->get_utilities()) {
					if (solver.solve({!utility.condition}) == z3::Result::UNSAT) {
						std::cout << "History " <<  input.root->strat2hist(utility.strategy) << " is practical." << std::endl;
					} else {
						std::cout << "History " <<  input.root->strat2hist(utility.strategy) << " is practical if " <<  utility.condition.simplify() << " holds." << std::endl;
					}
				}
			}
			prop_holds = true;
		} else { 
			std::cout << "NO, it is not " << prop_name << "." << std::endl;
			prop_holds = false;
		}
	} else {
		size_t number_groups = property == PropertyType::CollusionResilience ? pow(2,input.players.size())-1 : input.players.size();
		input.init_solved_for_group(number_groups);

		std::vector<PracticalitySubtreeResult> satisfied_in_case = {};
		if (property_rec(solver, options, input, property, std::vector<z3::Bool>(), history, satisfied_in_case)) {
			std::cout << "YES, it is " << prop_name << "." << std::endl;
			prop_holds = true;
		} else { 
			std::cout << "NO, it is not " << prop_name << "." << std::endl;
			prop_holds = false;
		}
	}
	
	// generate preconditions
	if (options.preconditions && !prop_holds) {
				std::cout << std::endl;
				std::vector<z3::Bool> disjuncts;
				std::vector<std::vector<z3::Bool>> simplified = input.precondition_simplify(); // disj of conjunctions

				for (const auto &sat_case: simplified) {
					z3::Bool conj;
					if (sat_case.size() == 0) {
						conj = z3::Bool(true); 
					} else {
						conj = conjunction(sat_case);
					}
					disjuncts.push_back(conj);
				}
				z3::Bool raw_prec;
				if (disjuncts.size() == 0) {
					raw_prec = z3::Bool(false);
				} else {
					raw_prec = disjunction(disjuncts);
				}
				z3::Bool simpl_prec = raw_prec.simplify();
				std::cout << "Weakest Precondition: " << std::endl << "\t" << simpl_prec << std::endl;
	}
	
	// generate strategies
	if (options.strategies && prop_holds){
		// for each case a strategy
		bool is_wi = (property == PropertyType::WeakerImmunity) || (property == PropertyType::WeakImmunity);
		bool is_pr = (property == PropertyType::Practicality);
		input.print_strategies(options, is_wi, is_pr);
	}

	if (options.counterexamples && !prop_holds){
		bool is_wi = (property == PropertyType::WeakerImmunity) || (property == PropertyType::WeakImmunity);
		bool is_cr = (property == PropertyType::CollusionResilience);
		input.print_counterexamples(options, is_wi, is_cr);
	}
	
	//outated
	// if(options.counterexamples && prop_holds && history == input.honest.size() && property == PropertyType::Practicality) {
	// 	input.print_counterexamples(options, false, false);
	// }
}

// function for subtree mode and honest_history, managing overall process and subtree results
void property_subtree(const Options &options, const Input &input, PropertyType property, size_t history, Subtree &subtree) {
	
	/* determine if the input has some property for the current honest history */
	Solver solver;
	solver.assert_(input.initial_constraint);
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
	std::cout << "Is history " << input.honest[history] << " " << prop_name << "?" << std::endl;

	assert(solver.solve() == z3::Result::SAT);

	if (property == PropertyType::Practicality) {
		input.reset_practical_utilities();

		std::vector<PracticalitySubtreeResult> subtree_results_pr = {};

		bool pr_result = property_rec(solver, options, input, property, std::vector<z3::Bool>(), history, subtree_results_pr);

		if (pr_result) {
			std::vector<std::vector<Utility>> honest_utilities;
			if (input.root->is_branch()) {
				assert(input.root->branch().practical_utilities.size() > 0);
				for (auto elem: input.root->branch().practical_utilities) {
					honest_utilities.push_back(elem.leaf);
				}
			} else if (input.root->is_condition_node()){
				assert(input.root->condition_node().practical_utilities.size() > 0);
				for (auto elem: input.root->condition_node().practical_utilities) {
					honest_utilities.push_back(elem.leaf);
				}
			}
			std::cout << "YES, it is " << prop_name << ", the honest practical utilities are "<<  honest_utilities << "." << std::endl;
		} else {
			// if (input.root->is_branch()) {
			//		assert( input.root->branch().practical_utilities.size() == 0); }
			// else if (input.root->is_condition_node()){
			//		assert( input.root->condition_node().practical_utilities.size() == 0); }
			// removed this assertion bacause it was failing
			// practical utilites is always at least once - we always set it
			// even though when it is not correct because we needed this for an 
			// additional feature (it was either the counterexamples, or strategies or all cases)
			
			std::cout << "NO, it is not " << prop_name << ", hence for at least one condition there is no honest practical utility." << std::endl;
		}

		subtree.practicality.insert(subtree.practicality.end(), subtree_results_pr.begin(), subtree_results_pr.end());

	} else { 
		size_t number_groups = property == PropertyType::CollusionResilience ? pow(2,input.players.size())-2 : input.players.size();

		std::string output_text = property == PropertyType::CollusionResilience ? " against group " : " for player ";

		std::vector<SubtreeResult> subtree_results;

		for (unsigned i = 0; i < number_groups; i++){
			input.reset_reset_point();
			if (input.root->is_branch()) {
				input.root->branch().reset_reason();
			} else {
				assert(input.root->is_condition_node());
				input.root->condition_node().reset_reason();
			}
			
			std::vector<std::string> players;

            if(property == PropertyType::CollusionResilience) {
                players = index2player(input, property, i+1);
            } else if (property == PropertyType::WeakImmunity || property == PropertyType::WeakerImmunity) {
                players = { input.players[i] };
            }

			SubtreeResult subtree_result_player;
			subtree_result_player.player_group = players;
			subtree_result_player.satisfied_in_case = {};

			if (property_rec_subtree(solver, options, input, property, std::vector<z3::Bool>(), history, i+1, subtree_result_player.satisfied_in_case)){
				std::cout << "YES, it is " << prop_name << output_text << players << "."  << std::endl;
			} else { 
				std::cout << "NO, it is not " << prop_name << output_text << players << "." << std::endl;
			}

			// Sophie claims the below cannot happen so she commented it out, if the assertion fails, we can uncomment and investigate
			
			// check whether we already have a SubtreeResult for this player
			// if yes: append sat cases
			// if not: pushback
			// bool found = false;
			// for(auto &subtree_result : subtree_results) {
			// 	if(subtree_result.player_group.size() == subtree_result_player.player_group.size()) {
			// 		if(std::equal(subtree_result.player_group.begin(), subtree_result.player_group.end(),subtree_result_player.player_group.begin())) {
			// 			found = true;
			// 			subtree_result.satisfied_in_case.insert(subtree_result.satisfied_in_case.end(), subtree_result_player.satisfied_in_case.begin(), subtree_result_player.satisfied_in_case.end());
			// 			break;
			// 		}
			// 	}
			// }
			// if(!found) {
			// 	subtree_results.push_back(subtree_result_player);
			// }
			subtree_results.push_back(subtree_result_player);
			assert(subtree_results.size() == i+1);
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

// function for subtree mode and honest utility (CR only), managing overall process and subtree results
void property_subtree_utility(const Options &options, const Input &input, PropertyType property, HonestUtilityTuple honest_utility, Subtree &subtree) {
	/* determine if the input has some property for the current honest history */

	assert(property == PropertyType::CollusionResilience);

	Solver solver;
	solver.assert_(input.initial_constraint);

	solver.assert_(input.collusion_resilience_constraint);

	std::vector<CondHonestUtility> honest_utility_vec = get_conditional_honest_utilities(honest_utility.element); // CONTINUE HERE

	std::cout << std::endl;
	std::cout << std::endl;
	std::cout << "Is conditional utility " << honest_utility_vec << " collusion resilient?" << std::endl;

	assert(solver.solve() == z3::Result::SAT);

	size_t number_groups = pow(2,input.players.size())-2;
	std::vector<SubtreeResult> subtree_results;

	for (unsigned i = 0; i < number_groups; i++){
		input.reset_reset_point();
		if (input.root->is_branch()) {
			input.root->branch().reset_reason();
		} else if (input.root->is_condition_node()){
			input.root->condition_node().reset_reason();
		}
		std::vector<std::string> players = index2player(input, property, i+1);

		SubtreeResult subtree_result_player;
		subtree_result_player.player_group = players;
		subtree_result_player.satisfied_in_case = {};

		std::bitset<Input::MAX_PLAYERS> group = i+1;
		std::vector<CondHonestTotalUtility> all_honest_total;

		for (const auto& cond_utility : honest_utility_vec) {

			Utility group_total{z3::Real::ZERO, z3::Real::ZERO};
			
			// compute the honest total for the current group
			for (size_t player = 0; player < input.players.size(); player++) {
				if (group[player]) {
					group_total = group_total + cond_utility.utility_tuple[player];
				}
			}
			CondHonestTotalUtility cond_total;
			cond_total.condition = cond_utility.condition;
			cond_total.utility = group_total;
			all_honest_total.push_back(cond_total);
		}

		if (property_rec_utility(solver, options, input, property, std::vector<z3::Bool>(), all_honest_total, i+1, subtree_result_player.satisfied_in_case)){
			std::cout << "YES, it is collusion resilient against group " <<  players << "."  << std::endl;
		} else { 
			std::cout << "NO, it is not  collusion resilient against group " << players << "." << std::endl;
		}

		// Sophie claims the below cannot happen so she commented it out, if the assertion fails, we can uncomment and investigate

		// check whether we already have a SubtreeResult for this player
		// if yes: append sat cases
		// if not: pushback
		// bool found = false;
		// for(auto &subtree_result : subtree_results) {
		// 	if(subtree_result.player_group.size() == subtree_result_player.player_group.size()) {
		// 		if(std::equal(subtree_result.player_group.begin(), subtree_result.player_group.end(),subtree_result_player.player_group.begin())) {
		// 			found = true;
		// 			subtree_result.satisfied_in_case.insert(subtree_result.satisfied_in_case.end(), subtree_result_player.satisfied_in_case.begin(), subtree_result_player.satisfied_in_case.end());
		// 			break;
		// 		}
		// 	}
		// }
		// if(!found) {
		// 	subtree_results.push_back(subtree_result_player);
		// }

		subtree_results.push_back(subtree_result_player);
		assert(subtree_results.size() == i+1);

	}

	subtree.collusion_resilience.insert(subtree.collusion_resilience.end(), subtree_results.begin(), subtree_results.end());
	
	return;
}

// function for subtree mode and no honest history (w(er)i and practicality), managing overall process and subtree results
void property_subtree_nohistory(const Options &options, const Input &input, PropertyType property, Subtree &subtree) {
	

	Solver solver;
	solver.assert_(input.initial_constraint);
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
	

	assert(solver.solve() == z3::Result::SAT);


	if (property == PropertyType::Practicality){
		input.reset_practical_utilities();

		std::vector<std::vector<z3::Bool>> satisfied_in_case;
		std::vector<PracticalitySubtreeResult> subtree_results_pr = {};

		std::cout << "Computing the subtree's practical histories." << std::endl;
		bool pr_result = property_rec_nohistory(solver, options, input, property, std::vector<z3::Bool>(), 0, satisfied_in_case, subtree_results_pr);

		assert(pr_result);

		const auto& practical_utilities = input.root->is_branch() ? input.root->branch().practical_utilities : input.root->condition_node().practical_utilities;
		assert(practical_utilities.size()>0);
		// ATTENTION THINK ABOUT HOW LATER (IN SUPERTREE) CASE SPLITS MAY IMPACT THE RESULT
		// we need to print the corresponding utilities for each case
		// kind of "all cases" for practicality_subtree
		// since in property_rec_nohistory we are not along honest, we consider all cases implicitely
		// it suffices to have a new data structure where we store <case, utulities> information and print them below
		//std::cout << "print utilities" << std::endl;

		for(auto &utilityCase : subtree_results_pr) {
			std::cout << "Case: " << utilityCase._case << std::endl;
			for(auto utility : utilityCase.utilities) {
				if (solver.solve({!utility.condition}) == z3::Result::UNSAT) {
					std::cout << "\t History " <<  utility.history_vector << " is practical." << std::endl;
				} else {
					std::cout << "\t History " <<  utility.history_vector << " is practical if " <<  utility.condition.simplify() << " holds." << std::endl;
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
			if (input.root->is_branch()) {
				input.root->branch().reset_reason();
			} else {
				assert(input.root->is_condition_node());
				input.root->condition_node().reset_reason();
			}

			size_t value = property == PropertyType::CollusionResilience? i+1 : i;
			std::vector<std::string> players = index2player(input, property, value);

			SubtreeResult subtree_result_player;
			subtree_result_player.player_group = players;
			subtree_result_player.satisfied_in_case = {};

			std::vector<PracticalitySubtreeResult> subtree_results_pr = {};

			// i+1 in index2player while i in property_rec_nohistory is on purpose
			if (property_rec_nohistory(solver, options, input, property, std::vector<z3::Bool>(), i, subtree_result_player.satisfied_in_case, subtree_results_pr)){
				std::cout << "YES, it is " << prop_name << " for player " <<  players << "."  << std::endl;
			} else { 
				std::cout << "NO, it is not " << prop_name << " for player " << players << "." << std::endl;
			}

			// Sophie claims the below cannot happen so she commented it out, if the assertion fails, we can uncomment and investigate

			// check whether we already have a SubtreeResult for this player
			// if yes: append sat cases
			// if not: pushback
			// bool found = false;
			// for(auto &subtree_result : subtree_results) {
			// 	if(subtree_result.player_group.size() == subtree_result_player.player_group.size()) {
			// 		if(std::equal(subtree_result.player_group.begin(), subtree_result.player_group.end(),subtree_result_player.player_group.begin())) {
			// 			found = true;
			// 			subtree_result.satisfied_in_case.insert(subtree_result.satisfied_in_case.end(), subtree_result_player.satisfied_in_case.begin(), subtree_result_player.satisfied_in_case.end());
			// 			break;
			// 		}
			// 	}
			// }
			// if(!found) {
			// 	subtree_results.push_back(subtree_result_player);
			// }
			subtree_results.push_back(subtree_result_player);
			assert(subtree_results.size() == i+1);
		}

		if(property == PropertyType::WeakImmunity) {
			subtree.weak_immunity.insert(subtree.weak_immunity.end(), subtree_results.begin(), subtree_results.end());
		} else if (property == PropertyType::WeakerImmunity) {
			subtree.weaker_immunity.insert(subtree.weaker_immunity.end(), subtree_results.begin(), subtree_results.end());
		}


	}
	
	return;
}



// top-level function: only called if not in subtree mode
void analyse_properties(const Options &options, const Input &input) {

	if(input.honest_utilities.size() != 0) { // running a subtree in default mode is fine
		// it enables the user to get counterexamples, strategies and preconditions
		std::cout << "INFO: This file is a subtree, but CheckMate is running in default mode." << std::endl;
	}

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
		std::cout << "Checking history " << input.honest[history] << std::endl; 

		if (input.root->is_branch()) {
			input.root->branch().reset_honest();
			input.root->branch().mark_honest(input.honest[history]);
		} else {
			assert(input.root->is_condition_node());
			input.root->condition_node().reset_honest();
			input.root->condition_node().mark_honest(input.honest[history]);
		}

		if(options.strategies) {
			input.root->reset_violation_cr();
		}

		std::vector<bool> property_chosen = {options.weak_immunity, options.weaker_immunity, options.collusion_resilience, options.practicality};
		std::vector<PropertyType> property_types = {PropertyType::WeakImmunity, PropertyType::WeakerImmunity, PropertyType::CollusionResilience, PropertyType::Practicality};

		assert(property_chosen.size() == property_types.size());

		for (size_t i=0; i<property_chosen.size(); i++) {
			if(property_chosen[i]) {
				
				if (input.root->is_branch()) {
					input.root->branch().reset_counterexample_choices();
					input.root->branch().reset_reason();
					input.root->branch().reset_strategy();
					input.root->branch().reset_problematic_group(i==2);
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().reset_counterexample_choices();
					input.root->condition_node().reset_reason();
					input.root->condition_node().reset_strategy();
					input.root->condition_node().reset_problematic_group(i==2);
				}
				input.reset_counterexamples();
				input.reset_logging();
				input.reset_sat_cases();
				input.reset_strategies(); 
				input.reset_reset_point();
				property(options, input, property_types[i], history);
			}
		}

		if(options.count_nodes) {
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Number of checked nodes for history: " << input.honest[history] << std::endl;
			print_global_counters(true, true, true, true);
		}

		if(options.count_calls) {
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Number of SMT calls for history: " << input.honest[history] << std::endl;
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

		if (input.root->is_branch()) {
			input.root->branch().reset_honest();
		} else {
			assert(input.root->is_condition_node());
			input.root->condition_node().reset_honest();
		}

		std::vector<bool> property_chosen = {options.weak_immunity, options.weaker_immunity, options.practicality};
		std::vector<PropertyType> property_types = {PropertyType::WeakImmunity, PropertyType::WeakerImmunity, PropertyType::Practicality};

		assert(property_chosen.size() == property_types.size());

		if (std::any_of(property_chosen.begin(), property_chosen.end(), [](bool chosen){ return chosen; })) {
   			// at least one is true
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Checking no honest history " << std::endl; 
			

			for (size_t i=0; i<property_chosen.size(); i++) {
				if(property_chosen[i]) {
					input.reset_counterexamples();
					if (input.root->is_branch()) {
						input.root->branch().reset_counterexample_choices();
					} else {
						assert(input.root->is_condition_node());
						input.root->condition_node().reset_counterexample_choices();
					}
					input.reset_logging();
					input.reset_sat_cases();
					if (input.root->is_branch()) {
						input.root->branch().reset_reason();
						input.root->branch().reset_strategy();
					} else {
						assert(input.root->is_condition_node());
						input.root->condition_node().reset_reason();
						input.root->condition_node().reset_strategy();
					}
					input.reset_strategies(); 
					if (input.root->is_branch()) {
						input.root->branch().reset_problematic_group(false);
					} else {
						assert(input.root->is_condition_node());
						input.root->condition_node().reset_problematic_group(false);
					}
					input.reset_reset_point();
					property(options, input, property_types[i], input.honest.size());
				}
			}

			if(options.count_nodes) {
				std::cout << std::endl;
				std::cout << std::endl;
				std::cout << "Number of checked nodes for no honest history: " << std::endl;
				print_global_counters(true, true, false, true);
			}

			if(options.count_calls) {
				std::cout << std::endl;
				std::cout << std::endl;
				std::cout << "Number of SMT calls for no honest history: " << std::endl;
				print_calls_counters(true, true, false, true);
			}
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
				std::cout << "Checking honest utility " << input.honest_utilities[honest_utility].element << std::endl; 

				if(options.strategies) {
					if (input.root->is_branch()) {
						input.root->branch().reset_violation_cr();
					} else {
						assert(input.root->is_condition_node());
						input.root->condition_node().reset_violation_cr();
					}
				}

				input.reset_counterexamples();
				if (input.root->is_branch()) {
					input.root->branch().reset_counterexample_choices();
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().reset_counterexample_choices();
				}
				input.reset_logging();
				input.reset_sat_cases();
				if (input.root->is_branch()) {
					input.root->branch().reset_reason();
					input.root->branch().reset_strategy();
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().reset_reason();
					input.root->condition_node().reset_strategy();
				}
				input.reset_strategies(); 
				if (input.root->is_branch()) {
					input.root->branch().reset_problematic_group(true);
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().reset_problematic_group(true);
				}
				input.reset_reset_point();
				// input.honest.size() + honest_utility means we are running a subree in default mode
				// and we consider collusion resilience for the honest utility
				property(options, input, PropertyType::CollusionResilience, input.honest.size() + honest_utility);

				if(options.count_nodes) {
					std::cout << std::endl;
					std::cout << std::endl;
					std::cout << "Number of checked nodes for honest utility: " << input.honest_utilities[honest_utility].element << std::endl;
					print_global_counters(false, false, true, false);
				}

				if(options.count_calls) {
					std::cout << std::endl;
					std::cout << std::endl;
					std::cout << "Number of checked nodes for honest utility: " << input.honest_utilities[honest_utility].element << std::endl;
					print_calls_counters(false, false, true, false);
				}

			}

		}

	}
}

// top-level function: only called in subtree mode
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
		std::cout << "Checking history " << input.honest[history] << std::endl; 

		if (input.root->is_branch()) {
			input.root->branch().reset_honest();
			input.root->branch().mark_honest(input.honest[history]);
			input.root->branch().reset_practical_utilities();
		} else {
			assert(input.root->is_condition_node());
			input.root->condition_node().reset_honest();
			input.root->condition_node().mark_honest(input.honest[history]);
			input.root->condition_node().reset_practical_utilities();
		}

		if(options.strategies) {
			input.root->reset_violation_cr();
		}

		std::vector<bool> property_chosen = {options.weak_immunity, options.weaker_immunity, options.collusion_resilience, options.practicality};
		std::vector<PropertyType> property_types = {PropertyType::WeakImmunity, PropertyType::WeakerImmunity, PropertyType::CollusionResilience, PropertyType::Practicality};

		assert(property_chosen.size() == property_types.size());

		HonestUtilityElement honest_utility_element = {};
		Subtree st({}, {}, {}, {}, honest_utility_element);
		Subtree &subtree = st;
		subtree.honest_utility = honest_history2utility(input.root.get(), input.honest[history]);
		

		for (size_t i=0; i<property_chosen.size(); i++) {
			if(property_chosen[i]) {
				input.reset_counterexamples();
				if (input.root->is_branch()) {
					input.root->branch().reset_counterexample_choices();
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().reset_counterexample_choices();
				}
				input.reset_logging();
				input.reset_sat_cases();
				if (input.root->is_branch()) {
					input.root->branch().reset_reason();
					input.root->branch().reset_strategy();
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().reset_reason();
					input.root->condition_node().reset_strategy();
				}
				input.reset_strategies(); 
				if (input.root->is_branch()) {
					input.root->branch().reset_problematic_group(i==2);
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().reset_problematic_group(i==2);
				}
				input.reset_reset_point();
				property_subtree(options, input, property_types[i], history, subtree);
			}
		}

		if(options.count_nodes) {
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Number of checked nodes for history: " << input.honest[history] << std::endl;
			print_global_counters(true, true, true, true);
		}

		if(options.count_calls) {
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Number of checked nodes for history: " << input.honest[history] << std::endl;
			print_calls_counters(true, true, true, true);
		}

		std::string file_name = options.input_path + std::string(".out");
        print_subtree_result_to_file(input, file_name, subtree);
		
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

		// possibly comment out
		if(options.strategies) {
			input.root->reset_violation_cr();
		}
		

		if (input.root->is_branch()) {
			input.root->branch().reset_honest();
			input.root->branch().reset_practical_utilities();
		} else {
			assert(input.root->is_condition_node());
			input.root->condition_node().reset_honest();
			input.root->condition_node().reset_practical_utilities();
		}

		HonestUtilityElement honest_utility_element = {};
		Subtree st({}, {}, {}, {}, honest_utility_element);
		Subtree &subtree = st;

		// cr handled below
		std::vector<bool> property_chosen = {options.weak_immunity, options.weaker_immunity, options.practicality};
		std::vector<PropertyType> property_types = {PropertyType::WeakImmunity, PropertyType::WeakerImmunity, PropertyType::Practicality};

		assert(property_chosen.size() == property_types.size());

		if (std::any_of(property_chosen.begin(), property_chosen.end(), [](bool chosen){ return chosen; })) {
   			// at least one is true
			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Checking no honest history " << std::endl;

			for (size_t i=0; i<property_chosen.size(); i++) {
				if(property_chosen[i]) {
					input.reset_counterexamples();
					if (input.root->is_branch()) {
						input.root->branch().reset_counterexample_choices();
					} else {
						assert(input.root->is_condition_node());
						input.root->condition_node().reset_counterexample_choices();
					}
					input.reset_logging();
					input.reset_sat_cases();
					if (input.root->is_branch()) {
						input.root->branch().reset_reason();
						input.root->branch().reset_strategy();
					} else {
						assert(input.root->is_condition_node());
						input.root->condition_node().reset_reason();
						input.root->condition_node().reset_strategy();
					}
					input.reset_strategies(); 
					input.reset_reset_point();
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

		}
		
		if (options.collusion_resilience){
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
				std::cout << "Checking utility " << input.honest_utilities[utility].element << std::endl; 

				if (input.root->is_branch()) {
					input.root->branch().reset_honest();
				} else {
					assert(input.root->is_condition_node());
					input.root->condition_node().reset_honest();
				}

				// possible comment out?
				if(options.strategies) {
					input.root->reset_violation_cr();
				}

				subtree.collusion_resilience = {};

				if(options.collusion_resilience) {
					input.reset_counterexamples();
					if (input.root->is_branch()) {
						input.root->branch().reset_counterexample_choices();
					} else {
						assert(input.root->is_condition_node());
						input.root->condition_node().reset_counterexample_choices();
					}
					input.reset_logging();
					input.reset_sat_cases();
					if (input.root->is_branch()) {
						input.root->branch().reset_reason();
						input.root->branch().reset_strategy();
					} else {
						assert(input.root->is_condition_node());
						input.root->condition_node().reset_reason();
						input.root->condition_node().reset_strategy();
					}
					input.reset_strategies(); 
					if (input.root->is_branch()) {
						input.root->branch().reset_problematic_group(true);
					} else {
						assert(input.root->is_condition_node());
						input.root->condition_node().reset_problematic_group(true);
					}
					input.reset_reset_point();
					property_subtree_utility(options, input, PropertyType::CollusionResilience, input.honest_utilities[utility].element, subtree);
				}		

				if(options.count_nodes) {
					std::cout << std::endl;
					std::cout << std::endl;
					std::cout << "Number of checked nodes for honest utility: " << input.honest_utilities[utility].element << std::endl;
					print_global_counters(false, false, true, false);
				}

				if(options.count_calls) {
					std::cout << std::endl;
					std::cout << std::endl;
					std::cout << "Number of checked nodes for honest utility: " << input.honest_utilities[utility].element << std::endl;
					print_calls_counters(false, false, true, false);
				}

				// create one file for this utility
				// set honest utility to this utility
				// set wi, weri, cr, pr subtree results
				// wi, weri, pr always the same, only cr changes
				subtree.honest_utility = input.honest_utilities[utility].element;

				std::string file_name = options.input_path + std::string(".out");
				print_subtree_result_to_file(input, file_name, subtree);
				
			}
		} else {
			// if we are not checking collusion resilience, we only need to create one file with the results for w(er)i and pr
			subtree.honest_utility = input.honest_utilities[0].element; // we can take any honest utility since they are all the same for w(er)i and pr

			std::string file_name = options.input_path + std::string(".out");
			print_subtree_result_to_file(input, file_name, subtree);
		}
		
	}

}
