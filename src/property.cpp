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

// third-party library for parsing JSON
using json = nlohmann::json;

json parse_sat_case(std::vector<z3::Bool> sat_case) {			
    json arr_case = json::array();
    if(sat_case.size() == 0) {
        arr_case.push_back("true");
    } else {
        for(auto &case_entry: sat_case) {
            std::string case_to_print = pretty_print(case_entry);
            arr_case.push_back(case_to_print);
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
        // parse utilities
        json utilities = json::array();
        for(auto &utility_list : subtree_result.utilities) {
            // parse utility
            json utility = parse_utility(input, utility_list);
            utilities.push_back(utility);
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
        json arr_honest_utility = parse_utility(input, subtree.honest_utility);

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
	//} 	
}

const Node& get_honest_leaf(Node *node, const std::vector<std::string> &history, unsigned index) {
	switch(node->type()) {
    case NodeType::LEAF:
		return node->leaf();
    case NodeType::SUBTREE:
        return node->subtree();
	case NodeType::BRANCH:
		break;
    // no need for default
    }

	unsigned next_index = index + 1;
	return get_honest_leaf(node->branch().get_choice(history[index]).node.get(), history, next_index);
}

bool utility_tuples_eq(UtilityTuple tuple1, UtilityTuple tuple2) {
	if(tuple1.size() != tuple2.size()) {
		return false;
	} else {
		bool all_same = true;
		for (size_t i = 0; i < tuple1.size(); i++) {
			if (!tuple1[i].is(tuple2[i])) {
				all_same = false;
			}
		}
		return all_same;
	}
	return false;

}

std::vector<std::string> index2player(const Input &input, unsigned index) {
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


	if (node->is_leaf()) {
		const auto &leaf = node->leaf();

		if ((player < leaf.problematic_group) && consider_prob_groups){
			return true;
		}
		// known utility for us
		auto utility = leaf.utilities[player];

		z3::Bool condition = weaker ? utility.real >= z3::Real::ZERO : utility >= Utility {z3::Real::ZERO, z3::Real::ZERO};

		if (solver.solve({!condition}) == z3::Result::UNSAT) {
			if (consider_prob_groups) {
				leaf.problematic_group = player + 1;
			}
			return true;
		}
		
		if (solver.solve({condition}) == z3::Result::UNSAT) {
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

			//std::cout << "Subtree result cases: " << subtree_result.satisfied_in_case << std::endl;

			assert(subtree_result.player_group.size() == 1);
			if (subtree_result.player_group[0] == player_name) {

				// (init_cons && wi_cons && curent_case) => disj_of_cases VALID
				// ! (init_cons && wi_cons && current_case) || disj_of_cases VALID
				// (init_cons && wi_cons && current_case) && !disj_of_cases UNSAT
				// init_cons && wi_cons && current_case    && !disj_of_cased UNSAT

				std::vector<z3::Bool> cases_as_conjunctions = {};
				for (auto _case: subtree_result.satisfied_in_case) {
					cases_as_conjunctions.push_back(z3::conjunction(_case));
				}

				z3::Bool disj_of_cases = z3::disjunction(cases_as_conjunctions);
				z3::Result z3_result_implied = solver.solve({!disj_of_cases});

				if (z3_result_implied == z3::Result::UNSAT) {
					return true;
				} else {

					// compute if current_case and case are disjoint:
					// is it sat that init && wi && case && current_case?
					// if no, then disjoint

					z3::Result z3_result_disjoint = solver.solve({disj_of_cases});
					
					if (z3_result_disjoint == z3::Result::SAT) {
						// set reason
						subtree.reason = disj_of_cases;
					}
					return false;
				}
			}
		}
	}

	

	const auto &branch = node->branch();

	if ((player < branch.problematic_group) && consider_prob_groups){
		return true;
	}


	// else we deal with a branch
	if (player == branch.player) { 	

		// player behaves honestly
		if (branch.honest) {
			// if we are along the honest history, we want to take an honest strategy
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

			branch.reason = subtree->reason;
			input.set_reset_point(branch);
			return false;
		}
		// otherwise we can take any strategy we please as long as it's weak immune
		z3::Bool reason;
		unsigned reset_index;
		unsigned i = 0;
		for (const Choice &choice: branch.choices) {
			if (weak_immunity_rec(input, solver, options, choice.node.get(), player, weaker, consider_prob_groups)) {
				// set chosen action, needed for printing strategy
				branch.strategy = choice.action;
				if (consider_prob_groups) {
						branch.problematic_group = player + 1;
					}
				return true;
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
		return false;

	} else {
		// if we are not the honest player, we could do anything,
		// so all branches should be weak immune for the player
		bool result = true;
		z3::Bool reason;
		unsigned reset_index;
		unsigned i = 0;
		for (const Choice &choice: branch.choices) {
			if (!weak_immunity_rec(input, solver, options, choice.node.get(), player, weaker, consider_prob_groups)) {
				if (choice.node->reason.null()){
					if (options.counterexamples) {
						branch.counterexample_choices.push_back(choice.action);
					}
					if (!options.all_counterexamples){
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
		if (result && consider_prob_groups) {
			branch.problematic_group = player + 1;
		}
		return result;
	}

} 

bool collusion_resilience_rec(const Input &input, z3::Solver &solver, const Options &options, Node *node, std::bitset<Input::MAX_PLAYERS> group, Utility honest_total, unsigned players, uint64_t group_nr, bool consider_prob_groups) {
	
	if (node->is_leaf()) {
		const auto &leaf = node->leaf();


		if  ((group_nr < leaf.problematic_group) && consider_prob_groups){
			return true;
		}

		// compute the total utility for the player group...
		Utility group_utility{z3::Real::ZERO, z3::Real::ZERO};
		
		for (size_t player = 0; player < players; player++)
			if (group[player])
				group_utility = group_utility + leaf.utilities[player];

		// ..and compare it to the honest total
		auto condition = honest_total >= group_utility;		
		
		if (solver.solve({!condition}) == z3::Result::UNSAT) {
			if (consider_prob_groups) {
				leaf.problematic_group = group_nr + 1;
			}
			return true;
		}

		if (solver.solve({condition}) == z3::Result::UNSAT) {

			if(options.strategies) {
				node->violates_cr[group_nr - 1] = true;
			}
			
			return false;
		}

		if (consider_prob_groups) {
			leaf.problematic_group = group_nr;
		}
		leaf.reason = get_split_approx(solver, honest_total, group_utility);
		input.set_reset_point(leaf);
		return false;

	} else if (node->is_subtree()){

		const auto &subtree = node->subtree();

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
		std::vector<std::string> player_names = index2player(input, group_nr); 


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
						cases_as_conjunctions.push_back(z3::conjunction(_case));
					}
					z3::Bool disj_of_cases = z3::disjunction(cases_as_conjunctions);
					z3::Result z3_result_implied = solver.solve({!disj_of_cases});

					if (z3_result_implied == z3::Result::UNSAT) {
						return true;
					} else {

						// compute if current_case and case are disjoint:
						// is it sat that init && wi && case && current_case?
						// if no, then disjoint

						z3::Result z3_result_disjoint = solver.solve({disj_of_cases});
						
						if (z3_result_disjoint == z3::Result::SAT) {
							// set reason
							subtree.reason = disj_of_cases;
						}
						return false;
					}
				}
			}		
		}
	} 

	const auto &branch = node->branch();

	if  ((group_nr < branch.problematic_group) && consider_prob_groups ){
		return true;
	}
	
	// else we deal with a branch
	if (!group[branch.player]) { 

		// player behaves honestly
		if (branch.honest) {
			// if we are along the honest history, we want to take an honest strategy
			auto &honest_choice = branch.get_honest_child();
			auto *subtree = honest_choice.node.get();

			// set chosen action, needed for printing strategy
			//branch.strategy = honest_choice.action;

			// the honest choice must be collusion resilient
			if (collusion_resilience_rec(input, solver, options, subtree, group, honest_total, players, group_nr, consider_prob_groups)) {
				if (consider_prob_groups) {
					branch.problematic_group = group_nr + 1;
				}
				return true;
			} 
			
			branch.reason = subtree->reason;
			input.set_reset_point(*subtree);
			return false;
		}
		// otherwise we can take any strategy we please as long as it's collusion resilient
		// if options.strategies is set, we have to consider all branches, otherwise we can stop after the first cr one
		if (options.strategies){
			bool result = false;
			z3::Bool reason;
			unsigned reset_index;
			unsigned i = 0;
			for (const Choice &choice: branch.choices) {
				if (collusion_resilience_rec(input, solver, options, choice.node.get(), group, honest_total, players, group_nr, consider_prob_groups)) {
					// set chosen action, needed for printing strategy
					//branch.strategy = choice.action;
					if (consider_prob_groups){
						branch.problematic_group = group_nr + 1;
					}
					result = true;
				// if not cr and reason is null, then violated
				} else if (choice.node->reason.null()) {

					choice.node->violates_cr[group_nr - 1] = true;
				}
					
				if ((!choice.node->reason.null()) && (reason.null())) {
					reason = choice.node->reason;
					reset_index = i;
				}
				i++;		
			}
			// only set reason if there is one
			if (!reason.null()) {
					branch.reason = reason;
					input.set_reset_point(*branch.choices[reset_index].node);
			}
			return result;
		} else {
			z3::Bool reason;
			unsigned reset_index;
			unsigned i = 0;
			for (const Choice &choice: branch.choices) {
				if (collusion_resilience_rec(input, solver, options, choice.node.get(), group, honest_total, players, group_nr, consider_prob_groups)) {
					// set chosen action, needed for printing strategy
					branch.strategy = choice.action;
					if (consider_prob_groups) {
						branch.problematic_group = group_nr + 1;
					}
					return true;
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
		}
		return false;
	} else {
		// if we are not the honest player, we could do anything,
		// so all branches should be collusion resilient for the player
		bool result = true;
		z3::Bool reason;
		unsigned reset_index;
		unsigned i = 0;
		for (const Choice &choice: branch.choices) {
			if (!collusion_resilience_rec(input, solver, options, choice.node.get(), group, honest_total, players, group_nr, consider_prob_groups)) {
				if (choice.node->reason.null()) {
					if (options.counterexamples) {
						branch.counterexample_choices.push_back(choice.action);
					}
					if (!options.all_counterexamples){
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
		if (result && consider_prob_groups) {
			branch.problematic_group = group_nr + 1;
		}
		return result;
	}
}

bool practicality_rec_old(const Input &input, const Options &options, z3::Solver &solver, Node *node, std::vector<std::string> actions_so_far, bool consider_prob_groups) {

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
			z3::Bool subtree_case = z3::conjunction(subtree_result._case);

			z3::Result overlapping = solver.solve({subtree_case});

			if (overlapping == z3::Result::SAT){
				z3::Result implied = solver.solve({!subtree_case});

				if (implied == z3::Result::SAT){
					subtree.reason = subtree_case;
					return false;
				} else {
					if (subtree_result.utilities.size() == 0) {
						// we have to be along honest at this point, otw we would have had at least one pr utility
						if(options.counterexamples) {
							input.counterexamples.push_back(input.root.get()->compute_pr_cecase(input.players, input.players.size(), actions_so_far, "", {}));
						}
						return false;
					}
					subtree.utilities.insert(subtree.utilities.end(), subtree_result.utilities.begin(), subtree_result.utilities.end());
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
	}

	// else we deal with a branch
 	const auto &branch = node->branch();

	if  (branch.problematic_group == 1 && consider_prob_groups){
		// std::cout << "already solved" << std::endl;
		return true;
	}	

	// get practical strategies and corresponding utilities recursively
	std::vector<UtilityTuplesSet> children;
	std::vector<std::string> children_actions;

	UtilityTuplesSet honest_utilities;
	unsigned int i = 0;
	unsigned honest_index = 0;
	std::string honest_choice;

	bool result = true;

	// tried to optimize but failed
	// z3::Bool reason;
	// bool is_unsat = false;


	// for (const Choice &choice: branch.choices) {
		 
	// 	// this child has no practical strategy (propagate reason for case split, if any) 
	// 	std::vector<std::string> updated_actions;
	// 	updated_actions.insert(updated_actions.begin(), actions_so_far.begin(), actions_so_far.end());
	// 	updated_actions.push_back(choice.action);

	// 	if(!practicality_rec_old(input, options, solver, choice.node.get(), updated_actions, consider_prob_groups)) {
	// 		if (result) {
	// 			// branch.reason = choice.node->reason;
	// 			reason = choice.node->reason;
	// 			//input.set_reset_point(branch);
	// 		}

	// 		result = false;
		
	// 		if (choice.node->reason.null()){
	// 			is_unsat = true;
	// 			if (!options.all_counterexamples){
	// 				return result;
	// 			}
	// 		}

	// 		// had to be moved out of loop 
	// 		// if(!options.all_counterexamples || !branch.reason.null()) {
	// 		// 	return result;
	// 		// }
	// 	}

	// 	// the part below can stay
	// 	if(choice.node->honest) {
	// 		honest_utilities = choice.node->get_utilities();
	// 		honest_choice = choice.action;
	// 		branch.strategy = choice.action; // choose the honest action along the honest history
	// 		honest_index = i;
	// 	} else {
	// 		// make sure we only have 0 practical utilities in case we are computing all counterexamples
	// 		// and we already have a counterexample, and hence result must be false
	// 		if (choice.node->get_utilities().size()==0){
	// 			assert(!result);
	// 			assert(options.all_counterexamples);
	// 			assert(input.counterexamples.size()>0);
	// 		}
	// 		// std::cout << "current child has " << choice.node->get_utilities().size() << " many practical histories" << std::endl;
	// 		// std::cout << actions_so_far << std::endl;
	// 		// std::cout << choice.action << std::endl;
	// 		children.push_back(choice.node->get_utilities());
	// 		children_actions.push_back(choice.action);
	// 	}
	// 	i++;
	// }

	// // we could not find an immediate unsat child, hence we need to case split if result is false;
	// // hence set reason and reset point accordingly
	// // we are in this case if we either need a case split, or  are sat or compute all counterexamples
	// if (!result && !is_unsat) {
	// 	branch.reason = reason;
	// 	assert(!branch.reason.null());
	// 	input.set_reset_point(branch);
	// }
	// if (!result){
	// 	if(!options.all_counterexamples || !branch.reason.null()) {
	// 		return result;
	// 	}
	// }



	// check honest branch first
	for (const Choice &choice: branch.choices) {
		if (choice.node->honest) {
			std::vector<std::string> updated_actions;
			updated_actions.insert(updated_actions.begin(), actions_so_far.begin(), actions_so_far.end());
			updated_actions.push_back(choice.action);
			if(!practicality_rec_old(input, options, solver, choice.node.get(), updated_actions, consider_prob_groups)) {
				if (result) {
					branch.reason = choice.node->reason;
					input.set_reset_point(branch);
				}

				result = false;

				if(!options.all_counterexamples || !branch.reason.null()) {
					return result;
				}
			}

			// if(choice.node->honest) {
				honest_utilities = choice.node->get_utilities();
				honest_choice = choice.action;
				branch.strategy = choice.action; // choose the honest action along the honest history
				honest_index = i;
			//} else {
			// 	// make sure we only have 0 practical utilities in case we are computing all counterexamples
			// 	// and we already have a counterexample, and hence result must be false
			// 	if (choice.node->get_utilities().size()==0){
			// 		assert(!result);
			// 		assert(options.all_counterexamples);
			// 		assert(input.counterexamples.size()>0);
			// 	}
			// 	// std::cout << "current child has " << choice.node->get_utilities().size() << " many practical histories" << std::endl;
			// 	// std::cout << actions_so_far << std::endl;
			// 	// std::cout << choice.action << std::endl;
			// 	children.push_back(choice.node->get_utilities());
			// 	children_actions.push_back(choice.action);
			// }
			break;
		}
		i++;
	}

	for (const Choice &choice: branch.choices) {
		if (!choice.node->honest) {
			//UtilityTuplesSet utilities = practicality_rec_old(input, solver, choice.node.get());

			// this child has no practical strategy (propagate reason for case split, if any) 
			std::vector<std::string> updated_actions;
			updated_actions.insert(updated_actions.begin(), actions_so_far.begin(), actions_so_far.end());
			updated_actions.push_back(choice.action);
			if(!practicality_rec_old(input, options, solver, choice.node.get(), updated_actions, consider_prob_groups)) {
				if (result) {
					branch.reason = choice.node->reason;
					input.set_reset_point(branch);
				}

				result = false;

				if(!options.all_counterexamples || !branch.reason.null()) {
					return result;
				}
			}

			// if(choice.node->honest) {
			// 	honest_utilities = choice.node->get_utilities();
			// 	honest_choice = choice.action;
			// 	branch.strategy = choice.action; // choose the honest action along the honest history
			// 	honest_index = i;
			// } else {
				// make sure we only have 0 practical utilities in case we are computing all counterexamples
				// and we already have a counterexample, and hence result must be false
				if (choice.node->get_utilities().size()==0){
					assert(!result);
					assert(options.all_counterexamples);
					assert(input.counterexamples.size()>0);
				}
				// std::cout << "current child has " << choice.node->get_utilities().size() << " many practical histories" << std::endl;
				// std::cout << actions_so_far << std::endl;
				// std::cout << choice.action << std::endl;
				children.push_back(choice.node->get_utilities());
				children_actions.push_back(choice.action);
			// }
		}
		// i++;
	}




	if (branch.honest) {
		// if we are at an honest node, our strategy must be the honest strategy
		
		assert(honest_utilities.size() == 1);
		// the utility at the leaf of the honest history
		std::vector<std::string> honest_strategy;
		std::vector<Utility> leaf;
		UtilityTuplesSet to_clear_strategy;
		for (const auto& hon_utility: honest_utilities){
		 	honest_strategy.insert(honest_strategy.end(), hon_utility.strategy_vector.begin(), hon_utility.strategy_vector.end());
			UtilityTuple cleared_strategy(hon_utility.leaf);
			to_clear_strategy.insert(cleared_strategy);
		}

		UtilityTuple honest_utility = *to_clear_strategy.begin();
		
		honest_utility.strategy_vector = {};
		honest_utility.strategy_vector.push_back(honest_choice);
		
		// this should be maximal against other players, so...
		Utility maximum = honest_utility[branch.player]; 

		// for all other children
		unsigned int j = 0;
		for (const auto& utilities : children) {
			bool found = false;
			// does there exist a possible utility such that `maximum` is geq than it?				

			for (const auto& utility : utilities) {
				//std::cout << "Strategy vector" << utility.strategy_vector << std::endl;
				auto condition =   maximum < utility[branch.player];
				if (solver.solve({condition}) == z3::Result::SAT) {
					if (solver.solve({!condition}) == z3::Result::SAT) {
						// might be maximal, just couldn't prove it
						if (result){
							branch.reason =  get_split_approx(solver, maximum, utility[branch.player]); 
							input.set_reset_point(branch);
						}
					}
				} 
				else {
					found = true;
					// need to insert strategy after honest at right point in vector
					if (j == honest_index){
						honest_utility.strategy_vector.insert(honest_utility.strategy_vector.end(), honest_strategy.begin(), honest_strategy.end());
					} 
					honest_utility.strategy_vector.insert(honest_utility.strategy_vector.end(), utility.strategy_vector.begin(), utility.strategy_vector.end());
					break;
				}
			}
			if (!found && utilities.size()>0) {
				
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
					// std::cout << "PUSHBACK COUNTEREXAMPLE with strategy: " << std::endl;
					// for (const auto &ut : utilities){
					// 	std::cout << ut.strategy_vector << std::endl;
					// }
					input.counterexamples.push_back(input.root.get()->compute_pr_cecase(input.players, branch.player, actions_so_far, deviating_action, utilities));
				}

				//return false; 
				result = false;

				if(!options.all_counterexamples || !branch.reason.null()) {
					return result; //false
				}
			}
			j++;
		}
		if(j == honest_index) {
			honest_utility.strategy_vector.insert(honest_utility.strategy_vector.end(), honest_strategy.begin(), honest_strategy.end());
		}
		/*if (result != false) {
			branch.practical_utilities = {honest_utility};
		}*/
		branch.practical_utilities = {honest_utility};
		
		// we return the maximal strategy 
		// honest choice is practical for current player
		// return true;

		return result;

	} else {
		// not in the honest history
		// to do: we could do this more efficiently by working out the set of utilities for the player
		// but utilities can't be put in a set easily -> fix this here in the C++ version

		// compute the set of possible utilities by merging the set of children's utilities
		UtilityTuplesSet utility_result;
		//std::vector<unsigned int> index_vector;
		unsigned int k = 0;
		for (const auto& utilities : children) {
			for (const auto& utility : utilities) {
				UtilityTuple to_insert(utility.leaf); 
				to_insert.strategy_vector.push_back(children_actions[k]);
				utility_result.insert(to_insert);
				// index_vector.push_back(k);
			}
			k++;
		}

		//std::cout << "UTIL Res size " << utility_result.size() << std::endl;

		// the set to drop
		UtilityTuplesSet remove;

		// work out whether to drop `candidate`
		unsigned int l = 0;
		for (const auto& candidate : utility_result) {
			// this player's utility
			auto dominatee = candidate[branch.player];
			// check all other children
            // if any child has the property that all its utilities are bigger than `dominatee`
            // it can be dropped
			// unsigned int child_index = 0;
            for (const auto& utilities : children) {
				// skip any where the cadidate is already contained

				// this logic can be factored out in an external function
				bool contained = false;
				for (const auto& utility : utilities) {
					if (utility_tuples_eq(utility, candidate)) {
						contained = true;
						candidate.strategy_vector.insert(candidate.strategy_vector.end(), utility.strategy_vector.begin(), utility.strategy_vector.end());
						break;
					}
				}

				if (contained) {
					continue;
				}

				// *all* utilities have to be bigger
				bool dominated = true;

				for (const auto& utility : utilities) {
					auto dominator = utility[branch.player];
					auto condition = dominator <= dominatee;
					if (solver.solve({condition}) == z3::Result::SAT) {
						if (dominated){
							candidate.strategy_vector.insert(candidate.strategy_vector.end(), utility.strategy_vector.begin(), utility.strategy_vector.end());
						}
						dominated = false;

						if (solver.solve({!condition}) == z3::Result::SAT) {
							branch.reason = get_split_approx(solver, dominatee, dominator); 
							input.set_reset_point(branch);
							return false; 
						}
					}
				}  

				if (dominated) {
					remove.insert(candidate);
					break;
				}
			}
			l++;
		}

		// result is all children's utilities inductively, minus those dropped
		for (const auto& elem : remove) {
			utility_result.erase(elem);
		}

		//std::cout << "UTIL Res size after removal " << utility_result.size() << std::endl;

		// if strategy has not been set, we are not along the honest history
		// go over all children and pick the one that has a utility tuple which is contained in the returned result
		// if (branch.strategy.empty()) {
		// 	for (unsigned i = 0; i < children.size() && branch.strategy.empty(); i++) {
		// 		auto& utilities = children[i];
		// 		for (const auto& utility : utilities) {
		// 			if(result.find(utility) != result.end()) {
		// 				branch.strategy = children_actions[i];
		// 				break;
		// 			}
		// 		}
		// 	}
		// }

		branch.practical_utilities = utility_result;
		// std::cout<< "Utility result set: " << std::endl;
		// for (const auto &elem : utility_result){
		// 	std::cout << "Utility " << elem.leaf << ", Strategy " << elem.strategy_vector << std::endl;
		// }

		assert(utility_result.size()>0);
		return true;

	} 

}


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
			//std::cout << "current player " << player << std::endl;
			
			if (!input.solved_for_group[player]) {
				// problematic groups are only considered when we haven't found a case split point yet
			
				bool weak_immune_for_player = weak_immunity_rec(input, solver, options, input.root.get(), player, property == PropertyType::WeakerImmunity, true);

				if (!weak_immune_for_player) {

					// std::cout << "not CR" << std::endl;
					// if (input.root->reason.null()){
					// 	std::cout << "for sure" << std::endl;
					// } else {
					// 	std::cout << "need case split" << std::endl;
					// }


					if (options.counterexamples && input.root->reason.null()){
						is_unsat = true;
						std::vector<size_t> pl = {player};
						input.compute_cecase(pl, property);
						input.root.get()->reset_counterexample_choices();
					}
					if (!options.all_counterexamples && input.root->reason.null()){
						return false;
					} else if ((!options.all_counterexamples || !is_unsat) && !input.root->reason.null() && reason.null()) {
						reason = input.root->reason;
						current_reset_point = input.reset_point;
						problematic_group_storage = input.root->store_problematic_groups();
						reason_storage = input.root->store_reason();
					}
					result = false;
				}
				// } else {
				// 	std::cout << "is cr" << std::endl;
				// }

				input.root.get()->reset_counterexample_choices();
				input.root->reset_reason();
			}
		}
		if (!options.all_counterexamples) {
			if (!reason.null()){
				input.root->restore_problematic_groups(problematic_group_storage);
				input.root->restore_reason(reason_storage);
				input.reset_point = current_reset_point;
			}
		} else {
			if ((!reason.null()) && !is_unsat){
				input.root->restore_problematic_groups(problematic_group_storage);
				input.root->restore_reason(reason_storage);
				input.reset_point = current_reset_point;
			}
		}
		return result;
	}

	else if (property == PropertyType::CollusionResilience) {
		// lookup the leaf for this history
		std::vector<Utility> utility;
		if(history < input.honest.size()) {
			const Node &honest_leaf = get_honest_leaf(input.root.get(), input.honest[history], 0);
			if (honest_leaf.is_leaf()){
				utility = honest_leaf.leaf().utilities;
			} else {
				// the case where the honest history ends in an subtree
				utility = honest_leaf.subtree().honest_utility;
			}
		} else {
			utility = input.honest_utilities[history - input.honest.size()].leaf;
		}
		

		// sneaky hack follows: all possible subgroups of n players can be implemented by counting through from 1 to (2^n - 2)
		// done this way more for concision than efficiency
		// std::cout << "next_group: " << next_group << std::endl;
		bool result = true;

		z3::Bool reason;
		Node *current_reset_point;
		std::vector<uint64_t> problematic_group_storage;
		std::vector<z3::Bool> reason_storage;
		bool is_unsat = false;
		for (uint64_t binary_counter = 1; binary_counter < -1ull >> (64 - input.players.size()); binary_counter++) {

			//std::cout << "current group " << binary_counter << std::endl;
			if (!input.solved_for_group[binary_counter]){
				if(options.strategies) {
					input.root->add_violation_cr();
				}

				std::bitset<Input::MAX_PLAYERS> group = binary_counter;
				Utility honest_total{z3::Real::ZERO, z3::Real::ZERO};
				// compute the honest total for the current group
				for (size_t player = 0; player < input.players.size(); player++) {
					if (group[player]) {
						Utility player_utility = utility[player];
						honest_total = honest_total + player_utility;
					}
				}
	
				// problematic groups are only considered when we haven't found a case split point yet
				bool collusion_resilient_for_group = collusion_resilience_rec(input, solver, options, input.root.get(), group, honest_total, input.players.size(), binary_counter, true);
				if (!collusion_resilient_for_group) {

					/*std::cout << "not CR" << std::endl;
					if (input.root->reason.null()){
						std::cout << "for sure" << std::endl;
					} else {
						std::cout << "need case split" << std::endl;
					}*/


					if (options.counterexamples && input.root->reason.null()){
						is_unsat = true;
						std::vector<size_t> pl;
						for (size_t player = 0; player < input.players.size(); player++) {
							if (group[player]) {
								pl.push_back(player);
							}
						}
						input.compute_cecase(pl, property);
						input.root.get()->reset_counterexample_choices();
					}
					
					if (!options.all_counterexamples && input.root->reason.null()){
						return false;
					} else if ((!options.all_counterexamples || !is_unsat ) && !input.root->reason.null() && reason.null()) {
						reason = input.root->reason;
						current_reset_point = input.reset_point;
						problematic_group_storage = input.root->store_problematic_groups();
						reason_storage = input.root->store_reason();	
					}
					result = false;
				} else {
					//std::cout << "is cr" << std::endl;
					input.solved_for_group[binary_counter] = true;
				}

				input.root.get()->reset_counterexample_choices();
				input.root->reset_reason();
			}
		}
		if (!options.all_counterexamples) {
			if (!reason.null()){
				input.root->restore_problematic_groups(problematic_group_storage);
				input.root->restore_reason(reason_storage);
				input.reset_point = current_reset_point;
			}
		} else {
			if ((!reason.null()) && !is_unsat){
				input.root->restore_problematic_groups(problematic_group_storage);
				input.root->restore_reason(reason_storage);
				input.reset_point = current_reset_point;
			}
		}
		return result;
	}

	else if (property == PropertyType::Practicality) {
		bool pr_result = practicality_rec_old(input, options, solver, input.root.get(), {}, true);
		if(pr_result && options.counterexamples && !input.root->branch().honest) {
			CeCase pr_ce_case;
			std::vector<CeChoice> pr_choices;
			for(const auto& pr_utility : input.root->practical_utilities) {
				CeChoice ce_choice;
				ce_choice.choices = input.root->strat2hist(pr_utility.strategy_vector);
				pr_choices.push_back(ce_choice);
			}
			pr_ce_case.counterexample = pr_choices;
			input.counterexamples.push_back(pr_ce_case);
		}
		return pr_result;
	}
	
 
	assert(false);
	UNREACHABLE
}


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
			std::vector<Utility> honest_utility;
			for (auto elem: input.root->branch().practical_utilities) {
				honest_utility = elem.leaf;
			}
			subtree_result_pr.utilities = {honest_utility};
			subtree_results_pr.push_back(subtree_result_pr);
		}


		// if strategies, add a "potential case" to keep track of all strategies
		if (options.strategies){
			input.compute_strategy_case(current_case, property);

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
	if (split.null()) {
		if (!input.stop_log){
			std::cout << "\tProperty violated in case: " << current_case << std::endl;
		}
		if (options.preconditions){
			input.add_unsat_case(current_case);
			input.stop_logging();
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

	std::vector<std::vector<bool>> violation;
	if (property == PropertyType::CollusionResilience && options.strategies){
		violation = input.root->store_violation_cr();
	}

	std::vector<std::vector<std::string>> ce_storage;
	if (options.counterexamples && property != PropertyType::Practicality) {
		ce_storage = input.root->store_counterexample_choices();
	}

	std::vector<bool> solved_for_storage;
	std::vector<uint64_t> problematic_groups;
	if (property != PropertyType::Practicality) {
		solved_for_storage = input.store_solved_for();
		problematic_groups = input.root->store_problematic_groups();
	}

	// std::cout << "problematic group: " << current_next_group << std::endl;
	auto &current_reset_point = input.reset_point;


	bool result = true;

	for (const z3::Bool& condition : {split, split.invert()}) {
		// reset reason and strategy
		// ? should be the same point of reset
		input.root->reset_reason();
		if(!input.reset_point->is_leaf() && !input.reset_point->is_subtree()) {
			auto &current_reset_branch = current_reset_point->branch();
			current_reset_branch.reset_strategy();
		}

		solver.push();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);


		bool attempt = property_rec(solver, options, input, property, new_current_case, history, subtree_results_pr);

		solver.pop();

		if (property != PropertyType::Practicality) {
			// reset the branch.problematic_group for all branches to presplit state, such that the other case split starts at the same point
			input.root->restore_problematic_groups(problematic_groups);
			input.restore_solved_for(solved_for_storage);

			if (options.counterexamples){
				input.root->restore_counterexample_choices(ce_storage);
			}
		}

		if (property == PropertyType::CollusionResilience && options.strategies){
			std::vector<std::vector<bool>> violation_copy;
			violation_copy.insert(violation_copy.end(), violation.begin(), violation.end());
			input.root->restore_violation_cr(violation_copy);
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
	return result;
}

bool property_rec_subtree(z3::Solver &solver, const Options &options, const Input &input, const PropertyType property, std::vector<z3::Bool> current_case, size_t history, unsigned group_nr, std::vector<std::vector<z3::Bool>> &satisfied_in_case) {
	/* 
		only called for weak(er) immunity and collusion resilience
		actual case splitting engine
		determine if the input has some property for the current honest history, splitting recursively
	*/

	// property holds under current split

	bool property_result;
	std::bitset<Input::MAX_PLAYERS> group;
	Utility honest_total{z3::Real::ZERO, z3::Real::ZERO};


	if(property == PropertyType::CollusionResilience){
		const Node &honest_leaf_pre = get_honest_leaf(input.root.get(), input.honest[history], 0);
		// in subtree mode there cannot be subtrees in the input;
		const Leaf &honest_leaf = honest_leaf_pre.leaf();
		group = group_nr;
		
		// compute the honest total for the current group
		for (size_t player = 0; player < input.players.size(); player++) {
			if (group[player]) {
				honest_total = honest_total + honest_leaf.utilities[player];
			}
		}
		property_result = collusion_resilience_rec(input, solver, options, input.root.get(), group, honest_total, input.players.size(), group_nr, false);
	} else {
		assert(property != PropertyType::Practicality);
		assert(group_nr > 0); // set to i+1 in previous fct
		property_result = weak_immunity_rec(input, solver, options, input.root.get(), group_nr-1, property == PropertyType::WeakerImmunity, false);
	}


	if (property_result) {
		if (!input.stop_log){
			std::cout << "\tProperty satisfied for case: " << current_case << std::endl; 
		}

		satisfied_in_case.push_back(current_case);

		// if strategies, add a "potential case" to keep track of all strategies
		// if (options.strategies){
		// 	input.compute_strategy_case(current_case, property);

		// 	if(options.all_cases && property == PropertyType::CollusionResilience) {
		// 		input.root->reset_violation_cr();
		// 	}
		// }
		return true;
	}

	// otherwise consider case split
	z3::Bool split = input.root->reason;
	// there is no case split
	if (split.null()) {
		if (!input.stop_log){
			std::cout << "\tProperty violated in case: " << current_case << std::endl;
		}
		// if (options.preconditions){
		// 	input.add_unsat_case(current_case);
		// 	input.stop_logging();
		// }
		// if (options.counterexamples){
		// 	input.add_case2ce(current_case);
		// }

		// if(options.all_cases && options.strategies && property == PropertyType::CollusionResilience) {
		// 	input.root->reset_violation_cr();
		// }

		return false;
	}
	if (!input.stop_log){
		std::cout << "\tSplitting on: " << split << std::endl;
	}

	// std::vector<std::vector<bool>> violation;
	// if (property == PropertyType::CollusionResilience && options.strategies){
	// 	violation = input.root->store_violation_cr();
	// }

	// std::vector<std::vector<std::string>> ce_storage;
	// if (options.counterexamples && property != PropertyType::Practicality) {
	// 	ce_storage = input.root->store_counterexample_choices();
	// }

	// std::vector<bool> solved_for_storage;
	// std::vector<uint64_t> problematic_groups;
	// if (property != PropertyType::Practicality) {
	// 	solved_for_storage = input.store_solved_for();
	// 	problematic_groups = input.root->store_problematic_groups();
	// }

	// std::cout << "problematic group: " << current_next_group << std::endl;
	auto &current_reset_point = input.reset_point;


	bool result = true;

	// both cr and w(er)i need all cases for soundness
	for (const z3::Bool& condition : {split, split.invert()}) {
		// reset reason and strategy
		// ? should be the same point of reset
		input.root->reset_reason();
		if(!input.reset_point->is_leaf() && !input.reset_point->is_subtree()) {
			auto &current_reset_branch = current_reset_point->branch();
			current_reset_branch.reset_strategy();
		}

		solver.push();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);


		bool attempt = property_rec_subtree(solver, options, input, property, new_current_case, history, group_nr, satisfied_in_case);

		solver.pop();

		// if (property != PropertyType::Practicality) {
		// 	// reset the branch.problematic_group for all branches to presplit state, such that the other case split starts at the same point
		// 	input.root->restore_problematic_groups(problematic_groups);
		// 	input.restore_solved_for(solved_for_storage);

		// 	if (options.counterexamples){
		// 		input.root->restore_counterexample_choices(ce_storage);
		// 	}
		// }

		// if (property == PropertyType::CollusionResilience && options.strategies){
		// 	std::vector<std::vector<bool>> violation_copy;
		// 	violation_copy.insert(violation_copy.end(), violation.begin(), violation.end());
		// 	input.root->restore_violation_cr(violation_copy);
		// }

		if (!attempt){
			// if ((!options.preconditions) && (!options.all_cases)){
			// 	return false;
			// }
			// else {
			// 	result = false;
			// 	if (options.preconditions){
			// 		input.stop_logging();
			// 	}
			// }
			result = false;
		}
	}
	return result;
}

bool property_rec_utility(z3::Solver &solver, const Options &options, const Input &input, const PropertyType property, std::vector<z3::Bool> current_case, std::vector<Utility> honest_utility, unsigned group_nr, std::vector<std::vector<z3::Bool>> &satisfied_in_case) {
	/* 
		only called for collusion resilience
		actual case splitting engine
		determine if the input has some property for the current honest history, splitting recursively
	*/

	// property holds under current split

	bool property_result;
	std::bitset<Input::MAX_PLAYERS> group = group_nr;
	Utility honest_total{z3::Real::ZERO, z3::Real::ZERO};

	
	// compute the honest total for the current group
	for (size_t player = 0; player < input.players.size(); player++) {
		if (group[player]) {
			honest_total = honest_total + honest_utility[player];
		}
	}
	property_result = collusion_resilience_rec(input, solver, options, input.root.get(), group, honest_total, input.players.size(), group_nr, false);



	if (property_result) {
		if (!input.stop_log){
			std::cout << "\tProperty satisfied for case: " << current_case << std::endl; 
		}
		// if strategies, add a "potential case" to keep track of all strategies
		// if (options.strategies){
		// 	input.compute_strategy_case(current_case, property);

		// 	if(options.all_cases && property == PropertyType::CollusionResilience) {
		// 		input.root->reset_violation_cr();
		// 	}
		// }
		satisfied_in_case.push_back(current_case);
		return true;
	}

	// otherwise consider case split
	z3::Bool split = input.root->reason;
	// there is no case split
	if (split.null()) {
		if (!input.stop_log){
			std::cout << "\tProperty violated in case: " << current_case << std::endl;
		}
		// if (options.preconditions){
		// 	input.add_unsat_case(current_case);
		// 	input.stop_logging();
		// }
		// if (options.counterexamples){
		// 	input.add_case2ce(current_case);
		// }

		// if(options.all_cases && options.strategies && property == PropertyType::CollusionResilience) {
		// 	input.root->reset_violation_cr();
		// }

		return false;
	}
	if (!input.stop_log){
		std::cout << "\tSplitting on: " << split << std::endl;
	}

	// std::vector<std::vector<bool>> violation;
	// if (property == PropertyType::CollusionResilience && options.strategies){
	// 	violation = input.root->store_violation_cr();
	// }

	// std::vector<std::vector<std::string>> ce_storage;
	// if (options.counterexamples && property != PropertyType::Practicality) {
	// 	ce_storage = input.root->store_counterexample_choices();
	// }

	// std::vector<bool> solved_for_storage;
	// std::vector<uint64_t> problematic_groups;
	// if (property != PropertyType::Practicality) {
	// 	solved_for_storage = input.store_solved_for();
	// 	problematic_groups = input.root->store_problematic_groups();
	// }

	// std::cout << "problematic group: " << current_next_group << std::endl;
	auto &current_reset_point = input.reset_point;


	bool result = true;

	for (const z3::Bool& condition : {split, split.invert()}) {
		// reset reason and strategy
		// ? should be the same point of reset
		input.root->reset_reason();
		if(!input.reset_point->is_leaf() && !input.reset_point->is_subtree()) {
			auto &current_reset_branch = current_reset_point->branch();
			current_reset_branch.reset_strategy();
		}

		solver.push();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);


		bool attempt = property_rec_utility(solver, options, input, property, new_current_case, honest_utility, group_nr, satisfied_in_case);

		solver.pop();

		// if (property != PropertyType::Practicality) {
		// 	// reset the branch.problematic_group for all branches to presplit state, such that the other case split starts at the same point
		// 	input.root->restore_problematic_groups(problematic_groups);
		// 	input.restore_solved_for(solved_for_storage);

		// 	if (options.counterexamples){
		// 		input.root->restore_counterexample_choices(ce_storage);
		// 	}
		// }

		// if (property == PropertyType::CollusionResilience && options.strategies){
		// 	std::vector<std::vector<bool>> violation_copy;
		// 	violation_copy.insert(violation_copy.end(), violation.begin(), violation.end());
		// 	input.root->restore_violation_cr(violation_copy);
		// }

		if (!attempt){
			// if ((!options.preconditions) && (!options.all_cases)){
			// 	return false;
			// }
			// else {
			// 	result = false;
			// 	if (options.preconditions){
			// 		input.stop_logging();
			// 	}
			// }
			result = false;
		}
	}
	return result;
}

bool property_rec_nohistory(z3::Solver &solver, const Options &options, const Input &input, const PropertyType property, std::vector<z3::Bool> current_case, unsigned player_nr, std::vector<std::vector<z3::Bool>> &satisfied_in_case, std::vector<PracticalitySubtreeResult> &subtree_results_pr) {
	
	/* 
		only called for w(er)i and practicality
		actual case splitting engine
		determine if the input has some property for the current honest history, splitting recursively
	*/

	assert(property != PropertyType::CollusionResilience);

	// property holds under current split
	
	bool property_result;
	if(property == PropertyType::WeakImmunity) {
		property_result = weak_immunity_rec(input, solver, options, input.root.get(), player_nr, false, false);
	} else if (property == PropertyType::WeakerImmunity) {
		property_result = weak_immunity_rec(input, solver, options, input.root.get(), player_nr, true, false);	
	} else if (property == PropertyType::Practicality) {
		property_result = practicality_rec_old(input, options, solver, input.root.get(),{}, false);
	}

	if (property_result) {
		if (!input.stop_log){
			std::cout << "\tProperty satisfied for case: " << current_case << std::endl; 
		}
		// if strategies, add a "potential case" to keep track of all strategies
		// if (options.strategies){
		// 	input.compute_strategy_case(current_case, property);

		// 	if(options.all_cases && property == PropertyType::CollusionResilience) {
		// 		input.root->reset_violation_cr();
		// 	}
		// }

		if(options.subtree && property == PropertyType::Practicality) {
			PracticalitySubtreeResult subtree_result_pr;
			subtree_result_pr._case = current_case;
			subtree_result_pr.utilities = {};
			for (auto elem: input.root->branch().practical_utilities) {
				subtree_result_pr.utilities.push_back(elem.leaf);
			}
			subtree_results_pr.push_back(subtree_result_pr);
		} else if (property != PropertyType::Practicality) {
			satisfied_in_case.push_back(current_case);
		}


		//if(property == PropertyType::WeakImmunity || property == PropertyType::WeakerImmunity) {
		if(property == PropertyType::Practicality) {	
			UtilityCase utilityCase;
			utilityCase._case = current_case;
			for(auto practical_utility : input.root.get()->practical_utilities) {
				utilityCase.utilities.push_back(practical_utility.leaf);
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
		// if (options.preconditions){
		// 	input.add_unsat_case(current_case);
		// 	input.stop_logging();
		// }
		// if (options.counterexamples){
		// 	input.add_case2ce(current_case);
		// }

		// if(options.all_cases && options.strategies && property == PropertyType::CollusionResilience) {
		// 	input.root->reset_violation_cr();
		// }

		return false;
	}
	if (!input.stop_log){
		std::cout << "\tSplitting on: " << split << std::endl;
	}

	// std::vector<std::vector<bool>> violation;
	// if (property == PropertyType::CollusionResilience && options.strategies){
	// 	violation = input.root->store_violation_cr();
	// }

	// std::vector<std::vector<std::string>> ce_storage;
	// if (options.counterexamples && property != PropertyType::Practicality) {
	// 	ce_storage = input.root->store_counterexample_choices();
	// }

	// std::vector<bool> solved_for_storage;
	// std::vector<uint64_t> problematic_groups;
	// if (property != PropertyType::Practicality) {
	// 	solved_for_storage = input.store_solved_for();
	// 	problematic_groups = input.root->store_problematic_groups();
	// }

	// std::cout << "problematic group: " << current_next_group << std::endl;
	auto &current_reset_point = input.reset_point;	
	
	bool result = true;

	for (const z3::Bool& condition : {split, split.invert()}) {
		// reset reason and strategy
		// ? should be the same point of reset
		input.root->reset_reason();
		if(!input.reset_point->is_leaf() && !input.reset_point->is_subtree()) {
			auto &current_reset_branch = current_reset_point->branch();
			current_reset_branch.reset_strategy();
		}

		solver.push();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);


		bool attempt = property_rec_nohistory(solver, options, input, property, new_current_case, player_nr, satisfied_in_case, subtree_results_pr);

		solver.pop();

		// if (property != PropertyType::Practicality) {
		// 	// reset the branch.problematic_group for all branches to presplit state, such that the other case split starts at the same point
		// 	input.root->restore_problematic_groups(problematic_groups);
		// 	input.restore_solved_for(solved_for_storage);

		// 	if (options.counterexamples){
		// 		input.root->restore_counterexample_choices(ce_storage);
		// 	}
		// }

		// if (property == PropertyType::CollusionResilience && options.strategies){
		// 	std::vector<std::vector<bool>> violation_copy;
		// 	violation_copy.insert(violation_copy.end(), violation.begin(), violation.end());
		// 	input.root->restore_violation_cr(violation_copy);
		// }

		if (!attempt){
			// if ((!options.preconditions) && (!options.all_cases)){
			// 	return false;
			// }
			// else {
			// 	result = false;
			// 	if (options.preconditions){
			// 		input.stop_logging();
			// 	}
			// }
			result = false;
		}
	}
	return result;
}


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
		/*
		default:
			std::cout << "Unknown property" << std::endl;
			return;
		*/
	}

	std::cout << std::endl;
	std::cout << std::endl;
	if(history < input.honest.size()) {
		std::cout << "Is history " << input.honest[history] << " " << prop_name << "?" << std::endl;
	} else {
		if(property == PropertyType::Practicality) {
			std::cout << "Computing practical histories/strategies." << std::endl;
		} else if (property == PropertyType::CollusionResilience) {
			// see comment in analyze properties
			// if history >= input.honest.size() then we are running subtree in default mode
			// and are considering an honest utility, not an honest history
			std::cout << "Is the subtree " << prop_name << " for honest utility " << input.honest_utilities[history - input.honest.size()].leaf << "?" << std::endl;
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
			}
			prop_holds = true;
		} else { 
			std::cout << "NO, it is not " << prop_name << "." << std::endl;
			prop_holds = false;
		}
	} else {

		//uint64_t next_group = property == PropertyType::CollusionResilience ? 1 : 0;
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
	}
	
	// generate strategies
	if (options.strategies && prop_holds){
		// for each case a strategy
		bool is_wi = (property == PropertyType::WeakerImmunity) || (property == PropertyType::WeakImmunity);
		input.print_strategies(is_wi);
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
		/*
		default:
			std::cout << "Unknown property" << std::endl;
			return;
		*/
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
			assert(input.root->branch().practical_utilities.size() == 1);
			std::vector<Utility> honest_utility;
			for (auto elem: input.root->branch().practical_utilities) {
				honest_utility = elem.leaf;
			}
			std::cout << "YES, it is " << prop_name << ", the honest practical utility is "<<  honest_utility << "." << std::endl;
			prop_holds = true;
		} else {
			//assert( input.root->branch().practical_utilities.size() == 0);
			// removed this assertion bacause it was failing
			// practical utilites is always at least once - we always set it
			// even though when it is not correct because we needed this for an 
			// additional feature (it was either the counterexamples, or strategies or all cases)
			
			std::cout << "NO, it is not " << prop_name << ", hence there is no honest practical utility." << std::endl;
			prop_holds = false;
		}

		subtree.practicality.insert(subtree.practicality.end(), subtree_results_pr.begin(), subtree_results_pr.end());

	} else {

		//uint64_t next_group = property == PropertyType::CollusionResilience ? 1 : 0;
		size_t number_groups = property == PropertyType::CollusionResilience ? pow(2,input.players.size())-2 : input.players.size();

		std::string output_text = property == PropertyType::CollusionResilience ? " against group " : " for player ";

		std::vector<SubtreeResult> subtree_results;

		for (unsigned i = 0; i < number_groups; i++){
			input.reset_reset_point();
			input.root.get()->reset_reason();
			
			std::vector<std::string> players;

            if(property == PropertyType::CollusionResilience) {
                players = index2player(input, i+1);
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

			// check whether we already have a SubtreeResult for this player
			// if yes: append sat cases
			// if not: pushback
			bool found = false;
			for(auto &subtree_result : subtree_results) {
				if(subtree_result.player_group.size() == subtree_result_player.player_group.size()) {
					if(std::equal(subtree_result.player_group.begin(), subtree_result.player_group.end(),subtree_result_player.player_group.begin())) {
						found = true;
						subtree_result.satisfied_in_case.insert(subtree_result.satisfied_in_case.end(), subtree_result_player.satisfied_in_case.begin(), subtree_result_player.satisfied_in_case.end());
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
	
	// generate preconditions -- not now, maybe consider later
	// if (options.preconditions && !prop_holds) {
	// 			std::cout << std::endl;
	// 			std::vector<z3::Bool> conjuncts;
	// 			std::vector<std::vector<z3::Bool>> simplified = input.precondition_simplify();

	// 			for (const auto &unsat_case: simplified) {
	// 				// negate each case (by disjoining the negated elements), then conjunct all - voila weakest prec to be added to the init constr
	// 				std::vector<z3::Bool> neg_case;
	// 				for (const auto &elem: unsat_case) {
	// 					neg_case.push_back(elem.invert());
	// 				}
	// 				z3::Bool disj = disjunction(neg_case);
	// 				conjuncts.push_back(disj);
	// 			}
	// 			z3::Bool raw_prec = conjunction(conjuncts);
	// 			z3::Bool simpl_prec = raw_prec.simplify();
	// 			std::cout << "Weakest Precondition: " << std::endl << "\t" << simpl_prec << std::endl;
	// }
	
	// generate strategies -- not now, maybe later
	// if (options.strategies && prop_holds){
	// 	// for each case a strategy
	// 	bool is_wi = (property == PropertyType::WeakerImmunity) || (property == PropertyType::WeakImmunity);
	// 	input.print_strategies(is_wi);
	// }

	// counterexamples -- not now, maybe later
	// if (options.counterexamples && !prop_holds){
	// 	bool is_wi = (property == PropertyType::WeakerImmunity) || (property == PropertyType::WeakImmunity);
	// 	bool is_cr = (property == PropertyType::CollusionResilience);
	// 	input.print_counterexamples(is_wi, is_cr);
	// }
	
	return;
}

void property_subtree_utility(const Options &options, const Input &input, PropertyType property, std::vector<Utility> honest_utility, Subtree &subtree) {
	/* determine if the input has some property for the current honest history */

	assert(property == PropertyType::CollusionResilience);

	Solver solver;
	solver.assert_(input.initial_constraint);
	bool prop_holds;

	solver.assert_(input.collusion_resilience_constraint);

	std::cout << std::endl;
	std::cout << std::endl;
	std::cout << "Is utility " << honest_utility << " collusion resilient?" << std::endl;

	assert(solver.solve() == z3::Result::SAT);

	size_t number_groups = pow(2,input.players.size())-2;
	std::vector<SubtreeResult> subtree_results;

	for (unsigned i = 0; i < number_groups; i++){
		input.reset_reset_point();
		input.root.get()->reset_reason();
		std::vector<std::string> players = index2player(input, i+1);

		SubtreeResult subtree_result_player;
		subtree_result_player.player_group = players;
		subtree_result_player.satisfied_in_case = {};

		if (property_rec_utility(solver, options, input, property, std::vector<z3::Bool>(), honest_utility, i+1, subtree_result_player.satisfied_in_case)){
			std::cout << "YES, it is collusion resilient against group " <<  players << "."  << std::endl;
		} else { 
			std::cout << "NO, it is not  collusion resilient against group " << players << "." << std::endl;
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
					break;
				}
			}
		}
		if(!found) {
			subtree_results.push_back(subtree_result_player);
		}

	}

	subtree.collusion_resilience.insert(subtree.collusion_resilience.end(), subtree_results.begin(), subtree_results.end());

	
	// generate preconditions -- not now, maybe consider later
	// if (options.preconditions && !prop_holds) {
	// 			std::cout << std::endl;
	// 			std::vector<z3::Bool> conjuncts;
	// 			std::vector<std::vector<z3::Bool>> simplified = input.precondition_simplify();

	// 			for (const auto &unsat_case: simplified) {
	// 				// negate each case (by disjoining the negated elements), then conjunct all - voila weakest prec to be added to the init constr
	// 				std::vector<z3::Bool> neg_case;
	// 				for (const auto &elem: unsat_case) {
	// 					neg_case.push_back(elem.invert());
	// 				}
	// 				z3::Bool disj = disjunction(neg_case);
	// 				conjuncts.push_back(disj);
	// 			}
	// 			z3::Bool raw_prec = conjunction(conjuncts);
	// 			z3::Bool simpl_prec = raw_prec.simplify();
	// 			std::cout << "Weakest Precondition: " << std::endl << "\t" << simpl_prec << std::endl;
	// }
	
	// generate strategies -- not now, maybe later
	// if (options.strategies && prop_holds){
	// 	// for each case a strategy
	// 	bool is_wi = (property == PropertyType::WeakerImmunity) || (property == PropertyType::WeakImmunity);
	// 	input.print_strategies(is_wi);
	// }

	// counterexamples -- not now, maybe later
	// if (options.counterexamples && !prop_holds){
	// 	bool is_wi = (property == PropertyType::WeakerImmunity) || (property == PropertyType::WeakImmunity);
	// 	bool is_cr = (property == PropertyType::CollusionResilience);
	// 	input.print_counterexamples(is_wi, is_cr);
	// }
	
	return;
}

void property_subtree_nohistory(const Options &options, const Input &input, PropertyType property, Subtree &subtree) {
	

	Solver solver;
	solver.assert_(input.initial_constraint);
	bool prop_holds;
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

		std::cout << "What are the subtree's practical utilities?" << std::endl;
		bool pr_result = property_rec_nohistory(solver, options, input, property, std::vector<z3::Bool>(), 0, satisfied_in_case, subtree_results_pr);

		assert(pr_result);

		assert(input.root.get()->practical_utilities.size()>0);
		// ATTENTION THINK ABOUT HOW LATER (IN SUPERTREE) CASE SPLITS MAY IMPACT THE RESULT
		// we need to print the corresponding utilities for each case
		// kind of "all cases" for practicality_subtree
		// since in property_rec_nohistory we are not along honest, we consider all cases implicitely
		// it suffices to have a new data structure where we store <case, utulities> information and print them below
		//std::cout << "print utilities" << std::endl;

		for(auto &utilityCase : input.utilities_pr_nohistory) {
			std::cout << "Case: " << utilityCase._case << std::endl;
			for(auto utility : utilityCase.utilities) {
				std::cout << "\t" << utility << std::endl;
			}
		}

		/*
		std::cout << std::endl;
		std::cout << "*****************" << std::endl;
		std::cout << "TO BE PRINTED IN FILE" << std::endl;
		for (auto &subtree_result : subtree_results_pr) {
			std::cout << "Case: " << subtree_result._case << std::endl;
			std::cout << "Utilities: " << std::endl;
			for(auto &utility : subtree_result.utilities) {
				std::cout << "\t Utility: " << utility << std::endl;
			}
			std::cout << std::endl;
		}*/

		subtree.practicality.insert(subtree.practicality.end(), subtree_results_pr.begin(), subtree_results_pr.end());
	} else {
		size_t number_groups = input.players.size();

		std::cout << "Is this subtree " << prop_name << "?" << std::endl;
		std::vector<SubtreeResult> subtree_results;

		for (unsigned i = 0; i < number_groups; i++){
			input.reset_reset_point();
			input.root.get()->reset_reason();
			std::vector<std::string> players = index2player(input, i+1);

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

			// check whether we already have a SubtreeResult for this player
			// if yes: append sat cases
			// if not: pushback
			bool found = false;
			for(auto &subtree_result : subtree_results) {
				if(subtree_result.player_group.size() == subtree_result_player.player_group.size()) {
					if(std::equal(subtree_result.player_group.begin(), subtree_result.player_group.end(),subtree_result_player.player_group.begin())) {
						found = true;
						subtree_result.satisfied_in_case.insert(subtree_result.satisfied_in_case.end(), subtree_result_player.satisfied_in_case.begin(), subtree_result_player.satisfied_in_case.end());
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

	
	
	// generate preconditions -- not now, maybe consider later
	// if (options.preconditions && !prop_holds) {
	// 			std::cout << std::endl;
	// 			std::vector<z3::Bool> conjuncts;
	// 			std::vector<std::vector<z3::Bool>> simplified = input.precondition_simplify();

	// 			for (const auto &unsat_case: simplified) {
	// 				// negate each case (by disjoining the negated elements), then conjunct all - voila weakest prec to be added to the init constr
	// 				std::vector<z3::Bool> neg_case;
	// 				for (const auto &elem: unsat_case) {
	// 					neg_case.push_back(elem.invert());
	// 				}
	// 				z3::Bool disj = disjunction(neg_case);
	// 				conjuncts.push_back(disj);
	// 			}
	// 			z3::Bool raw_prec = conjunction(conjuncts);
	// 			z3::Bool simpl_prec = raw_prec.simplify();
	// 			std::cout << "Weakest Precondition: " << std::endl << "\t" << simpl_prec << std::endl;
	// }
	
	// generate strategies -- not now, maybe later
	// if (options.strategies && prop_holds){
	// 	// for each case a strategy
	// 	bool is_wi = (property == PropertyType::WeakerImmunity) || (property == PropertyType::WeakImmunity);
	// 	input.print_strategies(is_wi);
	// }

	// counterexamples -- not now, maybe later
	// if (options.counterexamples && !prop_holds){
	// 	bool is_wi = (property == PropertyType::WeakerImmunity) || (property == PropertyType::WeakImmunity);
	// 	bool is_cr = (property == PropertyType::CollusionResilience);
	// 	input.print_counterexamples(is_wi, is_cr);
	// }
	
	return;
}


void analyse_properties(const Options &options, const Input &input) {

	if(input.honest_utilities.size() != 0) {
		std::cout << "INFO: This file is a subtree, but CheckMate is running in default mode" << std::endl;
	}

	/* iterate over all honest histories and check the properties for each of them */
	for (size_t history = 0; history < input.honest.size(); history++) { 

		std::cout << std::endl;
		std::cout << std::endl;
		std::cout << "Checking history " << input.honest[history] << std::endl; 

		input.root->reset_honest();
		input.root->mark_honest(input.honest[history]);

		if(options.strategies) {
			input.root->reset_violation_cr();
		}

		std::vector<bool> property_chosen = {options.weak_immunity, options.weaker_immunity, options.collusion_resilience, options.practicality};
		std::vector<PropertyType> property_types = {PropertyType::WeakImmunity, PropertyType::WeakerImmunity, PropertyType::CollusionResilience, PropertyType::Practicality};

		assert(property_chosen.size() == property_types.size());

		for (size_t i=0; i<property_chosen.size(); i++) {
			if(property_chosen[i]) {
				input.reset_counterexamples();
				input.root.get()->reset_counterexample_choices();
				input.reset_logging();
				input.reset_unsat_cases();
				input.root->reset_reason();
				input.root->reset_strategy();
				input.reset_strategies(); 
				input.root->reset_problematic_group(i==2); 
				input.reset_reset_point();
				property(options, input, property_types[i], history);
			}
		}
	}

	if(input.honest_utilities.size() != 0) {

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
				input.reset_logging();
				input.reset_unsat_cases();
				input.root->reset_reason();
				input.root->reset_strategy();
				input.reset_strategies(); 
				input.root->reset_problematic_group(false); 
				input.reset_reset_point();
				property(options, input, property_types[i], input.honest.size());
			}
		}

		if(options.collusion_resilience) {

			for(unsigned honest_utility = 0; honest_utility < input.honest_utilities.size(); honest_utility++) {
				std::cout << std::endl;
				std::cout << std::endl;
				std::cout << "Checking honest utility " << input.honest_utilities[honest_utility].leaf << std::endl; 

				if(options.strategies) {
					input.root->reset_violation_cr();
				}

				input.reset_counterexamples();
				input.root.get()->reset_counterexample_choices();
				input.reset_logging();
				input.reset_unsat_cases();
				input.root->reset_reason();
				input.root->reset_strategy();
				input.reset_strategies(); 
				input.root->reset_problematic_group(true); 
				input.reset_reset_point();
				// input.honest.size() + honest_utility means we are running a subree in default mode
				// and we consider collusion resilience for the honest utility
				property(options, input, PropertyType::CollusionResilience, input.honest.size() + honest_utility);

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

		std::cout << std::endl;
		std::cout << std::endl;
		std::cout << "Checking history " << input.honest[history] << std::endl; 

		input.root->reset_honest();
		input.root->mark_honest(input.honest[history]);
		input.root->reset_practical_utilities();

		if(options.strategies) {
			input.root->reset_violation_cr();
		}

		std::vector<bool> property_chosen = {options.weak_immunity, options.weaker_immunity, options.collusion_resilience, options.practicality};
		std::vector<PropertyType> property_types = {PropertyType::WeakImmunity, PropertyType::WeakerImmunity, PropertyType::CollusionResilience, PropertyType::Practicality};

		assert(property_chosen.size() == property_types.size());

		Subtree st({}, {}, {}, {}, {});
		Subtree &subtree = st;
		const Node &honest_leaf = get_honest_leaf(input.root.get(), input.honest[history], 0);
		subtree.honest_utility = honest_leaf.leaf().utilities;

		for (size_t i=0; i<property_chosen.size(); i++) {
			if(property_chosen[i]) {
				input.reset_counterexamples();
				input.root.get()->reset_counterexample_choices();
				input.reset_logging();
				input.reset_unsat_cases();
				input.root->reset_reason();
				input.root->reset_strategy();
				input.reset_strategies(); 
				input.root->reset_problematic_group(i==2); 
				input.reset_reset_point();
				property_subtree(options, input, property_types[i], history, subtree);
			}
		}

		// create one file for this history
		// set honest utility to the one corresponding to this honest history
		// set wi, weri, cr, pr subtree results
		/*
		std::cout << "********************" << std::endl;
		std::cout << "To be written in JSON" << std::endl;
		std::cout << "Honest utility" << subtree.honest_utility<< std::endl;
		std::cout << "WI" << std::endl;
		for (auto &subtree_result : subtree.weak_immunity) {
			std::cout << "Player(group): " << subtree_result.player_group << std::endl;
			std::cout << "Satisfied in case: " << subtree_result.satisfied_in_case << std::endl;
			std::cout << std::endl;
		}
		std::cout << "WERI" << std::endl;
		for (auto &subtree_result : subtree.weaker_immunity) {
			std::cout << "Player(group): " << subtree_result.player_group << std::endl;
			std::cout << "Satisfied in case: " << subtree_result.satisfied_in_case << std::endl;
			std::cout << std::endl;
		}
		std::cout << "CR" << std::endl;
		for (auto &subtree_result : subtree.collusion_resilience) {
			std::cout << "Player(group): " << subtree_result.player_group << std::endl;
			std::cout << "Satisfied in case: " << subtree_result.satisfied_in_case << std::endl;
			std::cout << std::endl;
		}
		std::cout << "PR" << std::endl;
		for (auto &subtree_result : subtree.practicality) {
			std::cout << "Case: " << subtree_result._case << std::endl;
			std::cout << "Utilities: " << std::endl;
			for(auto &utility : subtree_result.utilities) {
				std::cout << "\t Utility: " << utility << std::endl;
			}
			std::cout << std::endl;
		}

		*/

		std::string file_name = "subtree_result_history" + std::to_string(history) + ".txt";
        print_subtree_result_to_file(input, file_name, subtree);
		
	}

	// iterate over all honest utilities (only for cr) and check the properties for each of them 
	// compute w(er)i and pr results
	if (input.honest_utilities.size()>0) {
		
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
				input.reset_logging();
				input.reset_unsat_cases();
				input.root->reset_reason();
				input.root->reset_strategy();
				input.reset_strategies(); 
				input.reset_reset_point();
				property_subtree_nohistory(options, input, property_types[i], subtree);
			}
		}

		// for cr iterate over all honest utilities
		for (unsigned utility = 0; utility < input.honest_utilities.size(); utility++) { 

			std::cout << std::endl;
			std::cout << std::endl;
			std::cout << "Checking utility " << input.honest_utilities[utility].leaf << std::endl; 

			input.root->reset_honest();

			// possible comment out?
			if(options.strategies) {
				input.root->reset_violation_cr();
			}

			subtree.collusion_resilience = {};

			if(options.collusion_resilience) {
				input.reset_counterexamples();
				input.root.get()->reset_counterexample_choices();
				input.reset_logging();
				input.reset_unsat_cases();
				input.root->reset_reason();
				input.root->reset_strategy();
				input.reset_strategies(); 
				input.root->reset_problematic_group(true); 
				input.reset_reset_point();
				property_subtree_utility(options, input, PropertyType::CollusionResilience, input.honest_utilities[utility].leaf, subtree);
			}

			// create one file for this utility
			// set honest utility to this utility
			// set wi, weri, cr, pr subtree results
			// wi, weri, pr always the same, only cr changes
			subtree.honest_utility = input.honest_utilities[utility].leaf;

			/*
			std::cout << "********************" << std::endl;
			std::cout << "To be written in JSON" << std::endl;
			std::cout << "Honest utility" << subtree.honest_utility<< std::endl;
			std::cout << "WI" << std::endl;
			for (auto &subtree_result : subtree.weak_immunity) {
				std::cout << "Player(group): " << subtree_result.player_group << std::endl;
				std::cout << "Satisfied in case: " << subtree_result.satisfied_in_case << std::endl;
				std::cout << std::endl;
			}
			std::cout << "WERI" << std::endl;
			for (auto &subtree_result : subtree.weaker_immunity) {
				std::cout << "Player(group): " << subtree_result.player_group << std::endl;
				std::cout << "Satisfied in case: " << subtree_result.satisfied_in_case << std::endl;
				std::cout << std::endl;
			}
			std::cout << "CR" << std::endl;
			for (auto &subtree_result : subtree.collusion_resilience) {
				std::cout << "Player(group): " << subtree_result.player_group << std::endl;
				std::cout << "Satisfied in case: " << subtree_result.satisfied_in_case << std::endl;
				std::cout << std::endl;
			}
			std::cout << "PR" << std::endl;
			for (auto &subtree_result : subtree.practicality) {
				std::cout << "Case: " << subtree_result._case << std::endl;
				std::cout << "Utilities: " << std::endl;
				for(auto &utility : subtree_result.utilities) {
					std::cout << "\t Utility: " << utility << std::endl;
				}
				std::cout << std::endl;
			}*/

			std::string file_name = "subtree_result_utility" + std::to_string(utility) + ".txt";
        	print_subtree_result_to_file(input, file_name, subtree);
			
		}
		
	}

}


// FROM HERE ON ONLY COMMENTS


// std::vector<PotentialCase> compute_all_combinations(z3::Solver &solver, std::vector<std::vector<PotentialCase>> remove_sets, std::vector<z3::Bool> current_case) {
// 	if(remove_sets.size() == 0) 
// 		return {{{}, {}}};

// 	std::vector<unsigned> it(remove_sets.size(), 0);
// 	std::vector<PotentialCase> remove_sets_combined;
// 	bool last_case_computed = false;
// 	bool iterators_at_end = all_at_end(it, remove_sets);
	
// 	// I assume current case is asserted in solver;
// 	//solver.assert_(current_case);

// 	while (!iterators_at_end || !last_case_computed) {

// 		// compute case
// 		std::vector<z3::Bool> comb_case;
// 		UtilityTuplesSet comb_remove = remove_sets[0][it[0]].utilities;
// 		solver.push();
// 		for (unsigned k = 0; k < remove_sets.size(); k++){
			
// 			// comb_case.insert(comb_case.end(), remove_sets[k][it[k]]._case.begin(), remove_sets[k][it[k]]._case.end());
// 			for (auto constraint : remove_sets[k][it[k]]._case){
// 				// only add non trivial constriants
// 				if (solver.solve({!constraint})!= z3::Result::UNSAT){
// 					// std::cout << "constraint" << constraint << std::endl;
// 					comb_case.push_back(constraint);
// 					solver.assert_(constraint);
// 				}
// 			} 
			
			
			
// 			if(k != 0) {
// 				for (auto element : remove_sets[k][it[k]].utilities) {
// 					comb_remove.insert(element);
// 				}
// 			}
// 		}
// 		solver.pop();
// 		//std::cout << "comb case in comp_all_comb " << comb_case << std::endl;
// 		// might be unnecessary
// 		std::vector<z3::Bool> check_case(current_case.begin(), current_case.end());
// 		check_case.insert(check_case.end(), comb_case.begin(), comb_case.end());

// 		if (solver.solve(check_case)!= z3::Result::UNSAT) {
// 			// std::cout << "Combined case: " << comb_case << ", current case: " << current_case << std::endl;
// 			remove_sets_combined.push_back({comb_remove, comb_case});
// 		}

// 		if(iterators_at_end) {
// 			last_case_computed = true; 
// 		} else {
// 			unsigned n = remove_sets.size() -1;
// 			while (n > 0 && it[n] == remove_sets[n].size()-1) {
// 				it[n] = 0;
// 				n--;
// 			}
// 			it[n]++;
// 			iterators_at_end = all_at_end(it, remove_sets);
// 		}

// 	}

// 	return remove_sets_combined;
// }




// NOT NEEDED
// bool all_at_end(std::vector<unsigned> it, std::vector<std::vector<PotentialCase>> children) {

// 	for (unsigned i = 0; i < it.size(); i++){
// 		if (it[i] != children[i].size()-1){
// 			return false;
// 		}
// 	}
// 	return true;
// }

// NOT NEEDED
//bool practicality_entry(z3::Solver &solver, const Options &options, const Input &input, Node *root, std::vector<z3::Bool> current_case);


// NOT NEEDED
// template<typename Comparison>
// z3::Bool get_split_approx_old(z3::Solver &solver, Utility a, Utility b, Comparison comp) {
	
// 	// if they have to be equal, consider infinitesimals
// 	if(solver.solve({a.real != b.real}) == z3::Result::UNSAT) {
// 		return comp(a.infinitesimal, b.infinitesimal);
// 	}	
// 	// if they cannot be equal, consider strict inequality
// 	else if (solver.solve({a.real == b.real}) == z3::Result::UNSAT) {
// 		//std::cout << "Case B" << std::endl;
// 		//std::cout << "-> " << a.real << ">" << b.real << std::endl;
// 		return a.real > b.real;
// 	}
// 	else {
// 			return a.real == b.real;
// 	} 	
// }

// NOT NEEDED
// template<typename Comparison> // comparison either > or >=
// z3::Bool get_split(z3::Solver &solver, Utility a, Utility b, Comparison comp) {
// 	// std::cout << solver << std::endl;
// 	if(solver.solve({a.real != b.real}) == z3::Result::UNSAT) {
// 		//std::cout << "Case A" << std::endl;
// 		//std::cout << "-> " << comp(a.infinitesimal, b.infinitesimal) << std::endl;
// 		return comp(a.infinitesimal, b.infinitesimal);
// 	}	
// 	else if (solver.solve({a.real == b.real}) == z3::Result::UNSAT) {
// 		//std::cout << "Case B" << std::endl;
// 		//std::cout << "-> " << a.real << ">" << b.real << std::endl;
// 		return a.real > b.real;
// 	}
// 	else {
// 		//std::cout << "Case C" << std::endl;
// 		//return comp(a.real, b.real);
// 		//return a.real == b.real;
// 		if (solver.solve({!comp(a.infinitesimal, b.infinitesimal)}) == z3::Result::UNSAT) {
// 			return comp(a.real, b.real);
// 		}
// 		else if (solver.solve({comp(a.infinitesimal, b.infinitesimal)}) == z3::Result::UNSAT) {
// 			return a.real > b.real;
// 		}
// 		else {
// 			return a.real > b.real || (a.real == b.real && comp(a.infinitesimal, b.infinitesimal));
// 		}
// 	} 	
// }

// NOT NEEDED
// bool pr_case_split(z3::Solver &solver, const Options &options, const Input &input, UtilityTuple honest_utility, UtilityTuplesSet utilities, unsigned player, std::vector<z3::Bool> current_case){
// // fake case splitting to find out if honest is geq for at least 1 utility[player] in  utilities for current_case"""

// 	bool need_to_split = false;
// 	z3::Bool split;
// 	for (auto utility : utilities){
// 		z3::Bool condition_to_check = get_split_approx_old(solver, utility[player], honest_utility[player], [](z3::Real a, z3::Real b){return a > b;}); 
// 		auto z3_result = solver.solve({condition_to_check});
// 		if (z3_result == z3::Result::UNSAT) {	
// 			if (!input.stop_log){
// 			std::cout << "\tProperty satisfied in case "<< current_case << std::endl;
// 			}
// 			return true;
// 			}
// 		else {
// 			assert(z3_result == z3::Result::SAT);
// 			auto z3_result = solver.solve({!condition_to_check});
// 			if (z3_result == z3::Result::SAT) {	
// 				need_to_split = true;
// 				split = condition_to_check;
// 			}
// 		} 		
// 	}

// 	if (need_to_split){
// 		bool result = true;
// 		if (!input.stop_log){
// 			std::cout << "\tSplitting on: " << split << std::endl;
// 		}

// 		for (const z3::Bool& condition : {split, split.invert()}) {
// 			solver.push();
// 			solver.assert_(condition);
// 			assert (solver.solve() != z3::Result::UNSAT);
// 			std::vector<z3::Bool> new_current_case = {};
// 			new_current_case.insert(new_current_case.begin(), current_case.begin(), current_case.end());
// 			new_current_case.push_back(condition);
// 			bool attempt = pr_case_split(solver, options, input, honest_utility, utilities, player, new_current_case);
// 			solver.pop();
// 			if (!attempt){
// 				if (options.preconditions){
// 					result = false;
// 				} else {
// 				return false;
// 				}
// 			}
// 		}
// 		return result;
// 	} else {
// 		if (!input.stop_log){
// 		std::cout << "\tProperty violated in case "<< current_case << std::endl;
// 		}
// 		if (options.preconditions){
// 				input.add_unsat_case(current_case);
// 				input.stop_logging();
// 			}
// 		return false;
// 	}


// }

// NOT NEEDED
// bool practicality_entry(z3::Solver &solver, const Options &options, const Input &input, Node *root, std::vector<z3::Bool> current_case) {
// 	std::vector<PotentialCase> result = practicality_rec(solver, options, input, root, current_case);
// 	std::cout << "after practicality_rec" << std::endl;
// 	if (result.size() != 0) {	
// 		// strategy computation to be adapted 
// 		// if (options.strategies) {
// 		// 	for (auto &pot_case: result) {
// 		// 		root->branch().print_strategy_pr(input, pot_case._case);
// 		// 	}
// 		// }
			
// 		return true;
// 	}

// 	// there is no case split
// 	assert(root->reason.null());
// 	return false;
// }


// NOT NEEDED
// // refactoring try and avoid the copying here: each std::vector<T> (and UtilityTuplesSet) makes a new copy
// std::vector<PotentialCase> practicality_reasoning(z3::Solver &solver, const Options &options, const Input &input, Node *node, std::vector<z3::Bool> current_case, std::vector<UtilityTuplesSet> children, UtilityTuplesSet honest_utilities) {
// 		const auto &branch = node->branch();
// 		bool ret_empty = false;
		
// 		if (branch.honest) {
// 			// if we are at an honest node, our strategy must be the honest strategy

// 			// set chosen action i.e. startegy for this note to be honest_choice->action
// 			// for this we need to add a property strategy to our nodes
			
// 			assert(honest_utilities.size() == 1);
// 			// the utility at the leaf of the honest history
// 			const UtilityTuple &honest_utility = *honest_utilities.begin();
// 			// this should be maximal against other players, so...
// 			Utility maximum = honest_utility[branch.player];


// 			// if in the subsequent for loop never terminate:
// 			//	 	we return the maximal strategy 
// 			// 		honest choice is practical for current player
// 			PotentialCase pot_case = {{honest_utility}, {}};
// 			std::vector<PotentialCase> result = {pot_case};

// 			// for all other children
// 			for (const auto& utilities : children) {
// 				bool found = false;
// 				// does there exist a possible utility such that `maximum` is geq than it?
// 				for (const auto& utility : utilities) {
// 					//auto condition = maximum < utility[branch.player];
// 					//std::cout<<"Split needed: " << utility[branch.player] << "  " << maximum << std::endl;
// 					auto condition = get_split(solver, utility[branch.player], maximum, [](z3::Real a, z3::Real b){return a > b;});
// 					if (solver.solve({condition}) == z3::Result::SAT) {
// 						if (solver.solve({!condition}) == z3::Result::SAT) {
// 							// might be maximal, just couldn't prove it
// 							branch.reason = get_split_approx_old(solver, utility[branch.player], maximum, [](z3::Real a, z3::Real b){return a > b;});
// 						}
// 					} 
// 					else {
// 						found = true;

// 						break;
// 					}
// 				}
				
// 				if (!found) {
// 					// current_case_okay = false;
					
// 					// return empty set if no reason set
// 					if (branch.reason.null()) {
// 						if (!input.stop_log){
// 						std::cout << "\tProperty violated in case " << current_case << std::endl;
// 						}
// 						if (options.preconditions){
// 							input.add_unsat_case(current_case);
// 							input.stop_logging();
// 							ret_empty = true;
// 						} else {
// 							return {}; 
// 						}
// 					} else {

// 						// call this function for reason and !reason
// 						z3::Bool split = branch.reason;
// 						if (!input.stop_log){
// 							std::cout << "\tSplitting on: " << split << std::endl;
// 						}

// 						for (const z3::Bool& condition : {split, split.invert()}) {
// 							branch.reset_reason();

// 							solver.push();

// 							solver.assert_(condition);
// 							assert (solver.solve() != z3::Result::UNSAT);
// 							std::vector<z3::Bool> new_current_case = {};
// 							new_current_case.insert(new_current_case.begin(), current_case.begin(), current_case.end());
// 							new_current_case.push_back(condition);
// 							bool attempt = pr_case_split(solver, options, input, honest_utility, utilities, branch.player, new_current_case);
							
// 							solver.pop();
// 							if (!attempt) {
// 								if (options.preconditions){
// 									ret_empty = true;
// 								} else {
// 								return {};
// 								}
// 							} 
// 						}
// 						// std::cout << "\tSuccessful split on: " << split << "at history XXX" << std::endl;

// 					}
// 				}
// 			}

// 			if (ret_empty){
// 				assert(options.preconditions);
// 			} else {
// 				return result;
// 			}


// 	} else {
// 		// not in the honest history
// 		// TODO (maybe): we could do this more efficiently by working out the set of utilities for the player
// 		// but utilities can't be put in a set easily -> fix this here in the C++ version

// 		// compute the set of possible utilities by merging the set of children's utilities
// 		UtilityTuplesSet result;
// 		for (const auto& utilities : children) {
// 			for (const auto& utility : utilities) {
// 				result.insert(utility);
// 			}
// 		}

// 		std::vector<std::vector<PotentialCase>> remove_sets; //one per candidate in result, each candidate can have 1 or 2 PotentialCases
		
// 		// work out whether to drop `candidate`
// 		for (const auto& candidate : result) {
// 			std::vector<PotentialCase> remove_sets_of_candate;

// 			// this player's utility
// 			auto dominatee = candidate[branch.player];
// 			::new (&branch.reason) z3::Bool(); 

// 			bool dominated = true;
// 			z3::Bool split;

// 			// check all other children
// 			// if any child has the property that all its utilities are bigger than `dominatee`
// 			// it can be dropped
// 			for (const auto& utilities : children) {
// 				// skip any where the cadidate is already contained

// 				// this logic can be factored out in an external function
// 				bool contained = false;
// 				for (const auto& utility : utilities) {
// 					if (utility_tuples_eq(utility, candidate)) {
// 						contained = true;
// 						break;
// 					}
// 				}

// 				if (contained) {
// 					continue;
// 				}

// 				// *all* utilities have to be bigger
// 				dominated = true;

// 				for (const auto& utility : utilities) {
// 					auto dominator = utility[branch.player];
// 					//auto condition = dominator <= dominatee;
// 					//std::cout<<"Split needed: " << dominatee << "  " << dominator << std::endl;
// 					auto condition = get_split(solver, dominatee, dominator, [](z3::Real a, z3::Real b){return a >= b;});
// 					if (solver.solve({condition}) == z3::Result::SAT) {
// 						dominated = false;
// 						if (solver.solve({!condition}) == z3::Result::SAT) {
// 							if(split.null()) {
// 								split = condition.invert();
// 							} else {
// 								split = split || condition.invert();
// 							}
// 						}
// 					}
// 				}  

// 				if (dominated) {
// 					PotentialCase remove_struct = {{candidate}, {}};
// 					remove_sets_of_candate.push_back(std::move(remove_struct));
// 					break;

// 				} 
// 			}

// 			if (!dominated && !split.null()) {

// 				PotentialCase remove_struct_first = {{candidate}, {split}};
// 				PotentialCase remove_struct_second = {{}, {split.invert()}};

// 				for(PotentialCase remove_struct : {remove_struct_first, remove_struct_second}) {
// 					remove_sets_of_candate.push_back(std::move(remove_struct));
// 				}

// 			}

// 			if(remove_sets_of_candate.size() > 0) {
// 				remove_sets.push_back(std::move(remove_sets_of_candate));
// 			}
		
// 		}

// 		// combine remove sets to obtain O(2**n) remove sets
// 		std::vector<PotentialCase> remove_sets_combined = compute_all_combinations(solver, remove_sets, current_case);
// 		for (auto elem : remove_sets_combined){
// 			// std::cout << "remove sets combined cases " << elem._case << std::endl;
// 		}
// 		std::vector<PotentialCase> ret_result;

// 		for(auto remove_set : remove_sets_combined) {
// 			UtilityTuplesSet rec_result(result.begin(), result.end()); // cannot use std::move here, we need a new copy in each iteration
// 			for (const auto& elem : remove_set.utilities) {
// 				rec_result.erase(elem);
// 			}
// 			ret_result.push_back({std::move(rec_result), remove_set._case});
// 		}

// 		return ret_result;

// 	} 
// 	assert(false);
// 	return {};
// }

// NOT NEEDED
// bool are_compatible(const PotentialCase &pc1, const PotentialCase &pc2) {
// 	bool compatible_utilities = true;

// 	for (const auto& utility : pc1.utilities) {
// 		if(pc2.utilities.find(utility) == pc2.utilities.end()) {
// 			compatible_utilities = false;
// 			break;
// 		}
// 	}

// 	bool compatible_cases = are_compatible_cases(pc1._case, pc2._case);

// 	return compatible_utilities && compatible_cases;
// }


// OUTDATED PRACTICALITY VERSION
// std::vector<PotentialCase> practicality_rec(z3::Solver &solver, const Options &options, const Input &input, Node *node, std::vector<z3::Bool> current_case) {
// 	std::cout << "in practicality_rec" << std::endl;

// 	if (node->is_leaf()) {
// 		// return the utility tuple of the leaf as a set (of one element)
// 		const Leaf &leaf = node->leaf();
// 		std::cout << "return 1 practicality_rec" << std::endl;
// 		return {{{leaf.utilities}, {}}};
// 	}  
// 	// keeps track on whether we have to return the empty set
// 	bool ret_empty = false;

// 	// else we deal with a branch
//  	const auto &branch = node->branch();

// 	// get practical strategies and corresponding utilities recursively
// 	std::vector<std::vector<PotentialCase>> children;
// 	std::vector<std::string> children_actions;

// 	UtilityTuplesSet honest_utilities;
// 	std::vector<z3::Bool> honest_case;

// 	for (const Choice &choice: branch.choices) {
// 		std::vector<PotentialCase> potential_cases = practicality_rec(solver, options, input, choice.node.get(), current_case);

// 		// this child has no practical strategy (propagate reason for case split, if any) 
// 		if(potential_cases.empty()) {
// 			std::cout << "tada" << std::endl;
// 			branch.reason = choice.node->reason;
// 			assert(choice.node->honest);
// 			assert(choice.node->reason.null());
// 			std::cout << "what" << std::endl;


// 			// return empty set
// 			if (options.preconditions){
// 				ret_empty = true;
// 			} else {
// 				std::cout << "return 2 practicality_rec" << std::endl;
// 				return {};
// 			}
// 		}
// 		std::cout << "hmm" << std::endl;

// 		if(choice.node->honest) {
// 			std::cout << "visible" << std::endl;
// 			honest_utilities = potential_cases[0].utilities;
// 			std::cout << "invisible" << std::endl;
// 			honest_case = potential_cases[0]._case;

// 			//std::cout << "Before" << branch.pr_strategies_actions << std::endl;
// 			//std::cout << "---> add " << choice.action << " for case " << potential_cases[0]._case << std::endl;
// 			branch.pr_strategies_cases.push_back(potential_cases[0]._case); 
// 			branch.pr_strategies_actions.push_back(choice.action); // choose the honest action along the honest history
// 			//std::cout << "After" << branch.pr_strategies_actions << std::endl;
// 		} else {
// 			children.push_back(potential_cases);
// 			children_actions.push_back(choice.action);
// 		}
// 	}

// 	// compute all case combinations from the potential_case vector together with the corresponding utilities per child.
// 	// then iterate over it and call practicality_reasoning for each
// 	std::vector<std::vector<z3::Bool>> combined_cases;
// 	std::vector<std::vector<UtilityTuplesSet>> children_per_case;

// 	std::vector<unsigned> it(children.size(), 0);
// 	//std::cout << children.size() << std::endl;
	
// 	//TODO for debugging only -> remove afterwards
// 	/*unsigned big_product = 1; 
// 	for(auto something: children) {
// 		big_product *= something.size();
// 	}
// 	std::cout << "------------> "<< big_product<<std::endl;*/
// 	// until here to be removed

// 	bool last_case_computed = false;
// 	bool iterators_at_end = all_at_end(it, children);

// 	while (!iterators_at_end || !last_case_computed) {
// 		// compute case
// 		//solver.push(); -> TODO remove this, not needed, as we are not asserting anything
		
// 		//std::vector<z3::Bool> comb_case(children[0][it[0]]._case.begin(), children[0][it[0]]._case.end());
// 		//std::vector<UtilityTuplesSet> comb_case_children = {children[0][it[0]].utilities};
// 		std::vector<z3::Bool> comb_case;
// 		std::vector<UtilityTuplesSet> comb_case_children;

// 		solver.push();
// 		for (unsigned k = 0; k < children.size(); k++){
// 			//comb_case.insert(comb_case.end(), children[k][it[k]]._case.begin(), children[k][it[k]]._case.end());
// 			// add only non trivial constraints
			
// 			for (auto constraint : children[k][it[k]]._case) {
// 				if (solver.solve({!constraint}) != z3::Result::UNSAT){
// 					comb_case.push_back(constraint);
// 					solver.assert_(constraint);
// 				}
// 			}
			
// 			comb_case_children.push_back(children[k][it[k]].utilities);
// 		}
// 		solver.pop();
// 		if (solver.solve({comb_case})!= z3::Result::UNSAT) {
// 			combined_cases.push_back(comb_case);
// 			children_per_case.push_back(comb_case_children);
// 		}
		
// 		//solver.pop();
// 		if(iterators_at_end) {
// 			last_case_computed = true; 
// 		} else {
// 			unsigned n = children.size() -1;
// 			while (n > 0 && it[n] == children[n].size()-1) {
// 				it[n] = 0;
// 				n--;
// 			}
// 			it[n]++;
// 			iterators_at_end = all_at_end(it, children);
// 		}
		
// 	}


// 	std::vector<PotentialCase> result;
// 	for (unsigned i=0; i < combined_cases.size(); i++){
// 		std::vector<z3::Bool> new_case = {};
// 		new_case.insert(new_case.begin(), current_case.begin(), current_case.end());
// 		new_case.insert(new_case.end(), combined_cases[i].begin(), combined_cases[i].end());
// 		solver.push();
// 		for (auto asssertion : combined_cases[i]) {
// 			solver.assert_(asssertion);
// 		}
// 		std::cout << "pre practicality_reasoning" << std::endl;
// 		std::vector<PotentialCase> res_reasoning = practicality_reasoning(solver, options, input, node, new_case, children_per_case[i], honest_utilities);
// 		std::cout << "post practicality_reasoning" << std::endl;
// 		solver.pop();
		
// 		if (res_reasoning.size() == 0){
// 			// return empty set
// 			if (options.preconditions){
// 				ret_empty = true;
// 			} else {
// 			std::cout << "return 3 practicality_rec" << std::endl;
// 			return {};
// 			}
// 		}

// 		for(auto pot_case : res_reasoning) {
// 			UtilityTuplesSet utilities = pot_case.utilities;
// 			if (utilities.empty()){
// 				// return empty set
// 				if (options.preconditions){
// 					ret_empty = true;
// 				} else {
// 				std::cout << "return 4 practicality_rec" << std::endl;
// 				return {};
// 				}
// 			}
// 			// std::cout << "end of pr_rec potential case: " << pot_case._case << std::endl;
// 			// std::cout << "combined_cases[i]: " << combined_cases[i] << std::endl;
// 			// std::cout << "current case: " << current_case << std::endl;
// 			std::vector<z3::Bool> new_potential_case(combined_cases[i].begin(), combined_cases[i].end());
// 			new_potential_case.insert(new_potential_case.end(), pot_case._case.begin(), pot_case._case.end());
// 			PotentialCase pot = {utilities, new_potential_case};
// 			result.push_back(pot);
// 		}
		
// 	}

// 	// strategy extraction
// 	// for each potential case from result find the first child from children s.t.
// 	// child contains a potential case compatible with the potential case from result
// 	// a potential case (utilities1, case1) is compatible with potential case (utilities2, case2) iff.
// 	// utilities1 \subseteq utilities2 && case1 \subseteq case2
// 	if (!branch.honest) { // if strategy has not been set, we are not along the honest history
// 		for (unsigned i = 0; i < result.size(); i++) {
// 			PotentialCase &potential_case_from_result = result[i];
// 			bool found = false;
// 			for (unsigned j = 0; j < children.size() && !found; j++) {
// 				for (const auto& potential_case : children[j]) {
// 					if(are_compatible(potential_case, potential_case_from_result)) {
// 						branch.pr_strategies_cases.push_back(potential_case_from_result._case);
// 						branch.pr_strategies_actions.push_back(children_actions[j]);
// 						//std::cout << "---> add " << children_actions[j] << " for case " << potential_case_from_result._case << std::endl;
// 						found = true;
// 						break;
// 					}
// 				}
// 			}
// 		}
// 	} 

// 	if (ret_empty){
// 		assert(options.preconditions);
// 		std::cout << "return 5 practicality_rec" << std::endl;
// 		return {}; 
// 	} else {

// 		std::cout << "return 6 practicality_rec" << std::endl;
// 	return result;
// 	}
// }

