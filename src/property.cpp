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

		z3::Bool condition = weaker ? utility.real >= z3::Real::ZERO : utility >= Utility {z3::Real::ZERO, z3::Real::ZERO};

		if(options.count_calls) {
			weaker ? calls_weri++ : calls_wi++;
		}
		if (solver.solve({!condition}) == z3::Result::UNSAT) {
			if (consider_prob_groups) {
				leaf.problematic_group = player + 1;
			}
			return true;
		}
		
		if(options.count_calls) {
			weaker ? calls_weri++ : calls_wi++;
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

		if ((player < subtree.problematic_group) && consider_prob_groups){
			return true;
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
					
					if (z3_result_disjoint == z3::Result::SAT) {
						// set reason
						subtree.reason = disj_of_cases;
					}

					if (consider_prob_groups) {
						subtree.problematic_group = player;
					}
					input.set_reset_point(subtree);
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

bool collusion_resilience_rec(const Input &input, z3::Solver &solver, const Options &options, Node *node, std::bitset<Input::MAX_PLAYERS> group, const std::vector<Utility> &honest_utility, unsigned players, uint64_t group_nr);

bool collusion_resilience_rec_uncached(const Input &input, z3::Solver &solver, const Options &options, Node *node, std::bitset<Input::MAX_PLAYERS> group, const std::vector<Utility> &honest_utility, unsigned players, uint64_t group_nr) {
	
	if (node->is_leaf()) {
		const auto &leaf = node->leaf();

		// the honest utility is the utility of the honest leaf, so no group can gain anything there
		if (leaf.honest) {
			return true;
		}

		// check the property for all supergroups of group (including group itself),
		// except the group of all players:
		// enumerate all subsets `extra` of the players outside of group, except the full one
		const uint64_t all_players = players == 64 ? -1ull : (1ull << players) - 1;
		const uint64_t outside = all_players & ~group.to_ullong();
		if (leaf.cr_supergroup_memo.empty()) {
			leaf.cr_supergroup_memo.resize(all_players);
		}
		z3::Bool reason;
		for (uint64_t extra = 0; extra != outside; extra = (extra - outside) & outside) {
			std::bitset<Input::MAX_PLAYERS> supergroup = group.to_ullong() | extra;
			// the empty group cannot gain anything
			if (supergroup.none())
				continue;

			// look up whether this supergroup was already compared for another group
			CrMemo &memo = leaf.cr_supergroup_memo[supergroup.to_ullong()];
			if (input.memo_valid(memo)) {
				if (memo.status == CrMemo::VIOLATED)
					return false;
				if (memo.status == CrMemo::UNDECIDED && reason.null())
					reason = memo.reason;
				continue;
			}

			// compute the honest and the leaf total utility for the supergroup...
			Utility honest_total{z3::Real::ZERO, z3::Real::ZERO};
			Utility group_utility{z3::Real::ZERO, z3::Real::ZERO};

			for (size_t player = 0; player < players; player++)
				if (supergroup[player]) {
					honest_total = honest_total + honest_utility[player];
					group_utility = group_utility + leaf.utilities[player];
				}

			// ..and compare them
			auto condition = honest_total >= group_utility;

			if(options.count_calls) {
				calls_cr++;
			}
			if (solver.solve({!condition}) == z3::Result::UNSAT) {
				memo = input.memo(CrMemo::HOLDS);
				continue;
			}

			if(options.count_calls) {
				calls_cr++;
			}
			if (solver.solve({condition}) == z3::Result::UNSAT) {
				memo = input.memo(CrMemo::VIOLATED);
				return false;
			}

			// undecided for this supergroup: remember the first case split,
			// but keep looking for a supergroup that violates the property in any case
			memo = input.memo(CrMemo::UNDECIDED, get_split_approx(solver, honest_total, group_utility));
			if (reason.null())
				reason = memo.reason;
		}

		if (reason.null())
			return true;

		leaf.reason = reason;
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

		// search for the SubtreeResult that corresponds to a player group g,
		// and collect the cases it is satisfied in as a disjunction of conjunctions
		// (null if it is satisfied without any case split)
		auto satisfied_for = [&](uint64_t g, z3::Bool &disj_of_cases) {
			std::vector<std::string> player_names = index2player(input, PropertyType::CollusionResilience, g);

			for (const SubtreeResult &subtree_result : subtree.collusion_resilience) {
				// find the correct subtree_result
				if (subtree_result.player_group.size() != player_names.size())
					continue;
				bool correct_subtree = true;
				for (const std::string &subtree_player : subtree_result.player_group){
					if (std::find(player_names.begin(), player_names.end(), subtree_player) == player_names.end()) {
						correct_subtree = false;
						break;
					}
				}
				if (!correct_subtree)
					continue;

				std::vector<z3::Bool> cases_as_conjunctions = {};

				for (auto _case: subtree_result.satisfied_in_case) {
					// satisfied without any case split: leave disj_of_cases null
					if (_case.empty())
						return true;
					// try to optimize: if only 1 -> no need for conjunction
					if(_case.size() == 1) {
						cases_as_conjunctions.push_back(_case[0]);
					} else {
						cases_as_conjunctions.push_back(z3::conjunction(_case));
					}
				}

				if(cases_as_conjunctions.size() == 1) {
					disj_of_cases = cases_as_conjunctions[0];
				} else {
					disj_of_cases = z3::disjunction(cases_as_conjunctions);
				}
				return true;
			}
			return false;
		};

		z3::Bool disj_of_cases;
		bool found = satisfied_for(group_nr, disj_of_cases);

		// satisfied without any case split
		if (found && disj_of_cases.null())
			return true;

		if (found) {

			// (init_cons && wi_cons && curent_case) => disj_of_cases VALID
			// ! (init_cons && wi_cons && current_case) || disj_of_cases VALID
			// (init_cons && wi_cons && current_case) && !disj_of_cases UNSAT
			// init_cons && wi_cons && current_case    && !disj_of_cased UNSAT

			if(options.count_calls) {
				calls_cr++;
			}
			z3::Result z3_result_implied = solver.solve({!disj_of_cases});

			if (z3_result_implied == z3::Result::UNSAT) {
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

				input.set_reset_point(subtree);
				return false;
			}
		}
	} 

	const auto &branch = node->branch();

	// else we deal with a branch:
	// one choice (the honest one if the branch is honest, otherwise any) must be collusion resilient for group,
	// all other choices are deviations of branch.player, so they must be collusion resilient for group together with branch.player
	std::bitset<Input::MAX_PLAYERS> supergroup = group;
	supergroup[branch.player] = true;
	uint64_t supergroup_nr = supergroup.to_ullong();
	// the group of all players is not considered, so it trivially satisfies the property
	bool supergroup_trivial = supergroup.count() == players;

	// first reason (case split) found in a child, if any
	z3::Bool reason;
	Node *reset_node = nullptr;
	auto check = [&](const Choice &choice, std::bitset<Input::MAX_PLAYERS> check_group, uint64_t check_group_nr) {
		bool result = collusion_resilience_rec(input, solver, options, choice.node.get(), check_group, honest_utility, players, check_group_nr);
		if (!result && reason.null() && !choice.node->reason.null()) {
			reason = choice.node->reason;
			reset_node = choice.node.get();
		}
		return result;
	};

	const Choice *honest_choice = branch.honest ? &branch.get_honest_child() : nullptr;

	// note: being collusion resilient for group implies being collusion resilient for supergroup,
	// so a choice failing for supergroup also fails for group, i.e. it can neither be the choice taken by group
	// nor a deviation -- hence every choice has to be collusion resilient for supergroup

	// check the choice taken by group first, choices passing for group need not be checked for supergroup
	std::vector<bool> passed_group(branch.choices.size(), false);
	std::vector<bool> failed_group(branch.choices.size(), false);
	const Choice *found_choice = nullptr;
	for (size_t i = 0; i < branch.choices.size(); i++) {
		const Choice &choice = branch.choices[i];
		if (honest_choice && &choice != honest_choice)
			continue;

		if (check(choice, group, group_nr)) {
			passed_group[i] = true;
			found_choice = &choice;
			break;
		}
		failed_group[i] = true;
	}

	// check the deviations for supergroup
	// if branch.player is already in group, supergroup is group,
	// so choices that failed for group need not be checked again
	bool same_group = supergroup_nr == group_nr;
	bool result = found_choice != nullptr;
	bool violated = false;
	if (found_choice && !supergroup_trivial) {
		for (size_t i = 0; i < branch.choices.size(); i++) {
			const Choice &choice = branch.choices[i];
			if (passed_group[i])
				continue;
			if (!(same_group && failed_group[i]) && check(choice, supergroup, supergroup_nr))
				continue;

			result = false;
			// violated in any case: no need to split cases
			if (choice.node->reason.null()) {
				violated = true;
				if (options.counterexamples) {
					branch.counterexample_choices.push_back(choice.action);
				}
				if (!options.all_counterexamples)
					return false;
			}
		}
	} else if (!reason.null() && !supergroup_trivial && !options.counterexamples) {
		// no choice passed for group but a case split might help:
		// if a deviation is already known to be violated in any case, the case split is not needed
		// (only look this up, checking the deviations costs more than the case split saves)
		for (size_t i = 0; i < branch.choices.size(); i++) {
			const Choice &choice = branch.choices[i];
			bool known_violated = same_group && failed_group[i] && choice.node->reason.null();
			if (!known_violated && !choice.node->cr_memo.empty()) {
				const CrMemo &memo = choice.node->cr_memo[supergroup_nr];
				known_violated = input.memo_valid(memo) && memo.status == CrMemo::VIOLATED;
			}
			if (known_violated) {
				violated = true;
				break;
			}
		}
	}

	if (result) {
		// record the action taken by group, needed for printing strategy
		if (options.strategies) {
			branch.satisfies_cr[group_nr] = found_choice->action;
		}
		return true;
	}

	// only set reason if there is one and the branch is not violated in any case anyway
	if (!reason.null() && !violated) {
		branch.reason = reason;
		input.set_reset_point(*reset_node);
	}
	return false;
}

bool collusion_resilience_rec(const Input &input, z3::Solver &solver, const Options &options, Node *node, std::bitset<Input::MAX_PLAYERS> group, const std::vector<Utility> &honest_utility, unsigned players, uint64_t group_nr) {

	count_cr_repetitions++;
	if(!node->checked_cr) {
		count_cr++;
		node->checked_cr = true;
	}

	// a reason left from an earlier check of this node (e.g. for another group) must not be mistaken for this one's
	node->reason = z3::Bool();

	// look up a result from this case or a coarser one
	if (node->cr_memo.empty()) {
		const uint64_t all_players = players == 64 ? -1ull : (1ull << players) - 1;
		node->cr_memo.resize(all_players);
	}
	CrMemo &memo = node->cr_memo[group_nr];
	if (input.memo_valid(memo)) {
		if (memo.status == CrMemo::HOLDS)
			return true;
		// counterexamples are collected while checking violated choices, so these have to be checked again
		if (memo.status == CrMemo::VIOLATED && !options.counterexamples)
			return false;
	}

	bool result = collusion_resilience_rec_uncached(input, solver, options, node, group, honest_utility, players, group_nr);

	// remember results that hold in any case, i.e. true or false without a case split
	if (result) {
		memo = input.memo(CrMemo::HOLDS);
	} else if (node->reason.null()) {
		memo = input.memo(CrMemo::VIOLATED);
	}
	return result;
}

bool practicality_rec_old(const Input &input, const Options &options, z3::Solver &solver, Node *node, std::vector<std::string> actions_so_far, bool consider_prob_groups) {

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
					if (subtree_result.utilities.size() == 0) {
						// we have to be along honest at this point, otw we would have had at least one pr utility
						if(options.counterexamples) {
							input.counterexamples.push_back(input.root.get()->compute_pr_cecase(input.players, input.players.size(), actions_so_far, "", {}));
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
			input.counterexamples.push_back(input.root.get()->compute_pr_cecase(input.players, input.players.size(), actions_so_far, "", {}));
		}
		return false;
	}

	// else we deal with a branch
 	const auto &branch = node->branch();

	if  (branch.problematic_group == 1 && consider_prob_groups){
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

			
			honest_utilities = choice.node->get_utilities();
			honest_choice = choice.action;
			branch.strategy = choice.action; // choose the honest action along the honest history
			honest_index = i;
			
			break;
		}
		i++;
	}

	for (const Choice &choice: branch.choices) {
		if (!choice.node->honest) {
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

			
			if (choice.node->get_utilities().size()==0){
				assert(!result);
				assert(options.all_counterexamples);
				assert(input.counterexamples.size()>0);
			}
		
			children.push_back(choice.node->get_utilities());
			children_actions.push_back(choice.action);
			
		}
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
				auto condition =   maximum < utility[branch.player];
				if(options.count_calls) {
					calls_pr++;
				}
				if (solver.solve({condition}) == z3::Result::SAT) {
					if(options.count_calls) {
						calls_pr++;
					}
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
					input.counterexamples.push_back(input.root.get()->compute_pr_cecase(input.players, branch.player, actions_so_far, deviating_action, utilities));
				}

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
		unsigned int k = 0;
		for (const auto& utilities : children) {
			for (const auto& utility : utilities) {
				UtilityTuple to_insert(utility.leaf); 
				to_insert.strategy_vector.push_back(children_actions[k]);
				utility_result.insert(to_insert);
			}
			k++;
		}

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
					if(options.count_calls) {
						calls_pr++;
					}
					if (solver.solve({condition}) == z3::Result::SAT) {
						if (dominated){
							candidate.strategy_vector.insert(candidate.strategy_vector.end(), utility.strategy_vector.begin(), utility.strategy_vector.end());
						}
						dominated = false;

						if(options.count_calls) {
							calls_pr++;
						}
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

		branch.practical_utilities = utility_result;
		
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
			
			if (!input.solved_for_group[player]) {
				// problematic groups are only considered when we haven't found a case split point yet
			
				bool weak_immune_for_player = weak_immunity_rec(input, solver, options, input.root.get(), player, property == PropertyType::WeakerImmunity, true);

				if (!weak_immune_for_player) {

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
		

		// being collusion resilient for the empty group means being collusion resilient against all groups
		bool result = collusion_resilience_rec(input, solver, options, input.root.get(), 0, utility, input.players.size(), 0);

		// violated in any case: report the groups that can deviate profitably as counterexamples
		if (!result && input.root->reason.null() && options.counterexamples) {
			input.root->reset_counterexample_choices();
			// all possible subgroups of n players can be implemented by counting through from 1 to (2^n - 2)
			for (uint64_t group_nr = 1; group_nr < -1ull >> (64 - input.players.size()); group_nr++) {
				std::bitset<Input::MAX_PLAYERS> group = group_nr;
				input.root->reset_reason();
				bool collusion_resilient_for_group = collusion_resilience_rec(input, solver, options, input.root.get(), group, utility, input.players.size(), group_nr);
				if (!collusion_resilient_for_group && input.root->reason.null()) {
					std::vector<size_t> pl;
					for (size_t player = 0; player < input.players.size(); player++) {
						if (group[player]) {
							pl.push_back(player);
						}
					}
					input.compute_cecase(pl, property);
					if (!options.all_counterexamples) {
						input.root->reset_counterexample_choices();
						break;
					}
				}
				input.root->reset_counterexample_choices();
			}
			// the property is violated in any case, so no reason must remain
			input.root->reset_reason();
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
				input.root->reset_satisfies_cr((1ull << input.players.size()) - 1);
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
			input.root->reset_satisfies_cr((1ull << input.players.size()) - 1);
		}

		return false;
	}
	if (!input.stop_log){
		std::cout << "\tSplitting on: " << split << std::endl;
	}

	std::vector<std::vector<std::string>> satisfies;
	if (property == PropertyType::CollusionResilience && options.strategies){
		satisfies = input.root->store_satisfies_cr();
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
		input.enter_case();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);


		bool attempt = property_rec(solver, options, input, property, new_current_case, history, subtree_results_pr);

		solver.pop();
		input.leave_case();

		if (property != PropertyType::Practicality) {
			// reset the branch.problematic_group for all branches to presplit state, such that the other case split starts at the same point
			input.root->restore_problematic_groups(problematic_groups);
			input.restore_solved_for(solved_for_storage);

			if (options.counterexamples){
				input.root->restore_counterexample_choices(ce_storage);
			}
		}

		if (property == PropertyType::CollusionResilience && options.strategies){
			std::vector<std::vector<std::string>> satisfies_copy;
			satisfies_copy.insert(satisfies_copy.end(), satisfies.begin(), satisfies.end());
			input.root->restore_satisfies_cr(satisfies_copy);
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

	bool property_result;
	std::bitset<Input::MAX_PLAYERS> group;


	if(property == PropertyType::CollusionResilience){
		const Node &honest_leaf_pre = get_honest_leaf(input.root.get(), input.honest[history], 0);
		// in subtree mode there cannot be subtrees in the input;
		const Leaf &honest_leaf = honest_leaf_pre.leaf();
		group = group_nr;
		property_result = collusion_resilience_rec(input, solver, options, input.root.get(), group, honest_leaf.utilities, input.players.size(), group_nr);
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
		if(!input.reset_point->is_leaf() && !input.reset_point->is_subtree()) {
			auto &current_reset_branch = current_reset_point->branch();
			current_reset_branch.reset_strategy();
		}

		solver.push();
		input.enter_case();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);


		bool attempt = property_rec_subtree(solver, options, input, property, new_current_case, history, group_nr, satisfied_in_case);

		solver.pop();
		input.leave_case();

		if (!attempt){
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

	bool property_result;
	std::bitset<Input::MAX_PLAYERS> group = group_nr;
	property_result = collusion_resilience_rec(input, solver, options, input.root.get(), group, honest_utility, input.players.size(), group_nr);

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
		if(!input.reset_point->is_leaf() && !input.reset_point->is_subtree()) {
			auto &current_reset_branch = current_reset_point->branch();
			current_reset_branch.reset_strategy();
		}

		solver.push();
		input.enter_case();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);


		bool attempt = property_rec_utility(solver, options, input, property, new_current_case, honest_utility, group_nr, satisfied_in_case);

		solver.pop();
		input.leave_case();

		if (!attempt){
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
	
	bool property_result;
	if(property == PropertyType::WeakImmunity) {
		property_result = weak_immunity_rec(input, solver, options, input.root.get(), player_nr, false, false);
	} else if (property == PropertyType::WeakerImmunity) {
		property_result = weak_immunity_rec(input, solver, options, input.root.get(), player_nr, true, false);	
	} else if (property == PropertyType::Practicality) {
		property_result = practicality_rec_old(input, options, solver, input.root.get(),{}, false);
	}

	// property holds under current split
	if (property_result) {
		if (!input.stop_log){
			std::cout << "\tProperty satisfied for case: " << current_case << std::endl; 
		}

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
		if(!input.reset_point->is_leaf() && !input.reset_point->is_subtree()) {
			auto &current_reset_branch = current_reset_point->branch();
			current_reset_branch.reset_strategy();
		}

		solver.push();
		input.enter_case();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);


		bool attempt = property_rec_nohistory(solver, options, input, property, new_current_case, player_nr, satisfied_in_case, subtree_results_pr);

		solver.pop();
		input.leave_case();

		if (!attempt){
			result = false;
		}
	}
	return result;
}


void property(const Options &options, const Input &input, PropertyType property, size_t history) {
	/* determine if the input has some property for the current honest history */
	Solver solver;
	// remembered results depend on the solver and the honest utility
	input.reset_cases();
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
	// remembered results depend on the solver and the honest utility
	input.reset_cases();
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
			assert(input.root->branch().practical_utilities.size() == 1);
			std::vector<Utility> honest_utility;
			for (auto elem: input.root->branch().practical_utilities) {
				honest_utility = elem.leaf;
			}
			std::cout << "YES, it is " << prop_name << ", the honest practical utility is "<<  honest_utility << "." << std::endl;
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
		// for collusion resilience all groups except the group of all players, including the empty group:
		// the supertree reaches the subtree with the empty group if it is along the honest history
		size_t number_groups = property == PropertyType::CollusionResilience ? pow(2,input.players.size())-1 : input.players.size();

		std::string output_text = property == PropertyType::CollusionResilience ? " against group " : " for player ";

		std::vector<SubtreeResult> subtree_results;

		for (unsigned i = 0; i < number_groups; i++){
			input.reset_reset_point();
			input.root.get()->reset_reason();
			
			std::vector<std::string> players;
			// collusion resilience groups start at the empty group, weak(er) immunity players are counted from 1
			unsigned group_nr = property == PropertyType::CollusionResilience ? i : i+1;

            if(property == PropertyType::CollusionResilience) {
                players = index2player(input, property, group_nr);
            } else if (property == PropertyType::WeakImmunity || property == PropertyType::WeakerImmunity) {
                players = { input.players[i] };
            }

			SubtreeResult subtree_result_player;
			subtree_result_player.player_group = players;
			subtree_result_player.satisfied_in_case = {};

			if (property_rec_subtree(solver, options, input, property, std::vector<z3::Bool>(), history, group_nr, subtree_result_player.satisfied_in_case)){
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
	
	return;
}

void property_subtree_utility(const Options &options, const Input &input, PropertyType property, std::vector<Utility> honest_utility, Subtree &subtree) {
	/* determine if the input has some property for the current honest history */

	assert(property == PropertyType::CollusionResilience);

	Solver solver;
	// remembered results depend on the solver and the honest utility
	input.reset_cases();
	solver.assert_(input.initial_constraint);

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
		std::vector<std::string> players = index2player(input, property, i+1);

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
	
	return;
}

void property_subtree_nohistory(const Options &options, const Input &input, PropertyType property, Subtree &subtree) {
	

	Solver solver;
	// remembered results depend on the solver and the honest utility
	input.reset_cases();
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

		subtree.practicality.insert(subtree.practicality.end(), subtree_results_pr.begin(), subtree_results_pr.end());
	} else {
		size_t number_groups = input.players.size();

		std::cout << "Is this subtree " << prop_name << "?" << std::endl;
		std::vector<SubtreeResult> subtree_results;

		for (size_t i = 0; i < number_groups; i++){
			input.reset_reset_point();
			input.root.get()->reset_reason();

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
	
	return;
}


void analyse_properties(const Options &options, const Input &input) {

	if(input.honest_utilities.size() != 0) {
		std::cout << "INFO: This file is a subtree, but CheckMate is running in default mode" << std::endl;
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

		input.root->reset_honest();
		input.root->mark_honest(input.honest[history]);

		if(options.strategies) {
			input.root->reset_satisfies_cr((1ull << input.players.size()) - 1);
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
				input.root->reset_problematic_group(); 
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
				input.root->reset_problematic_group(); 
				input.reset_reset_point();
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
				std::cout << "Checking honest utility " << input.honest_utilities[honest_utility].leaf << std::endl; 

				if(options.strategies) {
					input.root->reset_satisfies_cr((1ull << input.players.size()) - 1);
				}

				input.reset_counterexamples();
				input.root.get()->reset_counterexample_choices();
				input.reset_logging();
				input.reset_unsat_cases();
				input.root->reset_reason();
				input.root->reset_strategy();
				input.reset_strategies(); 
				input.root->reset_problematic_group(); 
				input.reset_reset_point();
				// input.honest.size() + honest_utility means we are running a subree in default mode
				// and we consider collusion resilience for the honest utility
				property(options, input, PropertyType::CollusionResilience, input.honest.size() + honest_utility);

				if(options.count_nodes) {
					std::cout << std::endl;
					std::cout << std::endl;
					std::cout << "Number of checked nodes for honest utility: " << input.honest_utilities[honest_utility].leaf << std::endl;
					print_global_counters(false, false, true, false);
				}

				if(options.count_calls) {
					std::cout << std::endl;
					std::cout << std::endl;
					std::cout << "Number of checked nodes for honest utility: " << input.honest_utilities[honest_utility].leaf << std::endl;
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
		std::cout << "Checking history " << input.honest[history] << std::endl; 

		input.root->reset_honest();
		input.root->mark_honest(input.honest[history]);
		input.root->reset_practical_utilities();

		if(options.strategies) {
			input.root->reset_satisfies_cr((1ull << input.players.size()) - 1);
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
				input.root->reset_problematic_group(); 
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
		
		std::cout << std::endl;
		std::cout << std::endl;
		std::cout << "Checking no honest history " << std::endl;

		input.root->reset_honest();
		input.root->reset_practical_utilities();

		// possibly comment out
		if(options.strategies) {
			input.root->reset_satisfies_cr((1ull << input.players.size()) - 1);
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
			std::cout << "Checking utility " << input.honest_utilities[utility].leaf << std::endl; 

			input.root->reset_honest();

			// possible comment out?
			if(options.strategies) {
				input.root->reset_satisfies_cr((1ull << input.players.size()) - 1);
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
				input.root->reset_problematic_group(); 
				input.reset_reset_point();
				property_subtree_utility(options, input, PropertyType::CollusionResilience, input.honest_utilities[utility].leaf, subtree);
			}

			if(options.count_nodes) {
				std::cout << std::endl;
				std::cout << std::endl;
				std::cout << "Number of checked nodes for honest utility: " << input.honest_utilities[utility].leaf << std::endl;
				print_global_counters(false, false, true, false);
			}

			if(options.count_calls) {
				std::cout << std::endl;
				std::cout << std::endl;
				std::cout << "Number of checked nodes for honest utility: " << input.honest_utilities[utility].leaf << std::endl;
				print_calls_counters(false, false, true, false);
			}

			// create one file for this utility
			// set honest utility to this utility
			// set wi, weri, cr, pr subtree results
			// wi, weri, pr always the same, only cr changes
			subtree.honest_utility = input.honest_utilities[utility].leaf;

			std::string file_name = options.input_path + std::string(".out");
        	print_subtree_result_to_file(input, file_name, subtree);
			
		}
		
	}

}
