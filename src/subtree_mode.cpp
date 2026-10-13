#include <fstream>
#include <sstream>

#include "subtree_mode.hpp"
#include "property_checks.hpp"

using json = nlohmann::json;

// the names of the players in `group` (bitset over the players, in the order of input.players)
static std::vector<std::string> group_names(const Input &input, uint64_t group) {
	std::vector<std::string> names;
	for (size_t player = 0; player < input.players.size(); player++) {
		if (group >> player & 1) {
			names.push_back(input.players[player]);
		}
	}
	return names;
}

// the subtree result for `player_group` with `result` the constraints under which the property holds, given `ic`,
// and `holds` whether it holds for all values satisfying `ic` (i.e. not violated_somewhere):
// one case [result], normalised so that `true` and `false` never have to be written out:
// no case if it never holds, the empty case (written as "true") if it always holds
static SubtreeResult subtree_result(const std::vector<std::string> &player_group, const z3::Bool &ic, const z3::Bool &result, bool holds) {
	SubtreeResult subtree_result;
	subtree_result.player_group = player_group;
	if (holds) {
		subtree_result.satisfied_in_case = {{}};
	} else if (holds_somewhere(ic, result)) {
		subtree_result.satisfied_in_case = {{result}};
	}
	return subtree_result;
}

static void print_result(const char *what, const std::vector<std::string> &player_group, bool holds) {
	if (holds) {
		std::cout << "YES, the subtree is " << what << player_group << "." << std::endl;
	} else {
		std::cout << "NO, the subtree is not " << what << player_group << "." << std::endl;
	}
}

SubtreeResults subtree_mode(const Options &options, const Input &input, const UtilityTuplesSet &ustar) {
	SubtreeResults results;

	// weak(er) immunity: ComputeCWI for every player, as in SatisfiesProperty
	for (bool weaker : {false, true}) {
		if (!(weaker ? options.weaker_immunity : options.weak_immunity)) {
			continue;
		}
		PropertyType property = weaker ? PropertyType::WeakerImmunity : PropertyType::WeakImmunity;
		z3::Bool ic = property_constraints(input, property);
		std::vector<SubtreeResult> &property_results = weaker ? results.weaker_immunity : results.weak_immunity;
		bool holds = true;
		for (unsigned player = 0; player < input.players.size(); player++) {
			z3::Bool result = computeCWI(input, player, weaker);
			bool holds_for_player = !violated_somewhere(ic, result);
			print_result(weaker ? "weaker immune for player " : "weak immune for player ", {input.players[player]}, holds_for_player);
			holds = holds && holds_for_player;
			property_results.push_back(subtree_result({input.players[player]}, ic, result, holds_for_player));
		}
		std::cout << (holds ? "YES, the subtree is " : "NO, the subtree is not ") << (weaker ? "weaker immune" : "weak immune")
			<< " for the analyzed history." << std::endl;
	}

	// collusion resilience: ComputeCCR for every group except the group of all players
    // as the supertree may reach the subtree with any of them as deviators
	if (options.collusion_resilience) {
		z3::Bool ic = property_constraints(input, PropertyType::CollusionResilience);
		const uint64_t all_players = input.players.size() == 64 ? -1ull : (1ull << input.players.size()) - 1;
		for (uint64_t group = 0; group < all_players; group++) {
			z3::Bool result = computeCCR(input, ustar, z3::Bool(true), group);
			bool holds = !violated_somewhere(ic, result);
			print_result("collusion resilient against group ", group_names(input, group), holds);
			results.collusion_resilience.push_back(subtree_result(group_names(input, group), ic, result, holds));
			if (group == 0) {
				std::cout << (holds ? "YES, the subtree is " : "NO, the subtree is not ") << "collusion resilient for the analyzed history." << std::endl;
			}
		}
	}

	// TODO: practicality results of the subtree (practical utilities per case), once ComputeCPR provides them
	if (options.practicality) {
		bool holds = computeCPR(input);
		std::cout << (holds ? "YES, the subtree is " : "NO, the subtree is not ") << "practical for the analyzed history." << std::endl;
	}

	return results;
}



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

json subtree2json(const Input &input, const SubtreeResults &results) {
	json subtree_json;
	subtree_json["weak_immunity"] = parse_property_to_json(results.weak_immunity);
	subtree_json["weaker_immunity"] = parse_property_to_json(results.weaker_immunity);
	subtree_json["collusion_resilience"] = parse_property_to_json(results.collusion_resilience);
	subtree_json["practicality"] = parse_practicality_property_to_json(input, results.practicality);
	// only subtrees along the honest history have an honest utility;
	// leave it out otherwise, the parser rejects an empty one and defaults to empty if it is missing
	bool no_honest_utility = std::holds_alternative<std::vector<Utility>>(results.honest_utility)
		&& std::get<std::vector<Utility>>(results.honest_utility).empty();
	if (!no_honest_utility) {
		subtree_json["honest_utility"] = parse_honest_utility_element(input, results.honest_utility);
	}
	return subtree_json;
}

// an honest history in the input format: actions, and lists of {condition, path} at condition nodes
static json history2json(const HonestHistory &history) {
	json result = json::array();
	for (const HonestHistoryElement &element : history) {
		if (std::holds_alternative<std::string>(element)) {
			result.push_back(std::get<std::string>(element));
			continue;
		}
		json conditions = json::array();
		for (const HonestHistoryCondition &history_condition : std::get<std::vector<HonestHistoryCondition>>(element)) {
			std::stringstream ss;
			ss << history_condition.condition;
			conditions.push_back({{"condition", ss.str()}, {"path", history2json(history_condition.path)}});
		}
		result.push_back(conditions);
	}
	return result;
}

void data2json(const Input &input, const std::vector<SubtreeData> &data, const std::string &file_name) {
	json result = json::array();
	for (const SubtreeData &entry : data) {
		json entry_json;
		if (std::holds_alternative<HonestHistory>(entry.key)) {
			entry_json["honest_history"] = history2json(std::get<HonestHistory>(entry.key));
		} else if (std::holds_alternative<HonestUtilityElement>(entry.key)) {
			entry_json["honest_utility"] = parse_honest_utility_element(input, std::get<HonestUtilityElement>(entry.key));
		} else {
			// weak(er) immunity and practicality without honest history
			entry_json["no_honest_history"] = true;
		}
		entry_json["subtree"] = subtree2json(input, entry.result);
		result.push_back(entry_json);
	}

	std::ofstream output_file(file_name);
	if (!output_file.is_open()) {
		std::cerr << "checkmate: failed to create " << file_name << std::endl;
		std::exit(EXIT_FAILURE);
	}
	output_file << result.dump(4) << std::endl;
	std::cout << "Subtree results written to " << file_name << std::endl;
}
