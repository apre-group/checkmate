#include <fstream>
#include <sstream>

#include "subtree_mode.hpp"

using json = nlohmann::json;

// TODO: placeholder, only reports what would be checked and returns empty results
Subtree subtree_mode(const Options &options, [[maybe_unused]] const Input &input, const UtilityTuplesSet &ustar) {
	std::vector<std::pair<bool, std::string>> properties = {
		{options.weak_immunity, "weak immunity"},
		{options.weaker_immunity, "weaker immunity"},
		{options.collusion_resilience, "collusion resilience"},
		{options.practicality, "practicality"}
	};
	for (const auto &property : properties) {
		if (property.first) {
			std::cout << "\twould check " << property.second << std::endl;
		}
	}
	if (options.collusion_resilience) {
		std::cout << "\thonest utilities:" << std::endl;
		for (const UtilityTuple &utility : ustar) {
			std::cout << "\t\t" << utility.leaf << " if " << utility.condition << std::endl;
		}
	}
	return Subtree({}, {}, {}, {}, std::vector<Utility>());
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

json subtree2json(const Input &input, const Subtree &subtree) {
	json subtree_json;
	subtree_json["weak_immunity"] = parse_property_to_json(subtree.weak_immunity);
	subtree_json["weaker_immunity"] = parse_property_to_json(subtree.weaker_immunity);
	subtree_json["collusion_resilience"] = parse_property_to_json(subtree.collusion_resilience);
	subtree_json["practicality"] = parse_practicality_property_to_json(input, subtree.practicality);
	// only subtrees along the honest history have an honest utility;
	// leave it out otherwise, the parser rejects an empty one and defaults to empty if it is missing
	bool no_honest_utility = std::holds_alternative<std::vector<Utility>>(subtree.honest_utility)
		&& std::get<std::vector<Utility>>(subtree.honest_utility).empty();
	if (!no_honest_utility) {
		subtree_json["honest_utility"] = parse_honest_utility_element(input, subtree.honest_utility);
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
