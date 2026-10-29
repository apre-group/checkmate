#ifndef __checkmate_cefg_subtree_mode__
#define __checkmate_cefg_subtree_mode__

#include <string>
#include <variant>
#include <vector>

#include "input.hpp"
#include "options.hpp"
#include "../json.hpp"

// imported from the cefg branch (c9c6e6f); wrapped in namespace cefg next to the EFG engine in src/
namespace cefg {

// one entry of the data collected in subtree mode: what the result belongs to (see SubtreeEntryKey) and the result;
// an honest history is continued inside the subtree nodes it ends in, by the honest histories considered there
struct SubtreeData {
	SubtreeEntryKey key;
	SubtreeResults result;
};

// analyse the chosen properties in subtree mode, with `ustar` the honest utilities (only needed for collusion resilience)
SubtreeResults subtree_mode(const Options &options, const Input &input, const UtilityTuplesSet &ustar);

// all collected subtree results as a list of keyed entries {honest_history | honest_utility | no_honest_history, subtree},
// which as a whole can be the value of a "subtree" node in a supertree
nlohmann::json data2json(const Input &input, const std::vector<SubtreeData> &data);

// write `document` to `file_name`, exits the program on failure
void write_json(const nlohmann::json &document, const std::string &file_name);

// an honest history in the input format: actions, and lists of {condition, path} at condition nodes
nlohmann::json history2json(const HonestHistory &history);

// JSON conversion of (parts of) subtree results
nlohmann::json parse_sat_case(std::vector<z3::Bool> sat_case);
nlohmann::json parse_utility(const Input &input, std::vector<Utility> utility_to_parse);
nlohmann::json parse_honest_utility_element(const Input &input, const HonestUtilityElement &element);
nlohmann::json parse_property_to_json(std::vector<SubtreeResult> property_result);
nlohmann::json parse_practicality_property_to_json(const Input &input, std::vector<PracticalitySubtreeResult> property_result);
nlohmann::json subtree2json(const Input &input, const SubtreeResults &results);

} // namespace cefg

#endif
