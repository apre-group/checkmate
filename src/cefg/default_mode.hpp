#ifndef __checkmate_cefg_default_mode__
#define __checkmate_cefg_default_mode__

#include <optional>
#include <string>

#include "input.hpp"
#include "options.hpp"
#include "../json.hpp"

// imported from the cefg branch (c9c6e6f); wrapped in namespace cefg next to the EFG engine in src/
namespace cefg {

// analyse the chosen properties in default mode, with `ustar` the honest utilities (only needed for collusion resilience);
// for --json-out, one entry per property is appended to `results`: `run` (what was analysed) with the verdict added
void default_mode(const Options &options, const Input &input, const UtilityTuplesSet &ustar,
	nlohmann::json &results, const nlohmann::json &run);

// whether the game satisfies `property` for the honest history currently marked in `input`,
// with `ustar` the honest utilities (only needed for collusion resilience);
// no answer if it could not be decided (only for practicality, see selectors.hpp), with the reason in `undecided`
std::optional<bool> satisfiesProperty(const Input &input, const UtilityTuplesSet &ustar, PropertyType property,
	std::string &undecided);

} // namespace cefg

#endif
