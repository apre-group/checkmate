#ifndef __checkmate_default_mode__
#define __checkmate_default_mode__

#include <optional>
#include <string>

#include "input.hpp"
#include "options.hpp"

// analyse the chosen properties in default mode, with `ustar` the honest utilities (only needed for collusion resilience)
void default_mode(const Options &options, const Input &input, const UtilityTuplesSet &ustar);

// whether the game satisfies `property` for the honest history currently marked in `input`,
// with `ustar` the honest utilities (only needed for collusion resilience);
// no answer if it could not be decided (only for practicality, see selectors.hpp), with the reason in `undecided`
std::optional<bool> satisfiesProperty(const Input &input, const UtilityTuplesSet &ustar, PropertyType property,
	std::string &undecided);

#endif
