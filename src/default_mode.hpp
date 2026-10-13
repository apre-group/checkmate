#ifndef __checkmate_default_mode__
#define __checkmate_default_mode__

#include "input.hpp"
#include "options.hpp"

// analyse the chosen properties in default mode, with `ustar` the honest utilities (only needed for collusion resilience)
void default_mode(const Options &options, const Input &input, const UtilityTuplesSet &ustar);

#endif
