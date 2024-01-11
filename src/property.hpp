#ifndef __checkmate_property__
#define __checkmate_property__

#include "input.hpp"
#include "options.hpp"

template<bool weaker>
void weak_immunity(const Options &options, const Input &input);
void collusion_resilience(const Input &input);
void practicality(const Input &input);

#endif
