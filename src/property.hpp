#ifndef __checkmate_property__
#define __checkmate_property__

#include "input.hpp"
#include "z3++.hpp"

template<bool weaker>
void weak_immunity(const Input &input);
void collusion_resilience(const Input &input);
void practicality(const Input &input);

#endif
