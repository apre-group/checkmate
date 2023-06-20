#ifndef __checkmate_weak_immunity__
#define __checkmate_weak_immunity__

#include "solver.hpp"

template<bool weaker>
z3::Bool weak_immunity(const Input &input, Labels &labels);

#endif
