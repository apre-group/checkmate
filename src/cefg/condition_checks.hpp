#ifndef __checkmate_cefg_condition_checks__
#define __checkmate_cefg_condition_checks__

#include "input.hpp"
#include "options.hpp"

namespace cefg {

// Check that the conditions of every condition node are mutually exclusive and leave no gap, given the initial
// constraints, the constraints of each analysed property and the conditions on the way to the node (Definition 3.3 of
// the paper). The constraints may rule out some conditions of a node (with a note), but not all of them.
// Exits the program with an error if a check fails; warns if Z3 cannot decide a check.
void check_conditions(const Input &input, const Options &options);

} // namespace cefg

#endif
