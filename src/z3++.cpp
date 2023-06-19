#include "z3++.hpp"

namespace z3 {

Z3_context CONTEXT = Z3_mk_context(Z3_mk_config());

Z3_sort Expression::BOOL_SORT = Z3_mk_bool_sort(CONTEXT);
Z3_sort Expression::REAL_SORT = Z3_mk_real_sort(CONTEXT);

unsigned Bool::FRESH_INDEX = 0;
std::vector<int> Bool::ONES;

Real Real::ZERO = Real::value(0);
Real Real::ONE = Real::value(1);

}
