#include "z3++.hpp"

namespace z3 {

Z3_context CONTEXT;

struct Global {
	Global() {
		// TODO should we try and minimize unsat cores?
		//Z3_global_param_set("sat.core.minimize", "true");
		//Z3_global_param_set("smt.core.minimize", "true");
		CONTEXT = Z3_mk_context(Z3_mk_config());
		check_error();
	}

	~Global() {
		Z3_del_context(CONTEXT);
	}
};
struct Global GLOBAL;

Z3_sort Expression::BOOL_SORT = Z3_mk_bool_sort(CONTEXT);
Z3_sort Expression::REAL_SORT = Z3_mk_real_sort(CONTEXT);

Bool Bool::FALSE = Bool::value(false);
Bool Bool::TRUE = Bool::value(true);

unsigned Bool::FRESH_INDEX = 0;
std::vector<int> Bool::ONES;

Real Real::ZERO = Real::value(0);
Real Real::ONE = Real::value(1);

}
