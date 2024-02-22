#include <iostream>
#include <unordered_set>

#include "utils.hpp"
#include "z3++.hpp"

namespace z3 {

	// the only Z3 context - mostly just hangs out here to be passed to the Z3 API
	Z3_context CONTEXT;

	// thing constructed on program start to create a Z3 context
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
	} GLOBAL;

	Z3_sort Expression::BOOL_SORT = Z3_mk_bool_sort(CONTEXT);
	Z3_sort Expression::REAL_SORT = Z3_mk_real_sort(CONTEXT);

	Bool Bool::FALSE = Bool::value(false);
	Bool Bool::TRUE = Bool::value(true);

	unsigned Bool::FRESH_INDEX = 0;
	std::vector<int> Bool::ONES;

	Real Real::ZERO = Real::value(0);
	Real Real::ONE = Real::value(1);

	// MARCO algorithm for unsat cores
	// https://sun.iwu.edu/~mliffito/marco-viz/
	bool MinimalCores::next_core() {
		while (map.solve() == Result::SAT) {
			auto model = map.model();
			std::vector<Bool> seed;
			for (auto label: labels)
				if (!model.assigns<false>(label))
					seed.push_back(label);

			std::unordered_set<Bool> relevant(seed.begin(), seed.end());
			// the seed doesn't say enough to cause unsat
			if (solver.solve(seed) == Result::SAT) {
				// grow it as much as possible...
				std::vector<Bool> complement;
				for (auto label: labels) {
					if (relevant.count(label))
						continue;
					seed.push_back(label);
					if (solver.solve(seed) == Result::UNSAT) {
						complement.push_back(label);
						seed.pop_back();
					}
				}
				// ...then assert that one of the other labels must be true
				map.assert_(disjunction(complement));
				// to be removed
				std::cout << "\t(Found maximal satisfying subset, continuing...)" << std::endl;
			}
				// the seed contains an unsat core
			else {
				// get what Z3 thinks is an unsat core
				core.clear();
				for (auto label: solver.unsat_core())
					if (relevant.count(label))
						core.push_back(label);

				// NB currently buggy, seems to sometimes return an insufficient unsat core
				if (solver.solve(core) == Result::SAT) {
					std::cout << "\t(Z3 bug, retrying...)" << std::endl;
					// try again?
					continue;
				}

				// minimising the unsat core does not seem to pay off, most of the time
				// put behind a command-line option?
				/*
				// shrink it...
				for(unsigned i = 0; i < core.size();) {
					auto discard = core[i];
					auto end = core[core.size() - 1];
					core[i] = end;
					core.pop_back();
					if(solver.solve(core) == Result::SAT) {
						core.push_back(end);
						core[i++] = discard;
					}
				}
				std::cout << "minimised to: " << core.size() << std::endl;
				*/
				// ...then assert that we want a different core next time
				map.assert_(!conjunction(core));
				return true;
			}
		}
		return false;
	}

}
