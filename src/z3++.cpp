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

bool MinimalCores::more() {
	while(map.solve() == Result::SAT) {
		auto model = map.model();
		std::vector<Bool> seed;
		for(auto label : labels)
			if(!model.assigns<false>(label))
				seed.push_back(label);

		if(solver.solve(seed) == Result::SAT) {
			std::unordered_set<Bool> mss(seed.begin(), seed.end());
			std::vector<Bool> complement;
			for(auto label: labels) {
				if(mss.count(label))
					continue;
				seed.push_back(label);
				if(solver.solve(seed) == Result::UNSAT) {
					complement.push_back(label);
					seed.pop_back();
				}
			}
			std::cout << "mss: " << seed << std::endl;
			map.assert_(disjunction(complement));
		}
		else {
			auto candidate = solver.unsat_core();
			core.clear();
			for(unsigned i = 0; i < candidate.size(); i++) {
				auto discard = candidate[i];
				if(ignore.count(discard))
					continue;

				core.push_back(discard);
				/*
				candidate[i] = Bool::TRUE;
				if(solver.solve(candidate) == Result::SAT) {
					seed[i] = discard;
					core.push_back(discard);
				}
				*/
			}
			std::cout << "mus: " << core << std::endl;
			map.assert_(!conjunction(core));
			return true;
		}
	}
	return false;
}
/*
// MARCO algorithm for all unsat cores
bool Cores::more() {
	while(map.solve() == Result::SAT) {
		auto model = map.model();
		std::vector<Bool> seed;
		for(auto label : labels)
			if(!model.assigns<false>(label))
				seed.push_back(label);

		std::cout << "seed: " << seed << std::endl;
		if(solver.solve(seed) == Result::SAT) {
			std::unordered_set<Bool> mss(seed.begin(), seed.end());
			std::unordered_set<Bool> ps, backbones;
			for(auto label : labels)
				if(!mss.count(label))
					ps.insert(label);

			while(!ps.empty()) {
				std::cout << "ps: " << ps << std::endl;
				std::cout << "mss: " << mss << std::endl;
				std::cout << "backbones: " << backbones << std::endl;
				auto p = *ps.begin();
				std::cout << "p: " << p << std::endl;
				ps.erase(ps.begin());
				std::vector<Bool> combination(mss.begin(), mss.end());
				for(auto backbone : backbones)
					combination.push_back(backbone);
				combination.push_back(p);
				if(solver.solve(combination) == Result::SAT) {
					mss.insert(p);
					auto satisfying_model = solver.model();
					for(auto q : ps)
						if(satisfying_model.assigns<true>(q))
							mss.insert(q);
					for(auto it = ps.begin(); it != ps.end();)
						if(mss.count(*it))
							it = ps.erase(it);
						else
							++it;
				}
				else
					backbones.insert(!p);
			}
			std::cout << "final mss: " << mss << std::endl;
			std::vector<Bool> complement;
			for(auto label: labels)
				if(!mss.count(label))
					complement.push_back(label);
			std::cout << "complement: " << complement << std::endl;
			map.assert_(disjunction(complement));
		}
		else {
			std::cout << "unsat" << std::endl;
			__builtin_trap();
		}
	}
	return false;
}
*/

}
