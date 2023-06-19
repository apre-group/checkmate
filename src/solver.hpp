#ifndef __checkmate_solver__
#define __checkmate_solver__

#include <iostream>

#include "input.hpp"
#include "z3++.hpp"

class GeneralSolver {
public:
	GeneralSolver(const Input &input);
protected:
	void add_action_constraints(const Branch &branch);
	const Input &input;
	z3::Solver solver;
};

template<typename Property>
class Solver final: public GeneralSolver {
public:
	Solver(const Input &input) :
		GeneralSolver(input),
		property(input)
	{}

	void solve() {
		solver.assert_(input.honest_histories[0]);
		z3::Bool with_initial = input.initial_constraint.implies(property.computed);
		z3::Bool quantified = z3::Bool::forall(input.constants, with_initial);
		solver.assert_(quantified);
		z3::Result result = solver.solve();
		std::cout << result << std::endl;
	}
private:
	Property property;
};

#endif
