#ifndef __checkmate_solver__
#define __checkmate_solver__

#include "input.hpp"
#include "z3++.hpp"

class Solver {
public:
	Solver(const Input &input);

	template<bool weaker> void weak_immunity();
	void collusion_resilience();
	void practicality();

private:
	const Input &input;
	z3::Solver solver;

	void add_action_constraints();
	void solve(z3::Bool property);

	z3::Bool label(z3::Bool expr);
	std::unordered_map<z3::Bool, z3::Bool> label2expr;
	std::unordered_map<z3::Bool, z3::Bool> expr2label;
};

#endif
