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
	// parsed input
	const Input &input;
	// underlying Z3 solver
	z3::Solver solver;
	// list of assumptions that could appear in unsat cores
	std::vector<z3::Bool> assumptions;

	// assert that exactly one action must be taken
	void add_action_constraints();
	// solve an unquantified `property` under `honest_history`
	void solve(z3::Bool property, z3::Bool honest_history);

	// produce a fresh (or cached) label for `expr` and return `label => expr`
	z3::Bool label(z3::Bool expr);
	// produce a labelled version of `left >= right`
	z3::Bool label_geq(Utility left, Utility right);

	// label-to-expression map
	std::unordered_map<z3::Bool, z3::Bool> label2expr;
	// expression-to-label map
	std::unordered_map<z3::Bool, z3::Bool> expr2label;
};

#endif
