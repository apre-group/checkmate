#include <iostream>

#include "solver.hpp"

Solver::Solver(const Input &input) : input(input), labels(solver) {
	if(input.root->is_branch())
		add_action_constraints(input.root->branch());
}

void Solver::add_action_constraints(const Branch &branch) {
	std::vector<z3::Bool> actions;
	for(const Choice &choice : branch.choices) {
		actions.push_back(choice.action.variable);
		if(choice.tree->is_branch())
			add_action_constraints(choice.tree->branch());
	}
	solver.assert_(z3::Bool::exactly_one(actions));
}

void Solver::solve(z3::Bool property) {
	z3::Bool with_initial = input.initial_constraint.implies(property);
	z3::Bool quantified = z3::Bool::forall(input.constants, with_initial);
	solver.assert_(quantified);

	for(unsigned i = 0; i < input.honest_histories.size(); i++) {
		std::cout << "honest history #" << i + 1 << std::endl;
		std::cout << solver.solve_assuming(input.honest_histories[i]) << std::endl;
	}
}


