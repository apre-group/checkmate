#include <iostream>

#include "solver.hpp"

GeneralSolver::GeneralSolver(const Input &input) : input(input)
{
	if(input.root->is_branch())
		add_action_constraints(input.root->branch());
}

void GeneralSolver::add_action_constraints(const Branch &branch) {
	std::vector<z3::Bool> actions;
	for(const Choice &choice : branch.choices) {
		actions.push_back(choice.action.variable);
		if(choice.tree->is_branch())
			add_action_constraints(choice.tree->branch());
	}
	solver.assert_(z3::Bool::exactly_one(actions));
}
