#ifndef __checkmate_solver__
#define __checkmate_solver__

#include <iostream>

#include "input.hpp"
#include "utils.hpp"
#include "z3++.hpp"

class Labels {
public:
	Labels(z3::Solver &solver) : solver(solver) {}

	void clear() {
		label2expr.clear();
		expr2label.clear();
	}

	z3::Bool label(z3::Bool expr) {
		z3::Bool &cached_label = expr2label[expr.id()];
		if(!cached_label.null())
			return cached_label;

		z3::Bool label = z3::Bool::fresh();
		solver.assert_(label);
		label2expr[label.id()] = expr;
		cached_label = label;
		return label;
	}

	z3::Bool lookup(z3::Bool label) const { return label2expr.at(label.id()); }

private:
	z3::Solver &solver;
	std::unordered_map<unsigned, z3::Bool> label2expr, expr2label;
};

class Solver {
public:
	Solver(const Input &input);

	template<typename Property>
	void solve(Property property) {
		auto deferred = defer([&] {
			labels.clear();
			solver.pop();
		});

		solver.push();
		z3::Bool computed = property(input, labels);
		solve(computed);
	}

private:
	void add_action_constraints(const Branch &branch);
	void solve(z3::Bool property);

	const Input &input;
	z3::Solver solver;
	Labels labels;
};

#endif
