#ifndef __checkmate_property_checks__
#define __checkmate_property_checks__

#include <cstdint>
#include <iostream>
#include <sstream>

#include "input.hpp"
#include "utils.hpp"

// the checks of the single properties for the honest history currently marked in `input`
// (or no honest history, if none is marked)

// ComputeCWI (Algorithm 1): the constraints under which the game is weak immune for `player`
// (`weaker`: weaker immunity, on the real parts of the utilities); in weak_immunity.cpp
z3::Bool computeCWI(const Input &input, unsigned player, bool weaker);

// ComputeCCR (Algorithm 2): the constraints under which the game is collusion resilient against all supergroups
// of `group` (bitset over the players), given the conditions `cond` so far, compared to the honest utilities `ustar`;
// in collusion_resilience.cpp
z3::Bool computeCCR(const Input &input, const UtilityTuplesSet &ustar, const z3::Bool &cond, uint64_t group);

// practicality; in practicality.cpp
bool computeCPR(const Input &input);

// IC for checking `property`: the initial constraints together with the constraints of the property
inline z3::Bool property_constraints(const Input &input, PropertyType property) {
	switch (property) {
		case PropertyType::WeakImmunity:
			return input.initial_constraint && input.weak_immunity_constraint;
		case PropertyType::WeakerImmunity:
			return input.initial_constraint && input.weaker_immunity_constraint;
		case PropertyType::CollusionResilience:
			return input.initial_constraint && input.collusion_resilience_constraint;
		case PropertyType::Practicality:
			return input.initial_constraint && input.practicality_constraint;
	}
	return input.initial_constraint;
}

// Check(IC ∧ ¬result) = sat: for some values satisfying `ic`, the property described by `result` does not hold
inline bool violated_somewhere(const z3::Bool &ic, const z3::Bool &result) {
	z3::Solver solver;
	solver.assert_(ic);
	return solver.solve({!result}) == z3::Result::SAT;
}

// Check(IC ∧ result) = sat: for some values satisfying `ic`, the property described by `result` holds;
// no answer if Z3 cannot decide it within `timeout` milliseconds
inline std::optional<bool> holds_somewhere(const z3::Bool &ic, const z3::Bool &result, unsigned timeout) {
	z3::Solver solver;
	solver.assert_(ic);
	std::optional<z3::Result> answer = solver.solve_within({result}, timeout);
	if (!answer) {
		return std::nullopt;
	}
	return *answer == z3::Result::SAT;
}

// for checks that are not written yet: stop instead of returning a result that looks real
[[noreturn]] inline void not_implemented(const char *what) {
	std::cerr << "checkmate: " << what << " is not implemented yet" << std::endl;
	std::exit(EXIT_FAILURE);
}

[[noreturn]] inline void not_implemented(PropertyType property) {
	std::stringstream what;
	what << "checking " << property;
	not_implemented(what.str().c_str());
}

#endif
