#ifndef __checkmate_property_checks__
#define __checkmate_property_checks__

#include <cstdint>
#include <iostream>
#include <map>
#include <sstream>
#include <unordered_set>
#include <utility>

#include "input.hpp"
#include "utils.hpp"

// the checks of the single properties for the honest history currently marked in `input`
// (or no honest history, if none is marked)

// ComputeCWI (Algorithm 1): the constraints under which the game at `node` is weak immune for `player`,
// given the initial constraints `ic` (`weaker`: weaker immunity, on the real parts of the utilities); in weak_immunity.cpp
z3::Bool computeCWI(const Input &input, const Node *node, const z3::Bool &ic, unsigned player, bool weaker);

// conjunction/disjunction that leave out neutral and stop at dominating constants, to keep the results readable
inline z3::Bool all_of(const std::vector<z3::Bool> &conjuncts) {
	std::vector<z3::Bool> kept;
	for (const z3::Bool &conjunct : conjuncts) {
		if (conjunct.is(z3::Bool(false))) {
			return z3::Bool(false);
		}
		if (!conjunct.is(z3::Bool(true))) {
			kept.push_back(conjunct);
		}
	}
	return kept.empty() ? z3::Bool(true) : z3::conjunction(kept);
}

inline z3::Bool any_of(const std::vector<z3::Bool> &disjuncts) {
	std::vector<z3::Bool> kept;
	for (const z3::Bool &disjunct : disjuncts) {
		if (disjunct.is(z3::Bool(true))) {
			return z3::Bool(true);
		}
		if (!disjunct.is(z3::Bool(false))) {
			kept.push_back(disjunct);
		}
	}
	return kept.empty() ? z3::Bool(false) : z3::disjunction(kept);
}

// results of computeCCR within one run, i.e. for a fixed honest history, honest utilities and initial constraints:
// keep it for all groups of a run, as they share many subresults, and start a new one for the next run
struct CrCache {
	// the result for a node and a group (the path to a node is unique, so the conditions and revealed constants are fixed)
	std::map<std::pair<const Node *, uint64_t>, z3::Bool> results;
	// the entry used for a subtree node off the honest history: the one for the current honest utilities
	std::map<const Subtree *, const SubtreeEntry *> subtree_entries;
};

// ComputeCCR (Algorithm 2): the constraints under which the game at `node` is collusion resilient against all supergroups
// of `group` (bitset over the players), given the initial constraints `ic`, the conditions `cond` on the way to `node` and
// the unknown constants `revealed` on the way to `node`, compared to the honest utilities `ustar`; in collusion_resilience.cpp
z3::Bool computeCCR(const Input &input, const Node *node, const UtilityTuplesSet &ustar, const z3::Bool &ic, const z3::Bool &cond,
	uint64_t group, CrCache &cache, const std::unordered_set<std::string> &revealed = {});

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
