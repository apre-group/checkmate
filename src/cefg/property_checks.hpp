#ifndef __checkmate_cefg_property_checks__
#define __checkmate_cefg_property_checks__

#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <sstream>
#include <unordered_set>
#include <utility>

#include "input.hpp"
#include "../utils.hpp"

// imported from the cefg branch (c9c6e6f); wrapped in namespace cefg next to the EFG engine in src/
namespace cefg {

// the checks of the single properties for the honest history currently marked in `input`
// (or no honest history, if none is marked)

// the constants still unknown at a node: unknown at the root and not revealed on the way (`known_unknowns`)
inline std::vector<z3::Real> still_unknown(const Input &input, const std::unordered_set<std::string> &known_unknowns) {
	std::vector<z3::Real> unknown;
	for (const std::string &name : input.unknowns) {
		if (!known_unknowns.count(name)) {
			unknown.push_back(z3::Real::constant(name));
		}
	}
	return unknown;
}

// ComputeCWI (Algorithm 1): the constraints under which the game at `node` is weak immune for `player`,
// given the initial constraints `ic` (`weaker`: weaker immunity, on the real parts of the utilities);
// `known_unknowns` are the constants unknown at the root that were revealed on the way to `node`; in weak_immunity.cpp
z3::Bool computeCWI(const Input &input, const Node *node, const z3::Bool &ic, unsigned player, bool weaker,
	const std::unordered_set<std::string> &known_unknowns = {});

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
// of `group` (bitset over the players), given the initial constraints `ic` and the conditions `cond` on the way to `node`,
// compared to the honest utilities `ustar`; `known_unknowns` are the constants unknown at the root that were revealed
// on the way to `node` (only the leaves need them, to quantify over the ones still unknown); in collusion_resilience.cpp
z3::Bool computeCCR(const Input &input, const Node *node, const UtilityTuplesSet &ustar, const z3::Bool &ic, const z3::Bool &cond,
	uint64_t group, CrCache &cache, const std::unordered_set<std::string> &known_unknowns = {});

// a utility of a leaf with its liveness condition (Definition 4.23): live for the values of the unknowns satisfying `live`
// (`utility` points into the tree or a subtree result, so the input must outlive it)
struct LiveUtility {
	const std::vector<Utility> *utility;
	z3::Bool live;
};

// a conditional utility set that is a rationalizable utility set (Definition 4.24) under `constraint`
// on the constants known where it was computed
struct DomCandidate {
	z3::Bool constraint;
	std::vector<LiveUtility> utilities;
};

// ComputeDom (Algorithm 3): the rationalizable utility sets of the game at `node` off the honest history, each with the
// constraint under which it is one, given the initial constraints `ic` and the conditions `cond` on the way to `node`;
// `known_unknowns` as for computeCCR; at condition nodes, candidates are selected by selectors (see selectors.hpp),
// which may occur in the constraints and liveness conditions; in practicality.cpp
std::vector<DomCandidate> computeDom(const Input &input, const Node *node, const z3::Bool &ic, const z3::Bool &cond,
	const std::unordered_set<std::string> &known_unknowns = {});

// ComputeCPR (Algorithm 4): the constraints under which the game at `node` along the honest history is practical,
// given the initial constraints `ic` and the conditions `cond` on the way to `node`, compared to the honest utilities `ustar`;
// `known_unknowns` as for computeCCR; in practicality.cpp
z3::Bool computeCPR(const Input &input, const Node *node, const UtilityTuplesSet &ustar, const z3::Bool &ic, const z3::Bool &cond,
	const std::unordered_set<std::string> &known_unknowns = {});

// IC for checking `property`: the initial constraints together with the constraints of the property
inline z3::Bool property_constraints(const Input &input, PropertyType property) {
	switch (property) {
		case PropertyType::WeakImmunity:
			return all_of({input.initial_constraint, input.weak_immunity_constraint});
		case PropertyType::WeakerImmunity:
			return all_of({input.initial_constraint, input.weaker_immunity_constraint});
		case PropertyType::CollusionResilience:
			return all_of({input.initial_constraint, input.collusion_resilience_constraint});
		case PropertyType::Practicality:
			return all_of({input.initial_constraint, input.practicality_constraint});
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

} // namespace cefg

#endif
