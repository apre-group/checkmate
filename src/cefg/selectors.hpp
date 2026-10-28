#ifndef __checkmate_cefg_selectors__
#define __checkmate_cefg_selectors__

#include <optional>
#include <string>
#include <vector>

#include "input.hpp"

// imported from the cefg branch (c9c6e6f); wrapped in namespace cefg next to the EFG engine in src/
namespace cefg {

/*
 * Selectors for practicality (ComputeDom and ComputeCPR in the paper, Section 5.1).
 *
 * A rationalizable utility set of a condition node may select a candidate of the subgame after an edge by an arbitrary
 * function of the revealed values. Such a selection is represented by a selector: a fresh uninterpreted function symbol
 * over the constants known after the edge, whose value k says that the k-th candidate is selected.
 * The selectors are quantified existentially at the very end: the game is practical iff
 *     ∀ constants known at the root (IC → result)
 * is satisfiable with the selectors as uninterpreted function symbols.
 */

// a fresh selector over `arguments` (the constants known after the edge), choosing among `candidates` candidates
class Selector {
public:
	Selector(const std::vector<z3::Real> &arguments, unsigned candidates);

	// the formula "the k-th candidate is selected", for k = 1, ..., candidates
	z3::Bool selects(unsigned k) const;

private:
	Z3_ast application;
};

// a fresh selector symbol with `arity` real arguments, choosing among `candidates` candidates
// (e.g. for the selectors in the results of a subtree, which are renamed apart from all others)
Z3_func_decl fresh_selector(unsigned arity, unsigned candidates);

// does `formula` contain a selector?
bool contains_selectors(const z3::Bool &formula);

// Check(formula) = sat with Z3's general solver, which also handles the selectors as uninterpreted function symbols well;
// no answer if it cannot decide it within `timeout` milliseconds
std::optional<bool> satisfiable_within(const z3::Bool &formula, unsigned timeout);

// the answer of a check that may not be decided
enum class Answer { YES, NO, UNKNOWN };

// the final check of practicality (SatisfiesProperty) for `result` = ComputeCPR at the root under the initial constraints `ic`:
// 1. every selector that only occurs under one quantifier scope is replaced by a quantifier over its value,
// 2. Z3 decides the remaining formula, with the remaining selectors as uninterpreted function symbols, within a timeout,
// 3. if Z3 cannot decide it, cvc5 tries to synthesize the remaining selectors (SyGuS), within 20 minutes;
// cvc5 is called as `cvc5`, or as given in the environment variable CHECKMATE_CVC5;
// `how` describes which step decided, or why nothing did
Answer check_practicality(const Input &input, const z3::Bool &ic, const z3::Bool &result, std::string &how);

} // namespace cefg

#endif
