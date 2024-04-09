#ifndef __checkmate_z3pp__
#define __checkmate_z3pp__

/**
 * Our own wrapper around the Z3 C API
 *
 * Z3 has a similar C++ wrapper, but it doesn't suit our purposes very well.
 * This should be quite small and easy to maintain.
 **/

#include <cassert>
#include <ostream>
#include <string>
#include <vector>
#include <unordered_map>

#include "z3.h"

namespace z3 {
	// the only Z3 context we use
	extern Z3_context CONTEXT;

	// check for Z3 errors in debug mode
	inline void check_error() {
		assert(Z3_get_error_code(CONTEXT) == Z3_OK);
	}

	class Solver;
	class Model;
	class Bool;
	class Real;

	// base class for Real and Bool: trivially-copyable, just wraps a pointer
	class Expression {
		// Solver wants to access `ast`
		friend Solver;

	public:
		Expression() = default;

		// does this point to a valid expression?
		inline bool null() const { return ast == nullptr; }

		// is this expression exactly the same as `other`?
		inline bool is(Expression other) const { return ast == other.ast; }

		// Z3's internal ID for this AST
		inline unsigned id() const {
			unsigned result = Z3_get_ast_id(CONTEXT, ast);
			check_error();
			return result;
		}

		// invoke Z3's internal printer
		friend std::ostream &operator<<(std::ostream &out, Expression expr) {
			std::ostream &result = out << Z3_ast_to_string(CONTEXT, expr.ast);
			check_error();
			return result;
		}

	protected:
		// wrap `ast`
		Expression(Z3_ast ast) : ast(ast) {}

		// are we of Boolean sort? moderately expensive so protected
		bool is_bool() {
			Z3_sort sort = Z3_get_sort(CONTEXT, ast);
			check_error();
			return sort == BOOL_SORT;
		}

		// are we of real sort? moderately expensive so protected
		bool is_real() {
			Z3_sort sort = Z3_get_sort(CONTEXT, ast);
			check_error();
			return sort == REAL_SORT;
		}

		// pointer to Z3 AST, possibly null if default-constructed
		Z3_ast ast = nullptr;

		// Z3's Boolean sort
		static Z3_sort BOOL_SORT;
		// Z3's real sort
		static Z3_sort REAL_SORT;
	};

	// an Expression of Boolean sort, by construction
	class Bool : public Expression {
		// Real wants to construct Booleans from e.g. `x > y`
		friend Real;
		// Solver wants to construct Booleans from unsat cores
		friend Solver;
		// Model wants to construct Booleans from models
		friend Model;

	public:
		Bool() : Expression() {}

		Bool operator!() const {
			Z3_ast result = Z3_mk_not(CONTEXT, ast);
			check_error();
			return result;
		}

		Bool operator&&(Bool other) const {
			Z3_ast conjuncts[2]{ast, other.ast};
			Z3_ast result = Z3_mk_and(CONTEXT, 2, conjuncts);
			check_error();
			return result;
		}

		static Bool conjunction(const std::vector<Bool> &conjuncts) {
			Z3_ast result = Z3_mk_and(
				CONTEXT,
				conjuncts.size(),
				// safety: Z3_ast should have the same size/alignment as Bool
				reinterpret_cast<const Z3_ast *>(conjuncts.data())
			);
			check_error();
			return result;
		}

		Bool operator||(Bool other) const {
			Z3_ast disjuncts[2]{ast, other.ast};
			Z3_ast result = Z3_mk_or(CONTEXT, 2, disjuncts);
			check_error();
			return result;
		}

		Bool implies(Bool other) const {
			Z3_ast result = Z3_mk_implies(CONTEXT, ast, other.ast);
			check_error();
			return result;
		}

	private:
		Bool(Z3_ast ast) : Expression(ast) { assert(is_bool()); }
	};
	// we reinterpret_cast Bool to Z3_ast sometimes for performance reasons
	static_assert(
		sizeof(Bool) == sizeof(Z3_ast),
		"the size of Bool must be equal to that of Z3_ast to allow cast magic"
	);

	inline Bool conjunction(const std::vector<Bool> &conjuncts) { return Bool::conjunction(conjuncts); }

	// Expression of real sort by construction
	class Real : public Expression {
	public:
		Real() : Expression() {}

		// construct an integer-valued real expression
		static Real value(unsigned number) {
			Z3_ast result = Z3_mk_real(CONTEXT, number, 1);
			check_error();
			return result;
		}

		// construct a real value from a string
		static Real value(const std::string &number) {
			Z3_ast result = Z3_mk_numeral(CONTEXT, number.c_str(), REAL_SORT);
			check_error();
			return result;
		}

		// construct a real constant
		static Real constant(const std::string &name) {
			Z3_symbol symbol = Z3_mk_string_symbol(CONTEXT, name.c_str());
			check_error();
			Z3_ast constant = Z3_mk_const(CONTEXT, symbol, REAL_SORT);
			check_error();
			return constant;
		}

		Real operator+(Real other) const {
			if (is(ZERO))
				return other;
			if (other.is(ZERO))
				return *this;

			Z3_ast args[2] = {ast, other.ast};
			Z3_ast result = Z3_mk_add(CONTEXT, 2, args);
			check_error();
			return result;
		}

		Real operator-() const {
			if (is(ZERO))
				return *this;

			Z3_ast result = Z3_mk_unary_minus(CONTEXT, ast);
			check_error();
			return result;
		}

		Real operator-(Real other) const {
			if (other.is(ZERO))
				return *this;
			if (is(ZERO))
				return -other;

			Z3_ast args[2] = {ast, other.ast};
			Z3_ast result = Z3_mk_sub(CONTEXT, 2, args);
			check_error();
			return result;
		}

		Real operator*(Real other) const {
			if (is(ZERO) || other.is(ZERO))
				return ZERO;

			Z3_ast args[2] = {ast, other.ast};
			Z3_ast result = Z3_mk_mul(CONTEXT, 2, args);
			check_error();
			return result;
		}

		Bool operator==(Real other) const {
			Z3_ast result = Z3_mk_eq(CONTEXT, ast, other.ast);
			check_error();
			return result;
		}

		Bool operator!=(Real other) const {
			Z3_ast args[2] = {ast, other.ast};
			Z3_ast result = Z3_mk_distinct(CONTEXT, 2, args);
			check_error();
			return result;
		}

		Bool operator>(Real other) const {
			Z3_ast result = Z3_mk_gt(CONTEXT, ast, other.ast);
			check_error();
			return result;
		}

		Bool operator<(Real other) const {
			Z3_ast result = Z3_mk_lt(CONTEXT, ast, other.ast);
			check_error();
			return result;
		}

		Bool operator>=(Real other) const {
			Z3_ast result = Z3_mk_ge(CONTEXT, ast, other.ast);
			check_error();
			return result;
		}

		Bool operator<=(Real other) const {
			Z3_ast result = Z3_mk_le(CONTEXT, ast, other.ast);
			check_error();
			return result;
		}

		// zero constant
		static Real ZERO;

	private:
		Real(Z3_ast ast) : Expression(ast) { assert(is_real()); }
	};

	// possible results from a `solve()` call
	enum class Result {
		SAT,
		UNSAT
	};

	inline std::ostream &operator<<(std::ostream &out, Result result) {
		return out << (result == Result::SAT ? "sat" : "unsat");
	}

	// wrapper around a Z3 solver object
	class Solver {
	public:
		Solver() : solver(Z3_mk_simple_solver(CONTEXT)) {
			check_error();
			Z3_solver_inc_ref(CONTEXT, solver);
			check_error();
		}

		Solver(const Solver &) = delete;

		~Solver() {
			Z3_solver_dec_ref(CONTEXT, solver);
			check_error();
		}

		// push a new frame for assertions
		void push() {
			Z3_solver_push(CONTEXT, solver);
			check_error();
		}

		// pop the frame, forgetting everything asserted in it
		void pop() {
			Z3_solver_pop(CONTEXT, solver, 1);
			check_error();
		}

		// add to the current frame
		void assert_(Bool assertion) {
			Z3_solver_assert(CONTEXT, solver, assertion.ast);
			check_error();
		}

		// invoke the solver
		Result solve() {
			Z3_lbool result = Z3_solver_check(CONTEXT, solver);
			check_error();
			switch (result) {
				case Z3_L_FALSE:
					return Result::UNSAT;
				case Z3_L_TRUE:
					return Result::SAT;
				default:
					throw std::logic_error("Z3_solver_check() returned UNDEF - this shouldn't happen");
			}
		}

		// invoke the solver with extra `assumptions`
		Result solve(const std::vector<Bool> &assumptions) {
			Z3_lbool result = Z3_solver_check_assumptions(
					CONTEXT,
					solver,
					assumptions.size(),
					// safety: Z3_ast should have the same size/alignment as Bool
					reinterpret_cast<const Z3_ast *>(assumptions.data())
			);
			check_error();
			switch (result) {
				case Z3_L_FALSE:
					return Result::UNSAT;
				case Z3_L_TRUE:
					return Result::SAT;
				default:
					throw std::logic_error("Z3_solver_check_assumptions() returned UNDEF - this shouldn't happen");
			}
		}

		// invoke the solver with extra assumptions, using `assumptions` as a buffer for `extra` and `others`
		template<typename... BoolList>
		Result solve(std::vector<Bool> &assumptions, Bool extra, BoolList... others) {
			assumptions.push_back(extra);
			auto result = solve(assumptions, others...);
			assumptions.pop_back();
			return result;
		}

		friend std::ostream &operator<<(std::ostream &out, const Solver &solver) {
			return out << Z3_solver_to_string(CONTEXT, solver.solver);
		}

	private:
		// wrapper solver
		Z3_solver solver;
	};
}

// used in e.g. hash tables rather than operator==
template<>
struct std::equal_to<z3::Bool> {
	bool operator()(const z3::Bool &left, const z3::Bool &right) const {
		return left.is(right);
	}
};

// used in e.g. hash tables rather than operator==
template<>
struct std::equal_to<z3::Real> {
	bool operator()(const z3::Real &left, const z3::Real &right) const {
		return left.is(right);
	}
};

template<>
struct std::hash<z3::Bool> {
	size_t operator()(const z3::Bool &expr) const {
		return std::hash<unsigned>{}(expr.id());
	}
};

template<>
struct std::hash<z3::Real> {
	size_t operator()(const z3::Real &expr) const {
		return std::hash<unsigned>{}(expr.id());
	}
};

#endif
