#ifndef __checkmate_z3pp__
#define __checkmate_z3pp__

#include <cassert>
#include <ostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <utility>

#include "z3.h"

namespace z3 {
	// the only Z3 context we use
	extern Z3_context CONTEXT;

	// check for Z3 errors in debug mode
	inline void check_error() {
		assert(Z3_get_error_code(CONTEXT) == Z3_OK);
	}

	class Solver;
	struct Bool;
	struct Real;
	// base class for Real and Bool
	struct Expression {
		friend Solver;
		Expression() : ast(nullptr) {}
		Expression(Z3_ast ast) : ast(ast) {}

		inline bool null() const { return ast == nullptr; }

		// this expression is exactly the same as another
		inline bool is(Expression other) const { return ast == other.ast; }

		// Z3's internal ID for this AST
		inline unsigned id() const {
			unsigned result = Z3_get_ast_id(CONTEXT, ast);
			check_error();
			return result;
		}

		friend std::ostream &operator<<(std::ostream &out, Expression expr) {
			std::ostream &result = out << Z3_ast_to_string(CONTEXT, expr.ast);
			check_error();
			return result;
		}

	protected:
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

		// pointer to Z3 AST: possibly null
		Z3_ast ast;

		static Z3_sort BOOL_SORT, REAL_SORT;
	};

	// Expression of Boolean sort by construction
	struct Bool: public Expression {
		friend Real;
		friend Solver;

		Bool() : Expression() {}

		// construct a fresh Boolean variable
		static Bool fresh() {
			Z3_symbol fresh = Z3_mk_int_symbol(CONTEXT, FRESH_INDEX++);
			check_error();
			Z3_ast constant = Z3_mk_const(CONTEXT, fresh, BOOL_SORT);
			check_error();
			return constant;
		}

		// construct true or false
		static Bool value(bool value) {
			Z3_ast result = value ? Z3_mk_true(CONTEXT) : Z3_mk_false(CONTEXT);
			check_error();
			return result;
		}

		Bool operator!() const {
			Z3_ast result = Z3_mk_not(CONTEXT, ast);
			check_error();
			return result;
		}

		Bool operator&&(Bool other) const {
			if(is(FALSE) || other.is(FALSE))
				return FALSE;
			if(is(TRUE))
				return other;
			if(other.is(TRUE))
				return *this;

			Z3_ast conjuncts[2] {ast, other.ast};
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
			if(is(TRUE) || other.is(TRUE))
				return TRUE;
			if(is(FALSE))
				return other;
			if(other.is(FALSE))
				return *this;

			Z3_ast disjuncts[2] {ast, other.ast};
			Z3_ast result = Z3_mk_or(CONTEXT, 2, disjuncts);
			check_error();
			return result;
		}

		static Bool disjunction(const std::vector<Bool> &disjuncts) {
			Z3_ast result = Z3_mk_or(
				CONTEXT,
				disjuncts.size(),
				// safety: Z3_ast should have the same size/alignment as Bool
				reinterpret_cast<const Z3_ast *>(disjuncts.data())
			);
			check_error();
			return result;
		}

		Bool implies(Bool other) const {
			Z3_ast result = Z3_mk_implies(CONTEXT, ast, other.ast);
			check_error();
			return result;
		}

		static Bool exactly_one(const std::vector<Bool> &exactly_one_of) {
			while(ONES.size() < exactly_one_of.size())
				ONES.push_back(1);
			Z3_ast result = Z3_mk_pbeq(
				CONTEXT,
				exactly_one_of.size(),
				// safety: Z3_ast should have the same size/alignment as Bool
				reinterpret_cast<const Z3_ast *>(exactly_one_of.data()),
				ONES.data(),
				1
			);
			check_error();
			return result;
		}

		static Bool forall(const std::vector<Real> &bind, Bool bound) {
			Z3_ast result = Z3_mk_forall_const(
				CONTEXT,
				0,
				bind.size(),
				// safety: Z3_app should have the same size/alignment as Real
				reinterpret_cast<const Z3_app *>(bind.data()),
				0,
				nullptr,
				bound.ast
			);
			check_error();
			return result;
		}

		static Bool FALSE, TRUE;

	private:
		Bool(Z3_ast ast) : Expression(ast) { assert(is_bool()); }

		static unsigned FRESH_INDEX;
		static std::vector<int> ONES;
	};
	static_assert(
		sizeof(Bool) == sizeof(Z3_ast),
		"the size of Bool must be equal to that of Z3_ast to allow cast magic"
	);

	// Expression of real sort by construction
	struct Real: public Expression {
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
			if(is(ZERO))
				return other;
			if(other.is(ZERO))
				return *this;

			Z3_ast args[2] = {ast, other.ast};
			Z3_ast result = Z3_mk_add(CONTEXT, 2, args);
			check_error();
			return result;
		}

		Real operator-() const {
			if(is(ZERO))
				return *this;

			Z3_ast result = Z3_mk_unary_minus(CONTEXT, ast);
			check_error();
			return result;
		}

		Real operator-(Real other) const {
			if(other.is(ZERO))
				return *this;
			if(is(ZERO))
				return -other;

			Z3_ast args[2] = {ast, other.ast};
			Z3_ast result = Z3_mk_sub(CONTEXT, 2, args);
			check_error();
			return result;
		}

		Real operator*(Real other) const {
			if(is(ZERO) || other.is(ZERO))
				return ZERO;
			if(is(ONE))
				return other;
			if(other.is(ONE))
				return *this;

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

		Bool operator>=(Real other) const {
			Z3_ast result = Z3_mk_ge(CONTEXT, ast, other.ast);
			check_error();
			return result;
		}

		static Bool sum(const std::vector<Real> &terms) {
			Z3_ast result = Z3_mk_add(
				CONTEXT,
				terms.size(),
				// safety: Z3_ast should have the same size/alignment as Real
				reinterpret_cast<const Z3_ast *>(terms.data())
			);
			check_error();
			return result;
		}

		static Real ZERO, ONE;
	private:
		Real(Z3_ast ast) : Expression(ast) { assert(is_real()); }
	};
	static_assert(
		sizeof(Real) == sizeof(Z3_app),
		"the size of Real must be equal to that of Z3_app to allow cast magic"
	);

	enum class Result {
		SAT,
		UNSAT
	};

	inline std::ostream &operator <<(std::ostream &out, Result result) {
		return out << (result == Result::SAT ? "sat" : "unsat");
	}

	class Solver {
	public:
		Solver() : solver(Z3_mk_simple_solver(CONTEXT)) {
			check_error();
			Z3_solver_inc_ref(CONTEXT, solver);
			check_error();
		}

		~Solver() {
			Z3_solver_dec_ref(CONTEXT, solver);
			check_error();
		}

		// represents Z3's push/pop semantics: push on construction, pop on destruction
		class Pop {
		public:
			Pop(const Solver &solver) : solver(solver) {
				Z3_solver_push(CONTEXT, solver.solver);
				check_error();
			}

			~Pop() {
				Z3_solver_pop(CONTEXT, solver.solver, 1);
				check_error();
			}

		private:
			const Solver &solver;
		};

		void assert_(Bool assertion) {
			Z3_solver_assert(CONTEXT, solver, assertion.ast);
			check_error();
		}

		void assert_and_track(Bool assertion) {
			Z3_solver_assert_and_track(CONTEXT, solver, assertion.ast, assertion.ast);
			check_error();
		}

		Result solve(const std::vector<Bool> &assumptions) {
			Z3_lbool result = Z3_solver_check_assumptions(
				CONTEXT,
				solver,
				assumptions.size(),
				// safety: Z3_ast should have the same size/alignment as Bool
				reinterpret_cast<const Z3_ast *>(assumptions.data())
			);
			check_error();
			switch(result) {
			case Z3_L_FALSE:
				return Result::UNSAT;
			case Z3_L_TRUE:
				return Result::SAT;
			default:
				throw std::logic_error("Z3_solver_check() returned UNDEF - this shouldn't happen");
			}
		}

		template<typename... BoolList>
		Result solve(std::vector<Bool> &assumptions, Bool extra, BoolList... others) {
			assumptions.push_back(extra);
			Result result = solve(assumptions, others...);
			assumptions.pop_back();
			return result;
		}

		std::vector<Bool> unsat_core() {
			Z3_ast_vector core = Z3_solver_get_unsat_core(CONTEXT, solver);
			check_error();
			Z3_ast_vector_inc_ref(CONTEXT, core);
			check_error();
			unsigned length = Z3_ast_vector_size(CONTEXT, core);
			std::vector<Bool> result;
			for(unsigned i = 0; i < length; i++) {
				Z3_ast item = Z3_ast_vector_get(CONTEXT, core, i);
				check_error();
				result.push_back(Bool(item));
			}
			Z3_ast_vector_dec_ref(CONTEXT, core);
			check_error();
			return result;
		}

		friend std::ostream &operator<<(std::ostream &out, const Solver &solver) {
			return out << Z3_solver_to_string(CONTEXT, solver.solver);
		}

	private:
		Z3_solver solver;
	};
}

template<>
struct std::equal_to<z3::Bool> {
	bool operator()(const z3::Bool &left, const z3::Bool &right) const {
		return left.is(right);
	}
};

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
