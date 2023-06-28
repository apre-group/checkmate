#ifndef __checkmate_z3pp__
#define __checkmate_z3pp__

#include <cassert>
#include <ostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <utility>

#include "z3.h"

#include "utils.hpp"

namespace z3 {
	extern Z3_context CONTEXT;

	inline void check_error() {
		assert(Z3_get_error_code(CONTEXT) == Z3_OK);
	}

	class Solver;
	struct Expression {
		friend Solver;
		Expression() : ast(nullptr) {}
		Expression(Z3_ast ast) : ast(ast) {}

		inline bool null() const { return ast == nullptr; }

		inline bool is(Expression other) const { return ast == other.ast; }
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
		bool is_bool() {
			Z3_sort sort = Z3_get_sort(CONTEXT, ast);
			check_error();
			return sort == BOOL_SORT;
		}

		bool is_real() {
			Z3_sort sort = Z3_get_sort(CONTEXT, ast);
			check_error();
			return sort == REAL_SORT;
		}

		Z3_ast ast;
		static Z3_sort BOOL_SORT, REAL_SORT;
	};

	struct Real;
	struct Bool: public Expression {
		friend Real;

		Bool() : Expression() {}
		static Bool fresh() {
			Z3_symbol fresh = Z3_mk_int_symbol(CONTEXT, FRESH_INDEX++);
			check_error();
			Z3_ast constant = Z3_mk_const(CONTEXT, fresh, BOOL_SORT);
			check_error();
			return constant;
		}

		Bool operator&&(Bool other) const {
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

	private:
		Bool(Z3_ast ast) : Expression(ast) { assert(is_bool()); }

		static unsigned FRESH_INDEX;
		static std::vector<int> ONES;
	};
	static_assert(
		sizeof(Bool) == sizeof(Z3_ast),
		"the size of Bool must be equal to that of Z3_ast to allow cast magic"
	);

	struct Real: public Expression {
		Real() : Expression() {}
		static Real value(unsigned number) {
			Z3_ast result = Z3_mk_real(CONTEXT, number, 1);
			check_error();
			return result;
		}

		static Real value(const std::string &number) {
			Z3_ast result = Z3_mk_numeral(CONTEXT, number.c_str(), REAL_SORT);
			check_error();
			return result;
		}

		static Real constant(const std::string &name) {
			Z3_symbol symbol = Z3_mk_string_symbol(CONTEXT, name.c_str());
			check_error();
			Z3_ast constant = Z3_mk_const(CONTEXT, symbol, REAL_SORT);
			check_error();
			return constant;
		}

		bool is_zero() const { return ast == ZERO.ast; }
		bool is_one() const { return ast == ONE.ast; }

		Real operator+(Real other) const {
			if(is_zero())
				return other;
			if(other.is_zero())
				return *this;

			Z3_ast args[2] = {ast, other.ast};
			Z3_ast result = Z3_mk_add(CONTEXT, 2, args);
			check_error();
			return result;
		}

		Real operator-() const {
			if(is_zero())
				return *this;

			Z3_ast result = Z3_mk_unary_minus(CONTEXT, ast);
			check_error();
			return result;
		}

		Real operator-(Real other) const {
			if(other.is_zero())
				return *this;
			if(is_zero())
				return -other;

			Z3_ast args[2] = {ast, other.ast};
			Z3_ast result = Z3_mk_sub(CONTEXT, 2, args);
			check_error();
			return result;
		}

		Real operator*(Real other) const {
			if(is_zero() || other.is_zero())
				return ZERO;
			if(is_one())
				return other;
			if(other.is_one())
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

		static Real ZERO;
		static Real ONE;
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
		Solver() : solver(Z3_mk_simple_solver(CONTEXT)) { check_error(); }

		struct Frame {
			~Frame() {
				Z3_solver_pop(CONTEXT, solver.solver, 1);
				check_error();
			}
			const Solver &solver;
		};

		Frame push() {
			Z3_solver_push(CONTEXT, solver);
			check_error();
			return {*this};
		}

		void assert_(Bool assertion) {
			Z3_solver_assert(CONTEXT, solver, assertion.ast);
			check_error();
		}

		Result solve() {
			Z3_lbool result = Z3_solver_check(CONTEXT, solver);
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
