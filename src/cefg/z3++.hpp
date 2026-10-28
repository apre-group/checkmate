#ifndef __checkmate_cefg_z3pp__
#define __checkmate_cefg_z3pp__

/**
 * Our own wrapper around the Z3 C API
 *
 * Z3 has a similar C++ wrapper, but it doesn't suit our purposes very well.
 * This should be quite small and easy to maintain.
 **/

#include <cassert>
#include <iostream>
#include <optional>
#include <string>
#include <cctype>
#include <sstream>
#include <vector>
#include <unordered_map>

#include "../utils.hpp"
#include "z3.h"

// imported from the cefg branch (c9c6e6f); wrapped in namespace cefg next to the EFG engine in src/
namespace cefg {

namespace z3 {
	// the only Z3 context we use, created by initialize()
	extern Z3_context CONTEXT;

	// create the Z3 context; must be called before anything else uses Z3 (as for the EFG engine's z3::initialize())
	void initialize();

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
		// operator<< for Bool needs to access BOOL_SORT
		friend std::ostream &operator<<(std::ostream &, Bool);
		// sets BOOL_SORT and REAL_SORT
		friend void initialize();

	public:
		Expression() = default;

		// does this point to a valid expression?
		bool null() const { return ast == nullptr; }

		// is this expression exactly the same as `other`?
		bool is(Expression other) const { return ast == other.ast; }

		// Z3's internal ID for this AST
		unsigned id() const {
			unsigned result = Z3_get_ast_id(CONTEXT, ast);
			check_error();
			return result;
		}

		// return number of arguments of the applied operator
		unsigned num_args() const {
			Z3_app app = Z3_to_app(CONTEXT, ast);
			unsigned result = Z3_get_app_num_args(CONTEXT, app);
			check_error();
			return result;
		}

		// the nth child of an operator application
		Real real_child(unsigned n);

		// wrap `ast`
		Expression(Z3_ast ast) : ast(ast) {}

		// the wrapped Z3 AST, for code that works with the Z3 C API directly
		Z3_ast raw() const { return ast; }

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

		friend std::ostream &operator<<(std::ostream &, Bool);

	public:
		Bool() : Expression() {}

		// wrap a Z3 AST of Boolean sort built with the Z3 C API directly
		static Bool wrap(Z3_ast ast) { return Bool(ast); }

		Bool(bool b) {
			ast = b ? Z3_mk_true(CONTEXT) : Z3_mk_false(CONTEXT);
			check_error();
		}

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

		// a single conjunct is returned as is, without wrapping it in an `and`, and no conjunct as the literal true
		static Bool conjunction(const std::vector<Bool> &conjuncts) {
			if (conjuncts.empty())
				return Bool(true);
			if (conjuncts.size() == 1)
				return conjuncts[0];
			Z3_ast result = Z3_mk_and(
				CONTEXT,
				conjuncts.size(),
				// safety: Z3_ast should have the same size/alignment as Bool
				reinterpret_cast<const Z3_ast *>(conjuncts.data())
			);
			check_error();
			return result;
		}

		// a single disjunct is returned as is, without wrapping it in an `or`, and no disjunct as the literal false
		static Bool disjunction(const std::vector<Bool> &disjuncts) {
			if (disjuncts.empty())
				return Bool(false);
			if (disjuncts.size() == 1)
				return disjuncts[0];
			Z3_ast result = Z3_mk_or(
				CONTEXT,
				disjuncts.size(),
				// safety: Z3_ast should have the same size/alignment as Bool
				reinterpret_cast<const Z3_ast *>(disjuncts.data())
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

		Bool simplify() {
			Bool simp_exp = Z3_simplify(CONTEXT, ast);
			return simp_exp;
		}

		// ∀ `variables`. `body`; defined after Real
		static Bool forall(const std::vector<Real> &variables, Bool body);

		// for a quantifier: the variables it binds and its body in terms of them, as in forall(variables, body);
		// defined after Real
		std::vector<Real> bound_variables() const;
		Bool body() const;

		enum class Operator {
			TRUE,
			FALSE,
			NOT,
			AND,
			OR,
			EQ,
			NE,
			LT,
			LE,
			GT,
			GE,
			IMPLIES,
			FORALL
		};

		// what kind of operator we have
		Operator op() const {
			if (Z3_get_ast_kind(CONTEXT, ast) == Z3_QUANTIFIER_AST) {
				// we only ever construct universal quantifiers
				assert(Z3_is_quantifier_forall(CONTEXT, ast));
				return Operator::FORALL;
			}
			Z3_app app = Z3_to_app(CONTEXT, ast);
			Z3_func_decl decl = Z3_get_app_decl(CONTEXT, app);
			Z3_decl_kind kind = Z3_get_decl_kind(CONTEXT, decl);
			check_error();
			switch(kind) {
			case Z3_OP_TRUE:
				return Operator::TRUE;
			case Z3_OP_FALSE:
				return Operator::FALSE;
			case Z3_OP_NOT:
				return Operator::NOT;
			case Z3_OP_AND:
				return Operator::AND;
			case Z3_OP_OR:
				return Operator::OR;
			case Z3_OP_EQ:
				return Operator::EQ;
			case Z3_OP_DISTINCT:
				return Operator::NE;
			case Z3_OP_LT:
				return Operator::LT;
			case Z3_OP_LE:
				return Operator::LE;
			case Z3_OP_GT:
				return Operator::GT;
			case Z3_OP_GE:
				return Operator::GE;
			case Z3_OP_IMPLIES:
				return Operator::IMPLIES;
			default:
				assert(false);
				UNREACHABLE
			}
		}

		// the nth child of an operator application
		Bool bool_child(unsigned n) {
			Z3_app app = Z3_to_app(CONTEXT, ast);
			Z3_ast child = Z3_get_app_arg(CONTEXT, app, n);
			check_error();
			return child;
		}

		// TODO is this just checking that two things are syntactically identical?
		bool is_equal(const Bool other) const {
			Z3_app app = Z3_to_app(CONTEXT, ast);
			Z3_ast ast_left = Z3_get_app_arg(CONTEXT, app, 0);
			Z3_ast ast_right = Z3_get_app_arg(CONTEXT, app, 1);
			Z3_func_decl func_decl = Z3_get_app_decl(CONTEXT, app);
			Z3_decl_kind decl_kind = Z3_get_decl_kind(CONTEXT, func_decl);
			
			Z3_app other_app = Z3_to_app(CONTEXT, other.ast);
			Z3_ast other_ast_left = Z3_get_app_arg(CONTEXT, other_app, 0);
			Z3_ast other_ast_right = Z3_get_app_arg(CONTEXT, other_app, 1);
			Z3_func_decl other_func_decl = Z3_get_app_decl(CONTEXT, other_app);
			Z3_decl_kind other_decl_kind = Z3_get_decl_kind(CONTEXT, other_func_decl);

			if ((ast_left == other_ast_left) && (ast_right == other_ast_right) && (decl_kind == other_decl_kind)) {
				return true;
			} else {
				return false;
			}
		}

		Bool invert() const {
			Z3_app app = Z3_to_app(CONTEXT, ast);
			const unsigned int num_args =  Z3_get_app_num_args(CONTEXT, app);
			Z3_ast* args = new Z3_ast[num_args];
			//above line instead of: Z3_ast args[num_args]; cause that's not allowed in c++
			for (unsigned int i = 0; i < num_args; i++) {
				Z3_ast current_ast = Z3_get_app_arg(CONTEXT, app, i);
				args[i] = current_ast;
			}

			Z3_func_decl func_decl = Z3_get_app_decl(CONTEXT, app);
			Z3_decl_kind decl_kind = Z3_get_decl_kind(CONTEXT, func_decl);

			Bool new_expr;
			if (decl_kind == Z3_OP_TRUE) {
				new_expr = Z3_mk_false(CONTEXT);
			} else if (decl_kind == Z3_OP_FALSE) {
				new_expr = Z3_mk_true(CONTEXT);
			} else if (decl_kind == Z3_OP_LT) {
				new_expr = Z3_mk_ge(CONTEXT, args[0], args[1]);
			} else if (decl_kind == Z3_OP_LE) {
				new_expr = Z3_mk_gt(CONTEXT, args[0], args[1]);
			} else if (decl_kind == Z3_OP_GT) {
				new_expr = Z3_mk_le(CONTEXT, args[0], args[1]);
			} else if (decl_kind == Z3_OP_GE) {
				new_expr = Z3_mk_lt(CONTEXT, args[0], args[1]);
			} else if (decl_kind == Z3_OP_EQ) {
				new_expr = Z3_mk_distinct(CONTEXT, num_args, args);
			} else if (decl_kind == Z3_OP_DISTINCT) {
				new_expr = Z3_mk_eq(CONTEXT, args[0], args[1]);
			} else if (decl_kind == Z3_OP_OR) {
				std::vector<Bool> neg_args;
				for (unsigned int i = 0; i < num_args; i++) {
					Bool to_negate = args[i];
					neg_args.push_back(to_negate.invert());
				}
				new_expr = conjunction(neg_args);
			} else if (decl_kind == Z3_OP_AND) {
				std::vector<Bool> neg_args;
				for (unsigned int i = 0; i < num_args; i++) {
					Bool to_negate = args[i];
					neg_args.push_back(to_negate.invert());
				}
				new_expr = disjunction(neg_args);
			} else {
				std::cout << "unsupported z3 element of type " << decl_kind << std::endl;
				delete[] args;
				assert(false);
			}
			delete[] args;
			check_error();
			return new_expr;
		}

		std::string to_string() const {
			std::ostringstream oss;
			oss << *this;
			return oss.str();
		}

	private:
		Bool(Z3_ast ast) : Expression(ast) { assert(is_bool()); }
	};
	// we reinterpret_cast Bool to Z3_ast sometimes for performance reasons
	static_assert(
		sizeof(Bool) == sizeof(Z3_ast),
		"the size of Bool must be equal to that of Z3_ast to allow cast magic"
	);

	inline std::ostream &operator<<(std::ostream &out, Bool::Operator op) {
		using Operator = Bool::Operator;
		switch(op) {
		case Operator::TRUE:
			return out << "true";
		case Operator::FALSE:
			return out << "false";
		case Operator::NOT:
			return out << "!";
		case Operator::AND:
			return out << "&";
		case Operator::OR:
			return out << "|";
		case Operator::EQ:
			return out << "=";
		case Operator::NE:
			return out << "!=";
		case Operator::LT:
			return out << "<";
		case Operator::LE:
			return out << "<=";
		case Operator::GT:
			return out << ">";
		case Operator::GE:
			return out << ">=";
		case Operator::IMPLIES:
			// as the parser reads it
			return out << "=>";
		case Operator::FORALL:
			return out << "forall";
		}
		assert(false);
		UNREACHABLE;
	}

	inline Bool conjunction(const std::vector<Bool> &conjuncts) { return Bool::conjunction(conjuncts); }

	inline Bool disjunction(const std::vector<Bool> &disjuncts) { return Bool::disjunction(disjuncts); }


	// Expression of real sort by construction
	class Real : public Expression {
		friend Expression;
		// Bool wants to bind Reals in quantifiers
		friend Bool;
		friend std::ostream &operator<<(std::ostream &, Real);
	public:
		Real() : Expression() {}

		// wrap a Z3 AST of real sort built with the Z3 C API directly
		static Real wrap(Z3_ast ast) { return Real(ast); }

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

		Real operator/(Real other) const {
			if (is(ZERO))
				return ZERO;

			Z3_ast result = Z3_mk_div(CONTEXT, ast, other.ast);
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

		enum class Operator {
			NUMERAL,
			CONSTANT,
			MIN,
			ADD,
			SUB,
			MUL,
			DIV
		};

		// what kind of operator we have
		Operator op() const {
			Z3_app app = Z3_to_app(CONTEXT, ast);
			Z3_func_decl decl = Z3_get_app_decl(CONTEXT, app);
			Z3_decl_kind kind = Z3_get_decl_kind(CONTEXT, decl);
			check_error();
			switch(kind) {
			case Z3_OP_ANUM:
				return Operator::NUMERAL;
			case Z3_OP_UNINTERPRETED:
				return Operator::CONSTANT;
			case Z3_OP_UMINUS:
				return Operator::MIN;
			case Z3_OP_ADD:
				return Operator::ADD;
			case Z3_OP_SUB:
				return Operator::SUB;
			case Z3_OP_MUL:
				return Operator::MUL;
			case Z3_OP_DIV:
				return Operator::DIV;
			default:
				assert(false);
				UNREACHABLE
			}
		}

	private:
		Real(Z3_ast ast) : Expression(ast) { assert(is_real()); }
	};

	inline Bool Bool::forall(const std::vector<Real> &variables, Bool body) {
		if (variables.empty())
			return body;
		std::vector<Z3_app> bound;
		for (Real variable : variables)
			bound.push_back(Z3_to_app(CONTEXT, variable.ast));
		Z3_ast result = Z3_mk_forall_const(CONTEXT, 0, bound.size(), bound.data(), 0, nullptr, body.ast);
		check_error();
		return result;
	}

	// forall() binds the constants under their own names, so they can be recovered by name
	inline std::vector<Real> Bool::bound_variables() const {
		assert(Z3_get_ast_kind(CONTEXT, ast) == Z3_QUANTIFIER_AST);
		std::vector<Real> variables;
		for (unsigned i = 0; i < Z3_get_quantifier_num_bound(CONTEXT, ast); i++) {
			Z3_symbol name = Z3_get_quantifier_bound_name(CONTEXT, ast, i);
			assert(Z3_get_quantifier_bound_sort(CONTEXT, ast, i) == REAL_SORT);
			variables.push_back(Real::constant(Z3_get_symbol_string(CONTEXT, name)));
		}
		check_error();
		return variables;
	}

	inline Bool Bool::body() const {
		// in the body, bound variable i is the de Bruijn index (number of bound variables - 1 - i)
		std::vector<Real> variables = bound_variables();
		std::vector<Z3_ast> replacements;
		for (auto variable = variables.rbegin(); variable != variables.rend(); variable++)
			replacements.push_back(variable->ast);
		Z3_ast result = Z3_substitute_vars(CONTEXT, Z3_get_quantifier_body(CONTEXT, ast), replacements.size(), replacements.data());
		check_error();
		return result;
	}

	// the nth child of an operator application
	inline Real Expression::real_child(unsigned n) {
		Z3_app app = Z3_to_app(CONTEXT, ast);
		Z3_ast child = Z3_get_app_arg(CONTEXT, app, n);
		check_error();
		return child;
	}

	inline std::ostream &operator<<(std::ostream &out, Real::Operator op) {
		using Operator = Real::Operator;
		switch(op) {
		case Operator::NUMERAL:
		case Operator::CONSTANT:
			assert(false);
			UNREACHABLE;
		case Operator::MIN:
		case Operator::SUB:
			return out << '-';
		case Operator::ADD:
			return out << '+';
		case Operator::MUL:
			return out << '*';
		case Operator::DIV:
			return out << '/';
		}
		assert(false);
		UNREACHABLE;
	}

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

		// invoke the solver with extra `assumptions`, giving up after `timeout` milliseconds:
		// no result if Z3 cannot decide in time (or at all, e.g. for some quantified non-linear problems);
		// switches off the Horner and Gröbner heuristics for non-linear arithmetic, in which Z3 was seen
		// to run far past the timeout (it only stops where it checks for cancellation)
		std::optional<Result> solve_within(const std::vector<Bool> &assumptions, unsigned timeout) {
			// all parameters at once: setting parameters may reset the ones not given to their defaults
			Z3_params params = Z3_mk_params(CONTEXT);
			Z3_params_inc_ref(CONTEXT, params);
			Z3_params_set_uint(CONTEXT, params, Z3_mk_string_symbol(CONTEXT, "timeout"), timeout);
			Z3_params_set_bool(CONTEXT, params, Z3_mk_string_symbol(CONTEXT, "arith.nl.horner"), false);
			Z3_params_set_bool(CONTEXT, params, Z3_mk_string_symbol(CONTEXT, "arith.nl.grobner"), false);
			Z3_solver_set_params(CONTEXT, solver, params);
			Z3_params_dec_ref(CONTEXT, params);
			check_error();
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
					return std::nullopt;
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

	std::ostream &operator<<(std::ostream &out, z3::Real expr);
	std::ostream &operator<<(std::ostream &out, z3::Bool expr);
}


// used in e.g. hash tables rather than operator==
} // namespace cefg
template<>
struct std::equal_to<cefg::z3::Bool> {
	bool operator()(const cefg::z3::Bool &left, const cefg::z3::Bool &right) const {
		return left.is(right);
	}
};
namespace cefg {

// used in e.g. hash tables rather than operator==
} // namespace cefg
template<>
struct std::equal_to<cefg::z3::Real> {
	bool operator()(const cefg::z3::Real &left, const cefg::z3::Real &right) const {
		return left.is(right);
	}
};
namespace cefg {

} // namespace cefg
template<>
struct std::hash<cefg::z3::Bool> {
	size_t operator()(const cefg::z3::Bool &expr) const {
		return std::hash<unsigned>{}(expr.id());
	}
};
namespace cefg {

} // namespace cefg
template<>
struct std::hash<cefg::z3::Real> {
	size_t operator()(const cefg::z3::Real &expr) const {
		return std::hash<unsigned>{}(expr.id());
	}
};
namespace cefg {

} // namespace cefg

#endif
