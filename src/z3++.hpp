#ifndef __checkmate_z3pp__
#define __checkmate_z3pp__

/**
 * Our own wrapper around the Z3 C API
 *
 * Z3 has a similar C++ wrapper, but it doesn't suit our purposes very well.
 * This should be quite small and easy to maintain.
 **/

#include <cassert>
#include <iostream>
#include <string>
#include <cctype>
#include <sstream>
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

		// check whether this is an operator application
		bool wrap_Z3_is_app() {
			return Z3_is_app(CONTEXT, ast);
		}

		// return name of applied operator
		std::string get_operator_name_expr() {
			Z3_app app = Z3_to_app(CONTEXT, ast);
			Z3_func_decl decl = Z3_get_app_decl(CONTEXT, app);
			Z3_symbol symbol = Z3_get_decl_name(CONTEXT, decl);
			std::string op_name = Z3_get_symbol_string(CONTEXT, symbol);
			return op_name;
		}

		Z3_app wrap_Z3_to_app() {
			return Z3_to_app(CONTEXT, ast);
		}

		// return number of arguments of the applied operator
		unsigned wrap_Z3_get_app_num_args(){
			Z3_app app = Z3_to_app(CONTEXT, ast);
			return Z3_get_app_num_args(CONTEXT, app);
		}	

		// return the arguments of the applied operator
		Z3_ast wrap_Z3_get_app_arg(Z3_app a, unsigned i) {
			return Z3_get_app_arg(CONTEXT, a, i);
		}

		bool wrap_is_bool() {
			return is_bool();
		}

		// wrap `ast`
		Expression(Z3_ast ast) : ast(ast) {}

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

	public:
		Bool() : Expression() {}

		Bool True() {
			Z3_ast result = Z3_mk_true(CONTEXT);
			return result;
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
			if (decl_kind == Z3_OP_LT) {
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

	private:
		Bool(Z3_ast ast) : Expression(ast) { assert(is_bool()); }
	};
	// we reinterpret_cast Bool to Z3_ast sometimes for performance reasons
	static_assert(
		sizeof(Bool) == sizeof(Z3_ast),
		"the size of Bool must be equal to that of Z3_ast to allow cast magic"
	);

	inline Bool conjunction(const std::vector<Bool> &conjuncts) { return Bool::conjunction(conjuncts); }

	inline Bool disjunction(const std::vector<Bool> &disjuncts) { return Bool::disjunction(disjuncts); }	


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

	// Helper function to check if an expression is an application of an operator
	inline bool is_operator(Expression expr) {
		return expr.wrap_Z3_is_app();
	}

	// Helper function to get the operator name from an expression
	inline std::string get_operator_name(Expression expr) {
		if (!is_operator(expr)) return "";
		return expr.get_operator_name_expr();
	}

	// Recursive pretty-print function for Z3 expressions
	// Used when printing into a JSON file in subtree mode
	inline std::string pretty_print(Expression expr) {

		if (is_operator(expr)) {	
			std::string op_name = get_operator_name(expr);
			const unsigned int num_args =  expr.wrap_Z3_get_app_num_args();
			Z3_ast* args = new Z3_ast[num_args]; 
			//above line instead of: Z3_ast args[num_args]; cause that's not allowed in c++
			for (unsigned int i = 0; i < num_args; i++) {
				Z3_ast current_ast = expr.wrap_Z3_get_app_arg(expr.wrap_Z3_to_app(), i);
				args[i] = current_ast;
			}

			// Check for known operators and format accordingly
			if (op_name == "or") {
				std::string result = "(";
				for (unsigned i = 0; i < num_args; ++i) {
					result += pretty_print(args[i]);
					if (i < num_args - 1) result += " ∨ ";
				}
				result += ")";
				return result;
			} else if (op_name == "+") {
				return "(" + pretty_print(args[0]) + " + " + pretty_print(args[1]) + ")";
			} else if (op_name == "-") {
				if(num_args == 1) {
					return "(- " + pretty_print(args[0]) + ")";
				}
				return "(" + pretty_print(args[0]) + " - " + pretty_print(args[1]) + ")";
			} else if (op_name == "*") {
				return "(" + pretty_print(args[0]) + " * " + pretty_print(args[1]) + ")";
			} else if (op_name == "<=") {
				return "(" + pretty_print(args[0]) + " <= " + pretty_print(args[1]) + ")";
			} else if (op_name == "<") {
				return "(" + pretty_print(args[0]) + " < " + pretty_print(args[1]) + ")";
			} else if (op_name == ">=") {
				return "(" + pretty_print(args[0]) + " >= " + pretty_print(args[1]) + ")";
			} else if (op_name == ">") {
				return "(" + pretty_print(args[0]) + " > " + pretty_print(args[1]) + ")";
			}
		}

		// Fallback to Z3's default string representation
		std::stringstream ss;
		ss << expr;
		std::string std_representation = ss.str();

		return std_representation;
	}
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
