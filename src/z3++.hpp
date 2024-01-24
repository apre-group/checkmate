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
#include <stdexcept>
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
		// default constructor very convenient - initialises `ast` to `nullptr`
		Expression() : ast(nullptr) {}

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

		// bool is_app() {
		// 	bool app = Z3_is_app(CONTEXT, ast);
		// 	check_error();
		// 	return app;
		// }


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
		Z3_ast ast;

		// Z3's Boolean sort
		static Z3_sort BOOL_SORT;
		// Z3's real sort
		static Z3_sort REAL_SORT;
	};

	// an Expression of Boolean sort, by construction
	class Bool: public Expression {
		// Real wants to construct Booleans from e.g. `x > y`
		friend Real;
		// Solver wants to construct Booleans from unsat cores
		friend Solver;
		// Model wants to construct Booleans from models
		friend Model;

	public:
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

		// Boolean constants
		static Bool FALSE, TRUE;

		Bool invert() {
			Z3_app app = Z3_to_app(CONTEXT, ast);
			Z3_ast ast_left = Z3_get_app_arg(CONTEXT, app, 0);
			Z3_ast ast_right = Z3_get_app_arg(CONTEXT, app, 1);

			Z3_func_decl func_decl = Z3_get_app_decl(CONTEXT, app);
			Z3_decl_kind decl_kind = Z3_get_decl_kind(CONTEXT, func_decl);

			Bool new_expr;
			if(decl_kind == Z3_OP_LT){
				new_expr = Z3_mk_ge(CONTEXT, ast_left, ast_right);
			}
			else if (decl_kind == Z3_OP_LE)
			{
				new_expr = Z3_mk_gt(CONTEXT, ast_left, ast_right);
			}
			else if (decl_kind == Z3_OP_GT){
				new_expr = Z3_mk_le(CONTEXT, ast_left, ast_right);
			}
			else if (decl_kind == Z3_OP_GE){
				new_expr = Z3_mk_lt(CONTEXT, ast_left, ast_right);
			}
			else{
				assert(false);
			}
			check_error();
			return new_expr;
		}

	private:
		Bool(Z3_ast ast) : Expression(ast) { assert(is_bool()); }

		// index for generating fresh names
		static unsigned FRESH_INDEX;
		// a vector of 1 values for `exactly_one`
		static std::vector<int> ONES;
	};
	// we reinterpret_cast Bool to Z3_ast sometimes for performance reasons
	static_assert(
		sizeof(Bool) == sizeof(Z3_ast),
		"the size of Bool must be equal to that of Z3_ast to allow cast magic"
	);

	// for ADL
	inline Bool disjunction(const std::vector<Bool> &disjuncts) { return Bool::disjunction(disjuncts); }
	inline Bool conjunction(const std::vector<Bool> &conjuncts) { return Bool::conjunction(conjuncts); }
	inline Bool exactly_one(const std::vector<Bool> &exactly_one_of) { return Bool::exactly_one(exactly_one_of); }
	inline Bool forall(const std::vector<Real> &bind, Bool bound) { return Bool::forall(bind, bound); }

	// Expression of real sort by construction
	class Real: public Expression {
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

		// real constants
		static Real ZERO, ONE;

	private:
		Real(Z3_ast ast) : Expression(ast) { assert(is_real()); }
	};

	// possible results from a `solve()` call
	enum class Result {
		SAT,
		UNSAT
	};

	inline std::ostream &operator <<(std::ostream &out, Result result) {
		return out << (result == Result::SAT ? "sat" : "unsat");
	}

	// wrapper around a Z3 model
	class Model {
		// `Solver` wants to access `model`
		friend Solver;
	public:
		Model() = default;

		Model(Model &&other) noexcept {
			model = other.model;
			other.model = nullptr;
		}

		~Model() {
			if(!model)
				return;
			Z3_model_dec_ref(CONTEXT, model);
			check_error();
		}

		template<bool polarity>
		bool assigns(Bool domain) const {
			Z3_ast ast;
			Z3_model_eval(CONTEXT, model, domain.ast, false, &ast);
			check_error();
			Z3_app app = Z3_to_app(CONTEXT, ast);
			check_error();
			Z3_func_decl decl = Z3_get_app_decl(CONTEXT, app);
			check_error();
			Z3_decl_kind kind = Z3_get_decl_kind(CONTEXT, decl);
			check_error();
			return kind == (polarity ? Z3_OP_TRUE : Z3_OP_FALSE);
		}

	private:
		Z3_model model = nullptr;
	};

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

		// same as assert_() but enable the assertion to appear in unsat cores
		void assert_and_track(Bool assertion) {
			Z3_solver_assert_and_track(CONTEXT, solver, assertion.ast, assertion.ast);
			check_error();
		}

		// invoke the solver
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
			switch(result) {
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

		// retrieve an unsat core - must have just returned unsat
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
				result.push_back(item);
			}
			Z3_ast_vector_dec_ref(CONTEXT, core);
			check_error();
			return result;
		}

		// get a model - must have just returned sat
		Model model() const {
			Model result;
			result.model = Z3_solver_get_model(CONTEXT, solver);
			check_error();
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

namespace z3 {
	class MinimalCores {
	public:
		MinimalCores(
			Solver &solver,
			const std::vector<Bool> &labels,
			const std::unordered_map<Bool, Bool> &ignore
		) : solver(solver), labels(labels), ignore(ignore) {}
		bool more();
		std::vector<Bool> core;

	private:
		Solver &solver;
		const std::vector<Bool> &labels;
		const std::unordered_map<Bool, Bool> &ignore;
		Solver map;
	};
}

#endif
