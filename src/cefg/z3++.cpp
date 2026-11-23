#include <sstream>

#include "z3++.hpp"

// imported from the cefg branch (c9c6e6f); wrapped in namespace cefg next to the EFG engine in src/
namespace cefg {

namespace z3 {
	// the only Z3 context - mostly just hangs out here to be passed to the Z3 API
	Z3_context CONTEXT = nullptr;

	Z3_sort Expression::BOOL_SORT = nullptr;
	Z3_sort Expression::REAL_SORT = nullptr;

	Real Real::ZERO;

	// Not done by a static constructor, as for the EFG engine: when Z3 is linked statically (e.g. for WebAssembly),
	// a context created before Z3's own static initializers have run gets strict inequalities wrong.
	void initialize() {
		Z3_config config = Z3_mk_config();
		CONTEXT = Z3_mk_context(config);
		// errors are checked for after each call (check_error), so a failing check can be handled
		Z3_set_error_handler(CONTEXT, nullptr);
		Z3_del_config(config);
		check_error();
		Expression::BOOL_SORT = Z3_mk_bool_sort(CONTEXT);
		Expression::REAL_SORT = Z3_mk_real_sort(CONTEXT);
		Real::ZERO = Real::value(0);
	}

	struct Global {
		~Global() {
			if (CONTEXT)
				Z3_del_context(CONTEXT);
		}
	} GLOBAL;

	// TODO keep track of precedence
	std::ostream &operator<<(std::ostream &out, z3::Real expr) {
		auto op = expr.op();
		switch(op) {
		case Real::Operator::NUMERAL: {
			// Z3 writes a fraction as (/ n d), which is not the infix syntax the parser reads
			Z3_ast denominator = Z3_get_denominator(CONTEXT, expr.ast);
			Z3_ast numerator = Z3_get_numerator(CONTEXT, expr.ast);
			check_error();
			if (std::string(Z3_get_numeral_string(CONTEXT, denominator)) != "1")
				return out << '(' << Z3_ast_to_string(CONTEXT, numerator) << " / " << Z3_ast_to_string(CONTEXT, denominator) << ')';
			out << Z3_ast_to_string(CONTEXT, expr.ast);
			check_error();
			return out;
		}
		case Real::Operator::CONSTANT: {
			// a function applied to arguments (selectors of practicality) as the parser reads it: @name(x, y)
			unsigned arguments = expr.num_args();
			if (arguments > 0) {
				Z3_func_decl decl = Z3_get_app_decl(CONTEXT, Z3_to_app(CONTEXT, expr.ast));
				out << '@' << Z3_get_symbol_string(CONTEXT, Z3_get_decl_name(CONTEXT, decl)) << '(';
				for (unsigned i = 0; i < arguments; i++)
					out << (i ? ", " : "") << expr.real_child(i);
				return out << ')';
			}
			out << Z3_ast_to_string(CONTEXT, expr.ast);
			check_error();
			return out;
		}
		case Real::Operator::MIN:
			return out << '(' << op << ' ' << expr.real_child(0) << ')';
		case Real::Operator::ADD:
		case Real::Operator::SUB:
		case Real::Operator::MUL:
		case Real::Operator::DIV:
			out << '(';
			for(unsigned i = 0; i < expr.num_args(); i++) {
				if(i)
					out << ' ' << op << ' ';
				out << expr.real_child(i);
			}
			out << ')';
			return out;
		}
		assert(false);
		UNREACHABLE;
	}

	// TODO keep track of precedence
	std::ostream &operator<<(std::ostream &out, z3::Bool expr) {
		auto op = expr.op();
		switch(op) {
		case Bool::Operator::TRUE:
			return out << "true";
		case Bool::Operator::FALSE:
			return out << "false";
		case Bool::Operator::NOT:
			return out << "!(" << expr.bool_child(0) << ")";
		case Bool::Operator::AND:
		case Bool::Operator::OR:
			// the empty conjunction/disjunction, as the parser reads it
			if (expr.num_args() == 0)
				return out << (op == Bool::Operator::AND ? "true" : "false");
			out << '(';
			for(unsigned i = 0; i < expr.num_args(); i++) {
				if(i)
					out << ' ' << op << ' ';
				out << expr.bool_child(i);
			}
			out << ')';
			return out;
		case Bool::Operator::EQ:
		case Bool::Operator::NE:
			// EQ and NE can compare either Bools or Reals
			// Check the sort of the first argument
			{
				Z3_app app = Z3_to_app(CONTEXT, expr.ast);
				Z3_ast first_arg = Z3_get_app_arg(CONTEXT, app, 0);
				Z3_sort arg_sort = Z3_get_sort(CONTEXT, first_arg);
				check_error();
				
				if (arg_sort == Expression::BOOL_SORT) {
					return out << '(' << expr.bool_child(0) << ' ' << op << ' ' << expr.bool_child(1) << ')';
				} else {
					return out << '(' << expr.real_child(0) << ' ' << op << ' ' << expr.real_child(1) << ')';
				}
			}
		case Bool::Operator::IMPLIES:
			return out << '(' << expr.bool_child(0) << ' ' << op << ' ' << expr.bool_child(1) << ')';
		case Bool::Operator::FORALL: {
			// as the parser reads it: (forall [x, y] body)
			out << '(' << op << " [";
			std::vector<Real> variables = expr.bound_variables();
			for (size_t i = 0; i < variables.size(); i++)
				out << (i ? ", " : "") << variables[i];
			return out << "] " << expr.body() << ')';
		}
		case Bool::Operator::LT:
		case Bool::Operator::LE:
		case Bool::Operator::GT:
		case Bool::Operator::GE:
			// These only compare Reals
			return out << '(' << expr.real_child(0) << ' ' << op << ' ' << expr.real_child(1) << ')';
		}
		assert(false);
		UNREACHABLE;
	}

	// as pretty in src/z3++.cpp; anything unusual (quantifiers, selectors) is written as operator<< does
	struct Pretty {
		enum { SUM = 1, PRODUCT, NEGATION, ATOM };
		enum { OR = 1, AND, NOT, COMPARISON };

		static std::string wrap(const std::string &text, int precedence, int outer) {
			return precedence < outer ? "(" + text + ")" : text;
		}

		static std::string streamed(Real expr) {
			std::ostringstream out;
			out << expr;
			return out.str();
		}

		static std::string streamed(Bool expr) {
			std::ostringstream out;
			out << expr;
			return out.str();
		}

		static std::string numeral(Real expr) {
			std::string text = Z3_get_numeral_string(CONTEXT, expr.ast);
			check_error();
			return text;
		}

		static bool negative(Real expr) {
			return expr.op() == Real::Operator::MIN || (expr.op() == Real::Operator::NUMERAL && numeral(expr)[0] == '-');
		}

		static std::string negated(Real expr, int outer) {
			if (expr.op() == Real::Operator::MIN)
				return real(expr.real_child(0), outer);
			std::string number = numeral(expr);
			return wrap(number.substr(1), number.find('/') != std::string::npos ? PRODUCT : ATOM, outer);
		}

		static std::string real(Real expr, int outer) {
			switch (expr.op()) {
			case Real::Operator::NUMERAL: {
				std::string number = numeral(expr);
				return wrap(number, number[0] == '-' ? NEGATION : number.find('/') != std::string::npos ? PRODUCT : ATOM, outer);
			}
			case Real::Operator::CONSTANT:
				return streamed(expr);
			case Real::Operator::MIN:
				return wrap("-" + real(expr.real_child(0), NEGATION), NEGATION, outer);
			case Real::Operator::ADD:
			case Real::Operator::SUB: {
				std::string text = real(expr.real_child(0), SUM);
				for (unsigned i = 1; i < expr.num_args(); i++) {
					Real child = expr.real_child(i);
					bool minus = expr.op() == Real::Operator::SUB;
					if (negative(child))
						text += (minus ? " + " : " - ") + negated(child, minus ? SUM : PRODUCT);
					else
						text += (minus ? " - " : " + ") + real(child, minus ? PRODUCT : SUM);
				}
				return wrap(text, SUM, outer);
			}
			case Real::Operator::MUL:
			case Real::Operator::DIV: {
				std::string text = real(expr.real_child(0), PRODUCT);
				for (unsigned i = 1; i < expr.num_args(); i++)
					text += expr.op() == Real::Operator::MUL ? " * " + real(expr.real_child(i), PRODUCT)
						: " / " + real(expr.real_child(i), NEGATION);
				return wrap(text, PRODUCT, outer);
			}
			}
			return streamed(expr);
		}

		static const char *comparison(Bool::Operator op, bool inverted) {
			switch (op) {
			case Bool::Operator::EQ: return inverted ? "!=" : "=";
			case Bool::Operator::NE: return inverted ? "=" : "!=";
			case Bool::Operator::LT: return inverted ? ">=" : "<";
			case Bool::Operator::LE: return inverted ? ">" : "<=";
			case Bool::Operator::GT: return inverted ? "<=" : ">";
			case Bool::Operator::GE: return inverted ? "<" : ">=";
			default: return nullptr;
			}
		}

		// a comparison of numbers (EQ and NE can also compare Bools)
		static bool numeric(Bool expr) {
			if (!comparison(expr.op(), false))
				return false;
			Z3_ast first = Z3_get_app_arg(CONTEXT, Z3_to_app(CONTEXT, expr.ast), 0);
			bool result = Z3_get_sort(CONTEXT, first) == Expression::REAL_SORT;
			check_error();
			return result;
		}

		static std::string boolean(Bool expr, int outer) {
			auto op = expr.op();
			if (op == Bool::Operator::TRUE)
				return "true";
			if (op == Bool::Operator::FALSE)
				return "false";
			if (op == Bool::Operator::NOT) {
				Bool child = expr.bool_child(0);
				if (numeric(child))
					return wrap(real(child.real_child(0), SUM) + " " + comparison(child.op(), true) + " " +
						real(child.real_child(1), SUM), COMPARISON, outer);
				return wrap("not " + boolean(child, NOT), NOT, outer);
			}
			if ((op == Bool::Operator::AND || op == Bool::Operator::OR) && expr.num_args() > 0) {
				int precedence = op == Bool::Operator::AND ? AND : OR;
				std::string text;
				for (unsigned i = 0; i < expr.num_args(); i++)
					text += (i ? (op == Bool::Operator::AND ? " and " : " or ") : "") + boolean(expr.bool_child(i), precedence);
				return wrap(text, precedence, outer);
			}
			if (numeric(expr))
				return wrap(real(expr.real_child(0), SUM) + " " + comparison(op, false) + " " + real(expr.real_child(1), SUM),
					COMPARISON, outer);
			return streamed(expr);
		}
	};

	std::string pretty(Bool expr) {
		return Pretty::boolean(expr, 0);
	}
}

} // namespace cefg
