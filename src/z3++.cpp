#include "z3++.hpp"

namespace z3 {
	// the only Z3 context - mostly just hangs out here to be passed to the Z3 API
	Z3_context CONTEXT = nullptr;

	Z3_sort Expression::BOOL_SORT = nullptr;
	Z3_sort Expression::REAL_SORT = nullptr;

	Real Real::ZERO;

	// Not done by a static constructor: when Z3 is linked statically (e.g. for WebAssembly), a context
	// created before Z3's own static initializers have run gets strict inequalities wrong.
	void initialize() {
		// TODO should we try and minimize unsat cores?
		//Z3_global_param_set("sat.core.minimize", "true");
		//Z3_global_param_set("smt.core.minimize", "true");
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

	std::string Expression::to_smt2() const {
		// the print mode is context-wide, and operator<< relies on the default for numerals
		Z3_set_ast_print_mode(CONTEXT, Z3_PRINT_SMTLIB2_COMPLIANT);
		std::string result = Z3_ast_to_string(CONTEXT, ast);
		Z3_set_ast_print_mode(CONTEXT, Z3_PRINT_SMTLIB_FULL);
		check_error();
		return result;
	}

	// TODO keep track of precedence
	std::ostream &operator<<(std::ostream &out, z3::Real expr) {
		auto op = expr.op();
		switch(op) {
		case Real::Operator::NUMERAL:
		case Real::Operator::CONSTANT:
			out << Z3_ast_to_string(CONTEXT, expr.ast);
			check_error();
			return out;
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
		case Bool::Operator::LT:
		case Bool::Operator::LE:
		case Bool::Operator::GT:
		case Bool::Operator::GE:
			return out << '(' << expr.real_child(0) << ' ' << op << ' ' << expr.real_child(1) << ')';
		}
		assert(false);
		UNREACHABLE;
	}

	namespace {
		// precedence, loosest first
		enum { SUM = 1, PRODUCT, NEGATION, ATOM };
		enum { OR = 1, AND, NOT, COMPARISON };

		std::string wrap(const std::string &text, int precedence, int outer) {
			return precedence < outer ? "(" + text + ")" : text;
		}

		bool negative(Real expr) {
			return expr.op() == Real::Operator::MIN || (expr.op() == Real::Operator::NUMERAL && expr.numeral()[0] == '-');
		}

		// -x for a negative number or a negation x
		std::string negated(Real expr, int outer);

		std::string pretty(Real expr, int outer) {
			switch (expr.op()) {
			case Real::Operator::NUMERAL: {
				std::string number = expr.numeral();
				int precedence = number[0] == '-' ? NEGATION : number.find('/') != std::string::npos ? PRODUCT : ATOM;
				return wrap(number, precedence, outer);
			}
			case Real::Operator::CONSTANT:
				return expr.name();
			case Real::Operator::MIN:
				return wrap("-" + pretty(expr.real_child(0), NEGATION), NEGATION, outer);
			case Real::Operator::ADD:
			case Real::Operator::SUB: {
				std::string text = pretty(expr.real_child(0), SUM);
				for (unsigned i = 1; i < expr.num_args(); i++) {
					Real child = expr.real_child(i);
					bool minus = expr.op() == Real::Operator::SUB;
					// a + -b is written a - b, and a - -b as a + b
					if (negative(child))
						text += (minus ? " + " : " - ") + negated(child, minus ? SUM : PRODUCT);
					else
						text += (minus ? " - " : " + ") + pretty(child, minus ? PRODUCT : SUM);
				}
				return wrap(text, SUM, outer);
			}
			case Real::Operator::MUL:
			case Real::Operator::DIV: {
				std::string text = pretty(expr.real_child(0), PRODUCT);
				for (unsigned i = 1; i < expr.num_args(); i++)
					text += expr.op() == Real::Operator::MUL ? " * " + pretty(expr.real_child(i), PRODUCT)
						: " / " + pretty(expr.real_child(i), NEGATION);
				return wrap(text, PRODUCT, outer);
			}
			}
			assert(false);
			UNREACHABLE;
		}

		std::string negated(Real expr, int outer) {
			if (expr.op() == Real::Operator::MIN)
				return pretty(expr.real_child(0), outer);
			std::string number = expr.numeral();
			return wrap(number.substr(1), number.find('/') != std::string::npos ? PRODUCT : ATOM, outer);
		}

		const char *comparison(Bool::Operator op, bool inverted) {
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

		std::string pretty(Bool expr, int outer) {
			auto op = expr.op();
			switch (op) {
			case Bool::Operator::TRUE:
				return "true";
			case Bool::Operator::FALSE:
				return "false";
			case Bool::Operator::NOT: {
				// not (a >= b) is written a < b
				Bool child = expr.bool_child(0);
				if (const char *inverse = comparison(child.op(), true))
					return wrap(pretty(child.real_child(0), SUM) + " " + inverse + " " + pretty(child.real_child(1), SUM),
						COMPARISON, outer);
				return wrap("not " + pretty(child, NOT), NOT, outer);
			}
			case Bool::Operator::AND:
			case Bool::Operator::OR: {
				int precedence = op == Bool::Operator::AND ? AND : OR;
				std::string text;
				for (unsigned i = 0; i < expr.num_args(); i++)
					text += (i ? (op == Bool::Operator::AND ? " and " : " or ") : "") + pretty(expr.bool_child(i), precedence);
				return wrap(text, precedence, outer);
			}
			default:
				return wrap(pretty(expr.real_child(0), SUM) + " " + comparison(op, false) + " " + pretty(expr.real_child(1), SUM),
					COMPARISON, outer);
			}
		}
	}

	std::string pretty(Real expr) {
		std::string text = pretty(expr, 0);
		check_error();
		return text;
	}

	std::string pretty(Bool expr) {
		std::string text = pretty(expr, 0);
		check_error();
		return text;
	}
}
