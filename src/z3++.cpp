#include "z3++.hpp"

namespace z3 {
	// the only Z3 context - mostly just hangs out here to be passed to the Z3 API
	Z3_context CONTEXT;

	// thing constructed on program start to create a Z3 context
	struct Global {
		Global() {
			// TODO should we try and minimize unsat cores?
			//Z3_global_param_set("sat.core.minimize", "true");
			//Z3_global_param_set("smt.core.minimize", "true");
			Z3_config config = Z3_mk_config();
			CONTEXT = Z3_mk_context(config);
			Z3_del_config(config);
			check_error();
		}

		~Global() {
			Z3_del_context(CONTEXT);
		}
	} GLOBAL;

	Z3_sort Expression::BOOL_SORT = Z3_mk_bool_sort(CONTEXT);
	Z3_sort Expression::REAL_SORT = Z3_mk_real_sort(CONTEXT);

	Real Real::ZERO = Real::value(0);

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
}
