#include <fstream>
#include <iostream>
#include <memory>
#include "json.hpp"

#include "input.hpp"
#include "utils.hpp"
#include "z3++.hpp"

struct Lexer {
	enum class Token {
		NUMERAL,
		IDENTIFIER,
		PLUS,
		MINUS,
		MULTIPLY,
		NEGATE,
		EQ,
		NE,
		GT,
		GE,
		OR
	};

	Lexer() : unary(false), current(nullptr), remaining(nullptr) {}
	bool unary;
	const char *current;
	const char *remaining;
	std::string buffer;

	void start(const char *start) {
		unary = true;
		current = start;
		remaining = start;
	}

	bool has_more() {
		while(std::isspace(*remaining)) remaining++;
		return *remaining;
	}

	Token next() {
		buffer.clear();
		if(std::isalpha(*remaining)) {
			buffer.push_back(*remaining++);
			while(std::isalnum(*remaining) || *remaining == '_')
				buffer.push_back(*remaining++);
			unary = false;
			return Token::IDENTIFIER;
		}
		else if(std::isdigit(*remaining)) {
			buffer.push_back(*remaining++);
			while(std::isdigit(*remaining))
				buffer.push_back(*remaining++);
			unary = false;
			return Token::NUMERAL;
		}
		else if(*remaining == '+') {
			remaining++;
			unary = true;
			return Token::PLUS;
		}
		else if(*remaining == '-') {
			remaining++;
			if(unary)
				return Token::NEGATE;
			unary = true;
			return Token::MINUS;
		}
		else if(*remaining == '*') {
			remaining++;
			unary = true;
			return Token::MULTIPLY;
		}
		else if(*remaining == '=') {
			remaining++;
			unary = true;
			return Token::EQ;
		}
		else if(*remaining == '!' && remaining[1] == '=') {
			remaining += 2;
			unary = true;
			return Token::NE;
		}
		else if(*remaining == '>') {
			remaining++;
			if(*remaining == '=') {
				remaining++;
				unary = true;
				return Token::GE;
			}
			unary = true;
			return Token::GT;
		}
		else if(*remaining == '|') {
			remaining++;
			unary = true;
			return Token::OR;
		}
		else {
			std::cerr << "checkmate: unexpected character '" << *remaining << "' in expression " << current << std::endl;
			std::exit(EXIT_FAILURE);
		}
	}
};

struct Parser {
	enum class Operation {
		PLUS,
		MINUS,
		MULTIPLY,
		NEGATE,
		EQ,
		NE,
		GT,
		GE,
		OR
	};

	enum class Precedence {
		OR,
		COMPARISON,
		PLUSMINUS,
		MULTIPLY,
		NEGATE
	};

	static Precedence precedence(Operation operation) {
		switch(operation) {
		case Operation::PLUS:
		case Operation::MINUS:
			return Precedence::PLUSMINUS;
		case Operation::MULTIPLY:
			return Precedence::MULTIPLY;
		case Operation::NEGATE:
			return Precedence::NEGATE;
		case Operation::EQ:
		case Operation::NE:
		case Operation::GT:
		case Operation::GE:
			return Precedence::COMPARISON;
		case Operation::OR:
			return Precedence::OR;
		}
		UNREACHABLE;
	}

	Parser(std::unordered_map<std::string, Utility> &constants) : constants(constants) {}

	std::unordered_map<std::string, Utility> &constants;
	Lexer lexer;
	std::vector<Operation> operation_stack;
	std::vector<Utility> utility_stack;
	std::vector<z3::Bool> constraint_stack;

	[[noreturn]] void error() {
		std::cerr << "checkmate: could not parse expression " << lexer.current << std::endl;
		std::exit(EXIT_FAILURE);
	}

	Operation pop_operation() {
		assert(!operation_stack.empty());
		Operation operation = operation_stack.back();
		operation_stack.pop_back();
		return operation;
	}

	Utility pop_utility() {
		if(utility_stack.empty())
			error();
		Utility utility = utility_stack.back();
		utility_stack.pop_back();
		return utility;
	}

	z3::Bool pop_constraint() {
		if(constraint_stack.empty())
			error();
		z3::Bool constraint = constraint_stack.back();
		constraint_stack.pop_back();
		return constraint;
	}

	void commit(Operation operation) {
		switch(operation) {
		case Operation::PLUS: {
			Utility right = pop_utility();
			Utility left = pop_utility();
			utility_stack.push_back(left + right);
			break;
		}
		case Operation::MINUS: {
			Utility right = pop_utility();
			Utility left = pop_utility();
			utility_stack.push_back(left - right);
			break;
		}
		case Operation::MULTIPLY: {
			Utility right = pop_utility();
			Utility left = pop_utility();
			utility_stack.push_back(left * right);
			break;
		}
		case Operation::NEGATE: {
			Utility negate = pop_utility();
			utility_stack.push_back(-negate);
			break;
		}
		case Operation::EQ: {
			Utility right = pop_utility();
			Utility left = pop_utility();
			constraint_stack.push_back(left == right);
			break;
		}
		case Operation::NE: {
			Utility right = pop_utility();
			Utility left = pop_utility();
			constraint_stack.push_back(left != right);
			break;
		}
		case Operation::GT: {
			Utility right = pop_utility();
			Utility left = pop_utility();
			constraint_stack.push_back(left > right);
			break;
		}
		case Operation::GE: {
			Utility right = pop_utility();
			Utility left = pop_utility();
			constraint_stack.push_back(left >= right);
			break;
		}
		case Operation::OR:
			z3::Bool right = pop_constraint();
			z3::Bool left = pop_constraint();
			constraint_stack.push_back(left || right);
			break;
		}
	}

	void operation(Operation operation) {
		while(!operation_stack.empty() && precedence(operation_stack.back()) >= precedence(operation))
			commit(pop_operation());
		operation_stack.push_back(operation);
	}

	void parse(const char *start) {
		lexer.start(start);
		while(lexer.has_more()) {
			Lexer::Token token = lexer.next();
			switch(token) {
			case Lexer::Token::NUMERAL:
				utility_stack.push_back({z3::Real::value(lexer.buffer), z3::Real::ZERO});
				break;
			case Lexer::Token::IDENTIFIER: {
				Utility utility;
				try {
					utility = constants.at(lexer.buffer);
				}
				catch(const std::out_of_range &) {
					std::cerr << "checkmate: undeclared constant " << lexer.buffer << std::endl;
					std::exit(EXIT_FAILURE);
				}
				utility_stack.push_back(utility);
				break;
			}
			case Lexer::Token::PLUS:
				operation(Operation::PLUS);
				break;
			case Lexer::Token::MINUS:
				operation(Operation::MINUS);
				break;
			case Lexer::Token::MULTIPLY:
				operation(Operation::MULTIPLY);
				break;
			case Lexer::Token::NEGATE:
				operation(Operation::NEGATE);
				break;
			case Lexer::Token::EQ:
				operation(Operation::EQ);
				break;
			case Lexer::Token::NE:
				operation(Operation::NE);
				break;
			case Lexer::Token::GT:
				operation(Operation::GT);
				break;
			case Lexer::Token::GE:
				operation(Operation::GE);
				break;
			case Lexer::Token::OR:
				operation(Operation::OR);
			}
		}
		while(!operation_stack.empty())
			commit(pop_operation());
	}

	Utility parse_utility(const char *start) {
		parse(start);
		if(!constraint_stack.empty() || utility_stack.size() != 1)
			error();
		Utility utility = utility_stack.back();
		utility_stack.clear();
		return utility;
	}

	z3::Bool parse_constraint(const char *start) {
		parse(start);
		if(!utility_stack.empty() || constraint_stack.size() != 1)
			error();
		z3::Bool constraint = constraint_stack.back();
		constraint_stack.clear();
		return constraint;
	}
};

using json = nlohmann::json;

static std::unique_ptr<Node> tree(Parser &parser, const json &node) {
	if(node.contains("children")) {
		std::unique_ptr<Branch> branch(new Branch({node["player"]}));
		for(const json &child : node["children"])
			branch->choices.push_back({
				{child["action"], z3::Bool::fresh()},
				tree(parser, child["child"])
			});
		return branch;
	}
	if(node.contains("utility")) {
		std::unique_ptr<Leaf> leaf(new Leaf);
		for(const json &utility : node["utility"]) {
			const json &value = utility["value"];
			if(value.is_string()) {
				const std::string &string = value;
				leaf->utilities.push_back({
					{utility["player"]},
					parser.parse_utility(string.c_str())
				});
			}
			else if(value.is_number_unsigned()) {
				unsigned number = value;
				leaf->utilities.push_back({
					{utility["player"]},
					{z3::Real::value(number), z3::Real::ZERO}
				});
			}
			else {
				std::cerr << "checkmate: unsupported utility value " << value << std::endl;
				std::exit(EXIT_FAILURE);
			}
		}
		return leaf;
	}
	std::cerr << "checkmate: unexpected object in tree position " << node << std::endl;
	std::exit(EXIT_FAILURE);
}

Input::Input(const char *path) {
	std::ifstream input(path);
	json document;
	Parser parser(utilities);
	try {
		input.exceptions(std::ifstream::failbit | std::ifstream::badbit);
		document = json::parse(input);

		for(const json &player : document["players"])
			players.push_back({player});
		for(const json &real : document["constants"]) {
			const std::string &name = real;
			z3::Real constant = z3::Real::constant(name);
			constants.push_back(constant);
			utilities.insert({name, {constant, z3::Real::ZERO}});
		}
		for(const json &infinitesimal : document["infinitesimals"]) {
			const std::string &name = infinitesimal;
			z3::Real constant = z3::Real::constant(name);
			constants.push_back(constant);
			utilities.insert({name, {z3::Real::ZERO, constant}});
		}

		std::vector<z3::Bool> conjuncts;
		for(const json &initial_constraint : document["initial_constraints"]) {
			const std::string &constraint = initial_constraint;
			conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
		}
		initial_constraint = z3::Bool::conjunction(conjuncts);

		conjuncts.clear();
		for(const json &weak_immunity_constraint : document["property_constraints"]["weak_immunity"]) {
			const std::string &constraint = weak_immunity_constraint;
			conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
		}
		weak_immunity_constraint = z3::Bool::conjunction(conjuncts);

		conjuncts.clear();
		for(const json &weaker_immunity_constraint : document["property_constraints"]["weaker_immunity"]) {
			const std::string &constraint = weaker_immunity_constraint;
			conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
		}
		weaker_immunity_constraint = z3::Bool::conjunction(conjuncts);

		conjuncts.clear();
		for(const json &collusion_resilience_constraint : document["property_constraints"]["collusion_resilience"]) {
			const std::string &constraint = collusion_resilience_constraint;
			conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
		}
		collusion_resilience_constraint = z3::Bool::conjunction(conjuncts);

		conjuncts.clear();
		for(const json &practicality_constraint : document["property_constraints"]["practicality"]) {
			const std::string &constraint = practicality_constraint;
			conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
		}
		practicality_constraint = z3::Bool::conjunction(conjuncts);

		root = tree(parser, document["tree"]);
		for(const json &honest_history : document["honest_histories"]) {
			const Node *current = root.get();
			std::vector<z3::Bool> history;
			for(const json &action : honest_history) {
				const Branch &branch = current->branch();
				const Choice &choice = branch.get_choice(action);
				history.push_back(choice.action.variable);
				current = choice.tree.get();
			}
			honest_histories.push_back(z3::Bool::conjunction(history));
		}
	}
	catch(const std::ifstream::failure &fail) {
		std::cerr << "checkmate: " << std::strerror(errno) << std::endl;
		std::exit(EXIT_FAILURE);
	}
	catch(const json::exception &err) {
		std::cerr << "checkmate: " << err.what() << std::endl;
		std::exit(EXIT_FAILURE);
	}
}
