#include <fstream>
#include <iostream>
#include "json.hpp"

#include "input.hpp"
#include "utils.hpp"

// lexical analysis for expressions
struct Lexer {
	// possible tokens in expressions
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

	// should the next '-' be negation or subtraction?
	bool unary = false;
	// the start of the current expression
	const char *current = nullptr;
	// cursor to the remaining part of `current`
	const char *remaining = nullptr;
	// NUL-terminated copy of the previous token
	std::string buffer;

	// start analysis of the NUL-terminated expression `start`
	void start(const char *start) {
		unary = true;
		current = start;
		remaining = start;
	}

	// check if there are any more tokens, possibly advancing `remaining` past whitespace
	bool has_more() {
		while(std::isspace(*remaining)) remaining++;
		return *remaining;
	}

	// get the next token or exit with failure
	Token next() {
		buffer.clear();
		// a variable name
		if(std::isalpha(*remaining)) {
			buffer.push_back(*remaining++);
			while(std::isalnum(*remaining) || *remaining == '_')
				buffer.push_back(*remaining++);
			unary = false;
			return Token::IDENTIFIER;
		}
		// number
		else if(std::isdigit(*remaining)) {
			buffer.push_back(*remaining++);
			while(std::isdigit(*remaining))
				buffer.push_back(*remaining++);
			unary = false;
			return Token::NUMERAL;
		}
		// operators
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

// parsing for expressions based on the "shunting-yard" algorithm
struct Parser {
	// possible operators to apply to the stack
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

	// operator precedence classes, binding from loosest to tightest
	enum class Precedence {
		OR,
		COMPARISON,
		PLUSMINUS,
		MULTIPLY,
		NEGATE
	};

	// the precedence class of an operator
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

	// construct a parser object based on `identifiers`, but don't parse anything yet
	Parser(const std::unordered_map<std::string, Utility> &identifiers) : identifiers(identifiers) {}

	// map from identifiers to utility terms
	const std::unordered_map<std::string, Utility> &identifiers;
	// lexer for tokenisation
	Lexer lexer;

	// stack of operations
	std::vector<Operation> operation_stack;
	// stack of constructed utility terms
	std::vector<Utility> utility_stack;
	// stack of constructed Boolean expressions
	std::vector<z3::Bool> constraint_stack;

	// bail out from a malformed expression
	[[noreturn]] void error() {
		std::cerr << "checkmate: could not parse expression " << lexer.current << std::endl;
		std::exit(EXIT_FAILURE);
	}

	// pop an operation from the stack
	Operation pop_operation() {
		auto operation = operation_stack.back();
		operation_stack.pop_back();
		return operation;
	}

	// pop a utility from the stack
	Utility pop_utility() {
		if(utility_stack.empty())
			error();
		auto utility = utility_stack.back();
		utility_stack.pop_back();
		return utility;
	}

	// pop a Boolean from the stack
	z3::Bool pop_constraint() {
		if(constraint_stack.empty())
			error();
		auto constraint = constraint_stack.back();
		constraint_stack.pop_back();
		return constraint;
	}

	// once we know we have to apply an operation, commit to it
	void commit(Operation operation) {
		switch(operation) {
		case Operation::PLUS: {
			auto right = pop_utility();
			auto left = pop_utility();
			utility_stack.push_back(left + right);
			break;
		}
		case Operation::MINUS: {
			auto right = pop_utility();
			auto left = pop_utility();
			utility_stack.push_back(left - right);
			break;
		}
		case Operation::MULTIPLY: {
			auto right = pop_utility();
			auto left = pop_utility();
			utility_stack.push_back(left * right);
			break;
		}
		case Operation::NEGATE: {
			auto negate = pop_utility();
			utility_stack.push_back(-negate);
			break;
		}
		case Operation::EQ: {
			auto right = pop_utility();
			auto left = pop_utility();
			constraint_stack.push_back(left == right);
			break;
		}
		case Operation::NE: {
			auto right = pop_utility();
			auto left = pop_utility();
			constraint_stack.push_back(left != right);
			break;
		}
		case Operation::GT: {
			auto right = pop_utility();
			auto left = pop_utility();
			constraint_stack.push_back(left > right);
			break;
		}
		case Operation::GE: {
			auto right = pop_utility();
			auto left = pop_utility();
			constraint_stack.push_back(left >= right);
			break;
		}
		case Operation::OR:
			auto right = pop_constraint();
			auto left = pop_constraint();
			constraint_stack.push_back(left || right);
			break;
		}
	}

	// handle a new `operation`, committing higher-precedence operations and then pushing it on `operation_stack`
	void operation(Operation operation) {
		while(!operation_stack.empty() && precedence(operation_stack.back()) >= precedence(operation))
			commit(pop_operation());
		operation_stack.push_back(operation);
	}

	// parse either a utility term or a Boolean expression, leaving it in the stack
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
					utility = identifiers.at(lexer.buffer);
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
		// when there is no more input, we know all the operators have to be committed
		while(!operation_stack.empty())
			commit(pop_operation());
	}

	// parse a utility term, popping it out from the stack
	Utility parse_utility(const char *start) {
		parse(start);
		if(!constraint_stack.empty() || utility_stack.size() != 1)
			error();
		auto utility = utility_stack.back();
		utility_stack.clear();
		return utility;
	}

	// parse a Boolean term, popping it out from the stack
	z3::Bool parse_constraint(const char *start) {
		parse(start);
		if(!utility_stack.empty() || constraint_stack.size() != 1)
			error();
		auto constraint = constraint_stack.back();
		constraint_stack.clear();
		return constraint;
	}
};

// third-party library for parsing JSON
using json = nlohmann::json;

/*
 * load a tree from a JSON document `node`, assuming a certain format
 * - `input` is the input parsed so far
 * - `action_constraints` are filled out as we go
 *
 * TODO should not be recursive
 * TODO does not check all aspects
 * (hoping to have new input format based on s-expressions, which would be much easier to parse)
 */
static std::unique_ptr<Node> load_tree(const Input &input, std::vector<z3::Bool> &action_constraints, Parser &parser, const json &node) {
	// branch
	if(node.contains("children")) {
		// do linear-time lookup for the index of the node's player in the input player list
		unsigned player;
		for(player = 0; player < input.players.size(); player++)
			if(input.players[player] == node["player"])
				break;
		if(player == input.players.size())
			throw std::logic_error("undeclared player in the input");

		std::vector<z3::Bool> actions;
		std::unique_ptr<Branch> branch(new Branch(player));
		for(const json &child : node["children"]) {
			// fresh variable for each action
			auto action = z3::Bool::fresh();
			branch->choices.push_back({
				{child["action"], action},
				load_tree(input, action_constraints, parser, child["child"])
			});
			actions.push_back(action);
		}

		// single action constraint for this sub-tree
		action_constraints.push_back(exactly_one(actions));
		return branch;
	}

	// leaf
	if(node.contains("utility")) {
		// (player, utility) pairs
		using PlayerUtility = std::pair<std::string, Utility>;
		std::vector<PlayerUtility> player_utilities;
		for(const json &utility : node["utility"]) {
			const json &value = utility["value"];
			// parse a utility expression
			if(value.is_string()) {
				const std::string &string = value;
				player_utilities.push_back({
					utility["player"],
					parser.parse_utility(string.c_str())
				});
			}
			// numeric utility, assumed real
			else if(value.is_number_unsigned()) {
				unsigned number = value;
				player_utilities.push_back({
					utility["player"],
					{z3::Real::value(number), z3::Real::ZERO}
				});
			}
			// foreign object, bail
			else {
				std::cerr << "checkmate: unsupported utility value " << value << std::endl;
				std::exit(EXIT_FAILURE);
			}
		}

		// sort (player, utility) pairs alphabetically by player
		sort(
			player_utilities.begin(),
			player_utilities.end(),
			[](const PlayerUtility &left, const PlayerUtility &right) { return left.first < right.first; }
		);

		std::unique_ptr<Leaf> leaf(new Leaf);
		for(auto &player_utility : player_utilities)
			leaf->utilities.push_back(player_utility.second);
		return leaf;
	}

	// foreign object, bail
	std::cerr << "checkmate: unexpected object in tree position " << node << std::endl;
	std::exit(EXIT_FAILURE);
}

Input::Input(const char *path) {
	// parse a JSON document from `path`
	std::ifstream input(path);
	json document;
	Parser parser(utilities);
	try {
		input.exceptions(std::ifstream::failbit | std::ifstream::badbit);
		document = json::parse(input);
	}
	catch(const std::ifstream::failure &fail) {
		std::cerr << "checkmate: " << std::strerror(errno) << std::endl;
		std::exit(EXIT_FAILURE);
	}
	catch(const json::exception &err) {
		std::cerr << "checkmate: " << err.what() << std::endl;
		std::exit(EXIT_FAILURE);
	}

	if(document["players"].size() > MAX_PLAYERS) {
		std::cerr << "checkmate: more than 64 players not supported - are you sure you want this many?!" << std::endl;
		std::exit(EXIT_FAILURE);
	}

	// load list of players and sort alphabetically
	for(const json &player : document["players"])
		players.push_back({player});
	sort(players.begin(), players.end());

	// load real/infinitesimal identifiers
	for(const json &real : document["constants"]) {
		const std::string &name = real;
		auto constant = z3::Real::constant(name);
		quantify.push_back(constant);
		utilities.insert({name, {constant, z3::Real::ZERO}});
	}
	for(const json &infinitesimal : document["infinitesimals"]) {
		const std::string &name = infinitesimal;
		auto constant = z3::Real::constant(name);
		quantify.push_back(constant);
		utilities.insert({name, {z3::Real::ZERO, constant}});
	}

	// reusable buffer for constraint conjuncts
	std::vector<z3::Bool> conjuncts;

	// initial constraints
	for(const json &initial_constraint : document["initial_constraints"]) {
		const std::string &constraint = initial_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	initial_constraint = z3::Bool::conjunction(conjuncts);

	// weak immunity constraints
	conjuncts.clear();
	for(const json &weak_immunity_constraint : document["property_constraints"]["weak_immunity"]) {
		const std::string &constraint = weak_immunity_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	weak_immunity_constraint = z3::Bool::conjunction(conjuncts);

	// weaker immunity constraints
	conjuncts.clear();
	for(const json &weaker_immunity_constraint : document["property_constraints"]["weaker_immunity"]) {
		const std::string &constraint = weaker_immunity_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	weaker_immunity_constraint = conjunction(conjuncts);

	// collusion resilience constraints
	conjuncts.clear();
	for(const json &collusion_resilience_constraint : document["property_constraints"]["collusion_resilience"]) {
		const std::string &constraint = collusion_resilience_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	collusion_resilience_constraint = conjunction(conjuncts);

	// practicality constraints
	conjuncts.clear();
	for(const json &practicality_constraint : document["property_constraints"]["practicality"]) {
		const std::string &constraint = practicality_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	practicality_constraint = conjunction(conjuncts);

	// buffer for per-node action constraints
	std::vector<z3::Bool> action_constraints;

	// load the game tree and leak it so we can downcast to Branch
	auto node = load_tree(*this, action_constraints, parser, document["tree"]).release();
	if(node->is_leaf()) {
		std::cerr << "checkmate: root node is a leaf (?!) - exiting" << std::endl;
		std::exit(EXIT_FAILURE);
	}
	// un-leaked and downcasted here
	root = std::unique_ptr<Branch>(static_cast<Branch *>(node));

	// load honest histories and work out which leaves they go to
	for(const json &honest_history : document["honest_histories"]) {
		const Node *current = root.get();
		std::vector<z3::Bool> history;
		for(const json &action : honest_history) {
			const auto &branch = current->branch();
			const auto &choice = branch.get_choice(action);
			history.push_back(choice.action.variable);
			current = choice.node.get();
		}
		const auto &leaf = current->leaf();
		honest_histories.push_back(conjunction(history));
		honest_history_leaves.push_back(leaf);
	}
	action_constraint = conjunction(action_constraints);
}
