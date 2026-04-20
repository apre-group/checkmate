#include <fstream>
#include <iostream>
#include "json.hpp"
#include <optional>
#include <variant>

#include "input.hpp"

// lexical analysis for expressions
struct Lexer {
	// possible tokens in expressions
	enum class Token {
		NUMERAL,
		IDENTIFIER,
		LPAREN,
		RPAREN,
		PLUS,
		MINUS,
		MULTIPLY,
		DIVIDE,
		NEGATE,
		EQ,
		NE,
		GT,
		GE,
		LT,
		LE,
		AND,
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
		while (std::isspace(*remaining)) remaining++;
		return *remaining;
	}

	// get the next token or exit with failure
	Token next() {
		buffer.clear();
		// a variable name
		if (std::isalpha(*remaining)) {
			buffer.push_back(*remaining++);
			while (std::isalnum(*remaining) || *remaining == '_')
				buffer.push_back(*remaining++);
			unary = false;
			return Token::IDENTIFIER;
		}
		// number
		else if (std::isdigit(*remaining)) {
			buffer.push_back(*remaining++);
			while (std::isdigit(*remaining) || *remaining == '.')
				buffer.push_back(*remaining++);
			unary = false;
			return Token::NUMERAL;
		}
		else if(*remaining == '(') {
			remaining++;
			unary = true;
			return Token::LPAREN;
		}
		else if(*remaining == ')') {
			remaining++;
			unary = false;
			return Token::RPAREN;
		}
		// operators
		else if (*remaining == '+') {
			remaining++;
			unary = true;
			return Token::PLUS;
		} else if (*remaining == '-') {
			remaining++;
			if (unary)
				return Token::NEGATE;
			unary = true;
			return Token::MINUS;
		} else if (*remaining == '*') {
			remaining++;
			unary = true;
			return Token::MULTIPLY;
		} else if (*remaining == '/') {
			remaining++;
			unary = true;
			return Token::DIVIDE;
		} else if (*remaining == '=') {
			remaining++;
			unary = true;
			return Token::EQ;
		} else if (*remaining == '!' && remaining[1] == '=') {
			remaining += 2;
			unary = true;
			return Token::NE;
		} else if (*remaining == '>') {
			remaining++;
			if (*remaining == '=') {
				remaining++;
				unary = true;
				return Token::GE;
			}
			unary = true;
			return Token::GT;
		} else if (*remaining == '<') {
			remaining++;
			if (*remaining == '=') {
				remaining++;
				unary = true;
				return Token::LE;
			}
			unary = true;
			return Token::LT;
		} else if (*remaining == '|') {
			remaining++;
			unary = true;
			return Token::OR;
		} else if (*remaining == '&') {
			remaining++;
			unary = true;
			return Token::AND;
		} else {
			std::cerr << "checkmate: unexpected character '" << *remaining << "' in expression " << current << std::endl;
			std::exit(EXIT_FAILURE);
		}
	}
};

// parsing for expressions based on the "shunting-yard" algorithm
struct Parser {
	// possible operators to apply to the stack
	enum class Operation {
		PAREN,
		PLUS,
		MINUS,
		MULTIPLY,
		DIVIDE,
		NEGATE,
		EQ,
		NE,
		GT,
		GE,
		LE,
		LT,
		AND,
		OR
	};

	// operator precedence classes, binding from loosest to tightest
	enum class Precedence {
		PAREN,
		ANDOR,
		COMPARISON,
		PLUSMINUS,
		DIVIDE,
		MULTIPLY,
		NEGATE,
	};

	// the precedence class of an operator
	static Precedence precedence(Operation operation) {
		switch (operation) {
			case Operation::PAREN:
				return Precedence::PAREN;
			case Operation::PLUS:
			case Operation::MINUS:
				return Precedence::PLUSMINUS;
			case Operation::MULTIPLY:
				return Precedence::MULTIPLY;
			case Operation::DIVIDE:
				return Precedence::DIVIDE;
			case Operation::NEGATE:
				return Precedence::NEGATE;
			case Operation::EQ:
			case Operation::NE:
			case Operation::GT:
			case Operation::GE:
				return Precedence::COMPARISON;
			case Operation::LT:
			case Operation::LE:
				return Precedence::COMPARISON;
			case Operation::AND:
			case Operation::OR:
				return Precedence::ANDOR;
				return Precedence::ANDOR;
		}
		assert(false);
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
		if (utility_stack.empty())
			error();
		auto utility = utility_stack.back();
		utility_stack.pop_back();
		return utility;
	}

	// pop a Boolean from the stack
	z3::Bool pop_constraint() {
		if (constraint_stack.empty())
			error();
		auto constraint = constraint_stack.back();
		constraint_stack.pop_back();
		return constraint;
	}

	// once we know we have to apply an operation, commit to it
	void commit(Operation operation) {
		switch (operation) {
			case Operation::PAREN:
				// nothing to do
				break;
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
			case Operation::DIVIDE: {
				auto right = pop_utility();
				auto left = pop_utility();
				utility_stack.push_back(left / right);
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
			case Operation::LT: {
				auto right = pop_utility();
				auto left = pop_utility();
				constraint_stack.push_back(left < right);
				break;
			}
			case Operation::LE: {
				auto right = pop_utility();
				auto left = pop_utility();
				constraint_stack.push_back(left <= right);
				break;
			}
			case Operation::AND: {
				auto right = pop_constraint();
				auto left = pop_constraint();
				constraint_stack.push_back(left && right);
				break;
			}
			case Operation::OR: {
				auto right = pop_constraint();
				auto left = pop_constraint();
				constraint_stack.push_back(left || right);
				break;
			}
		}
	}

	// handle a new `operation`, committing higher-precedence operations and then pushing it on `operation_stack`
	void operation(Operation operation) {
		while (!operation_stack.empty() && precedence(operation_stack.back()) >= precedence(operation))
			commit(pop_operation());
		operation_stack.push_back(operation);
	}

	// parse either a utility term or a Boolean expression, leaving it in the stack
	void parse(const char *start) {
		lexer.start(start);
		while (lexer.has_more()) {
			Lexer::Token token = lexer.next();
			switch (token) {
				case Lexer::Token::NUMERAL:
					utility_stack.push_back({z3::Real::value(lexer.buffer), z3::Real::ZERO});
					break;
				case Lexer::Token::IDENTIFIER: {
					Utility utility;
					try {
						utility = identifiers.at(lexer.buffer);
					}
					catch (const std::out_of_range &) {
						std::cerr << "checkmate: undeclared constant " << lexer.buffer << std::endl;
						std::exit(EXIT_FAILURE);
					}
					utility_stack.push_back(utility);
					break;
				}
				case Lexer::Token::LPAREN: {
					operation_stack.push_back(Operation::PAREN);
					break;
				}
				case Lexer::Token::RPAREN: {
					while (!operation_stack.empty() && operation_stack.back() != Operation::PAREN)
						commit(pop_operation());
					pop_operation();
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
				case Lexer::Token::DIVIDE:
					operation(Operation::DIVIDE);
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
				case Lexer::Token::LT:
					operation(Operation::LT);
					break;
				case Lexer::Token::LE:
					operation(Operation::LE);
					break;
				case Lexer::Token::AND:
					operation(Operation::AND);
					break;
				case Lexer::Token::OR:
					operation(Operation::OR);
					break;
			}
		}
		// when there is no more input, we know all the operators have to be committed
		while (!operation_stack.empty())
			commit(pop_operation());
	}

	// parse a utility term, popping it out from the stack
	Utility parse_utility(const char *start) {
		parse(start);
		if (!constraint_stack.empty() || utility_stack.size() != 1)
			error();
		auto utility = utility_stack.back();
		utility_stack.clear();
		return utility;
	}

	// parse a Boolean term, popping it out from the stack
	z3::Bool parse_constraint(const char *start) {
		parse(start);
		if (!utility_stack.empty() || constraint_stack.size() != 1)
			error();
		auto constraint = constraint_stack.back();
		constraint_stack.clear();
		return constraint;
	}
};

// third-party library for parsing JSON
using json = nlohmann::json;

static z3::Bool parse_case(Parser &parser, const std::string &_case) {
	if(_case == "true")
		return true;

	return parser.parse_constraint(_case.c_str());
}

// Forward declarations
static HonestUtilityElement parse_honest_utility_element(Parser &parser, const json &element, const Input &input);

/*
 * load a tree from a JSON document `node`, assuming a certain format
 * - `input` is the input parsed so far
 * - `action_constraints` are filled out as we go
 *
 * TODO does not check all aspects
 * (hoping to have new input format based on s-expressions, which would be much easier to parse)
 */
static std::unique_ptr<Node> load_tree(const Input &input, Parser &parser, const json &node, bool supertree) {
	// branch
	if (node.contains("children")) {
		// do linear-time lookup for the index of the node's player in the input player list
		unsigned player;
		for (player = 0; player < input.players.size(); player++)
			if (input.players[player] == node["player"])
				break;
		if (player == input.players.size())
			throw std::logic_error("undeclared player in the input");

		std::unique_ptr<Branch> branch(new Branch(player));
		for (const json &child: node["children"]) {
			auto loaded = load_tree(input, parser, child["child"], supertree);

			branch->choices.push_back({child["action"], std::move(loaded)});
		}
		return branch;
	}

	// condition node
	if (node.contains("condition")) {
		std::unique_ptr<ConditionNode> condition_node(new ConditionNode());
		for (const json &cond: node["condition"]) {
			// parse the condition constraint
			const std::string &condition_str = cond["constraint"];
			z3::Bool condition = parser.parse_constraint(condition_str.c_str());
			
			// load the child subtree
			auto loaded = load_tree(input, parser, cond["child"], supertree);
			
			condition_node->conditions.push_back({condition, std::move(loaded)});
		}
		return condition_node;
	}

	// leaf 
	if (node.contains("utility")) {
		// (player, utility) pairs
		using PlayerUtility = std::pair<std::string, Utility>;
		std::vector<PlayerUtility> player_utilities;
		for (const json &utility: node["utility"]) {
			const json &value = utility["value"];
			// parse a utility expression
			if (value.is_string()) {
				const std::string &string = value;
				player_utilities.push_back({
												   utility["player"],
												   parser.parse_utility(string.c_str())
										   });
			}
				// numeric utility, assumed real
			else if (value.is_number_unsigned()) {
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
		for (auto &player_utility: player_utilities)
			leaf->utilities.push_back(player_utility.second);
		return leaf;
	}

	// subtree summary
	if (node.contains("subtree")) {

		// Remove the check below for the purpose of allowing nesting of subtrees in subtress 
		/*if (!supertree) {
			// subtree nodes can only occur in supertree mode!
			std::cerr << "checkmate: unexpected subtree node; call in --supertree mode " << node << std::endl;
			std::exit(EXIT_FAILURE);
		}*/

		std::vector<SubtreeResult> weak_immunity = {};
		std::vector<SubtreeResult> weaker_immunity = {};
		std::vector<SubtreeResult> collusion_resilience = {};
		std::vector<PracticalitySubtreeResult> practicality = {};


		if (node["subtree"].contains("weak_immunity")){
			for (const json &wi: node["subtree"]["weak_immunity"]) {
				const json &players_json = wi["player_group"];
				std::vector<std::string> player_group;
				for (const auto &player : players_json){
					if (player.is_string()){
						player_group.push_back(player);
					} else {
						std::cerr << "checkmate: unsupported player value " << player << std::endl;
						std::exit(EXIT_FAILURE);
					}
				}
				std::vector<std::vector<z3::Bool>> satisfied_in_case = {};

				const json &cases = wi["satisfied_in_case"];
				for (const json &json_case: cases) {
					std::vector<z3::Bool> _case = {};
					for (const json &_case_entry: json_case) {
						if(_case_entry != "true") {
							const std::string &_case_e = _case_entry;
							_case.push_back(parse_case(parser, _case_e));
						}
					}
					satisfied_in_case.push_back(_case);					
				}

				SubtreeResult wi_result { player_group, satisfied_in_case };
				weak_immunity.push_back(wi_result);
			}
		}

		if (node["subtree"].contains("weaker_immunity")){
			for (const json &weri: node["subtree"]["weaker_immunity"]) {
				const json &players_json = weri["player_group"];
				std::vector<std::string> player_group = {};
				for (const auto &player : players_json){
					if (player.is_string()){
						player_group.push_back(player);
					} else {
						std::cerr << "checkmate: unsupported player value " << player << std::endl;
						std::exit(EXIT_FAILURE);
					}
				}
				std::vector<std::vector<z3::Bool>> satisfied_in_case = {};

				const json &cases = weri["satisfied_in_case"];
				for (const json &json_case: cases) {
					std::vector<z3::Bool> _case = {};
					for (const json &_case_entry: json_case) {
						if(_case_entry != "true") {
							const std::string &_case_e = _case_entry;
							_case.push_back(parse_case(parser, _case_e));
						}
					}
					satisfied_in_case.push_back(_case);					
				}

				SubtreeResult weri_result { player_group, satisfied_in_case };
				weaker_immunity.push_back(weri_result);
			}
		}

		if (node["subtree"].contains("collusion_resilience")){
			for (const json &cr: node["subtree"]["collusion_resilience"]) {
				const json &players_json = cr["player_group"];
				std::vector<std::string> player_group = {};
				for (const auto &player : players_json){
					if (player.is_string()){
						player_group.push_back(player);
					} else {
						std::cerr << "checkmate: unsupported player value " << player << std::endl;
						std::exit(EXIT_FAILURE);
					}
				}
				std::vector<std::vector<z3::Bool>> satisfied_in_case = {};

				const json &cases = cr["satisfied_in_case"];
				for (const json &json_case: cases) {
					std::vector<z3::Bool> _case = {};
					for (const json &_case_entry: json_case) {
						if(_case_entry != "true") {
							const std::string &_case_e = _case_entry;
							_case.push_back(parse_case(parser, _case_e));
						}
					}
					satisfied_in_case.push_back(_case);					
				}

				SubtreeResult cr_result { player_group, satisfied_in_case };
				collusion_resilience.push_back(cr_result);
			}
		}

		if (node["subtree"].contains("practicality")) {
			
			for (const json &pr: node["subtree"]["practicality"]) {
				const json &_case_pr = pr["case"];
				std::vector<z3::Bool> _case = {};
				for (const json &_case_entry: _case_pr) {
					if(_case_entry != "true") {
						const std::string &_case_e = _case_entry;
						_case.push_back(parse_case(parser, _case_e));
					}
				}
				std::vector<Cond_Utility> utilities = {};

				for (const json& utility_tuple: pr["utilities"]) {

					
					using PlayerUtility = std::pair<std::string, Utility>;
					std::vector<PlayerUtility> player_utilities;
					for (const json &utility: utility_tuple["utility"]) {
						const json &value = utility["value"];
						// parse a utility expression
						if (value.is_string()) {
							const std::string &string = value;
							player_utilities.push_back({
															utility["player"],
															parser.parse_utility(string.c_str())
													});
						}
							// numeric utility, assumed real
						else if (value.is_number_unsigned()) {
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

					std::vector<Utility> pr_utility = {};
					for (auto &player_utility: player_utilities)
						pr_utility.push_back(player_utility.second);

					const json &pr_condition_json = utility_tuple["condition"];
					assert(pr_condition_json.is_string());
					const std::string &string = pr_condition_json;
				
					z3::Bool pr_condition = parser.parse_constraint(string.c_str());

					Cond_Utility cond_utility {pr_utility, pr_condition};
					//std::cout << pr_utility << std::endl;
					utilities.push_back(cond_utility);
				}

				PracticalitySubtreeResult pr_sub_result { _case, utilities };

				practicality.push_back(pr_sub_result);
			}
		}

		// Parse honest_utility (default to empty vector if not present)
		HonestUtilityElement honest_utility = std::vector<Utility>();
		if (node["subtree"].contains("honest_utility")) {
			honest_utility = parse_honest_utility_element(parser, node["subtree"]["honest_utility"], input);
		}


		std::unique_ptr<Subtree> subtree(new Subtree(weak_immunity, weaker_immunity, collusion_resilience, practicality, honest_utility));

		return subtree;
	}

	// foreign object, bail
	std::cerr << "checkmate: unexpected object in tree position " << node << std::endl;
	std::exit(EXIT_FAILURE);
}

// Parse a single honest history element (can be an action string or a list of conditional branches)
static HonestHistoryElement parse_honest_history_element(Parser &parser, const json &element) {
	// If it's a string, it's an action
	if (element.is_string()) {
		return HonestHistoryElement(std::string(element));
	}
	
	// If it's an array of condition objects, parse each
	if (element.is_array()) {
		std::vector<HonestHistoryCondition> conditions;
		for (const json &cond_obj : element) {
			if (cond_obj.contains("condition")) {
				const std::string &condition_str = cond_obj["condition"];
				z3::Bool condition = parser.parse_constraint(condition_str.c_str());
				
				// Recursively parse the path
				std::vector<HonestHistoryElement> path;
				for (const json &path_element : cond_obj["path"]) {
					path.push_back(parse_honest_history_element(parser, path_element));
				}
				
				conditions.push_back(HonestHistoryCondition(condition, path));
			}
			else {
				std::cerr << "checkmate: expected condition object in honest history element " << cond_obj << std::endl;
				std::exit(EXIT_FAILURE);
			}
		}
		return HonestHistoryElement(conditions);
	}
	
	// Unknown format, bail
	std::cerr << "checkmate: unexpected honest history element format " << element << std::endl;
	std::exit(EXIT_FAILURE);
}

// Parse a complete honest history (sequence of elements)
static HonestHistory parse_honest_history(Parser &parser, const json &history_json) {
	HonestHistory history;
	for (const json &element : history_json) {
		history.push_back(parse_honest_history_element(parser, element));
	}
	return history;
}

// Parse utility vector from JSON (helper for honest_utility)
static std::vector<Utility> parse_utility_vector(Parser &parser, const json &utility_json) {
	using PlayerUtility = std::pair<std::string, Utility>;
	std::vector<PlayerUtility> player_utilities;
	
	for (const json &utility: utility_json) {
		const json &value = utility["value"];
		// parse a utility expression
		if (value.is_string()) {
			const std::string &string = value;
			player_utilities.push_back({
											utility["player"],
											parser.parse_utility(string.c_str())
									});
		}
		// numeric utility, assumed real
		else if (value.is_number_unsigned()) {
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

	std::vector<Utility> result;
	for (auto &player_utility: player_utilities)
		result.push_back(player_utility.second);
	
	return result;
}

// Parse a single honest utility element (can be a utility vector or a list of conditional branches)
static HonestUtilityElement parse_honest_utility_element(Parser &parser, const json &element, const Input &input) {

	// If it's an array, check if it contains condition objects or utility objects
	if (element.is_array()) {
		// Check first element to determine type
		if (!element.empty() && element[0].is_object()) {
			if (element[0].contains("condition")) {
				// It's an array of condition objects
				std::vector<HonestUtilityCondition> conditions;
				for (const json &cond_obj : element) {
					const std::string &condition_str = cond_obj["condition"];
					z3::Bool condition = parser.parse_constraint(condition_str.c_str());
					
					// Recursively parse the utility
					HonestUtilityElement utility_element = parse_honest_utility_element(parser, cond_obj["utility"], input);
					
					conditions.push_back(HonestUtilityCondition(condition, utility_element));
				}
				return HonestUtilityElement(conditions);
			} else if (element[0].contains("player")) {
				// It's a utility vector
				return HonestUtilityElement(parse_utility_vector(parser, element));
			}
		}
	}
	
	// Unknown format, bail
	std::cerr << "checkmate: unexpected honest utility format " << element << std::endl;
	std::exit(EXIT_FAILURE);
}



Input::Input(const char *path, bool supertree) : sat_cases(), strategies() , stop_log(false) {
	// parse a JSON document from `path`
	std::ifstream input(path);
	json document;
	try {
		input.exceptions(std::ifstream::failbit | std::ifstream::badbit);
		document = json::parse(input);
	}
	catch (const std::ifstream::failure &fail) {
		std::cerr << "checkmate: " << std::strerror(errno) << std::endl;
		std::exit(EXIT_FAILURE);
	}
	catch (const json::exception &err) {
		std::cerr << "checkmate: " << err.what() << std::endl;
		std::exit(EXIT_FAILURE);
	}

	if (document["players"].size() > MAX_PLAYERS) {
		std::cerr << "checkmate: more than 64 players not supported - are you sure you want this many?!" << std::endl;
		std::exit(EXIT_FAILURE);
	}

	// load list of players and sort alphabetically
	for (const json &player: document["players"])
		players.push_back(std::string(player));
	sort(players.begin(), players.end());

	// load real/infinitesimal identifiers
	for (const json &real: document["constants"]) {
		const std::string &name = real;
		auto constant = z3::Real::constant(name);
		utilities.insert({name, {constant, z3::Real::ZERO}});
	}
	for (const json &infinitesimal: document["infinitesimals"]) {
		const std::string &name = infinitesimal;
		auto constant = z3::Real::constant(name);
		utilities.insert({name, {z3::Real::ZERO, constant}});
	}

	Parser parser(utilities);
	// load honest histories automatically
	for (const json &history_json : document["honest_histories"]) {
		honest.push_back(parse_honest_history(parser, history_json));
	}



	if(document["honest_utilities"].size() > 0 && supertree) {
		std::cerr << "checkmate: honest utilities should not be specified in supertree mode " << std::endl;
		std::exit(EXIT_FAILURE);
	}

	// load honest utilities
	for (const auto &utility_dict : document["honest_utilities"]) {
		// Parse the "utility" field which can be either a simple utility vector or conditional structure
		HonestUtilityElement *element = new HonestUtilityElement(
			parse_honest_utility_element(parser, utility_dict["utility"], *this)
		);
		
		HonestUtilityTuple utilityTuple(*element);
		honest_utilities.push_back(utilityTuple);
	}


	// reusable buffer for constraint conjuncts
	std::vector<z3::Bool> conjuncts;

	// initial constraints
	for (const json &initial_constraint: document["initial_constraints"]) {
		const std::string &constraint = initial_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	initial_constraint = z3::Bool::conjunction(conjuncts);

	// weak immunity constraints
	conjuncts.clear();
	for (const json &weak_immunity_constraint: document["property_constraints"]["weak_immunity"]) {
		const std::string &constraint = weak_immunity_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	weak_immunity_constraint = z3::Bool::conjunction(conjuncts);

	// weaker immunity constraints
	conjuncts.clear();
	for (const json &weaker_immunity_constraint: document["property_constraints"]["weaker_immunity"]) {
		const std::string &constraint = weaker_immunity_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	weaker_immunity_constraint = conjunction(conjuncts);

	// collusion resilience constraints
	conjuncts.clear();
	for (const json &collusion_resilience_constraint: document["property_constraints"]["collusion_resilience"]) {
		const std::string &constraint = collusion_resilience_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	collusion_resilience_constraint = conjunction(conjuncts);

	// practicality constraints
	conjuncts.clear();
	for (const json &practicality_constraint: document["property_constraints"]["practicality"]) {
		const std::string &constraint = practicality_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	practicality_constraint = conjunction(conjuncts);


	// load the game tree and leak it so we can downcast to Branch or ConditionNode
	auto node = load_tree(*this, parser, document["tree"], supertree).release();

	if (node->is_leaf() || node->is_subtree()) {
		std::cerr << "checkmate: root node is a leaf or a subtree (?!) - exiting" << std::endl;
		std::exit(EXIT_FAILURE);
	}
	// un-leaked and downcasted here
	root = std::unique_ptr<Node>(static_cast<Node *>(node));
}



std::vector<HistoryChoice> Node::compute_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far) const {

		if (this -> is_leaf() || this->is_subtree()){
			return {};
		}
		std::vector<HistoryChoice> strategy;

		if (this->is_branch()) {
			if (!this->branch().strategy.empty()){
				HistoryChoice hist_choice;
				hist_choice.player = players[this->branch().player];
				hist_choice.choice = this->branch().strategy;
				hist_choice.history = actions_so_far;

				strategy.push_back(hist_choice);
			}
			
			for (const Choice &choice: this->branch().choices) {
				std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
				updated_actions.push_back(choice.action);
				std::vector<HistoryChoice> child_strategy = choice.node->compute_strategy(players, updated_actions);
				strategy.insert(strategy.end(), child_strategy.begin(), child_strategy.end());
			}
		} else if (this->is_condition_node()) {
			// For condition nodes, recursively compute strategy for all conditional branches
			// since no action itself is taken at a condition node, we only track the condition in the history;
			for (const ConditionChoice &cond_choice: this->condition_node().conditions) {
				std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
				z3::Bool condition = cond_choice.condition;
				updated_actions.push_back(condition.to_string()); // Add the condition to the history for tracking purposes
				std::vector<HistoryChoice> child_strategy = cond_choice.node->compute_strategy(players, updated_actions);
				strategy.insert(strategy.end(), child_strategy.begin(), child_strategy.end());
			}
		}
		
		return strategy;
	}

bool Node::cr_against_all() const {
	bool cr_against_all = true;

	for(auto violates_colluding_group : violates_cr) {

		if(violates_colluding_group) {
			cr_against_all = false;
		}
	}

	return cr_against_all;
}

std::vector<bool> convertToBinary(uint n)
{
	std::vector<bool> bit_reps;

    if (n / 2 != 0) {
        bit_reps = convertToBinary(n / 2);
    }

	bit_reps.push_back(n % 2 == 1);
	return bit_reps;
}

bool Node::cr_against_supergroups_of(std::vector<uint> deviating_players) const {

	for(uint64_t i=0; i < violates_cr.size(); i++) {
		std::vector<bool> bin_rep = convertToBinary(i+1);

		bool all_deviating_deviate = true;

		for(auto player: deviating_players) {
			if(player > bin_rep.size()) {
				all_deviating_deviate = false;
			} else {
				if(!bin_rep[player-1]) {
					all_deviating_deviate = false;
				}
			}			
		}

		if(all_deviating_deviate && violates_cr[i]) {
			return false;
		}

	}

	return true;

}

void Node::add_violation_cr() const {
	violates_cr.push_back(false);

	if (!this->is_leaf() && !this->is_subtree()){

		if (this->is_branch()) {
			for (const auto& child: this->branch().choices){
				child.node->add_violation_cr();
			}
		} else if (this->is_condition_node()) {
			for (const auto& cond_choice: this->condition_node().conditions) {
				cond_choice.node->add_violation_cr();
			}
		}
	}
	return;
}

std::vector<HistoryChoice> Node::compute_cr_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<uint> deviating_players) const {

		if (this -> is_leaf() || this->is_subtree()){
			return {};
		}
		std::vector<HistoryChoice> strategy;
		std::string strategy_choice;

		if (this->is_branch()) {
			if (honest) {
				for (const Choice &choice: this->branch().choices) {

					if (choice.node->honest) {
						assert(choice.node->cr_against_all());
						HistoryChoice hist_choice;
						hist_choice.player = players[this->branch().player];
						hist_choice.choice = choice.action;
						hist_choice.history = actions_so_far;
						strategy_choice = choice.action;

						strategy.push_back(hist_choice);
						break;
					}
				}
			} else {
				bool have_found_cr = false;
				for (const Choice &choice: this->branch().choices) {

					if (choice.node->cr_against_supergroups_of(deviating_players)){
						if(!have_found_cr) {
							have_found_cr = true;
							HistoryChoice hist_choice;
							hist_choice.player = players[this->branch().player];
							hist_choice.choice = choice.action;
							hist_choice.history = actions_so_far;
							strategy_choice = choice.action;

							strategy.push_back(hist_choice);
						}
					}

				}
				assert(have_found_cr);
			}
			
			for (const Choice &choice: this->branch().choices) {
				std::vector<uint> new_deviating_players;
				new_deviating_players.insert(new_deviating_players.end(), deviating_players.begin(), deviating_players.end());

				int cnt = std::count(deviating_players.begin(), deviating_players.end(), this->branch().player + 1);
				if((choice.action != strategy_choice) && (cnt == 0)) {
					new_deviating_players.push_back(this->branch().player + 1);
				}

				std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
				updated_actions.push_back(choice.action);

				std::vector<HistoryChoice> child_strategy = choice.node->compute_cr_strategy(players, updated_actions, new_deviating_players); 
				strategy.insert(strategy.end(), child_strategy.begin(), child_strategy.end());
			}
		} else if (this->is_condition_node()) {
			// For condition nodes, recursively compute cr_strategy for all conditional branches
			for (const ConditionChoice &cond_choice: this->condition_node().conditions) {

				std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
				z3::Bool condition = cond_choice.condition;
				updated_actions.push_back(condition.to_string()); // Add the condition to the history for tracking purposes

				std::vector<HistoryChoice> child_strategy = cond_choice.node->compute_cr_strategy(players, updated_actions, deviating_players);
				strategy.insert(strategy.end(), child_strategy.begin(), child_strategy.end());
			}
		}
		
		return strategy;
	}

std::vector<HistoryChoice> Node::compute_pr_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far, const StrategyElement& strategy_element, std::vector<std::string> conditions_so_far) const {

	if (this -> is_leaf() || this->is_subtree()){
		assert(std::holds_alternative<std::optional<Strategy>>(strategy_element));
		assert(!std::get<std::optional<Strategy>>(strategy_element).has_value());
		return {};
	}

	std::vector<HistoryChoice> choices;

	if (std::holds_alternative<std::optional<Strategy>>(strategy_element)) {

		assert(std::get<std::optional<Strategy>>(strategy_element).has_value());
		const Strategy& given_strategy = std::get<std::optional<Strategy>>(strategy_element).value();

		if (this->is_branch()){				
			HistoryChoice hist_choice;
			hist_choice.player = players[this->branch().player];
			hist_choice.choice = given_strategy.root_action;
			hist_choice.history = actions_so_far;
			hist_choice.condition = conditions_so_far;
			choices.push_back(hist_choice);

			unsigned int i = 0;
			for (const StrategyElement& child_strategy_element: given_strategy.children_strategies) {
				std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
				updated_actions.push_back(this->branch().choices[i].action);
				
				std::vector<HistoryChoice> child_choices = this->branch().choices[i].node->compute_pr_strategy(players, updated_actions, child_strategy_element, conditions_so_far);


				choices.insert(choices.end(), child_choices.begin(), child_choices.end());
				i++;
			}

			return choices;

		}
		else if (this->is_condition_node()) {
			// For condition nodes, only one condition is there since these are the strategies that make a specific utility practical,
			// this condition probably has to be added to case

			std::string current_condition = std::get<std::optional<Strategy>>(strategy_element).value().root_action;
			assert(std::get<std::optional<Strategy>>(strategy_element).value().children_strategies.size() == 1); // should only be one child strategy since only one condition should make the utility practical
			for (const ConditionChoice &cond_choice: this->condition_node().conditions) {
				if (cond_choice.condition.to_string() == current_condition) {

					std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
					updated_actions.push_back(current_condition); // Add the condition to the history for tracking purposes
					std::vector<HistoryChoice> child_choices = cond_choice.node->compute_pr_strategy(players, updated_actions, std::get<std::optional<Strategy>>(strategy_element).value().children_strategies[0], conditions_so_far);					// this condition is added later when different choices have to be combined (ConditionStrategy)
					// for (StrategyCase& child_case: child_strategy_case) {
					// 	child_case._case.push_back(cond_choice.condition); 
					// }
					
					return child_choices;
				}
			}
			assert(false); // should have found the condition in the condition node
		}

		return choices;

	} else {
		std::vector<ConditionStrategy> condition_strategies = std::get<std::vector<ConditionStrategy>>(strategy_element);

		if (this->is_branch()){
			assert(!condition_strategies.empty());
			for (ConditionStrategy& condition_strategy: condition_strategies) {

				assert(condition_strategy.strategy.has_value());
				Strategy& given_strategy = condition_strategy.strategy.value();

				std::vector<std::string> updated_conditions(conditions_so_far.begin(), conditions_so_far.end());
				updated_conditions.push_back(condition_strategy.condition.to_string()); 

				HistoryChoice hist_choice;
				hist_choice.player = players[this->branch().player];
				hist_choice.choice = given_strategy.root_action;
				hist_choice.history = actions_so_far;
				hist_choice.condition = updated_conditions;
				choices.push_back(hist_choice);

				unsigned int i = 0;
				for (const StrategyElement& child_strategy_element: given_strategy.children_strategies) {
					std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
					updated_actions.push_back(this->branch().choices[i].action);
					
					std::vector<HistoryChoice> child_choices = this->branch().choices[i].node->compute_pr_strategy(players, updated_actions, child_strategy_element, updated_conditions);


					choices.insert(choices.end(), child_choices.begin(), child_choices.end());
					i++;
				}
	
			}
			return choices;
			

		} else {
			assert(this->is_condition_node()); 
			assert(!condition_strategies.empty());
			for (ConditionStrategy& condition_strategy: condition_strategies) {
				assert(condition_strategy.strategy.has_value());
				Strategy& given_strategy = condition_strategy.strategy.value();

				std::vector<std::string> updated_conditions(conditions_so_far.begin(), conditions_so_far.end());
				updated_conditions.push_back(condition_strategy.condition.to_string()); 

				std::string current_condition = given_strategy.root_action;
				assert(given_strategy.children_strategies.size() == 1); // should only be one child strategy since only one condition should make the utility practical
				for (const ConditionChoice &cond_choice: this->condition_node().conditions) {
					if (cond_choice.condition.to_string() == current_condition) {

						std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
						updated_actions.push_back(current_condition); // Add the condition to the history for tracking purposes
						std::vector<HistoryChoice> child_choices = cond_choice.node->compute_pr_strategy(players, updated_actions, given_strategy.children_strategies[0], updated_conditions);

						// this condition is added later when different choices have to be combined (ConditionStrategy)
						// for (StrategyCase& child_case: child_strategy_case) {
						// 	child_case._case.push_back(cond_choice.condition); 
						// }
						
						return child_choices;
					}
				}
			}
			assert(false); // should have found the condition in the condition node
		}
		
	}
	
	return choices;
}


std::vector<CeChoice> Node::compute_wi_ce(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<size_t> player_group) const {

		if (this->is_leaf() || this->is_subtree()){
			return {};
		}
		std::vector<CeChoice> counterexample;

		assert(player_group.size() == 1);

		if (this->is_branch()){
			if (player_group[0] == this->branch().player) {
				if (honest){
					for (auto& child: this->branch().choices){
						if (child.node->honest) {
							std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
							updated_actions.push_back(child.action);
							counterexample = child.node->compute_wi_ce(players, updated_actions, player_group);
							break;
						}
					}
				} else {
					for (auto& child: this->branch().choices){
							std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
							updated_actions.push_back(child.action);
							std::vector<CeChoice> child_counterexample = child.node->compute_wi_ce(players, updated_actions, player_group);
							counterexample.insert(counterexample.end(),child_counterexample.begin(), child_counterexample.end());
					}
				}
			} else {
				assert(!this->branch().counterexample_choices.empty());
				CeChoice ce_choice;
				ce_choice.player = players[this->branch().player];
				ce_choice.choices = this->branch().counterexample_choices;
				ce_choice.history = actions_so_far;

				counterexample.push_back(ce_choice);

				for (const Choice &choice: this->branch().choices) {

					int cnt = std::count(this->branch().counterexample_choices.begin(), this->branch().counterexample_choices.end(), choice.action);
					if (cnt > 0) {
						std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
						updated_actions.push_back(choice.action);
						std::vector<CeChoice> child_ce = choice.node->compute_wi_ce(players, updated_actions, player_group);
						counterexample.insert(counterexample.end(), child_ce.begin(), child_ce.end());
					}
				}
			}
		} else if (this->is_condition_node()) {
			assert(!this->condition_node().counterexample_choices.empty());
				CeChoice ce_choice;
				ce_choice.player = std::nullopt; // no player associated with condition nodes
				ce_choice.choices = this->condition_node().counterexample_choices;
				ce_choice.history = actions_so_far;

				counterexample.push_back(ce_choice);

				for (const ConditionChoice &cond_choice: this->condition_node().conditions) {
				z3::Bool condition = cond_choice.condition;
				int cnt = std::count(this->condition_node().counterexample_choices.begin(), this->condition_node().counterexample_choices.end(), condition.to_string());
				if (cnt > 0) {
					std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
					}
				}
		}
		return counterexample;
	}

std::vector<CeChoice> Node::compute_cr_ce(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<size_t> player_group) const {

		if (this->is_leaf() || this->is_subtree()){
			return {};
		}
		std::vector<CeChoice> counterexample;

		assert(player_group.size() >= 1);

		if (this->is_branch()){
			int cnt = std::count(player_group.begin(), player_group.end(), this->branch().player);
			if (cnt == 0) {
				if (honest){
					for (auto& child: this->branch().choices){
						if (child.node->honest) {
							std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
							updated_actions.push_back(child.action);
							counterexample = child.node->compute_cr_ce(players, updated_actions, player_group);
							break;
						}
					}
				} else {
					for (auto& child: this->branch().choices){
							std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
							updated_actions.push_back(child.action);
							std::vector<CeChoice> child_counterexample = child.node->compute_cr_ce(players, updated_actions, player_group);
							counterexample.insert(counterexample.end(),child_counterexample.begin(), child_counterexample.end());
					}
				}
			} else {
				assert(!this->branch().counterexample_choices.empty());
				CeChoice ce_choice;
				ce_choice.player = players[this->branch().player];
				ce_choice.choices = this->branch().counterexample_choices;
				ce_choice.history = actions_so_far;

				counterexample.push_back(ce_choice);

				for (const Choice &choice: this->branch().choices) {

					int cnt = std::count(this->branch().counterexample_choices.begin(), this->branch().counterexample_choices.end(), choice.action);
					if (cnt > 0) {
						std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
						updated_actions.push_back(choice.action);
						std::vector<CeChoice> child_ce = choice.node->compute_cr_ce(players, updated_actions, player_group);
						counterexample.insert(counterexample.end(), child_ce.begin(), child_ce.end());
					}
				}
			}
		} else if (this->is_condition_node()) {
			assert(!this->condition_node().counterexample_choices.empty());
				CeChoice ce_choice;
				ce_choice.player = std::nullopt; // no player associated with condition nodes
				ce_choice.choices = this->condition_node().counterexample_choices;
				ce_choice.history = actions_so_far;

				counterexample.push_back(ce_choice);

				for (const ConditionChoice &cond_choice: this->condition_node().conditions) {
				z3::Bool condition = cond_choice.condition;
				int cnt = std::count(this->condition_node().counterexample_choices.begin(), this->condition_node().counterexample_choices.end(), condition.to_string());
				if (cnt > 0) {
					std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
					}
				}
		}
		return counterexample;
	}

CeCase Node::compute_pr_cecase(std::vector<std::string> players, unsigned current_player, std::vector<std::string> actions_so_far, std::string current_action, UtilityTuplesSet practical_utilities) const {
	
	// regular case (called from branch or a condition node)
	if(current_player < players.size()) {
		CeCase cecase;
		cecase.player_group = {players[current_player]};

		const Node* deviation_node = nullptr;

		std::vector<std::string> actions_to_deviation;
		actions_to_deviation.insert(actions_to_deviation.end(), actions_so_far.begin(), actions_so_far.end());
		actions_to_deviation.push_back(current_action); // BE AWARE: current_action = action leading to subtree where pr histories are ce

		deviation_node = compute_deviation_node(actions_to_deviation);
		std::vector<CeChoice> rec_choices = deviation_node->compute_pr_ce(current_action, actions_so_far, practical_utilities);
		cecase.counterexample.insert(cecase.counterexample.end(), rec_choices.begin(), rec_choices.end());
		return cecase;
	} else {
		// called from subtree
		CeCase cecase;
		cecase.player_group = {}; // check and handle this when printing counterexamples

		CeChoice deviation;
		deviation.history = actions_so_far;
		cecase.counterexample = {deviation};
	
		return cecase;

	}
}

const Node* Node::compute_deviation_node(std::vector<std::string> actions_so_far) const {
	
	if(actions_so_far.size() > 0) { 
		assert(!this->is_leaf());
		assert(!this->is_subtree());
		if (this->is_branch()) {
			for (const auto &child: this->branch().choices){
				if(child.action == actions_so_far[0]) {
					actions_so_far.erase(actions_so_far.begin());
					return child.node.get()->compute_deviation_node(actions_so_far);
				}
			}
		} else if (this->is_condition_node()) {
			for (const auto &cond_choice: this->condition_node().conditions) {
				z3::Bool condition = cond_choice.condition;
				if(condition.to_string() == actions_so_far[0]) {
					actions_so_far.erase(actions_so_far.begin());
					return cond_choice.node.get()->compute_deviation_node(actions_so_far);
				}
			}
		}
	}

	return this;

}

// Be aware that return value represents a set of histories, rather than one partial strategy
// This has to be taken into account when printing the counterexamples
std::vector<CeChoice> Node::compute_pr_ce(std::string current_action, std::vector<std::string> actions_so_far, UtilityTuplesSet practical_utilities) const {
	std::vector<CeChoice> cechoices;

	for(auto &utility : practical_utilities) {

		CeChoice cechoice;
		cechoice.player = "";

		cechoice.choices = {};
		
		std::vector<std::string> result_hist = strat2hist(utility.strategy);
		cechoice.choices.insert(cechoice.choices.end(), result_hist.begin(), result_hist.end());
		cechoice.condition = utility.condition;
		
		std::vector<std::string> updated_history;
		updated_history.insert(updated_history.end(), actions_so_far.begin(), actions_so_far.end());
		updated_history.push_back(current_action);
		cechoice.history = updated_history;
		cechoices.push_back(cechoice);		

	}

	return cechoices;
}

std::vector<std::string> Node::strat2hist(std::optional<Strategy> &strategy) const {
	
	if(this->is_leaf()) {
		return {};
	} else if (this->is_subtree()) {
		return {};
	}

	assert(strategy.has_value());

	// std::vector<std::string> strategy_copy;
	// strategy_copy.insert(strategy_copy.begin(), strategy.begin(), strategy.end());
	
	std::vector<std::string> hist_player_pairs;
	std::string first_action = strategy.value().root_action;
	// strategy_copy.erase(strategy_copy.begin());
	hist_player_pairs.push_back(first_action);

	bool found = false;
	if (this->is_branch()) {
		int i = 0;
		for(auto &child: this->branch().choices) {
			if(child.action == first_action) {
				// along the utility's history it will always be a strategy not a condition strategy
				assert(std::holds_alternative<std::optional<Strategy>>(strategy.value().children_strategies[i]));
				std::vector<std::string> child_result = child.node->strat2hist(std::get<std::optional<Strategy>>(strategy.value().children_strategies[i]));
				hist_player_pairs.insert(hist_player_pairs.end(), child_result.begin(), child_result.end());
				found = true;
			} 
			// else {
			// 	child.node->prune_actions_from_strategy(strategy_copy);
			// }
			i++;
		}
	} else if (this->is_condition_node()) { // assuming this is a strategy leading to one specific utility, there is only one condition (= child) there
		assert(strategy.value().children_strategies.size() == 1);
		// along the utility's history it will always be a strategy not a condition strategy
		assert(std::holds_alternative<std::optional<Strategy>>(strategy.value().children_strategies[0]));
		for (auto &cond_choice: this->condition_node().conditions) {
			z3::Bool condition = cond_choice.condition;
			if(condition.to_string() == first_action) {
				std::vector<std::string> child_result = cond_choice.node->strat2hist(std::get<std::optional<Strategy>>(strategy.value().children_strategies[0]));
				hist_player_pairs.insert(hist_player_pairs.end(), child_result.begin(), child_result.end());
				found = true;
			} 
		}
	}

	assert(found);
 	
	return hist_player_pairs;

}

// void Node::prune_actions_from_strategy(std::vector<std::string> &strategy) const {

// 	if(this->is_leaf() || this->is_subtree()) {
// 		return;
// 	} 

// 	assert(strategy.size() > 0);
// 	std::string first_item = strategy[0];
// 	strategy.erase(strategy.begin());
// 	if (this->is_branch()) {
// 		for(auto &child: this->branch().choices) {
// 			child.node->prune_actions_from_strategy(strategy);
// 		}
// 	} else if (this->is_condition_node()) {
// 		for (auto &cond_choice: this->condition_node().conditions) {
// 			z3::Bool condition = cond_choice.condition;
// 			if (condition.to_string() == first_item) {
// 				cond_choice.node->prune_actions_from_strategy(strategy);
// 			} 
// 		}
// 	}
// }


void Node::reset_violation_cr() const {
	violates_cr = {};

	if (!this->is_leaf() && !this->is_subtree()){

		if (this->is_branch()) {
			for (const auto& child: this->branch().choices){
				child.node->reset_violation_cr();
			}
		} else if (this->is_condition_node()) {
			for (const auto& cond_choice: this->condition_node().conditions) {
				cond_choice.node->reset_violation_cr();
			}
		}
	}
	return;
}

std::vector<std::vector<bool>> Node::store_violation_cr() const {

	std::vector<std::vector<bool>> violation = {violates_cr};

	if (!this->is_branch()){

		for (const auto& child: this->branch().choices){
			std::vector<std::vector<bool>> child_violation = child.node->store_violation_cr();
			violation.insert(violation.end(), child_violation.begin(), child_violation.end());
		}

	} else if (this->is_condition_node()) {

		for (const auto& cond_choice: this->condition_node().conditions) {
			std::vector<std::vector<bool>> child_violation = cond_choice.node->store_violation_cr();
			violation.insert(violation.end(), child_violation.begin(), child_violation.end());
		}
	}
	return violation;
}

void Node::restore_violation_cr(std::vector<std::vector<bool>> &violation) const {

	assert(violation.size()>0);
	violates_cr = violation[0];
	violation.erase(violation.begin());

	if (!this->is_branch()){

		for (const auto& child: this->branch().choices){
			child.node->restore_violation_cr(violation);
		}
	} else if (this->is_condition_node()) {

		for (const auto& cond_choice: this->condition_node().conditions) {
			cond_choice.node->restore_violation_cr(violation);
		}
	}

	return;
}

void Node::reset_count_check(bool wi, bool weri, bool cr, bool pr) const {
	if(wi)
		checked_wi = false;

	if(weri)
		checked_weri = false;
	
	if(cr)
		checked_cr = false;

	if(pr)
		checked_pr = false;

	if(this->is_branch()) {
		const auto &branch = this->branch();
		for(auto &child : branch.choices) {
			child.node.get()->reset_count_check(wi, weri, cr, pr);
		}
	} else if (this->is_condition_node()) {
		const auto &cond_node = this->condition_node();
		for(auto &cond_choice : cond_node.conditions) {
			cond_choice.node.get()->reset_count_check(wi, weri, cr, pr);
		}
	}
}




void Branch::reset_counterexample_choices() const {
	counterexample_choices = {};
	for (auto& choice: choices) {
		if (choice.node->is_branch()) {
			choice.node->branch().reset_counterexample_choices();
		} else if (choice.node->is_condition_node()){
			choice.node->condition_node().reset_counterexample_choices();
		} 
	}
}

std::vector<z3::Bool> Branch::store_reason() const {

	std::vector<z3::Bool> reason_vector = {reason};

	for (const auto& child: choices){
		if (child.node->is_branch()){
			std::vector<z3::Bool> child_reason = child.node->branch().store_reason();
			reason_vector.insert(reason_vector.end(), child_reason.begin(), child_reason.end());
		} else if (child.node->is_leaf()){
			reason_vector.push_back(child.node->leaf().reason);
		} else if (child.node->is_subtree()) {
			reason_vector.push_back(child.node->subtree().reason);
		} else if (child.node->is_condition_node()) {
			std::vector<z3::Bool> child_reason = child.node->condition_node().store_reason();
			reason_vector.insert(reason_vector.end(), child_reason.begin(), child_reason.end());
		}
	}

	return reason_vector;
}

void Branch::restore_reason(std::vector<z3::Bool> &reasons) const {

	if (reasons.size() == 0) {
		return;
	}
	reason = reasons[0];
	reasons.erase(reasons.begin());

	for (const auto& child: this->branch().choices){
		if (child.node->is_branch()){
			child.node->branch().restore_reason(reasons);
		} else if (child.node->is_condition_node()) {
			child.node->condition_node().restore_reason(reasons);
		} else if (child.node->is_leaf()) {
			if (reasons.size() == 0) {
				return;
			}
			child.node->leaf().reason = reasons[0];
			reasons.erase(reasons.begin());
		} else {
			if (reasons.size() == 0) {
				return;
			}
			child.node->subtree().reason = reasons[0];
			reasons.erase(reasons.begin());
		}
	}

	return;
}

std::vector<uint64_t> Branch::store_problematic_groups() const {

	std::vector<uint64_t> problematic_groups_vector = {problematic_group};

	for (const auto& child: choices){
		if(child.node->is_leaf()) {
			problematic_groups_vector.push_back(child.node->leaf().problematic_group);
		}
		else if (child.node->is_subtree()){
			problematic_groups_vector.push_back(child.node->subtree().problematic_group);
		}
		else if (child.node->is_condition_node()) {
			std::vector<uint64_t> child_pg = child.node->condition_node().store_problematic_groups();
			problematic_groups_vector.insert(problematic_groups_vector.end(), child_pg.begin(), child_pg.end());
		}
		else {
			std::vector<uint64_t> child_pg = child.node->branch().store_problematic_groups();
			problematic_groups_vector.insert(problematic_groups_vector.end(), child_pg.begin(), child_pg.end());
		}
	}
	return problematic_groups_vector;
}

void Branch::restore_problematic_groups(std::vector<uint64_t> &pg) const {

	if (pg.size() == 0) {
		return;
	}
	problematic_group = pg[0];
	pg.erase(pg.begin());

	for (const auto& child: this->branch().choices){
		if(child.node->is_leaf()){
			child.node->leaf().problematic_group = pg[0];
			pg.erase(pg.begin());
		}
		else if (child.node->is_subtree()) {
			child.node->subtree().problematic_group = pg[0];
			pg.erase(pg.begin());
		}
		else if (child.node->is_condition_node()) {
			child.node->condition_node().restore_problematic_groups(pg);
		}
		else {
			child.node->branch().restore_problematic_groups(pg);
		}
	}

	return;
}

std::vector<std::vector<std::string>> Branch::store_counterexample_choices() const {

	std::vector<std::vector<std::string>> counterexample_choices_vector = {counterexample_choices};

	for (const auto& child: choices){
		if (child.node->is_branch()) {
			std::vector<std::vector<std::string>> child_ces = child.node->branch().store_counterexample_choices();
			counterexample_choices_vector.insert(counterexample_choices_vector.end(), child_ces.begin(), child_ces.end());
		} else if (child.node->is_condition_node()) {
			std::vector<std::vector<std::string>> child_ces = child.node->condition_node().store_counterexample_choices();
			counterexample_choices_vector.insert(counterexample_choices_vector.end(), child_ces.begin(), child_ces.end());
		}
	}

	return counterexample_choices_vector;
}

void Branch::restore_counterexample_choices(std::vector<std::vector<std::string>> &ces) const {

	if (ces.size() == 0) {
		return;
	}
	counterexample_choices = ces[0];
	ces.erase(ces.begin());

	for (const auto& child: this->branch().choices){
		if (child.node->is_branch()){
		child.node->branch().restore_counterexample_choices(ces);
		} else if (child.node->is_condition_node()) {
			child.node->condition_node().restore_counterexample_choices(ces);
		}
	}

	return;
}

void Branch::mark_honest(const HonestHistory &history) const {
	assert(!honest);
	honest = true;
	
	if (history.empty()) {
		std::cerr << "checkmate: honest history not fitting the game tree (too short)" << std::endl;
		std::exit(EXIT_FAILURE);
	}
	
	const auto &first_element = history[0];
	
	if (!std::holds_alternative<std::string>(first_element)) {
		std::cerr << "checkmate: honest history does not fit tree shape (conditions provided where action expected)" << std::endl;
		std::exit(EXIT_FAILURE);
	}

	else{
		// Branch case: recurse on honest child
		const std::string &action = std::get<std::string>(first_element);
		const Choice &honest_choice = this->branch().get_choice(action);
		
		// Prepare remaining history for recursion
		HonestHistory remaining_history(history.begin() + 1, history.end());
		
		// Recurse if the child is a branch or condition node
		if (honest_choice.node->is_branch() || honest_choice.node->is_condition_node()) {
			if (honest_choice.node->is_branch()) {
				honest_choice.node->branch().mark_honest(remaining_history);
			} else {
				honest_choice.node->condition_node().mark_honest(remaining_history);
			}
		}
		else {
			//otherwise set honest to true for the child node and check that the history is fully consumed
			honest_choice.node->honest = true;
			if (!remaining_history.empty()) {
				std::cerr << "checkmate: honest history not fitting the game tree (too long)" << std::endl;
				std::exit(EXIT_FAILURE);
			}
		}
	} 
}

void Branch::reset_honest() const {
	if(!honest)
		return;

	honest = false;
	
	const Node * current = this->branch().get_honest_child().node.get();
	if (current->is_branch()) {
		current->branch().reset_honest();
	} else if (current->is_condition_node()) {
		current->condition_node().reset_honest();
	} else if (current->is_leaf()) {
		current->leaf().honest = false;
	} else {
		current->subtree().honest = false;
	}
	
}

void Branch::reset_reason() const {
	::new (&reason) z3::Bool();
	for(auto &choice: choices)
		if(choice.node->is_branch()){
			choice.node->branch().reset_reason();
		}
		else if (choice.node->is_condition_node()) {
			choice.node->condition_node().reset_reason();
		}
		else if (choice.node->is_leaf()) {
			choice.node->leaf().reset_reason();
		} else {
			choice.node->subtree().reset_reason();
		}
}

void Branch::reset_strategy() const {
	strategy.clear();
	for(auto &choice: choices)
		if(choice.node->is_branch())
			choice.node->branch().reset_strategy();
		else if (choice.node->is_condition_node()) {
			choice.node->condition_node().reset_strategy();
		}
}

void Branch::reset_problematic_group(bool is_cr) const {
	problematic_group = is_cr ? 1 : 0;
	for(auto &choice: choices)
		if(choice.node->is_branch()) {
			choice.node->branch().reset_problematic_group(is_cr);
		} else if (choice.node->is_condition_node()){
			choice.node->condition_node().reset_problematic_group(is_cr);
		} else if (choice.node->is_leaf()){
			choice.node->leaf().reset_problematic_group(is_cr);
		} else {
			choice.node->subtree().reset_problematic_group(is_cr);
		}
}

void Branch::reset_practical_utilities() const {
	practical_utilities = {};
	for (auto& choice: choices){
		if (choice.node->is_condition_node()) {
			choice.node->condition_node().reset_practical_utilities();
		} else if (choice.node->is_branch()) {
				choice.node->branch().reset_practical_utilities();
			
		} else if (choice.node->is_subtree()) {
			choice.node->subtree().reset_practical_utilities();
		}
	}
}
