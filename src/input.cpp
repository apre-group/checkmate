#include <fstream>
#include <iostream>
#include <iterator>
#include <set>
#include <tuple>
#include "json.hpp"

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
		NEGATE,
		EQ,
		NE,
		GT,
		GE,
		LT,
		LE,
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
		NEGATE,
		EQ,
		NE,
		GT,
		GE,
		LE,
		LT,
		OR
	};

	// operator precedence classes, binding from loosest to tightest
	enum class Precedence {
		PAREN,
		OR,
		COMPARISON,
		PLUSMINUS,
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
			case Operation::OR:
				return Precedence::OR;
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
			case Operation::OR:
				auto right = pop_constraint();
				auto left = pop_constraint();
				constraint_stack.push_back(left || right);
				break;
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
				case Lexer::Token::OR:
					operation(Operation::OR);
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

/*
 * load a tree from a JSON document `node`, assuming a certain format
 * - `input` is the input parsed so far
 * - `action_constraints` are filled out as we go
 *
 * TODO does not check all aspects
 * (hoping to have new input format based on s-expressions, which would be much easier to parse)
 */
static std::unique_ptr<Node> load_tree(const Input &input, Parser &parser, const json &node, bool &has_subtrees) {
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
			auto loaded = load_tree(input, parser, child["child"], has_subtrees);

			branch->choices.push_back({child["action"], std::move(loaded)});
		}
		return branch;
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
		has_subtrees = true;

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
				std::vector<std::vector<Utility>> utilities = {};

				for (const json& utility_tuple: pr["utilities"]) {
					using PlayerUtility = std::pair<std::string, Utility>;
					std::vector<PlayerUtility> player_utilities;
					for (const json &utility: utility_tuple) {
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

					//std::cout << pr_utility << std::endl;
					utilities.push_back(pr_utility);
				}

				PracticalitySubtreeResult pr_sub_result { _case, utilities };

				practicality.push_back(pr_sub_result);
			}
		}

		std::vector<Utility> honest_utility;
		if (node["subtree"].contains("honest_utility")) {
			using PlayerUtility = std::pair<std::string, Utility>;
			std::vector<PlayerUtility> player_utilities;
			for (const json &utility: node["subtree"]["honest_utility"]) {
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

			for (auto &player_utility: player_utilities)
				honest_utility.push_back(player_utility.second);

		}


		std::unique_ptr<Subtree> subtree(new Subtree(weak_immunity, weaker_immunity, collusion_resilience, practicality, honest_utility));

		return subtree;
	}

	// foreign object, bail
	std::cerr << "checkmate: unexpected object in tree position " << node << std::endl;
	std::exit(EXIT_FAILURE);
}



Input::Input(const char *path) : unsat_cases(), strategies() , stop_log(false) {
	// parse a JSON document from `path`
	std::ifstream input(path);
	json document;
	Parser parser(utilities);
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

	// load honest histories automatically
	honest = document["honest_histories"];


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

	// load honest utilities
	for (auto utility_dict : document["honest_utilities"]) {

		// terrible code for now, @Ivana: please clean up

		// (player, utility) pairs
		using PlayerUtility = std::pair<std::string, Utility>;
		std::vector<PlayerUtility> player_utilities;
		for (const json &utility: utility_dict["utility"]) {
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

		// leaked on purpose (honest_utilities utilities are also references but do not refer to a leaf in the tree)
		std::vector<Utility> *leaf = new std::vector<Utility>;
		for (auto &player_utility: player_utilities) {
			leaf->push_back(player_utility.second);
		}

		UtilityTuple utilityTuple(*leaf);
		
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


	// load the game tree and leak it so we can downcast to Branch
	auto node = load_tree(*this, parser, document["tree"], has_subtrees).release();

	if (node->is_leaf() || node->is_subtree()) {
		std::cerr << "checkmate: root node is a leaf or a subtree (?!) - exiting" << std::endl;
		std::exit(EXIT_FAILURE);
	}
	// un-leaked and downcasted here
	root = std::unique_ptr<Branch>(static_cast<Branch *>(node));

}

std::vector<HistoryChoice> Node::compute_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far) const {

		if (this -> is_leaf() || this->is_subtree()){
			return {};
		}
		std::vector<HistoryChoice> strategy;

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
		return strategy;
	}

std::vector<HistoryChoice> Node::compute_cr_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far, uint64_t deviating_players) const {

		if (this -> is_leaf() || this->is_subtree()){
			return {};
		}
		const Branch &branch = this->branch();
		const uint64_t all_players = players.size() == 64 ? -1ull : (1ull << players.size()) - 1;

		std::string strategy_choice;
		if (deviating_players == all_players) {
			// the group of all players is not considered, so any action is fine
			strategy_choice = branch.choices[0].action;
		} else {
			// take the action recorded for the deviating players
			// if there is none (the check skips choices that are already collusion resilient for a subgroup),
			// take the one recorded for a subgroup: being collusion resilient for a group
			// implies being collusion resilient for all its supergroups
			for (uint64_t group = deviating_players; ; group = (group - 1) & deviating_players) {
				if (!branch.satisfies_cr[group].empty()) {
					strategy_choice = branch.satisfies_cr[group];
					break;
				}
				if (group == 0)
					break;
			}
		}
		assert(!strategy_choice.empty());

		std::vector<HistoryChoice> strategy;
		HistoryChoice hist_choice;
		hist_choice.player = players[branch.player];
		hist_choice.choice = strategy_choice;
		hist_choice.history = actions_so_far;
		strategy.push_back(hist_choice);

		for (const Choice &choice: branch.choices) {
			// taking another action than the strategy, the player deviates
			uint64_t new_deviating_players = deviating_players;
			if (choice.action != strategy_choice) {
				new_deviating_players |= 1ull << branch.player;
			}

	 		std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
	 		updated_actions.push_back(choice.action);

	 		std::vector<HistoryChoice> child_strategy = choice.node->compute_cr_strategy(players, updated_actions, new_deviating_players); 
			strategy.insert(strategy.end(), child_strategy.begin(), child_strategy.end());
	 	}
		return strategy;
	}

std::vector<HistoryChoice> Node::compute_pr_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<std::string>& strategy_vector) const {

		if (this -> is_leaf() || this->is_subtree()){
			return {};
		}

		assert(strategy_vector.size()>0);
		std::vector<HistoryChoice> strategy;

		HistoryChoice hist_choice;
		hist_choice.player = players[this->branch().player];
		hist_choice.choice = strategy_vector[0];
		strategy_vector.erase(strategy_vector.begin());
		hist_choice.history = actions_so_far;

		strategy.push_back(hist_choice);

		
		for (const Choice &choice: this->branch().choices) {
	 		std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
	 		updated_actions.push_back(choice.action);
	 		std::vector<HistoryChoice> child_strategy = choice.node->compute_pr_strategy(players, updated_actions, strategy_vector);
			strategy.insert(strategy.end(), child_strategy.begin(), child_strategy.end());
	 	}
		return strategy;
	}

std::vector<CeChoice> Node::compute_wi_ce(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<size_t> player_group) const {

		if (this->is_leaf() || this->is_subtree()){
			return {};
		}
		std::vector<CeChoice> counterexample;

		assert(player_group.size() == 1);

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
		return counterexample;
	}

// a collusion resilience counterexample while reconstructing it: sets, so that identical ones compare equal
struct CrCounterexample {
	// history, player, action
	std::set<std::tuple<std::vector<std::string>, std::string, std::string>> deviations;
	// history, subtree?, groups
	std::set<std::tuple<std::vector<std::string>, bool, std::vector<std::vector<std::string>>>> leaves;

	bool operator<(const CrCounterexample &other) const {
		return std::tie(deviations, leaves) < std::tie(other.deviations, other.leaves);
	}

	void merge(const CrCounterexample &other) {
		deviations.insert(other.deviations.begin(), other.deviations.end());
		leaves.insert(other.leaves.begin(), other.leaves.end());
	}
};

// all_counterexamples: combining counterexamples can grow exponentially, so at most this many are kept per case
static const size_t MAX_CR_COUNTEREXAMPLES = 100;

// keep at most MAX_CR_COUNTEREXAMPLES, remembering if some were dropped
static void cap_counterexamples(std::set<CrCounterexample> &counterexamples, bool &truncated) {
	if (counterexamples.size() > MAX_CR_COUNTEREXAMPLES) {
		counterexamples.erase(std::next(counterexamples.begin(), MAX_CR_COUNTEREXAMPLES), counterexamples.end());
		truncated = true;
	}
}

static std::vector<std::string> group_names(const Input &input, uint64_t group) {
	std::vector<std::string> names;
	for (size_t player = 0; player < input.players.size(); player++) {
		if (group >> player & 1) {
			names.push_back(input.players[player]);
		}
	}
	return names;
}

// walk the tree like compute_cr_strategy, with `group` the players that deviated so far and
// `honest` the players that stay honest (never deviate) in this counterexample;
// returns only actual counterexamples: every leaf reached has a profiting group without honest players
// - a deviating player picks a choice violating collusion resilience for group
// - an honest player may take any choice group cannot avoid (the honest one at honest branches, all choices otherwise),
//   so the counterexample has to cover all of them; if group can avoid them, there is no counterexample
// - a player that is neither becomes honest (if no choice is collusion resilient for group, except along the honest history)
//   or a deviator (taking a choice violating collusion resilience for group together with the player)
// - at a leaf, report the supergroups of group without honest players that gain more than on the honest history
// without `all`, only the first counterexample found is returned
static std::set<CrCounterexample> cr_counterexamples(const Input &input, const Node *node, std::vector<std::string> history, uint64_t group, uint64_t honest, bool all, bool &truncated) {

	if (node->is_leaf()) {
		const Leaf &leaf = node->leaf();
		const uint64_t all_players = input.players.size() == 64 ? -1ull : (1ull << input.players.size()) - 1;
		const uint64_t outside = all_players & ~group & ~honest;
		std::vector<std::vector<std::string>> groups;
		for (uint64_t extra = 0; ; extra = (extra - outside) & outside) {
			uint64_t supergroup = group | extra;
			if (supergroup != 0 && supergroup != all_players && !leaf.cr_supergroup_memo.empty()) {
				const CrMemo &memo = leaf.cr_supergroup_memo[supergroup];
				if (input.memo_valid(memo) && memo.status == CrMemo::VIOLATED) {
					groups.push_back(group_names(input, supergroup));
				}
			}
			if (extra == outside)
				break;
		}
		// no group without honest players profits: not a counterexample
		if (groups.empty())
			return {};
		CrCounterexample counterexample;
		counterexample.leaves.insert({history, false, groups});
		return {counterexample};
	}

	if (node->is_subtree()) {
		CrCounterexample counterexample;
		counterexample.leaves.insert({history, true, {group_names(input, group)}});
		return {counterexample};
	}

	const Branch &branch = node->branch();
	const uint64_t player = 1ull << branch.player;
	auto child_history = [&](const Choice &choice) {
		std::vector<std::string> updated = history;
		updated.push_back(choice.action);
		return updated;
	};
	bool no_choice = group < branch.cr_no_choice.size() && branch.cr_no_choice[group];
	std::vector<std::string> no_deviations;
	const std::vector<std::string> &violating_deviations = group < branch.cr_violating_deviations.size() ? branch.cr_violating_deviations[group] : no_deviations;

	std::set<CrCounterexample> result;

	// the player takes `choice`, deviating there: one counterexample per counterexample after it
	auto deviate = [&](const Choice &choice, uint64_t new_group) {
		for (CrCounterexample counterexample: cr_counterexamples(input, choice.node.get(), child_history(choice), new_group, honest, all, truncated)) {
			counterexample.deviations.insert({history, input.players[branch.player], choice.action});
			result.insert(counterexample);
		}
		cap_counterexamples(result, truncated);
	};

	// the player is honest: one counterexample for every combination of counterexamples of the choices it may take
	auto stay_honest = [&](uint64_t new_honest) {
		std::set<CrCounterexample> combined = {CrCounterexample()};
		for (const Choice &choice: branch.choices) {
			if (branch.honest && !choice.node->honest)
				continue;
			std::set<CrCounterexample> next;
			for (const CrCounterexample &child: cr_counterexamples(input, choice.node.get(), child_history(choice), group, new_honest, all, truncated)) {
				for (CrCounterexample counterexample: combined) {
					if (next.size() > MAX_CR_COUNTEREXAMPLES)
						break;
					counterexample.merge(child);
					next.insert(counterexample);
				}
			}
			cap_counterexamples(next, truncated);
			combined = next;
			// some choice has no counterexample: the player could take it
			if (combined.empty())
				return;
		}
		result.insert(combined.begin(), combined.end());
		cap_counterexamples(result, truncated);
	};

	if (group & player) {
		// the player deviates already: it picks a violating choice (all choices violate if no choice is collusion resilient)
		for (const Choice &choice: branch.choices) {
			bool violating = no_choice || std::find(violating_deviations.begin(), violating_deviations.end(), choice.action) != violating_deviations.end();
			if (violating) {
				deviate(choice, group);
				if (!all && !result.empty())
					break;
			}
		}
	} else if (honest & player) {
		if (no_choice)
			stay_honest(honest);
	} else {
		// taking the honest action along the honest history does not make a player honest:
		// group members take it as well
		if (no_choice)
			stay_honest(branch.honest ? honest : honest | player);
		for (const std::string &action: violating_deviations) {
			if (!all && !result.empty())
				break;
			deviate(branch.get_choice(action), group | player);
		}
	}

	// without `all`, only the first counterexample
	if (!all && result.size() > 1) {
		result.erase(std::next(result.begin()), result.end());
	}
	return result;
}

void Input::compute_cr_cecases(bool all) const {
	bool truncated = false;
	for (const CrCounterexample &counterexample: cr_counterexamples(*this, root.get(), {}, 0, 0, all, truncated)) {
		CeCase ce_case;
		for (const auto &deviation: counterexample.deviations) {
			CeChoice ce_choice;
			ce_choice.history = std::get<0>(deviation);
			ce_choice.player = std::get<1>(deviation);
			ce_choice.choices = {std::get<2>(deviation)};
			ce_case.counterexample.push_back(ce_choice);
		}
		for (const auto &leaf: counterexample.leaves) {
			CrLeafViolation violation;
			violation.history = std::get<0>(leaf);
			violation.subtree = std::get<1>(leaf);
			violation.groups = std::get<2>(leaf);
			ce_case.cr_leaves.push_back(violation);
		}
		counterexamples.push_back(ce_case);
	}
	if (truncated) {
		counterexamples.back().cr_more_omitted = true;
	}
}

CeCase Node::compute_pr_cecase(std::vector<std::string> players, unsigned current_player, std::vector<std::string> actions_so_far, std::string current_action, UtilityTuplesSet practical_utilities) const {
	
	// regular case (called from branch)
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
		for (const auto &child: this->branch().choices){
			if(child.action == actions_so_far[0]) {
				actions_so_far.erase(actions_so_far.begin());
				return child.node.get()->compute_deviation_node(actions_so_far);
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
		
		std::vector<std::string> result_hist = strat2hist(utility.strategy_vector);
		cechoice.choices.insert(cechoice.choices.end(), result_hist.begin(), result_hist.end());
		
		std::vector<std::string> updated_history;
		updated_history.insert(updated_history.end(), actions_so_far.begin(), actions_so_far.end());
		updated_history.push_back(current_action);
		cechoice.history = updated_history;
		cechoices.push_back(cechoice);		

	}

	return cechoices;
}

std::vector<std::string> Node::strat2hist(std::vector<std::string> &strategy) const {
	
	if(this->is_leaf()) {
		return {};
	} else if (this->is_subtree()) {
		return {};
	}

	assert(strategy.size() > 0);

	std::vector<std::string> strategy_copy;
	strategy_copy.insert(strategy_copy.begin(), strategy.begin(), strategy.end());
	
	std::vector<std::string> hist_player_pairs;
	std::string first_action = strategy_copy[0];
	strategy_copy.erase(strategy_copy.begin());
	hist_player_pairs.push_back(first_action);

	bool found = false;
	for(auto &child: this->branch().choices) {

		if(child.action == first_action) {
			std::vector<std::string> child_result = child.node->strat2hist(strategy_copy);
			hist_player_pairs.insert(hist_player_pairs.end(), child_result.begin(), child_result.end());
			found = true;
		} else {
			child.node->prune_actions_from_strategy(strategy_copy);
		}
	}

	assert(found);
 	
	return hist_player_pairs;

}

void Node::prune_actions_from_strategy(std::vector<std::string> &strategy) const {

	if(this->is_leaf() || this->is_subtree()) {
		return;
	} 

	assert(strategy.size() > 0);
	strategy.erase(strategy.begin());
	for(auto &child: this->branch().choices) {
		child.node->prune_actions_from_strategy(strategy);
	}
}

void Node::reset_satisfies_cr(size_t number_groups) const {

	if (this->is_leaf() || this->is_subtree()){
		return;
	}

	this->branch().satisfies_cr.assign(number_groups, "");
	for (const auto& child: this->branch().choices){
		child.node->reset_satisfies_cr(number_groups);
	}
}

std::vector<std::vector<std::string>> Node::store_satisfies_cr() const {

	if (this->is_leaf() || this->is_subtree()){
		return {};
	}

	std::vector<std::vector<std::string>> satisfies = {this->branch().satisfies_cr};
	for (const auto& child: this->branch().choices){
		std::vector<std::vector<std::string>> child_satisfies = child.node->store_satisfies_cr();
		satisfies.insert(satisfies.end(), child_satisfies.begin(), child_satisfies.end());
	}
	return satisfies;
}

void Node::restore_satisfies_cr(std::vector<std::vector<std::string>> &satisfies) const {

	if (this->is_leaf() || this->is_subtree()){
		return;
	}

	assert(satisfies.size()>0);
	this->branch().satisfies_cr = satisfies[0];
	satisfies.erase(satisfies.begin());
	for (const auto& child: this->branch().choices){
		child.node->restore_satisfies_cr(satisfies);
	}
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
	}
}
