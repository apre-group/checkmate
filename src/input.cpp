#include <fstream>
#include <iostream>
#include "json.hpp"

#include "input.hpp"

// Need global copy due to issue with dangling references in load_tree
// Alternatively, we can wrap UtilityTuple s.t. it creates a copy and does not just use the reference
std::vector<std::vector<std::vector<Utility>>> utilities_storage;
size_t index_utilities_storage = 0;

// lexical analysis for expressions
struct Lexer
{
	// possible tokens in expressions
	enum class Token
	{
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
		OR,
		AND
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
	void start(const char *start)
	{
		unary = true;
		current = start;
		remaining = start;
	}

	// check if there are any more tokens, possibly advancing `remaining` past whitespace
	bool has_more()
	{
		while (std::isspace(*remaining))
			remaining++;
		return *remaining;
	}

	// get the next token or exit with failure
	Token next()
	{
		buffer.clear();
		// a variable name
		if (std::isalpha(*remaining))
		{
			buffer.push_back(*remaining++);
			while (std::isalnum(*remaining) || *remaining == '_')
				buffer.push_back(*remaining++);
			unary = false;
			return Token::IDENTIFIER;
		}
		// number
		else if (std::isdigit(*remaining))
		{
			buffer.push_back(*remaining++);
			while (std::isdigit(*remaining) || *remaining == '.')
				buffer.push_back(*remaining++);
			unary = false;
			return Token::NUMERAL;
		}
		else if (*remaining == '(')
		{
			remaining++;
			unary = true;
			return Token::LPAREN;
		}
		else if (*remaining == ')')
		{
			remaining++;
			unary = false;
			return Token::RPAREN;
		}
		// operators
		else if (*remaining == '+')
		{
			remaining++;
			unary = true;
			return Token::PLUS;
		}
		else if (*remaining == '-')
		{
			remaining++;
			if (unary)
				return Token::NEGATE;
			unary = true;
			return Token::MINUS;
		}
		else if (*remaining == '*')
		{
			remaining++;
			unary = true;
			return Token::MULTIPLY;
		}
		else if (*remaining == '/')
		{
			remaining++;
			unary = true;
			return Token::DIVIDE;
		}
		else if (*remaining == '=')
		{
			remaining++;
			unary = true;
			return Token::EQ;
		}
		else if (*remaining == '!' && remaining[1] == '=')
		{
			remaining += 2;
			unary = true;
			return Token::NE;
		}
		else if (*remaining == '>')
		{
			remaining++;
			if (*remaining == '=')
			{
				remaining++;
				unary = true;
				return Token::GE;
			}
			unary = true;
			return Token::GT;
		}
		else if (*remaining == '<')
		{
			remaining++;
			if (*remaining == '=')
			{
				remaining++;
				unary = true;
				return Token::LE;
			}
			unary = true;
			return Token::LT;
		}
		else if (*remaining == '|')
		{
			remaining++;
			unary = true;
			return Token::OR;
		}
		else if (*remaining == '&')
		{
			remaining++;
			unary = true;
			return Token::AND;
		}
		else
		{
			std::cerr << "checkmate: unexpected character '" << *remaining << "' in expression " << current << std::endl;
			std::exit(EXIT_FAILURE);
		}
	}
};

// parsing for expressions based on the "shunting-yard" algorithm
struct Parser
{
	// possible operators to apply to the stack
	enum class Operation
	{
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
		OR,
		AND
	};

	// operator precedence classes, binding from loosest to tightest
	enum class Precedence
	{
		PAREN,
		AND,
		OR,
		COMPARISON,
		PLUSMINUS,
		MULTIPLY,
		DIVIDE,
		NEGATE,
	};

	// the precedence class of an operator
	static Precedence precedence(Operation operation)
	{
		switch (operation)
		{
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
		case Operation::OR:
			return Precedence::OR;
		case Operation::AND:
			return Precedence::AND;
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
	[[noreturn]] void error()
	{
		std::cerr << "checkmate: could not parse expression " << lexer.current << std::endl;
		std::exit(EXIT_FAILURE);
	}

	// pop an operation from the stack
	Operation pop_operation()
	{
		auto operation = operation_stack.back();
		operation_stack.pop_back();
		return operation;
	}

	// pop a utility from the stack
	Utility pop_utility()
	{
		if (utility_stack.empty())
			error();
		auto utility = utility_stack.back();
		utility_stack.pop_back();
		return utility;
	}

	// pop a Boolean from the stack
	z3::Bool pop_constraint()
	{
		if (constraint_stack.empty())
			error();
		auto constraint = constraint_stack.back();
		constraint_stack.pop_back();
		return constraint;
	}

	// once we know we have to apply an operation, commit to it
	void commit(Operation operation)
	{
		switch (operation)
		{
		case Operation::PAREN:
			// nothing to do
			break;
		case Operation::PLUS:
		{
			auto right = pop_utility();
			auto left = pop_utility();
			utility_stack.push_back(left + right);
			break;
		}
		case Operation::MINUS:
		{
			auto right = pop_utility();
			auto left = pop_utility();
			utility_stack.push_back(left - right);
			break;
		}
		case Operation::MULTIPLY:
		{
			auto right = pop_utility();
			auto left = pop_utility();
			utility_stack.push_back(left * right);
			break;
		}
		case Operation::DIVIDE:
		{
			auto right = pop_utility();
			auto left = pop_utility();
			utility_stack.push_back(left / right);
			break;
		}
		case Operation::NEGATE:
		{
			auto negate = pop_utility();
			utility_stack.push_back(-negate);
			break;
		}
		case Operation::EQ:
		{
			auto right = pop_utility();
			auto left = pop_utility();
			constraint_stack.push_back(left == right);
			break;
		}
		case Operation::NE:
		{
			auto right = pop_utility();
			auto left = pop_utility();
			constraint_stack.push_back(left != right);
			break;
		}
		case Operation::GT:
		{
			auto right = pop_utility();
			auto left = pop_utility();
			constraint_stack.push_back(left > right);
			break;
		}
		case Operation::GE:
		{
			auto right = pop_utility();
			auto left = pop_utility();
			constraint_stack.push_back(left >= right);
			break;
		}
		case Operation::LT:
		{
			auto right = pop_utility();
			auto left = pop_utility();
			constraint_stack.push_back(left < right);
			break;
		}
		case Operation::LE:
		{
			auto right = pop_utility();
			auto left = pop_utility();
			constraint_stack.push_back(left <= right);
			break;
		}
		case Operation::OR:
		{
			auto right = pop_constraint();
			auto left = pop_constraint();
			constraint_stack.push_back(left || right);
			break;
		}
		case Operation::AND:
			auto right = pop_constraint();
			auto left = pop_constraint();
			constraint_stack.push_back(left && right);
			break;
		}
	}

	// handle a new `operation`, committing higher-precedence operations and then pushing it on `operation_stack`
	void operation(Operation operation)
	{
		while (!operation_stack.empty() && precedence(operation_stack.back()) >= precedence(operation))
			commit(pop_operation());
		operation_stack.push_back(operation);
	}

	// parse either a utility term or a Boolean expression, leaving it in the stack
	void parse(const char *start)
	{
		lexer.start(start);
		while (lexer.has_more())
		{
			Lexer::Token token = lexer.next();
			switch (token)
			{
			case Lexer::Token::NUMERAL:
				utility_stack.push_back({z3::Real::value(lexer.buffer), z3::Real::ZERO});
				break;
			case Lexer::Token::IDENTIFIER:
			{
				Utility utility;
				try
				{
					utility = identifiers.at(lexer.buffer);
				}
				catch (const std::out_of_range &)
				{
					std::cerr << "checkmate: undeclared constant " << lexer.buffer << std::endl;
					std::exit(EXIT_FAILURE);
				}
				utility_stack.push_back(utility);
				break;
			}
			case Lexer::Token::LPAREN:
			{
				operation_stack.push_back(Operation::PAREN);
				break;
			}
			case Lexer::Token::RPAREN:
			{
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
			case Lexer::Token::OR:
				operation(Operation::OR);
				break;
			case Lexer::Token::AND:
				operation(Operation::AND);
				break;
			}
		}
		// when there is no more input, we know all the operators have to be committed
		while (!operation_stack.empty())
			commit(pop_operation());
	}

	// parse a utility term, popping it out from the stack
	Utility parse_utility(const char *start)
	{
		parse(start);
		if (!constraint_stack.empty() || utility_stack.size() != 1)
			error();
		auto utility = utility_stack.back();
		utility_stack.clear();
		return utility;
	}

	// parse a Boolean term, popping it out from the stack
	z3::Bool parse_constraint(const char *start)
	{
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

static z3::Bool parse_case(Parser &parser, const std::string &_case)
{
	if (_case == "true")
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
static Node *load_tree(const Input &input, Parser &parser, const json &node, bool supertree)
{
	// branch
	if (node.contains("children"))
	{
		// do linear-time lookup for the index of the node's player in the input player list
		unsigned player;
		for (player = 0; player < input.players.size(); player++)
			if (input.players[player] == node["player"])
				break;
		if (player == input.players.size())
			throw std::logic_error("undeclared player in the input");

		std::vector<Condition> conditions = {};
		if (node["children"][0].contains("condition"))
		{
			for (const json &condition_node : node["children"])
			{
				const json &condition_json = condition_node["condition"];
				z3::Bool condition = parse_case(parser, condition_json);

				Condition cond;
				cond.condition = condition;
				// iterate over the actions and populate the cond.children
				for (const json &child : condition_node["actions"])
				{
					auto loaded = load_tree(input, parser, child["child"], supertree);
					Choice c;
					c.action = child["action"];
					c.node = loaded;
					cond.children.push_back(c);
				}
				conditions.push_back(cond);
			}
		}
		else
		{
			Condition cond;
			z3::Bool bool_obj;
			cond.condition = bool_obj.True();
			for (const json &child : node["children"])
			{
				auto loaded = load_tree(input, parser, child["child"], supertree);
				cond.children.push_back({child["action"], std::move(loaded)});
			}
			conditions.push_back(cond);
		}

		Branch *branch(new Branch(player, conditions));
		return branch;
	}

	// leaf
	if (node.contains("utility"))
	{
		// (player, utility) pairs
		using PlayerUtility = std::pair<std::string, Utility>;
		std::vector<PlayerUtility> player_utilities;
		for (const json &utility : node["utility"])
		{
			const json &value = utility["value"];
			// parse a utility expression
			if (value.is_string())
			{
				const std::string &string = value;
				player_utilities.push_back({utility["player"],
											parser.parse_utility(string.c_str())});
			}
			// numeric utility, assumed real
			else if (value.is_number_unsigned())
			{
				unsigned number = value;
				player_utilities.push_back({utility["player"],
											{z3::Real::value(number), z3::Real::ZERO}});
			}
			// foreign object, bail
			else
			{
				std::cerr << "checkmate: unsupported utility value " << value << std::endl;
				std::exit(EXIT_FAILURE);
			}
		}

		// sort (player, utility) pairs alphabetically by player
		sort(
			player_utilities.begin(),
			player_utilities.end(),
			[](const PlayerUtility &left, const PlayerUtility &right)
			{ return left.first < right.first; });

		Leaf *leaf(new Leaf);
		for (auto &player_utility : player_utilities)
			leaf->utilities.push_back(player_utility.second);
		return leaf;
	}

	// subtree summary
	if (node.contains("subtree"))
	{

		// Remove the check below for the purpose of allowing nesting of subtrees in subtress
		/*
		if (!supertree)
		{
			// subtree nodes can only occur in supertree mode!
			std::cerr << "checkmate: unexpected subtree node; call in --supertree mode " << node << std::endl;
			std::exit(EXIT_FAILURE);
		}*/

		std::vector<SubtreeResult> weak_immunity = {};
		std::vector<SubtreeResult> weaker_immunity = {};
		std::vector<SubtreeResult> collusion_resilience = {};
		std::vector<PracticalitySubtreeResult> practicality = {};

		if (node["subtree"].contains("weak_immunity"))
		{
			for (const json &wi : node["subtree"]["weak_immunity"])
			{
				const json &players_json = wi["player_group"];
				std::vector<std::string> player_group;
				for (const auto &player : players_json)
				{
					if (player.is_string())
					{
						player_group.push_back(player);
					}
					else
					{
						std::cerr << "checkmate: unsupported player value " << player << std::endl;
						std::exit(EXIT_FAILURE);
					}
				}
				std::vector<std::vector<z3::Bool>> satisfied_in_case = {};

				const json &cases = wi["satisfied_in_case"];
				for (const json &json_case : cases)
				{
					std::vector<z3::Bool> _case = {};
					for (const json &_case_entry : json_case)
					{
						if (_case_entry != "true")
						{
							const std::string &_case_e = _case_entry;
							_case.push_back(parse_case(parser, _case_e));
						}
					}
					satisfied_in_case.push_back(_case);
				}

				SubtreeResult wi_result{player_group, satisfied_in_case};
				weak_immunity.push_back(wi_result);
			}
		}

		if (node["subtree"].contains("weaker_immunity"))
		{
			for (const json &weri : node["subtree"]["weaker_immunity"])
			{
				const json &players_json = weri["player_group"];
				std::vector<std::string> player_group = {};
				for (const auto &player : players_json)
				{
					if (player.is_string())
					{
						player_group.push_back(player);
					}
					else
					{
						std::cerr << "checkmate: unsupported player value " << player << std::endl;
						std::exit(EXIT_FAILURE);
					}
				}
				std::vector<std::vector<z3::Bool>> satisfied_in_case = {};

				const json &cases = weri["satisfied_in_case"];
				for (const json &json_case : cases)
				{
					std::vector<z3::Bool> _case = {};
					for (const json &_case_entry : json_case)
					{
						if (_case_entry != "true")
						{
							const std::string &_case_e = _case_entry;
							_case.push_back(parse_case(parser, _case_e));
						}
					}
					satisfied_in_case.push_back(_case);
				}

				SubtreeResult weri_result{player_group, satisfied_in_case};
				weaker_immunity.push_back(weri_result);
			}
		}

		if (node["subtree"].contains("collusion_resilience"))
		{
			for (const json &cr : node["subtree"]["collusion_resilience"])
			{
				const json &players_json = cr["player_group"];
				std::vector<std::string> player_group = {};
				for (const auto &player : players_json)
				{
					if (player.is_string())
					{
						player_group.push_back(player);
					}
					else
					{
						std::cerr << "checkmate: unsupported player value " << player << std::endl;
						std::exit(EXIT_FAILURE);
					}
				}
				std::vector<std::vector<z3::Bool>> satisfied_in_case = {};

				const json &cases = cr["satisfied_in_case"];
				for (const json &json_case : cases)
				{
					std::vector<z3::Bool> _case = {};
					for (const json &_case_entry : json_case)
					{
						if (_case_entry != "true")
						{
							const std::string &_case_e = _case_entry;
							_case.push_back(parse_case(parser, _case_e));
						}
					}
					satisfied_in_case.push_back(_case);
				}

				SubtreeResult cr_result{player_group, satisfied_in_case};
				collusion_resilience.push_back(cr_result);
			}
		}

		if (node["subtree"].contains("practicality"))
		{

			if(node["subtree"]["practicality"].size() == 0) {
				// do nothing
			}
			else if (node["subtree"]["practicality"][0].contains("conditional_utilities"))
			{

				for (const json &pr : node["subtree"]["practicality"])
				{
					const json &_case_pr = pr["case"];
					std::vector<z3::Bool> _case = {};
					for (const json &_case_entry : _case_pr)
					{
						if (_case_entry != "true")
						{
							const std::string &_case_e = _case_entry;
							_case.push_back(parse_case(parser, _case_e));
						}
					}
					std::vector<std::vector<Utility>> utilities = {};

					ConditionalUtilities cu;
					for (const json &utility_tuple : pr["conditional_utilities"])
					{
						const json &_cond_actions = utility_tuple["conditional_actions"];
						z3::Bool _conditional_actions = {};
						const std::string &_case_e = _cond_actions;
						_conditional_actions = parse_case(parser, _case_e);

						cu.condition.push_back(_conditional_actions);

						for (const json &utility_tup : utility_tuple["utilities"])
						{

							using PlayerUtility = std::pair<std::string, Utility>;
							std::vector<PlayerUtility> player_utilities;
							for (const json &utility : utility_tup)
							{
								const json &value = utility["value"];
								// parse a utility expression
								if (value.is_string())
								{
									const std::string &string = value;
									player_utilities.push_back({utility["player"],
																parser.parse_utility(string.c_str())});
								}
								// numeric utility, assumed real
								else if (value.is_number_unsigned())
								{
									unsigned number = value;
									player_utilities.push_back({utility["player"],
																{z3::Real::value(number), z3::Real::ZERO}});
								}
								// foreign object, bail
								else
								{
									std::cerr << "checkmate: unsupported utility value " << value << std::endl;
									std::exit(EXIT_FAILURE);
								}
							}

							// sort (player, utility) pairs alphabetically by player
							sort(
								player_utilities.begin(),
								player_utilities.end(),
								[](const PlayerUtility &left, const PlayerUtility &right)
								{ return left.first < right.first; });

							std::vector<Utility> pr_utility = {};
							for (auto &player_utility : player_utilities)
								pr_utility.push_back(player_utility.second);

							utilities.push_back(pr_utility);
						}

						utilities_storage.push_back({});
						for (auto const util : utilities) {
							utilities_storage[index_utilities_storage].push_back(util);
						}


						UtilityTuplesSet utilities_set = {};
						for(auto const &util : utilities_storage[index_utilities_storage]) {
							UtilityTuple ut(util);
							utilities_set.insert(ut);
						}
						cu.utilities.push_back(utilities_set);

						index_utilities_storage++;

					}

					PracticalitySubtreeResult pr_sub_result{_case, cu};

					practicality.push_back(pr_sub_result);
				}

			} else {

				for (const json &pr : node["subtree"]["practicality"])
				{

					const json &_case_pr = pr["case"];
					std::vector<z3::Bool> _case = {};
					for (const json &_case_entry : _case_pr)
					{
						if (_case_entry != "true")
						{
							const std::string &_case_e = _case_entry;
							_case.push_back(parse_case(parser, _case_e));
						}
					}

					std::vector<std::vector<Utility>> utilities = {};

					for (const json &utility_tuple : pr["utilities"])
					{

						using PlayerUtility = std::pair<std::string, Utility>;
						std::vector<PlayerUtility> player_utilities;
						for (const json &utility : utility_tuple)
						{
							const json &value = utility["value"];
							// parse a utility expression
							if (value.is_string())
							{
								const std::string &string = value;
								player_utilities.push_back({utility["player"],
															parser.parse_utility(string.c_str())});
							}
							// numeric utility, assumed real
							else if (value.is_number_unsigned())
							{
								unsigned number = value;
								player_utilities.push_back({utility["player"],
															{z3::Real::value(number), z3::Real::ZERO}});
							}
							// foreign object, bail
							else
							{
								std::cerr << "checkmate: unsupported utility value " << value << std::endl;
								std::exit(EXIT_FAILURE);
							}
						}

						// sort (player, utility) pairs alphabetically by player
						sort(
							player_utilities.begin(),
							player_utilities.end(),
							[](const PlayerUtility &left, const PlayerUtility &right)
							{ return left.first < right.first; });

						std::vector<Utility> pr_utility = {};
						for (auto &player_utility : player_utilities)
							pr_utility.push_back(player_utility.second);

						utilities.push_back(pr_utility);
					}

					utilities_storage.push_back({});
					// utilities_storage[index_utilities_storage] = {};
					for (auto const util : utilities) {
						utilities_storage[index_utilities_storage].push_back(util);
					}

					ConditionalUtilities cu;
					cu.condition.push_back(z3::conjunction({}));
					UtilityTuplesSet utilities_set = {};
					for(auto const &util : utilities_storage[index_utilities_storage]) {
						UtilityTuple ut(util);
						utilities_set.insert(ut);
					}

					index_utilities_storage++;

					cu.utilities.push_back(utilities_set);
					PracticalitySubtreeResult pr_sub_result{_case, cu};

					practicality.push_back(pr_sub_result);

				}
			}
		}

		std::vector<CondActionsUtilityPair> cond_actions_honest_utility_pairs;
		if (node["subtree"].contains("honest_utility"))
		{
			if (node["subtree"]["honest_utility"][0].contains("conditional_actions"))
			{

				for (const json &pair : node["subtree"]["honest_utility"])
				{

					std::vector<z3::Bool> _cond_actions = {};
					const json &_conditional_actions = pair["conditional_actions"];

					for (const json &_action_entry : _conditional_actions)
					{
						if (_action_entry != "true")
						{
							const std::string &_case_e = _action_entry;
							_cond_actions.push_back(parse_case(parser, _case_e));
						}
					}

					using PlayerUtility = std::pair<std::string, Utility>;
					std::vector<PlayerUtility> player_utilities;
					for (const json &utility : pair["utility"])
					{
						const json &value = utility["value"];
						// parse a utility expression
						if (value.is_string())
						{
							const std::string &string = value;
							player_utilities.push_back({utility["player"],
														parser.parse_utility(string.c_str())});
						}
						// numeric utility, assumed real
						else if (value.is_number_unsigned())
						{
							unsigned number = value;
							player_utilities.push_back({utility["player"],
														{z3::Real::value(number), z3::Real::ZERO}});
						}
						// foreign object, bail
						else
						{
							std::cerr << "checkmate: unsupported utility value " << value << std::endl;
							std::exit(EXIT_FAILURE);
						}
					}

					// sort (player, utility) pairs alphabetically by player
					sort(
						player_utilities.begin(),
						player_utilities.end(),
						[](const PlayerUtility &left, const PlayerUtility &right)
						{ return left.first < right.first; });

					std::vector<Utility> hon_utility = {};
					for (auto &player_utility : player_utilities)
						hon_utility.push_back(player_utility.second);

					CondActionsUtilityPair new_pair;
					new_pair.conditional_actions.insert(new_pair.conditional_actions.begin(), _cond_actions.begin(), _cond_actions.end());
					new_pair.utility.insert(new_pair.utility.begin(), hon_utility.begin(), hon_utility.end());
					cond_actions_honest_utility_pairs.push_back(new_pair);
				}
			}
			else
			{
				using PlayerUtility = std::pair<std::string, Utility>;
				std::vector<PlayerUtility> player_utilities;
				for (const json &utility : node["subtree"]["honest_utility"])
				{
					const json &value = utility["value"];
					// parse a utility expression
					if (value.is_string())
					{
						const std::string &string = value;
						player_utilities.push_back({utility["player"],
													parser.parse_utility(string.c_str())});
					}
					// numeric utility, assumed real
					else if (value.is_number_unsigned())
					{
						unsigned number = value;
						player_utilities.push_back({utility["player"],
													{z3::Real::value(number), z3::Real::ZERO}});
					}
					// foreign object, bail
					else
					{
						std::cerr << "checkmate: unsupported utility value " << value << std::endl;
						std::exit(EXIT_FAILURE);
					}
				}

				// sort (player, utility) pairs alphabetically by player
				sort(
					player_utilities.begin(),
					player_utilities.end(),
					[](const PlayerUtility &left, const PlayerUtility &right)
					{ return left.first < right.first; });

				std::vector<Utility> hon_utility = {};
				for (auto &player_utility : player_utilities)
					hon_utility.push_back(player_utility.second);


			CondActionsUtilityPair new_pair;
			new_pair.conditional_actions = {};
			new_pair.utility.insert(new_pair.utility.begin(), hon_utility.begin(), hon_utility.end());
			cond_actions_honest_utility_pairs.push_back(new_pair);

			}
		}

		bool type_cond_actions = false;
		if (node["subtree"].contains("solved_for_weak_conditional_actions"))
		{
			type_cond_actions = node["subtree"]["solved_for_weak_conditional_actions"];
		}

		Subtree *subtree(new Subtree(weak_immunity, weaker_immunity, collusion_resilience, practicality, cond_actions_honest_utility_pairs));
		subtree->solved_weak_cond_actions = type_cond_actions;
		return subtree;
	}


	// foreign object, bail
	std::cerr << "checkmate: unexpected object in tree position " << node << std::endl;
	std::exit(EXIT_FAILURE);

}

static HonestNode *load_honest_history_conditional_actions(const json &honest_node)
{

	std::string act = honest_node["action"];
	std::vector<HonestNode *> children;

	for (const json &child : honest_node["children"])
	{
		children.push_back(load_honest_history_conditional_actions(child));
	}

	return new HonestNode(act, children);
}

static HonestNode *load_honest_history_no_conditional_actions(const json &actions)
{

	assert(!actions.empty());

	HonestNode *root = nullptr;

	for (auto it = actions.rbegin(); it != actions.rend(); ++it)
	{
		root = new HonestNode(*it, root ? std::vector<HonestNode *>{root} : std::vector<HonestNode *>{});
	}
	return new HonestNode("", {root});
}

static HonestNode *load_honest_history(const json &honest_node)
{

	if (honest_node.is_array())
	{
		return load_honest_history_no_conditional_actions(honest_node);
	}
	else
	{
		return load_honest_history_conditional_actions(honest_node);
	}
}

Input::Input(const char *path, bool supertree) : unsat_cases(), strategies(), stop_log(false)
{
	// parse a JSON document from `path`
	std::ifstream input(path);
	json document;
	Parser parser(utilities);
	try
	{
		input.exceptions(std::ifstream::failbit | std::ifstream::badbit);
		document = json::parse(input);
	}
	catch (const std::ifstream::failure &fail)
	{
		std::cerr << "checkmate: " << std::strerror(errno) << std::endl;
		std::exit(EXIT_FAILURE);
	}
	catch (const json::exception &err)
	{
		std::cerr << "checkmate: " << err.what() << std::endl;
		std::exit(EXIT_FAILURE);
	}

	if (document["players"].size() > MAX_PLAYERS)
	{
		std::cerr << "checkmate: more than 64 players not supported - are you sure you want this many?!" << std::endl;
		std::exit(EXIT_FAILURE);
	}

	// load list of players and sort alphabetically
	for (const json &player : document["players"])
		players.push_back(std::string(player));
	sort(players.begin(), players.end());

	// load honest histories
	for (const json &honest_history_json : document["honest_histories"])
	{
		auto *h = load_honest_history(honest_history_json);
		honest.push_back(h);
	}

	// load real/infinitesimal identifiers
	for (const json &real : document["constants"])
	{
		const std::string &name = real;
		auto constant = z3::Real::constant(name);
		utilities.insert({name, {constant, z3::Real::ZERO}});
	}
	for (const json &infinitesimal : document["infinitesimals"])
	{
		const std::string &name = infinitesimal;
		auto constant = z3::Real::constant(name);
		utilities.insert({name, {z3::Real::ZERO, constant}});
	}

	if (document["honest_utilities"].size() > 0 && supertree)
	{
		std::cerr << "checkmate: honest utility should not be specified in supertree mode " << std::endl;
		std::exit(EXIT_FAILURE);
	}

	// load honest utilities
	for (auto utility_dict : document["honest_utilities"])
	{
		// terrible code for now, @Ivana: please clean up

		std::vector<z3::Bool> _cond_actions = {};
		for (const json &_action_entry : utility_dict["conditional_actions"])
		{
			if (_action_entry != "true")
			{
				const std::string &_case_e = _action_entry;
				_cond_actions.push_back(parse_case(parser, _case_e));
			}
		}

		// (player, utility) pairs
		using PlayerUtility = std::pair<std::string, Utility>;
		std::vector<PlayerUtility> player_utilities;
		for (const json &utility : utility_dict["utility"])
		{
			const json &value = utility["value"];
			// parse a utility expression
			if (value.is_string())
			{
				const std::string &string = value;
				player_utilities.push_back({utility["player"],
											parser.parse_utility(string.c_str())});
			}
			// numeric utility, assumed real
			else if (value.is_number_unsigned())
			{
				unsigned number = value;
				player_utilities.push_back({utility["player"],
											{z3::Real::value(number), z3::Real::ZERO}});
			}
			// foreign object, bail
			else
			{
				std::cerr << "checkmate: unsupported utility value " << value << std::endl;
				std::exit(EXIT_FAILURE);
			}
		}

		// sort (player, utility) pairs alphabetically by player
		sort(
			player_utilities.begin(),
			player_utilities.end(),
			[](const PlayerUtility &left, const PlayerUtility &right)
			{ return left.first < right.first; });

		// leaked on purpose (honest_utilities utilities are also references but do not refer to a leaf in the tree)
		std::vector<Utility> hon_utility = {};
		for (auto &player_utility : player_utilities)
		{
			hon_utility.push_back(player_utility.second);
		}

		CondActionsUtilityPair new_pair;
		new_pair.conditional_actions.insert(new_pair.conditional_actions.begin(), _cond_actions.begin(), _cond_actions.end());
		new_pair.utility.insert(new_pair.utility.begin(), hon_utility.begin(), hon_utility.end());

		honest_utilities.push_back(new_pair);
	}

	// reusable buffer for constraint conjuncts
	std::vector<z3::Bool> conjuncts;
	std::vector<z3::Bool> initialconstrs;

	// initial constraints
	for (const json &initial_constraint : document["initial_constraints"])
	{
		const std::string &constraint = initial_constraint;
		initialconstrs.push_back(parser.parse_constraint(constraint.c_str()));
	}
	initial_constraints = initialconstrs;

	// weak immunity constraints
	conjuncts.clear();
	for (const json &weak_immunity_constraint : document["property_constraints"]["weak_immunity"])
	{
		const std::string &constraint = weak_immunity_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	weak_immunity_constraint = z3::Bool::conjunction(conjuncts);

	// weaker immunity constraints
	conjuncts.clear();
	for (const json &weaker_immunity_constraint : document["property_constraints"]["weaker_immunity"])
	{
		const std::string &constraint = weaker_immunity_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	weaker_immunity_constraint = conjunction(conjuncts);

	// collusion resilience constraints
	conjuncts.clear();
	for (const json &collusion_resilience_constraint : document["property_constraints"]["collusion_resilience"])
	{
		const std::string &constraint = collusion_resilience_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	collusion_resilience_constraint = conjunction(conjuncts);

	// practicality constraints
	conjuncts.clear();
	for (const json &practicality_constraint : document["property_constraints"]["practicality"])
	{
		const std::string &constraint = practicality_constraint;
		conjuncts.push_back(parser.parse_constraint(constraint.c_str()));
	}
	practicality_constraint = conjunction(conjuncts);

	// load the game tree and leak it so we can downcast to Branch
	Node *node = load_tree(*this, parser, document["tree"], supertree);

	if (node->is_leaf() || node->is_subtree())
	{
		std::cerr << "checkmate: root node is a leaf or a subtree (?!) - exiting" << std::endl;
		std::exit(EXIT_FAILURE);
	}
	// un-leaked and downcasted here
	root = std::unique_ptr<Branch>(static_cast<Branch *>(node));
}

// std::vector<HistoryChoice> Node::compute_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far) const {

// 		if (this -> is_leaf() || this->is_subtree()){
// 			return {};
// 		}
// 		std::vector<HistoryChoice> strategy;

// 		if (!this->branch().strategy.empty()){
// 			HistoryChoice hist_choice;
// 			hist_choice.player = players[this->branch().player];
// 			hist_choice.choice = this->branch().strategy;
// 			hist_choice.history = actions_so_far;

// 			strategy.push_back(hist_choice);
// 		}

// 		for (const Choice &choice: this->branch().choices) {
// 	 		std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
// 	 		updated_actions.push_back(choice.action);
// 	 		std::vector<HistoryChoice> child_strategy = choice.node->compute_strategy(players, updated_actions);
// 			strategy.insert(strategy.end(), child_strategy.begin(), child_strategy.end());
// 	 	}
// 		return strategy;
// 	}

// bool Node::cr_against_all() const {
// 	bool cr_against_all = true;

// 	for(auto violates_colluding_group : violates_cr) {

// 		if(violates_colluding_group) {
// 			cr_against_all = false;
// 		}
// 	}

// 	return cr_against_all;
// }

// std::vector<bool> convertToBinary(uint n)
// {
// 	std::vector<bool> bit_reps;

//     if (n / 2 != 0) {
//         bit_reps = convertToBinary(n / 2);
//     }

// 	bit_reps.push_back(n % 2 == 1);
// 	return bit_reps;
// }

// bool Node::cr_against_supergroups_of(std::vector<uint> deviating_players) const {

// 	for(uint64_t i=0; i < violates_cr.size(); i++) {
// 		std::vector<bool> bin_rep = convertToBinary(i+1);

// 		bool all_deviating_deviate = true;

// 		for(auto player: deviating_players) {
// 			if(player > bin_rep.size()) {
// 				all_deviating_deviate = false;
// 			} else {
// 				if(!bin_rep[player-1]) {
// 					all_deviating_deviate = false;
// 				}
// 			}
// 		}

// 		if(all_deviating_deviate && violates_cr[i]) {
// 			return false;
// 		}

// 	}

// 	return true;

// }

// void Node::add_violation_cr() const {
// 	violates_cr.push_back(false);

// 	if (!this->is_leaf() && !this->is_subtree()){

// 		for (const auto& child: this->branch().choices){
// 			child.node->add_violation_cr();
// 		}
// 	}
// 	return;
// }

// std::vector<HistoryChoice> Node::compute_cr_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<uint> deviating_players) const {

// 		if (this -> is_leaf() || this->is_subtree()){
// 			return {};
// 		}
// 		std::vector<HistoryChoice> strategy;
// 		std::string strategy_choice;

// 		if (honest) {
// 			for (const Choice &choice: this->branch().choices) {

// 				if (choice.node->honest) {
// 					assert(choice.node->cr_against_all());
// 					HistoryChoice hist_choice;
// 					hist_choice.player = players[this->branch().player];
// 					hist_choice.choice = choice.action;
// 					hist_choice.history = actions_so_far;
// 					strategy_choice = choice.action;

// 					strategy.push_back(hist_choice);
// 					break;
// 				}
// 			}
// 		} else {
// 			bool have_found_cr = false;
// 			for (const Choice &choice: this->branch().choices) {

// 				if (choice.node->cr_against_supergroups_of(deviating_players)){
// 					if(!have_found_cr) {
// 						have_found_cr = true;
// 						HistoryChoice hist_choice;
// 						hist_choice.player = players[this->branch().player];
// 						hist_choice.choice = choice.action;
// 						hist_choice.history = actions_so_far;
// 						strategy_choice = choice.action;

// 						strategy.push_back(hist_choice);
// 					}
// 				}

// 			}
// 			assert(have_found_cr);
// 		}

// 		for (const Choice &choice: this->branch().choices) {
// 			std::vector<uint> new_deviating_players;
// 			new_deviating_players.insert(new_deviating_players.end(), deviating_players.begin(), deviating_players.end());

// 			int cnt = std::count(deviating_players.begin(), deviating_players.end(), this->branch().player + 1);
// 			if((choice.action != strategy_choice) && (cnt == 0)) {
// 				new_deviating_players.push_back(this->branch().player + 1);
// 			}

// 	 		std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
// 	 		updated_actions.push_back(choice.action);

// 	 		std::vector<HistoryChoice> child_strategy = choice.node->compute_cr_strategy(players, updated_actions, new_deviating_players);
// 			strategy.insert(strategy.end(), child_strategy.begin(), child_strategy.end());
// 	 	}
// 		return strategy;
// 	}

// std::vector<HistoryChoice> Node::compute_pr_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<std::string>& strategy_vector) const {

// 		if (this -> is_leaf() || this->is_subtree()){
// 			return {};
// 		}

// 		assert(strategy_vector.size()>0);
// 		std::vector<HistoryChoice> strategy;

// 		HistoryChoice hist_choice;
// 		hist_choice.player = players[this->branch().player];
// 		hist_choice.choice = strategy_vector[0];
// 		strategy_vector.erase(strategy_vector.begin());
// 		hist_choice.history = actions_so_far;

// 		strategy.push_back(hist_choice);

// 		for (const Choice &choice: this->branch().choices) {
// 	 		std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
// 	 		updated_actions.push_back(choice.action);
// 	 		std::vector<HistoryChoice> child_strategy = choice.node->compute_pr_strategy(players, updated_actions, strategy_vector);
// 			strategy.insert(strategy.end(), child_strategy.begin(), child_strategy.end());
// 	 	}
// 		return strategy;
// 	}

// std::vector<CeChoice> Node::compute_wi_ce(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<size_t> player_group) const {

// 		if (this->is_leaf() || this->is_subtree()){
// 			return {};
// 		}
// 		std::vector<CeChoice> counterexample;

// 		assert(player_group.size() == 1);

// 		if (player_group[0] == this->branch().player) {
// 			if (honest){
// 				for (auto& child: this->branch().choices){
// 					if (child.node->honest) {
// 						std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
// 	 					updated_actions.push_back(child.action);
// 						counterexample = child.node->compute_wi_ce(players, updated_actions, player_group);
// 						break;
// 					}
// 				}
// 			} else {
// 				for (auto& child: this->branch().choices){
// 						std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
// 	 					updated_actions.push_back(child.action);
// 						std::vector<CeChoice> child_counterexample = child.node->compute_wi_ce(players, updated_actions, player_group);
// 						counterexample.insert(counterexample.end(),child_counterexample.begin(), child_counterexample.end());
// 				}
// 			}
// 		} else {
// 			assert(!this->branch().counterexample_choices.empty());
// 			CeChoice ce_choice;
// 			ce_choice.player = players[this->branch().player];
// 			ce_choice.choices = this->branch().counterexample_choices;
// 			ce_choice.history = actions_so_far;

// 			counterexample.push_back(ce_choice);

// 			for (const Choice &choice: this->branch().choices) {

// 				int cnt = std::count(this->branch().counterexample_choices.begin(), this->branch().counterexample_choices.end(), choice.action);
// 				if (cnt > 0) {
// 					std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
// 					updated_actions.push_back(choice.action);
// 					std::vector<CeChoice> child_ce = choice.node->compute_wi_ce(players, updated_actions, player_group);
// 					counterexample.insert(counterexample.end(), child_ce.begin(), child_ce.end());
// 				}
// 			}
// 		}
// 		return counterexample;
// 	}

// std::vector<CeChoice> Node::compute_cr_ce(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<size_t> player_group) const {

// 		if (this->is_leaf() || this->is_subtree()){
// 			return {};
// 		}
// 		std::vector<CeChoice> counterexample;

// 		assert(player_group.size() >= 1);

// 		int cnt = std::count(player_group.begin(), player_group.end(), this->branch().player);
// 		if (cnt == 0) {
// 			if (honest){
// 				for (auto& child: this->branch().choices){
// 					if (child.node->honest) {
// 						std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
// 	 					updated_actions.push_back(child.action);
// 						counterexample = child.node->compute_cr_ce(players, updated_actions, player_group);
// 						break;
// 					}
// 				}
// 			} else {
// 				for (auto& child: this->branch().choices){
// 						std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
// 	 					updated_actions.push_back(child.action);
// 						std::vector<CeChoice> child_counterexample = child.node->compute_cr_ce(players, updated_actions, player_group);
// 						counterexample.insert(counterexample.end(),child_counterexample.begin(), child_counterexample.end());
// 				}
// 			}
// 		} else {
// 			assert(!this->branch().counterexample_choices.empty());
// 			CeChoice ce_choice;
// 			ce_choice.player = players[this->branch().player];
// 			ce_choice.choices = this->branch().counterexample_choices;
// 			ce_choice.history = actions_so_far;

// 			counterexample.push_back(ce_choice);

// 			for (const Choice &choice: this->branch().choices) {

// 				int cnt = std::count(this->branch().counterexample_choices.begin(), this->branch().counterexample_choices.end(), choice.action);
// 				if (cnt > 0) {
// 					std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
// 					updated_actions.push_back(choice.action);
// 					std::vector<CeChoice> child_ce = choice.node->compute_cr_ce(players, updated_actions, player_group);
// 					counterexample.insert(counterexample.end(), child_ce.begin(), child_ce.end());
// 				}
// 			}
// 		}
// 		return counterexample;
// 	}

// CeCase Node::compute_pr_cecase(std::vector<std::string> players, unsigned current_player, std::vector<std::string> actions_so_far, std::string current_action, UtilityTuplesSet practical_utilities) const {

// 	// regular case (called from branch)
// 	if(current_player < players.size()) {
// 		CeCase cecase;
// 		cecase.player_group = {players[current_player]};

// 		const Node* deviation_node = nullptr;

// 		std::vector<std::string> actions_to_deviation;
// 		actions_to_deviation.insert(actions_to_deviation.end(), actions_so_far.begin(), actions_so_far.end());
// 		actions_to_deviation.push_back(current_action); // BE AWARE: current_action = action leading to subtree where pr histories are ce

// 		deviation_node = compute_deviation_node(actions_to_deviation);
// 		std::vector<CeChoice> rec_choices = deviation_node->compute_pr_ce(current_action, actions_so_far, practical_utilities);
// 		cecase.counterexample.insert(cecase.counterexample.end(), rec_choices.begin(), rec_choices.end());
// 		return cecase;
// 	} else {
// 		// called from subtree
// 		CeCase cecase;
// 		cecase.player_group = {}; // check and handle this when printing counterexamples

// 		CeChoice deviation;
// 		deviation.history = actions_so_far;
// 		cecase.counterexample = {deviation};

// 		return cecase;

// 	}
// }

// const Node* Node::compute_deviation_node(std::vector<std::string> actions_so_far) const {

// 	if(actions_so_far.size() > 0) {
// 		assert(!this->is_leaf());
// 		assert(!this->is_subtree());
// 		for (const auto &child: this->branch().choices){
// 			if(child.action == actions_so_far[0]) {
// 				actions_so_far.erase(actions_so_far.begin());
// 				return child.node.get()->compute_deviation_node(actions_so_far);
// 			}
// 		}
// 	}

// 	return this;

// }

// // Be aware that return value represents a set of histories, rather than one partial strategy
// // This has to be taken into account when printing the counterexamples
// std::vector<CeChoice> Node::compute_pr_ce(std::string current_action, std::vector<std::string> actions_so_far, UtilityTuplesSet practical_utilities) const {
// 	std::vector<CeChoice> cechoices;

// 	for(auto &utility : practical_utilities) {

// 		CeChoice cechoice;
// 		cechoice.player = "";

// 		cechoice.choices = {};

// 		std::vector<std::string> result_hist = strat2hist(utility.strategy_vector);
// 		cechoice.choices.insert(cechoice.choices.end(), result_hist.begin(), result_hist.end());

// 		std::vector<std::string> updated_history;
// 		updated_history.insert(updated_history.end(), actions_so_far.begin(), actions_so_far.end());
// 		updated_history.push_back(current_action);
// 		cechoice.history = updated_history;
// 		cechoices.push_back(cechoice);

// 	}

// 	return cechoices;
// }

// std::vector<std::string> Node::strat2hist(std::vector<std::string> &strategy) const {

// 	if(this->is_leaf()) {
// 		return {};
// 	} else if (this->is_subtree()) {
// 		return {};
// 	}

// 	assert(strategy.size() > 0);

// 	std::vector<std::string> strategy_copy;
// 	strategy_copy.insert(strategy_copy.begin(), strategy.begin(), strategy.end());

// 	std::vector<std::string> hist_player_pairs;
// 	std::string first_action = strategy_copy[0];
// 	strategy_copy.erase(strategy_copy.begin());
// 	hist_player_pairs.push_back(first_action);

// 	bool found = false;
// 	for(auto &child: this->branch().choices) {

// 		if(child.action == first_action) {
// 			std::vector<std::string> child_result = child.node->strat2hist(strategy_copy);
// 			hist_player_pairs.insert(hist_player_pairs.end(), child_result.begin(), child_result.end());
// 			found = true;
// 		} else {
// 			child.node->prune_actions_from_strategy(strategy_copy);
// 		}
// 	}

// 	assert(found);

// 	return hist_player_pairs;

// }

// void Node::prune_actions_from_strategy(std::vector<std::string> &strategy) const {

// 	if(this->is_leaf() || this->is_subtree()) {
// 		return;
// 	}

// 	assert(strategy.size() > 0);
// 	strategy.erase(strategy.begin());
// 	for(auto &child: this->branch().choices) {
// 		child.node->prune_actions_from_strategy(strategy);
// 	}
// }

// void Node::reset_violation_cr() const {
// 		violates_cr = {};

// 		if (!this->is_leaf() && !this->is_subtree()){

// 			for (const auto& child: this->branch().choices){
// 				child.node->reset_violation_cr();
// 			}
// 		}
// 		return;
// }

// std::vector<std::vector<bool>> Node::store_violation_cr() const {

// 	std::vector<std::vector<bool>> violation = {violates_cr};

// 	if (!this->is_leaf() && !this->is_subtree()){

// 		for (const auto& child: this->branch().choices){
// 			std::vector<std::vector<bool>> child_violation = child.node->store_violation_cr();
// 			violation.insert(violation.end(), child_violation.begin(), child_violation.end());
// 		}
// 	}
// 	return violation;
// }

// void Node::restore_violation_cr(std::vector<std::vector<bool>> &violation) const {

// 	assert(violation.size()>0);
// 	violates_cr = violation[0];
// 	violation.erase(violation.begin());

// 	if (!this->is_leaf() && !this->is_subtree()){

// 		for (const auto& child: this->branch().choices){
// 			child.node->restore_violation_cr(violation);
// 		}
// 	}

// 	return;
// }
