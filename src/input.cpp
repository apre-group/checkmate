#include <fstream>
#include <iostream>
#include "json.hpp"

#include "input.hpp"

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
		OR,
		COMPARISON,
		PLUSMINUS,
		MULTIPLY,
		NEGATE
	};

	// the precedence class of an operator
	static Precedence precedence(Operation operation) {
		switch (operation) {
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

/*
 * load a tree from a JSON document `node`, assuming a certain format
 * - `input` is the input parsed so far
 * - `action_constraints` are filled out as we go
 *
 * TODO does not check all aspects
 * (hoping to have new input format based on s-expressions, which would be much easier to parse)
 */
static std::unique_ptr<Node> load_tree(const Input &input, Parser &parser, const json &node) {
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
			auto loaded = load_tree(input, parser, child["child"]);
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
		players.push_back({player});
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
	auto node = load_tree(*this, parser, document["tree"]).release();
	if (node->is_leaf()) {
		std::cerr << "checkmate: root node is a leaf (?!) - exiting" << std::endl;
		std::exit(EXIT_FAILURE);
	}
	// un-leaked and downcasted here
	root = std::unique_ptr<Branch>(static_cast<Branch *>(node));

}

std::vector<HistoryChoice> Node::compute_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far) const {

		if (this -> is_leaf()){
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

		/*for(auto player: deviating_players) {
			if(player <= bin_rep.size()) {
				if(bin_rep[player-1]) {
					std::cout << "bin rep " << bin_rep << std::endl;
					std::cout << "deviating players " << deviating_players << std::endl;
					std::cout << "i " << i << std::endl;
					if(violates_cr[i]) {
						std::cout << "in if" << std::endl;
						cr_against_supergroups = false;
					}
				}
			}
		}*/

	}

	return true;

}

void Node::add_violation_cr() const {
	violates_cr.push_back(false);

	if (!this->is_leaf()){

		for (const auto& child: this->branch().choices){
			child.node->add_violation_cr();
		}
	}
	return;
}

std::vector<HistoryChoice> Node::compute_cr_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<uint> deviating_players) const {

		if (this -> is_leaf()){
			return {};
		}
		std::vector<HistoryChoice> strategy;
		std::string strategy_choice;

		if (honest) {
			for (const Choice &choice: this->branch().choices) {

				if (choice.node->honest) {
					assert(choice.node->cr_against_all());
					HistoryChoice hist_choice;
					hist_choice.player = players[this->branch().player];
					hist_choice.choice = choice.action;
					hist_choice.history = actions_so_far;
					strategy_choice = choice.action;

					// std::cout << "player " << hist_choice.player << " takes action " << choice.action << " after history " << actions_so_far << std::endl;
					strategy.push_back(hist_choice);
					break;
				}
			}
		} else {
			bool have_found_cr = false;
			for (const Choice &choice: this->branch().choices) {

				//std::cout << "After history " << actions_so_far << " action " << choice.action << " violates_cr: " << choice.node->violates_cr << " deviating players" << deviating_players << std::endl;
				if (choice.node->cr_against_supergroups_of(deviating_players)){
					if(!have_found_cr) {
						have_found_cr = true;
						HistoryChoice hist_choice;
						hist_choice.player = players[this->branch().player];
						hist_choice.choice = choice.action;
						hist_choice.history = actions_so_far;
						strategy_choice = choice.action;

						//std::cout << "player " << hist_choice.player << " takes action " << choice.action << " after history " << actions_so_far << std::endl;
						strategy.push_back(hist_choice);
						//break; 
					}
				}

			}
			//std::cout << actions_so_far << std::endl;
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
		return strategy;
	}

std::vector<HistoryChoice> Node::compute_pr_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<std::string>& strategy_vector) const {

		if (this -> is_leaf()){
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

		if (this->is_leaf()){
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

std::vector<CeChoice> Node::compute_cr_ce(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<size_t> player_group) const {

		if (this->is_leaf()){
			return {};
		}
		std::vector<CeChoice> counterexample;

		assert(player_group.size() >= 1);


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
		return counterexample;
	}


CeCase Node::compute_pr_cecase(std::vector<std::string> players, unsigned current_player, std::vector<std::string> actions_so_far, std::string current_action, UtilityTuplesSet practical_utilities) const {
	
	CeCase cecase;
	cecase.player_group = {players[current_player]};
	CeChoice deviation;
	deviation.history = actions_so_far;
	deviation.choices = {current_action};
	deviation.player = players[current_player];
	//cecase.counterexample = {deviation};

	const Node* deviation_node = nullptr;

	std::vector<std::string> actions_to_deviation;
	actions_to_deviation.insert(actions_to_deviation.end(), actions_so_far.begin(), actions_so_far.end());
	actions_to_deviation.push_back(current_action); // BE AWARE current_action = action leading to subtree where pr histories are ce

	deviation_node = compute_deviation_node(actions_to_deviation);

	std::vector<CeChoice> rec_choices = deviation_node->compute_pr_ce(current_action, actions_so_far, practical_utilities);
	cecase.counterexample.insert(cecase.counterexample.end(), rec_choices.begin(), rec_choices.end());
	return cecase;
}

const Node* Node::compute_deviation_node(std::vector<std::string> actions_so_far) const {
	
	if(actions_so_far.size() > 0) {
		assert(!this->is_leaf());
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

		//cechoice.choices = {current_action};
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
	} 

	assert(strategy.size() > 0);
	
	std::vector<std::string> hist_player_pairs;
	std::string first_action = strategy[0];
	strategy.erase(strategy.begin());
	hist_player_pairs.push_back(first_action);

	bool found = false;
	for(auto &child: this->branch().choices) {

		if(child.action == first_action) {
			std::vector<std::string> child_result = child.node->strat2hist(strategy);
			hist_player_pairs.insert(hist_player_pairs.end(), child_result.begin(), child_result.end());
			found = true;
		} else {
			child.node->prune_actions_from_strategy(strategy);
		}
	}

	assert(found);
 	
	return hist_player_pairs;

}

void Node::prune_actions_from_strategy(std::vector<std::string> &strategy) const {

	if(this->is_leaf()) {
		return;
	} 

	assert(strategy.size() > 0);
	strategy.erase(strategy.begin());
	for(auto &child: this->branch().choices) {
		child.node->prune_actions_from_strategy(strategy);
	}
}

void Node::reset_violation_cr() const {
		violates_cr = {};

		if (!this->is_leaf()){

			for (const auto& child: this->branch().choices){
				child.node->reset_violation_cr();
			}
		}
		return;
}

std::vector<std::vector<bool>> Node::store_violation_cr() const {

	std::vector<std::vector<bool>> violation = {violates_cr};

	if (!this->is_leaf()){

		for (const auto& child: this->branch().choices){
			std::vector<std::vector<bool>> child_violation = child.node->store_violation_cr();
			violation.insert(violation.end(), child_violation.begin(), child_violation.end());
		}
	} 
	return violation;
}

void Node::restore_violation_cr(std::vector<std::vector<bool>> &violation) const {

	assert(violation.size()>0);
	violates_cr = violation[0];
	violation.erase(violation.begin());

	if (!this->is_leaf()){

		for (const auto& child: this->branch().choices){
			child.node->restore_violation_cr(violation);
		}
	}

	return;
}