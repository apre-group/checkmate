#ifndef __checkmate_input__
#define __checkmate_input__

#include <memory>
#include <string>
#include <unordered_map>

#include "utility.hpp"
#include "utils.hpp"
#include "z3++.hpp"

// forward declarations for Node methods
struct Leaf;
struct Branch;
struct Choice;

// TODO: make find() work for vector<z3::Bool> instead of using this function
inline bool case_found (z3::Bool _case_to_find, const std::vector<z3::Bool> _case) {
	std::equal_to<z3::Bool> eq1;
	bool found = false;

	for(auto _c : _case) {
		if (eq1(_case_to_find, _c)) {
			found = true;
			break;
		}
	}
	return found;
}

inline bool are_compatible_cases(const std::vector<z3::Bool> _case1, const std::vector<z3::Bool> _case2) {
	bool compatible_cases = true;

	for (const auto& _case : _case1) {
		if(!case_found(_case, _case2)) {
			compatible_cases = false;
			break;
		}
	}

	return compatible_cases;
}

struct Input {
	// parse an input from `path`, exiting if malformed
	Input(const char *path);

	// list of players in alphabetical order
	std::vector<std::string> players;
	// list of honest histories
	std::vector<std::vector<std::string>> honest;

	// a real or infinitesimal utility for each string
	std::unordered_map<std::string, Utility> utilities;

	// global initial constraints
	z3::Bool initial_constraint;
	// weak immunity initial constraints
	z3::Bool weak_immunity_constraint;
	// weaker immunity initial constraints
	z3::Bool weaker_immunity_constraint;
	// collusion resilience initial constraints
	z3::Bool collusion_resilience_constraint;
	// practicality initial constraints
	z3::Bool practicality_constraint;

	// root: NB must be a branch
	std::unique_ptr<Branch> root;

	// maximum number of players currently supported
	// no reason there couldn't be more, but convenient for implementation (cf collusion resilience)
	static const size_t MAX_PLAYERS = 64;
};

// an action available at a branch
struct Action {
	// the name of the action
	std::string name;

	friend std::ostream &operator<<(std::ostream &out, const Action &action) {
		return out << action.name;
	}
};

// abstract base class for Leaf and Branch
struct Node {
	// can default-construct and move Nodes...
	Node() = default;

	Node(Node &&) = default;

	Node &operator=(Node &&) = default;

	// ...but not copy them to avoid accidentally copying a whole tree
	Node(const Node &) = delete;

	Node &operator=(const Node &) = delete;

	virtual ~Node() {};

	// is this a leaf?
	virtual bool is_leaf() const = 0;

	// if is_leaf(), do the downcast
	const Leaf &leaf() const;

	// if !is_leaf(), do the downcast
	const Branch &branch() const;

	// are we (currently) along the honest history?
	mutable bool honest = false;

	// the reason that a check for a property failed:
	// null if didn't fail or no case split would help
	mutable z3::Bool reason;

};

// a choice available at a branch
struct Choice {
	// take this action
	std::string action;
	// end up in this subtree
	std::unique_ptr<Node> node;

	friend std::ostream &operator<<(std::ostream &out, const Choice &choice) {
		return out << choice.action;
	}
};

// leaf node
struct Leaf final : public Node {
	virtual bool is_leaf() const { return true; }

	// utilities for each player: NB in lexicographic order of players!
	std::vector<Utility> utilities;

	void reset_reason() const {
		::new (&reason) z3::Bool();
	}
};

// branch node
struct Branch final : public Node {
	Branch(unsigned player) : player(player) {}

	virtual bool is_leaf() const { return false; }

	// do a linear-time lookup of `action` by name in the branch, which must be present
	const Choice &get_choice(const std::string &action) const {
		for (const Choice &choice: choices)
			if (choice.action == action)
				return choice;

		assert(false);
		UNREACHABLE;
	}

	// do a linear-time lookup of `action` by child address in the branch, which must be present
	const Choice &get_choice(const Node *child) const {
		for (const Choice &choice: choices)
			if (choice.node.get() == child)
				return choice;

		assert(false);
		UNREACHABLE;
	}

	const Choice &get_honest_child() const {
		for (const Choice &choice: choices)
			if (choice.node->honest)
				return choice;

		assert(false);
		UNREACHABLE;
	}

	// whose turn is it?
	unsigned player;
	// available choices, from which actions should be unique
	std::vector<Choice> choices;
	// take this action
	mutable std::string strategy;

	mutable std::vector<std::vector<z3::Bool>> pr_strategies_cases;
	mutable std::vector<std::string> pr_strategies_actions;

	void mark_honest(const std::vector<std::string> &history) const {
		assert(!honest);

		honest = true;
		const Node *current = this;
		unsigned index = 0;
		do {
			current = current->branch().get_choice(history[index++]).node.get();
			current->honest = true;
		} while(!current->is_leaf());
	}

	void reset_honest() const {
		if(!honest)
			return;

		honest = false;
		const Node *current = this;
		do {
			current = current->branch().get_honest_child().node.get();
			current->honest = false;
		} while(!current->is_leaf());
	}

	void reset_reason() const {
		::new (&reason) z3::Bool();
		for(auto &choice: choices)
			if(!choice.node->is_leaf())
				choice.node->branch().reset_reason();
			else
				choice.node->leaf().reset_reason();
	}

	void reset_strategy() const {
		strategy.clear();
		for(auto &choice: choices)
			if(!choice.node->is_leaf())
				choice.node->branch().reset_strategy();
	}

	void reset_strategy_pr() const {
		pr_strategies_cases = {};
		pr_strategies_actions = {};
		for(auto &choice: choices)
			if(!choice.node->is_leaf())
				choice.node->branch().reset_strategy();
	}

	void print_strategy(const Input &input) const {
		std::vector<std::string> actions_so_far;
		std::cout << "Printing strategy..." << std::endl;
		const Node *current = this;
		print_strategy_rec(current, input, {});	
		std::cout << "\tPlayers can choose the rest of the actions arbitrarily ..." << std::endl;	
	}

	void print_strategy_rec(const Node *current, const Input &input, std::vector<std::string> actions_so_far) const {
		if(current->is_leaf()) 
			return;

		if(!current->branch().strategy.empty()) {
			std::cout
					<< "\tPlayer "
					<< input.players[current->branch().player]
					<< " takes action "
					<< current->branch().strategy
					<< " after history "
					<< actions_so_far
					<< std::endl;
		}

		for (const Choice &choice: current->branch().choices) {
			std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
			updated_actions.push_back(choice.action);
			print_strategy_rec(choice.node.get(), input, updated_actions);
		}
	}

	void print_strategy_pr(const Input &input, std::vector<z3::Bool> &current_case) const {
		std::vector<std::string> actions_so_far;
		const Node *current = this;

		std::cout << "Printing strategy for case " << current_case << "..." << std::endl;
		
		//std::cout << "...................." << std::endl;
		//std::cout << current->branch().pr_strategies_cases << std::endl;
		//std::cout << "....Actions................" << std::endl;
		//std::cout << current->branch().pr_strategies_actions << std::endl;
		//std::cout << "...................." << std::endl;
		
		
		print_strategy_pr_rec(current, input, {}, current_case);	

		std::cout << std::endl;
		std::cout << std::endl;

	}

	void print_strategy_pr_rec(const Node *current, const Input &input, std::vector<std::string> actions_so_far, std::vector<z3::Bool> &current_case) const {
		if(current->is_leaf()) 
			return;

		if(!current->branch().pr_strategies_cases.empty()) {

			for (unsigned i = 0; i < current->branch().pr_strategies_cases.size(); i++) {
				if(are_compatible_cases(current->branch().pr_strategies_cases[i], current_case)) {
					std::cout
					<< "\tPlayer "
					<< input.players[current->branch().player]
					<< " takes action "
					<< current->branch().pr_strategies_actions[i]
					<< " after history "
					<< actions_so_far
					<< std::endl;
					break;
				}
			}			
		}

		for (const Choice &choice: current->branch().choices) {
			std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
			updated_actions.push_back(choice.action);
			print_strategy_pr_rec(choice.node.get(), input, updated_actions, current_case);
		}
	}

};

inline const Leaf &Node::leaf() const {
	return *static_cast<const Leaf *>(this);
}

inline const Branch &Node::branch() const {
	return *static_cast<const Branch *>(this);
}

#endif
