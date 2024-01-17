#ifndef __checkmate_input__
#define __checkmate_input__

#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>

#include "utility.hpp"
#include "utils.hpp"
#include "z3++.hpp"

// an action available at a branch
struct Action {
	// the name of the action
	std::string name;
	// a Z3 variable representing taking this action
	z3::Bool variable;

	friend std::ostream &operator<<(std::ostream &out, const Action &action) {
		return out << action.name;
	}
};

// forward declarations for Node::leaf() and Node::branch()
struct Leaf;
struct Branch;

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
	// if is_branch(), do the downcast
	const Branch &branch() const;

	// parent node, or `nullptr` if the root
	Branch *parent = nullptr;
	// traverse upwards to compute the history for this node
	std::vector<std::reference_wrapper<const Action>> compute_history() const;
	// the length of that history
	size_t history_length() const;
};

// a choice available at a branch
struct Choice {
	// take this action
	Action action;
	// end up in this subtree
	std::unique_ptr<Node> node;
};

// leaf node
struct Leaf final : public Node {
	virtual bool is_leaf() const { return true; }
	// utilities for each player: NB in lexicographic order of players!
	std::vector<Utility> utilities;
};

// branch node
struct Branch final : public Node {
	Branch(unsigned player) : player(player), label(z3::Bool::fresh()) {}
	virtual bool is_leaf() const { return false; }

	// do a linear-time lookup of `action` by name in the branch, which must be present
	const Choice &get_choice(const std::string &action) const {
		for(const Choice &choice : choices)
			if(choice.action.name == action)
				return choice;

		assert(false);
		UNREACHABLE;
	}

	// do a linear-time lookup of `action` by child address in the branch, which must be present
	const Choice &get_choice(const Node *child) const {
		for(const Choice &choice : choices)
			if(choice.node.get() == child)
				return choice;

		assert(false);
		UNREACHABLE;
	}


	// whose turn is it?
	unsigned player;
	// label for this branch
	z3::Bool label;
	// available choices, from which actions should be unique
	std::vector<Choice> choices;
};

inline const Leaf &Node::leaf() const {
	return *static_cast<const Leaf *>(this);
}

inline const Branch &Node::branch() const {
	return *static_cast<const Branch *>(this);
}

struct Input {
	// parse an input from `path`, exiting if malformed
	Input(const char *path);

	// list of players in alphabetical order
	std::vector<std::string> players;
	// all real or infinitesimal constants
	std::vector<z3::Real> quantify;
	// a real or infinitesimal utility for each string
	std::unordered_map<std::string, Utility> utilities;

	// constraint: at each branch exactly one action must be taken
	z3::Bool action_constraint;

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
	// honest histories
	std::vector<z3::Bool> honest_histories;

	// honest histories for output
	std::vector<std::vector<std::string>> readable_honest_histories;

	// the leaves reached by each honest history, living as long as the containing input
	std::vector<std::reference_wrapper<const Leaf>> honest_history_leaves;

	// root: NB must be a branch
	std::unique_ptr<Branch> root;

	// maximum number of players currently supported
	// no reason there couldn't be more, but convenient for implementation (cf collusion resilience)
	static const size_t MAX_PLAYERS = 64;
};

#endif
