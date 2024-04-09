#ifndef __checkmate_input__
#define __checkmate_input__

#include <memory>
#include <string>
#include <unordered_map>

#include "utility.hpp"
#include "utils.hpp"
#include "z3++.hpp"

// an action available at a branch
struct Action {
	// the name of the action
	std::string name;

	friend std::ostream &operator<<(std::ostream &out, const Action &action) {
		return out << action.name;
	}
};

// forward declarations for Node methods
struct Leaf;
struct Branch;
struct Choice;

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

	// the reason that a check for a property failed:
	// null if didn't fail or no case split would help
	mutable z3::Bool reason;

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
		if(reason.null())
			return;

		::new (&reason) z3::Bool();
		for(auto &choice: choices)
			if(!choice.node->is_leaf())
				choice.node->branch().reset_reason();
	}
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

#endif
