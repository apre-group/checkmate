#ifndef __checkmate_input__
#define __checkmate_input__

#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>

#include "z3++.hpp"
#include "utility.hpp"

struct Action {
	bool operator==(const Action &other) const { return name == other.name; }
	std::string name;
	z3::Bool variable;
};

struct Leaf;
struct Branch;
struct Node {
	Node() = default;
	Node(const Node &) = delete;
	Node &operator=(const Node &) = delete;
	Node(Node &&) = default;
	Node &operator=(Node &&) = default;
	virtual ~Node() {};

	virtual bool is_leaf() const = 0;
	virtual bool is_branch() const { return !is_leaf(); }
	const Leaf &leaf() const;
	const Branch &branch() const;
};

struct Choice {
	Action action;
	std::unique_ptr<Node> node;
};

struct Leaf final : public Node {
	virtual bool is_leaf() const { return true; }
	std::vector<Utility> utilities;
};

struct Branch final : public Node {
	Branch(unsigned player) : player(player) {}
	virtual bool is_leaf() const { return false; }

	const Choice &get_choice(const std::string &action) const {
		for(const Choice &choice : choices)
			if(choice.action.name == action)
				return choice;
		throw std::logic_error("Branch::get_choice() failed to find anything");
	}

	unsigned player;
	std::vector<Choice> choices;
};

inline const Leaf &Node::leaf() const {
	return *static_cast<const Leaf *>(this);
}

inline const Branch &Node::branch() const {
	return *static_cast<const Branch *>(this);
}

class Input {
public:
	// parse an input from `path`
	Input(const char *path);

	// list of players in alphabetical order
	std::vector<std::string> players;
	// all real or infinitesimal constants
	std::vector<z3::Real> quantify;
	// a real or infinitesimal utility for each string
	std::unordered_map<std::string, Utility> utilities;

	z3::Bool action_constraint;
	z3::Bool initial_constraint;
	z3::Bool weak_immunity_constraint;
	z3::Bool weaker_immunity_constraint;
	z3::Bool collusion_resilience_constraint;
	z3::Bool practicality_constraint;
	std::vector<z3::Bool> honest_histories;
	// the leaves reached by each honest history
	std::vector<std::reference_wrapper<const Leaf>> honest_history_leaves;
	// root: NB must be a branch
	std::unique_ptr<Branch> root;

	// maximum number of players currently supported
	// no reason there couldn't be more, but convenient for implementation (cf collusion resilience)
	static const size_t MAX_PLAYERS = 64;
};

#endif
