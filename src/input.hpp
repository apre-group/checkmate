#ifndef __checkmate_input__
#define __checkmate_input__

#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>

#include "z3++.hpp"
#include "utility.hpp"

struct Leaf;
struct Branch;

struct Action {
	bool operator==(const Action &other) const { return name == other.name; }
	std::string name;
	z3::Bool variable;
};

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

	template<typename State, typename VisitLeaf, typename VisitBranch, typename Recurse>
	void visit(VisitLeaf, VisitBranch, Recurse);
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
		throw std::logic_error("Branch::get_player_utility() failed to find anything");
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

template<typename State, typename VisitLeaf, typename VisitBranch, typename Recurse>
inline void Node::visit(VisitLeaf visit_leaf, VisitBranch visit_branch, Recurse recurse) {
	struct Todo {
		Todo(const Branch &branch, State state) :
			branch(branch),
			state(state),
			choices(branch.choices.begin())
		{}
		const Branch &branch;
		State state;
		std::vector<Choice>::const_iterator choices;
	};
	std::vector<Todo> todo;

	auto enqueue = [&](const Node &node, State state) {
		if(node.is_leaf()) {
			visit_leaf(state, node.leaf());
			return;
		}
		const Branch &branch = node.branch();
		visit_branch(state, branch);
		todo.emplace_back(branch, std::move(state));
	};

	enqueue(*this, State());
	while(!todo.empty()) {
		Todo &current = todo.back();
		if(current.choices == current.branch.choices.end()) {
			todo.pop_back();
			continue;
		}
		const Choice &choice = *current.choices++;
		State next_state(current.state);
		recurse(next_state, choice);
		enqueue(*choice.node, next_state);
	};
}

class Input {
public:
	Input(const char *path);
	std::vector<std::string> players;
	std::vector<z3::Real> quantify;
	std::unordered_map<std::string, Utility> utilities;
	z3::Bool initial_constraint;
	z3::Bool weak_immunity_constraint;
	z3::Bool weaker_immunity_constraint;
	z3::Bool collusion_resilience_constraint;
	z3::Bool practicality_constraint;
	std::vector<z3::Bool> honest_histories;
	std::vector<std::reference_wrapper<const Leaf>> honest_history_leaves;
	std::unique_ptr<Node> root;
};

#endif
