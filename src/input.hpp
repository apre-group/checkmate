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

	template<
		typename State,
		typename VisitLeaf,
		typename StartBranch,
		typename StartChoice,
		typename EndChoice,
		typename EndBranch
	>
	void visit(VisitLeaf, StartBranch, StartChoice, EndChoice, EndBranch);
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

template<
	typename State,
	typename VisitLeaf,
	typename StartBranch,
	typename StartChoice,
	typename EndChoice,
	typename EndBranch
>
inline void Node::visit(
	VisitLeaf visit_leaf,
	StartBranch start_branch,
	StartChoice start_choice,
	EndChoice end_choice,
	EndBranch end_branch
) {
	State initial;
	if(is_leaf()) {
		visit_leaf(initial, leaf());
		return;
	}

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
	const Branch &root = branch();
	start_branch(initial, root);
	todo.emplace_back(root, std::move(initial));

	while(true) {
		Todo &current = todo.back();
		if(current.choices == current.branch.choices.end()) {
			end_branch(current.state, current.branch);
			State state = std::move(current.state);
			todo.pop_back();
			if(todo.empty())
				break;
			Todo &parent = todo.back();
			const Choice &choice = *parent.choices++;
			end_choice(parent.state, std::move(state), parent.branch, choice);
			continue;
		}
		const Choice &choice = *current.choices;
		State next_state;
		start_choice(current.state, next_state, current.branch, choice);
		if(choice.node->is_leaf()) {
			visit_leaf(next_state, choice.node->leaf());
			State state = std::move(current.state);
			todo.pop_back();
			if(todo.empty())
				break;
			Todo &parent = todo.back();
			const Choice &choice = *parent.choices++;
			end_choice(parent.state, std::move(state), parent.branch, choice);
		}
		else {
			const Branch &next_branch = choice.node->branch();
			start_branch(next_state, next_branch);
			todo.emplace_back(next_branch, std::move(next_state));
		}
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
	std::unique_ptr<Branch> root;

	static const size_t MAX_PLAYERS = 64;
};

#endif
