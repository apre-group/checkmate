#ifndef __checkmate_input__
#define __checkmate_input__

#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>

#include "z3++.hpp"
#include "utility.hpp"

struct Leaf;
struct Branch;

struct Player {
	bool operator ==(const Player &other) const {
		return name == other.name;
	}

	std::string name;
};

struct PlayerUtility {
	Player player;
	Utility utility;
};

struct Action {
	bool operator ==(const Action &other) const {
		return name == other.name;
	}

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
};

struct Choice {
	Action action;
	std::unique_ptr<Node> tree;
};

struct Leaf final : public Node {
	virtual bool is_leaf() const { return true; }
	const PlayerUtility &get_player_utility(const std::string &player) const {
		for(const PlayerUtility &player_utility : utilities)
			if(player_utility.player.name == player)
				return player_utility;
		throw std::logic_error("Leaf::get_player_utility() failed to find anything");
	}

	std::vector<PlayerUtility> utilities;
};

struct Branch final : public Node {
	Branch(Player player) : player(player) {}
	virtual bool is_leaf() const { return false; }

	const Choice &get_choice(const std::string &action) const {
		for(const Choice &choice : choices)
			if(choice.action.name == action)
				return choice;
		throw std::logic_error("Choice::get_player_utility() failed to find anything");
	}

	Player player;
	std::vector<Choice> choices;
};

inline const Leaf &Node::leaf() const {
	return *static_cast<const Leaf *>(this);
}

inline const Branch &Node::branch() const {
	return *static_cast<const Branch *>(this);
}

struct Input {
	Input(const char *path);
	std::vector<Player> players;
	std::vector<z3::Real> constants;
	std::unordered_map<std::string, Utility> utilities;
	z3::Bool initial_constraint;
	z3::Bool weak_immunity_constraint;
	z3::Bool weaker_immunity_constraint;
	z3::Bool collusion_resilience_constraint;
	z3::Bool practicality_constraint;
	std::vector<z3::Bool> honest_histories;
	std::unique_ptr<Node> root;
};

#endif
