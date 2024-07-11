#ifndef __checkmate_input__
#define __checkmate_input__

#include <memory>
#include <string>
#include <bitset>
#include <unordered_map>

#include "utility.hpp"
#include "utils.hpp"
#include "z3++.hpp"

// forward declarations for Node methods
struct Leaf;
struct Branch;
struct Choice;
struct Node;

// reference to a utility tuple in a leaf
struct UtilityTuple {
	const std::vector<Utility> &leaf;
	mutable std::vector<std::string> strategy_vector;



	UtilityTuple(decltype(leaf) leaf) : leaf(leaf), strategy_vector() {}
	size_t size() const { return leaf.size(); }
	const Utility &operator[](size_t index) const { return leaf[index]; }
	std::vector<Utility>::const_iterator begin() const { return leaf.cbegin(); }
	std::vector<Utility>::const_iterator end() const { return leaf.cend(); }

	bool operator==(const UtilityTuple &other) const {
		// quick return for when you have the same reference
		if(this == &other)
			return true;
		if(size() != other.size())
			return false;
		for(size_t i = 0; i < size(); i++)
			if(!leaf[i].is(other.leaf[i]))
				return false;
		return true;
	}
};

// when hashing, hash its utilities sequentially
template<>
struct std::hash<UtilityTuple> {
	size_t operator()(UtilityTuple tuple) const {
		 size_t hash = 0;
		 for(const Utility &utility : tuple)
			 hash ^= std::hash<Utility>{}(utility);
		 return hash;
	}
};

using UtilityTuplesSet = std::unordered_set<UtilityTuple>;

struct HistoryChoice{
	std::string player;
	std::string choice;
	std::vector<std::string> history;
};

struct StrategyCase {
	std::vector<z3::Bool> _case;
	std::vector<HistoryChoice> strategy; 
};

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

	mutable bool violates_cr = false; // set to true as soon as its not cr for one deviating group

	virtual UtilityTuplesSet get_utilities() const = 0;

	std::vector<HistoryChoice> compute_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far) const;

	std::vector<HistoryChoice> compute_cr_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far) const;

	std::vector<HistoryChoice> compute_pr_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<std::string>& strategy_vector) const;

	void reset_violation_cr() const;

	std::vector<bool> store_violation_cr() const;

	void restore_violation_cr(std::vector<bool> &violation) const;

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

	virtual UtilityTuplesSet get_utilities() const {return {utilities}; }

	// utilities for each player: NB in lexicographic order of players!
	std::vector<Utility> utilities;

	mutable uint64_t problematic_group;

	void reset_reason() const {
		::new (&reason) z3::Bool();
	}

	void restore_problematic_group(uint64_t problematic_group, Node &reset_node, bool below_problematic) const {
		/*after the first case of a case split, reset the problematic group and reset point (reset node) in the tree to pre-case splitting settings
		to ensure correct computation
		after reset_node every node has to be set to problematic group, also all the parent nodes of reset_node
		all the others have to be set to problematic group + 1*/
		
		bool new_below_problematic = below_problematic;
		if (reset_node.is_leaf()){
			if (this == &reset_node.leaf()){
				new_below_problematic = true;
			}
		}
		
		if (new_below_problematic){
			this->problematic_group = problematic_group;
		} else {
			this->problematic_group = problematic_group + 1;
		}

	}

	void reset_problematic_group() const {
		problematic_group = 0;
	}
};

// branch node
struct Branch final : public Node {
	Branch(unsigned player) : player(player) {}

	virtual bool is_leaf() const { return false; }

	virtual UtilityTuplesSet get_utilities() const {return practical_utilities; }

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

	mutable uint64_t problematic_group;
	mutable UtilityTuplesSet practical_utilities;

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

	void reset_problematic_group() const {
		problematic_group = 0;
		for(auto &choice: choices)
			if(!choice.node->is_leaf()) {
				choice.node->branch().reset_problematic_group();
			} else {
				choice.node->leaf().reset_problematic_group();
			}
	}

	void reset_practical_utilities() const {
		practical_utilities = {};
		for (auto& choice: choices){
			if (!choice.node->is_leaf()){
				choice.node->branch().reset_practical_utilities();
			}
		}
	}


	void restore_problematic_group(uint64_t problematic_group, Node &reset_node, bool below_problematic) const {
		/*after the first case of a case split, reset the problematic group and reset point (reset node) in the tree to pre-case splitting settings
		to ensure correct computation
		after reset_node every node has to be set to problematic group, also all the parent nodes of reset_node
		all the others have to be set to problematic group + 1*/
		


		// above problematic is considered
		// below problematic is considered
		bool new_below_problematic = below_problematic;
		if (!reset_node.is_leaf()){
			if (this == &reset_node.branch()){
				new_below_problematic = true;
			}
		}

		bool above_prob = false;
		for (auto &choice : choices){
			auto &child_node = choice.node;
			if (child_node->is_leaf()){
				child_node->leaf().restore_problematic_group(problematic_group, reset_node, new_below_problematic);
				if (child_node->branch().problematic_group == problematic_group) {
					above_prob = true;
				}

			} else {
				child_node->branch().restore_problematic_group(problematic_group, reset_node, new_below_problematic);
				if (child_node->branch().problematic_group == problematic_group) {
					above_prob = true;
				}
			}
		}
		if (above_prob || new_below_problematic){
			problematic_group = problematic_group;
		} else {
			problematic_group = problematic_group + 1;
		}

		}

	// void reset_strategy_pr() const {
	// 	pr_strategies_cases = {};
	// 	pr_strategies_actions = {};
	// 	for(auto &choice: choices)
	// 		if(!choice.node->is_leaf())
	// 			choice.node->branch().reset_strategy();
	// }



	// void print_strategy(const Input &input) const {
	// 	std::vector<std::string> actions_so_far;
	// 	std::cout << std::endl;
	// 	std::cout << "Strategy:" << std::endl;
	// 	const Node *current = this;
	// 	print_strategy_rec(current, input, {});	
	// 	std::cout << "\tPlayers can choose the rest of the actions arbitrarily." << std::endl;	
	// }

	// void print_strategy_rec(const Node *current, const Input &input, std::vector<std::string> actions_so_far) const {
	// 	if(current->is_leaf()) 
	// 		return;

	// 	if(!current->branch().strategy.empty()) {
	// 		std::cout
	// 				<< "\tPlayer "
	// 				<< input.players[current->branch().player]
	// 				<< " takes action "
	// 				<< current->branch().strategy
	// 				<< " after history "
	// 				<< actions_so_far
	// 				<< std::endl;
	// 	}

	// 	for (const Choice &choice: current->branch().choices) {
	// 		std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
	// 		updated_actions.push_back(choice.action);
	// 		print_strategy_rec(choice.node.get(), input, updated_actions);
	// 	}
	// }

	// void print_strategy_pr(const Input &input, std::vector<z3::Bool> &current_case) const {
	// 	std::vector<std::string> actions_so_far;
	// 	const Node *current = this;

	// 	std::cout << "Printing strategy for case " << current_case << "..." << std::endl;
		
	// 	//std::cout << "...................." << std::endl;
	// 	//std::cout << current->branch().pr_strategies_cases << std::endl;
	// 	//std::cout << "....Actions................" << std::endl;
	// 	//std::cout << current->branch().pr_strategies_actions << std::endl;
	// 	//std::cout << "...................." << std::endl;
		
		
	// 	print_strategy_pr_rec(current, input, {}, current_case);	

	// 	std::cout << std::endl;
	// 	std::cout << std::endl;

	// }

	// void print_strategy_pr_rec(const Node *current, const Input &input, std::vector<std::string> actions_so_far, std::vector<z3::Bool> &current_case) const {
	// 	if(current->is_leaf()) 
	// 		return;

	// 	if(!current->branch().pr_strategies_cases.empty()) {

	// 		for (unsigned i = 0; i < current->branch().pr_strategies_cases.size(); i++) {
	// 			if(are_compatible_cases(current->branch().pr_strategies_cases[i], current_case)) {
	// 				std::cout
	// 				<< "\tPlayer "
	// 				<< input.players[current->branch().player]
	// 				<< " takes action "
	// 				<< current->branch().pr_strategies_actions[i]
	// 				<< " after history "
	// 				<< actions_so_far
	// 				<< std::endl;
	// 				break;
	// 			}
	// 		}			
	// 	}

	// 	for (const Choice &choice: current->branch().choices) {
	// 		std::vector<std::string> updated_actions(actions_so_far.begin(), actions_so_far.end());
	// 		updated_actions.push_back(choice.action);
	// 		print_strategy_pr_rec(choice.node.get(), input, updated_actions, current_case);
	// 	}
	// }

};




// an action available at a branch
struct Action {
	// the name of the action
	std::string name;

	friend std::ostream &operator<<(std::ostream &out, const Action &action) {
		return out << action.name;
	}
};

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

	mutable std::vector<std::vector<z3::Bool>> unsat_cases;

	mutable std::vector<StrategyCase> strategies;

	mutable bool stop_log;

	mutable Node *reset_point;

	// root: NB must be a branch
	std::unique_ptr<Branch> root;

	// maximum number of players currently supported
	// no reason there couldn't be more, but convenient for implementation (cf collusion resilience)
	static const size_t MAX_PLAYERS = 64;

	void set_reset_point(const Node &node) const {
		Node* tmp = const_cast<Node *>(&node);
		reset_point = tmp;
	}

	void reset_reset_point() const {
		reset_point = root.get();
	}

	void reset_unsat_cases() const {
		unsat_cases.clear();
	}

	void stop_logging() const {
		stop_log = true;
	}

	void reset_logging() const {
		stop_log = false;
	}

	void reset_strategies() const {
		strategies = {};
	}

	void reset_practical_utilities() const {
		root.get()->reset_practical_utilities();
	}

	void compute_strategy_case(std::vector<z3::Bool> _case, PropertyType property) const {
		StrategyCase new_strat_case;

		new_strat_case._case = _case;
		if (property == PropertyType::Practicality){
			std::vector<std::string> strategy_vector;
			assert(root.get()->practical_utilities.size()==1);
			for (const auto& pr_utility: root.get()->practical_utilities){
				strategy_vector = pr_utility.strategy_vector;
			}
			new_strat_case.strategy = root.get()->compute_pr_strategy(players, {}, strategy_vector);
		} else if (property == PropertyType::CollusionResilience) {
			new_strat_case.strategy = root.get()->compute_cr_strategy(players, {});
		} else {
			new_strat_case.strategy = root.get()->compute_strategy(players, {});
		}

		strategies.push_back(new_strat_case);
	}

	void print_strategies(bool is_wi) const {
		std::cout << std::endl;
		for (StrategyCase strategy_case : strategies){
			std::cout << "Strategy for case: " <<  strategy_case._case << std::endl;
			for (HistoryChoice hist_choice : strategy_case.strategy){
				std::cout
					<< "\tPlayer "
					<< hist_choice.player
					<< " takes action "
					<< hist_choice.choice
					<< " after history "
					<< hist_choice.history
					<< std::endl;
			}
			if (is_wi){
				std::cout << "\tPlayers can choose the rest of the actions arbitrarily." << std::endl;	
			}
		}
	}

	void add_unsat_case(std::vector<z3::Bool> _case) const {
		unsat_cases.push_back(_case);
	}

	std::vector<std::vector<z3::Bool>> precondition_simplify() const {

		std::vector<std::vector<z3::Bool>> simp;
		for (const std::vector<z3::Bool> &case_: unsat_cases) {
			std::vector<z3::Bool> copy;
			for (const z3::Bool &atom: case_) {
				copy.push_back(atom);
			}
			simp.push_back(copy);
		}
		bool any_rule1 = true;
		bool any_rule2 = true;
		while (any_rule1 || any_rule2) {
			any_rule1 = false;
			any_rule2 = false;
			for (long unsigned int j = 0; j < simp.size(); j++) {
				auto case_ = simp[j];
				for (long unsigned int k = j + 1; k < simp.size(); k++) {
					auto other_case = simp[k];
					bool rule1 = true;
					bool rule2 = false;
					if (case_.size() == other_case.size()) {
						bool one_inverse = false;
						long unsigned int inverse;
						for (long unsigned int i = 0; i < case_.size(); i++) {
							if (case_[i].is_equal(other_case[i].invert()) && not one_inverse) {
								one_inverse = true;
								inverse = i;
							} else if (case_[i].is_equal(other_case[i].invert()) && one_inverse) {
								rule1 = false;
								break;
							} else if (not case_[i].is_equal(other_case[i])) {
								rule1 = false;
								break;
							}
						}
						rule1 = rule1 && one_inverse;
						if (rule1) {
							// remove other_case
							std::swap(simp[k], simp.back());
							simp.pop_back();
							// remove case_[i] from case_
							std::swap(case_[inverse], case_.back());
							case_.pop_back();
							simp[j] = case_;
							any_rule1 = true;
							break;
						}
					} else {
						rule1 = false;
					}
					if ((case_.size() == 1) | (other_case.size() == 1)) {
						// continue
						std::vector<z3::Bool> singleton;
						std::vector<z3::Bool> other;
						int which_singleton;
						if (case_.size() == 1) {
							singleton = case_;
							other = other_case;
							which_singleton = 0;
						} else {
							singleton = other_case;
							other = case_;
							which_singleton = 1;
						}
						int inverse;
						for (long unsigned int l = 0; l < other.size(); l++) {
							z3::Bool other_bool = other[l].invert();
							z3::Bool this_bool = singleton[0];
							bool the_hell = this_bool.is_equal(other_bool);
							if (the_hell) {
								rule2 = true;
								inverse = l;
							}
						}
						if (rule2) {
							std::swap(other[inverse], other.back());
							other.pop_back();
							if (which_singleton == 0) {
								simp[k] = other;
							} else {
								simp[j] = other;
							}
							any_rule2 = true;
						}

					} else {
						rule2 = false;
					}

				}
			}
		}

		return simp;
	}
};



inline const Leaf &Node::leaf() const {
	return *static_cast<const Leaf *>(this);
}

inline const Branch &Node::branch() const {
	return *static_cast<const Branch *>(this);
}

#endif
