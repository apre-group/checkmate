#ifndef __checkmate_input__
#define __checkmate_input__

#include <memory>
#include <string>
#include <unordered_map>

#include "utility.hpp"
#include "utils.hpp"
#include "z3++.hpp"
#include "options.hpp"

// forward declarations for Node methods
class Leaf;
class Subtree;
class Branch;
struct Choice;
class Node;

enum class NodeType {
    LEAF,
    BRANCH,
    SUBTREE
};

// reference to a utility tuple in a leaf
struct UtilityTuple {
	const std::vector<Utility> &leaf;
	mutable std::vector<std::string> strategy_vector;

	// GCC doesn't like copy-assign without explicit copy constructor
	UtilityTuple(const UtilityTuple &other) = default;

	// Anja's compiler doesn't want to generate this because leaf is a reference
	// Therefore: delegate to copy constructor via placement-new
	UtilityTuple &operator=(const UtilityTuple &other) {
		// need to destruct `this` now to deallocate `strategy_vector`
		this->~UtilityTuple();
		::new (this) UtilityTuple(other);
		return *this;
	}

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

struct CeChoice{
	std::string player;
	std::vector<std::string> choices;
	std::vector<std::string> history;
};

struct StrategyCase {
	std::vector<z3::Bool> _case;
	std::vector<HistoryChoice> strategy; 
};

struct CeCase {
	std::vector<z3::Bool> _case;
	std::vector<std::string> player_group;
	std::vector<CeChoice> counterexample; 
};

struct UtilityCase {
	std::vector<z3::Bool> _case;
	std::vector<std::vector<Utility>> utilities; 
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

class Node {
public:
	virtual NodeType type() const = 0;
	mutable bool checked_wi = false;
	mutable bool checked_weri = false;
	mutable bool checked_cr = false;
	mutable bool checked_pr = false;


	// convenience functions
	bool is_leaf() const { return type() == NodeType::LEAF; }
	bool is_branch() const { return type() == NodeType::BRANCH; }
	bool is_subtree() const { return type() == NodeType::SUBTREE; }

	// can default-construct and move Nodes...
	Node() = default;

	Node(Node &&) = default;

	Node &operator=(Node &&) = default;

	// ...but not copy them to avoid accidentally copying a whole tree
	Node(const Node &) = delete;

	Node &operator=(const Node &) = delete;

	virtual ~Node() {};

	// if is_leaf(), do the downcast
	const Leaf &leaf() const;

	// if is_subtree(), do the downcast
	const Subtree &subtree() const;

	// if !is_leaf() and !is_subtree(), do the downcast
	const Branch &branch() const;

	// are we (currently) along the honest history?
	mutable bool honest = false;

	// the reason that a check for a property failed:
	// null if didn't fail or no case split would help
	mutable z3::Bool reason;

	mutable std::vector<bool> violates_cr; // set to true as soon as its not cr for one deviating group

	virtual UtilityTuplesSet get_utilities() const = 0;

	std::vector<HistoryChoice> compute_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far) const;

	std::vector<HistoryChoice> compute_cr_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<uint> deviating_players) const;

	std::vector<HistoryChoice> compute_pr_strategy(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<std::string>& strategy_vector) const;

	std::vector<CeChoice> compute_wi_ce(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<size_t> player_group) const;

	std::vector<CeChoice> compute_cr_ce(std::vector<std::string> players, std::vector<std::string> actions_so_far, std::vector<size_t> player_group) const;

	CeCase compute_pr_cecase(std::vector<std::string> players, unsigned current_player, std::vector<std::string> actions_so_far, std::string current_action, UtilityTuplesSet practical_utilities) const;

	std::vector<CeChoice> compute_pr_ce(std::string current_action, std::vector<std::string> actions_so_far, UtilityTuplesSet practical_utilities) const;

	const Node* compute_deviation_node(std::vector<std::string> actions_so_far) const;

	std::vector<std::string> strat2hist(std::vector<std::string> &strategy) const;

	void prune_actions_from_strategy(std::vector<std::string> &strategy) const;
	
	void reset_violation_cr() const;

	std::vector<std::vector<bool>> store_violation_cr() const;

	bool cr_against_all() const;

	bool cr_against_supergroups_of(std::vector<uint> deviating_players) const;

	void restore_violation_cr(std::vector<std::vector<bool>> &violation) const;

	void add_violation_cr() const;

	void reset_count_check(bool wi, bool weri, bool cr, bool pr) const;

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

struct SubtreeResult {
	std::vector<std::string> player_group;
	std::vector<std::vector<z3::Bool>> satisfied_in_case;
};

struct PracticalitySubtreeResult {
	std::vector<z3::Bool> _case;
	std::vector<std::vector<Utility>> utilities;
};


// subtree node
class Subtree : public Node {

	public:
	mutable uint64_t problematic_group = 0;
	mutable std::vector<std::vector<Utility>> utilities;

	NodeType type() const override { return NodeType::SUBTREE; }

	std::vector<SubtreeResult> weak_immunity; // each player occurs exactly once in vector
	std::vector<SubtreeResult> weaker_immunity;
	std::vector<SubtreeResult> collusion_resilience;
	std::vector<PracticalitySubtreeResult> practicality;
	// honest utility needed in case the honest history ends in this subtree
	std::vector<Utility> honest_utility;

	Subtree(std::vector<SubtreeResult> _weak_immunity,
        std::vector<SubtreeResult> _weaker_immunity,
        std::vector<SubtreeResult> _collusion_resilience,
        std::vector<PracticalitySubtreeResult> _practicality,
        std::vector<Utility> _honest_utility)
    : weak_immunity(_weak_immunity),
      weaker_immunity(_weaker_immunity),
      collusion_resilience(_collusion_resilience),
      practicality(_practicality),
      honest_utility(_honest_utility) {}

	void reset_reason() const {
		::new (&reason) z3::Bool();
	}

	void reset_problematic_group(bool is_cr) const {
		problematic_group = is_cr ? 1 : 0;
	}

	virtual UtilityTuplesSet get_utilities() const override {
		
		UtilityTuplesSet result;

		for (const auto &utility_tuple: utilities){
			result.insert(result.end(), utility_tuple);
		}

		return result; 
	}

	void reset_practical_utilities() const {
		utilities = {};
	}
};


// leaf node
class Leaf final : public Node {

	public:
	// utilities for each player: NB in lexicographic order of players!
	std::vector<Utility> utilities;

	mutable uint64_t problematic_group;

	NodeType type() const override { return NodeType::LEAF; }

	virtual UtilityTuplesSet get_utilities() const override {return {utilities}; }

	void reset_reason() const {
		::new (&reason) z3::Bool();
	}

	void reset_problematic_group(bool is_cr) const {
		problematic_group = is_cr ? 1 : 0;
	}
};

// branch node
class Branch final : public Node {

	public:
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
	mutable std::vector<std::string> counterexample_choices;

	NodeType type() const override { return NodeType::BRANCH; }

	Branch(unsigned player) : player(player), counterexample_choices({}) {}

	virtual UtilityTuplesSet get_utilities() const override {return practical_utilities;}

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

	void reset_counterexample_choices() const {
		counterexample_choices = {};
		for (auto& choice: choices) {
			if (!choice.node->is_leaf() && !choice.node->is_subtree()) {
				choice.node->branch().reset_counterexample_choices();
			}
		}
	}

	std::vector<z3::Bool> store_reason() const {

		std::vector<z3::Bool> reason_vector = {reason};

		for (const auto& child: choices){
			if (!child.node->is_leaf() && !child.node->is_subtree()){
				std::vector<z3::Bool> child_reason = child.node->branch().store_reason();
				reason_vector.insert(reason_vector.end(), child_reason.begin(), child_reason.end());
			} else if (child.node->is_leaf()){
				reason_vector.push_back(child.node->leaf().reason);
			} else {
				reason_vector.push_back(child.node->subtree().reason);
			}
		}

		return reason_vector;
	}

	void restore_reason(std::vector<z3::Bool> &reasons) const {

		if (reasons.size() == 0) {
			return;
		}
		reason = reasons[0];
		reasons.erase(reasons.begin());

		for (const auto& child: this->branch().choices){
			if (!child.node->is_leaf() && !child.node->is_subtree()){
			child.node->branch().restore_reason(reasons);
			} else if (child.node->is_leaf()) {
				if (reasons.size() == 0) {
					return;
				}
				child.node->leaf().reason = reasons[0];
				reasons.erase(reasons.begin());
			} else {
				if (reasons.size() == 0) {
					return;
				}
				child.node->subtree().reason = reasons[0];
				reasons.erase(reasons.begin());
			}
		}

		return;
	}

	std::vector<uint64_t> store_problematic_groups() const {

		std::vector<uint64_t> problematic_groups_vector = {problematic_group};

		for (const auto& child: choices){
			if(child.node->is_leaf()) {
				problematic_groups_vector.push_back(child.node->leaf().problematic_group);
			}
			else if (child.node->is_subtree()){
				problematic_groups_vector.push_back(child.node->subtree().problematic_group);
			}
			else {
				std::vector<uint64_t> child_pg = child.node->branch().store_problematic_groups();
				problematic_groups_vector.insert(problematic_groups_vector.end(), child_pg.begin(), child_pg.end());
			}
		}

		return problematic_groups_vector;
	}

	void restore_problematic_groups(std::vector<uint64_t> &pg) const {

		if (pg.size() == 0) {
			return;
		}
		problematic_group = pg[0];
		pg.erase(pg.begin());

		for (const auto& child: this->branch().choices){
			if(child.node->is_leaf()){
				child.node->leaf().problematic_group = pg[0];
				pg.erase(pg.begin());
			}
			else if (child.node->is_subtree()) {
				child.node->subtree().problematic_group = pg[0];
				pg.erase(pg.begin());
			}
			else {
				child.node->branch().restore_problematic_groups(pg);
			}
		}

		return;
	}

	std::vector<std::vector<std::string>> store_counterexample_choices() const {

		std::vector<std::vector<std::string>> counterexample_choices_vector = {counterexample_choices};

		for (const auto& child: choices){
			if (!child.node->is_leaf() && !child.node->is_subtree()){
				std::vector<std::vector<std::string>> child_ces = child.node->branch().store_counterexample_choices();
				counterexample_choices_vector.insert(counterexample_choices_vector.end(), child_ces.begin(), child_ces.end());
			}
		}

		return counterexample_choices_vector;
	}

	void restore_counterexample_choices(std::vector<std::vector<std::string>> &ces) const {

		if (ces.size() == 0) {
			return;
		}
		counterexample_choices = ces[0];
		ces.erase(ces.begin());

		for (const auto& child: this->branch().choices){
			if (!child.node->is_leaf() && !child.node->is_subtree()){
			child.node->branch().restore_counterexample_choices(ces);
			}
		}

		return;
	}


	void mark_honest(const std::vector<std::string> &history) const {
		assert(!honest);

		honest = true;
		const Node *current = this;
		unsigned index = 0;
		do {
			current = current->branch().get_choice(history[index++]).node.get();
			current->honest = true;
		} while(!current->is_leaf() && !current->is_subtree());
	}

	void reset_honest() const {
		if(!honest)
			return;

		honest = false;
		const Node *current = this;
		do {
			current = current->branch().get_honest_child().node.get();
			current->honest = false;
		} while(!current->is_leaf() && !current->is_subtree());
	}

	void reset_reason() const {
		::new (&reason) z3::Bool();
		for(auto &choice: choices)
			if(!choice.node->is_leaf() && !choice.node->is_subtree()){
				choice.node->branch().reset_reason();
			}
			else if (choice.node->is_leaf()) {
				choice.node->leaf().reset_reason();
			} else {
				choice.node->subtree().reset_reason();
			}
	}

	void reset_strategy() const {
		strategy.clear();
		for(auto &choice: choices)
			if(!choice.node->is_leaf() && !choice.node->is_subtree())
				choice.node->branch().reset_strategy();
	}

	void reset_problematic_group(bool is_cr) const {
		problematic_group = is_cr ? 1 : 0;
		for(auto &choice: choices)
			if(!choice.node->is_leaf() && !choice.node->is_subtree()) {
				choice.node->branch().reset_problematic_group(is_cr);
			} else if (choice.node->is_leaf()){
				choice.node->leaf().reset_problematic_group(is_cr);
			} else {
				choice.node->subtree().reset_problematic_group(is_cr);
			}
	}

	void reset_practical_utilities() const {
		practical_utilities = {};
		for (auto& choice: choices){
			if (!choice.node->is_leaf()){
				if (!choice.node->is_subtree()){
					choice.node->branch().reset_practical_utilities();
				} else {
					choice.node->subtree().reset_practical_utilities();
				}
			}
		}
	}

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
	Input(const char *path, bool supertree);

	// list of players in alphabetical order
	std::vector<std::string> players;
	// list of honest histories
	std::vector<std::vector<std::string>> honest;
	// list of honest utilities - for the subtree option
	std::vector<UtilityTuple> honest_utilities;

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

	mutable std::vector<CeCase> counterexamples;

	mutable bool stop_log;

	mutable Node *reset_point;

	mutable std::vector<bool> solved_for_group;

	mutable std::vector<UtilityCase> utilities_pr_nohistory;

	// root: NB must be a branch
	std::unique_ptr<Branch> root;

	// maximum number of players currently supported
	// no reason there couldn't be more, but convenient for implementation (cf collusion resilience)
	static const size_t MAX_PLAYERS = 64;

	void reset_solved_for() const {
		solved_for_group = {};
	}

	void init_solved_for_group(size_t number_groups) const {
		solved_for_group = {};
		for ( uint i = 0; i< number_groups; i++) {
			solved_for_group.push_back(false);
		}
		
	}

	std::vector<bool> store_solved_for() const {

		std::vector<bool> result;
		result.insert(result.begin(), solved_for_group.begin(), solved_for_group.end());

		return result;
	}

	void restore_solved_for(std::vector<bool> storage) const {
		solved_for_group = storage;
	}

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

	void reset_counterexamples() const {
		counterexamples = {};
	}

	void reset_practical_utilities() const {
		root.get()->reset_practical_utilities();
	}

	void compute_strategy_case(std::vector<z3::Bool> _case, PropertyType property) const {
		
		if (property == PropertyType::Practicality){
			if(root.get()->branch().honest) {
				// the honest one has to be the practical one
				// otw (if we call a subtree in default mode to obtain the strategies)
				//  there can be more than one pr strategy if the subtree is not along the 
				//  honest history 
				assert(root.get()->practical_utilities.size()==1);
			}
			for (const auto& pr_utility: root.get()->practical_utilities){
				StrategyCase new_strat_case;
				new_strat_case._case = _case;
				std::vector<std::string> strategy_vector;
				strategy_vector.insert(strategy_vector.begin(), pr_utility.strategy_vector.begin(), pr_utility.strategy_vector.end()); 
				new_strat_case.strategy = root.get()->compute_pr_strategy(players, {}, strategy_vector);
				strategies.push_back(new_strat_case);
			}

		} else {

			StrategyCase new_strat_case;
			new_strat_case._case = _case;

			if (property == PropertyType::CollusionResilience) {
				new_strat_case.strategy = root.get()->compute_cr_strategy(players, {}, {});
			} else {
				new_strat_case.strategy = root.get()->compute_strategy(players, {});
			}

			strategies.push_back(new_strat_case);

		}
	}

	void print_strategies(const Options &options, bool is_wi) const {
		std::cout << std::endl;
		for (StrategyCase strategy_case : strategies) {
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
			if (is_wi) {
				std::cout << "\tPlayers can choose the rest of the actions arbitrarily." << std::endl;	
			}
			if(options.supertree) {
				std::cout << "\tYou need to run subtrees in default mode with option strategies for complete strategies." << std::endl;
			}
		}
	}

	void compute_cecase(std::vector<size_t> player_group, PropertyType property) const {
		CeCase new_ce_case;

		new_ce_case._case = {};
		for (auto player : player_group) {
			new_ce_case.player_group.push_back(players[player]);
		}
		
		if (property == PropertyType::WeakImmunity || property == PropertyType::WeakerImmunity) {
			new_ce_case.counterexample = root.get()->compute_wi_ce(players, {}, player_group);
		} else if (property == PropertyType::CollusionResilience) {
			new_ce_case.counterexample = root.get()->compute_cr_ce(players, {}, player_group);
		}

		counterexamples.push_back(new_ce_case);
	}

	void add_case2ce(std::vector<z3::Bool> _case) const {
		// the empty case has a counterexample -> no case splitting
		// case splitting -> the empty case has no counterexample
		for (CeCase& ce: counterexamples){
			if (ce._case.size() == 0){
				ce._case = _case;
			}
		}
	}

	void print_counterexamples(const Options &options, bool is_wi, bool is_cr) const {
		int no_counterexamples = 0;
		if(is_wi || is_cr) {
			std::cout << std::endl;
			for (CeCase ce_case : counterexamples){
				no_counterexamples++;
				std::cout << "Counterexample for case: " <<  ce_case._case << std::endl;
				if(ce_case.counterexample.size() == 0) {
					if(is_wi) {
						if(options.supertree) {
							std::cout << "Player " << ce_case.player_group[0] << " is harmed, if they follow the honest history. Run subtree along honest history in default mode with option counterexamples." << std::endl;
						} else {
							std::cout << "Player " << ce_case.player_group[0] << " is harmed, if they follow the honest history." << std::endl;
						}
					}
					else if(is_cr) {
						if(options.supertree) {
							std::cout << "Group " << ce_case.player_group << " can deviate profitably. Run subtree along honest history in default mode with option counterexamples." << std::endl;
						} else {
							std::cout << "Group " << ce_case.player_group << " can deviate profitably." << std::endl;
						}
					}
				} else {
					if(is_wi){
						std::cout << "Player " << ce_case.player_group[0] << " can be harmed, if" << std::endl;
					}
					else if(is_cr){
						std::cout << "Group " << ce_case.player_group << " can deviate profitably, if" << std::endl;
					}
					for (CeChoice ce_choice : ce_case.counterexample){
						std::cout
							<< "\tPlayer "
							<< ce_choice.player
							<< " takes one of the actions "
							<< ce_choice.choices
							<< " after history "
							<< ce_choice.history
							<< std::endl;
					}
					if(options.supertree) {
						std::cout << "You might need to run subtrees in default mode with option counterexamples for complete counterexamples." << std::endl;
					}
				}
				
			}
		} else {
			for (CeCase ce_case : counterexamples){
				no_counterexamples++;
				if(ce_case.player_group.size() == 0) {
					if(options.supertree) {
						// user should check ce in subtree mode manually
						std::cout << "Counterexample for case: " <<  ce_case._case << std::endl;
						std::cout << "The subtree after history " << ce_case.counterexample[0].history << " is not practical. Run subtree in default mode with option counterexamples." << std::endl;
					} else {
						assert(!options.subtree);
						std::cout << "Practical histories that extend supertree counterexamples for case: " << ce_case._case <<  std::endl;
						for(auto history : ce_case.counterexample) {
							std::cout << history.choices << std::endl;	
						}
					}
				} else {
					std::cout << "Counterexample for case: " <<  ce_case._case << std::endl;
					std::cout << "For player " << ce_case.player_group[0] << " all practical histories after " << ce_case.counterexample[0].history <<" yield a better utility than the honest one." << std::endl;
					std::cout << "Practical histories:" << std::endl;
					for(auto history : ce_case.counterexample) {
						std::vector<std::string> history_to_print;
						history_to_print.insert(history_to_print.end(), ce_case.counterexample[0].history.begin(), ce_case.counterexample[0].history.end());
						history_to_print.insert(history_to_print.end(), history.choices.begin(), history.choices.end());
						std::cout << history_to_print << std::endl;	
					}
					if(options.supertree) {
						std::cout << "You might need to run subtrees in default mode with option counterexamples for complete counterexamples." << std::endl;
					}
				}
			}
		}

		std::cout << std::endl;
		std::cout << std::endl;
		std::cout << "----> Number of counterexamples found: " << no_counterexamples << std::endl;
		
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
					if ((case_.size() == 1) || (other_case.size() == 1)) {
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
	assert(is_leaf());
	return *static_cast<const Leaf *>(this);
}

inline const Subtree &Node::subtree() const {
	assert(is_subtree());
	return *static_cast<const Subtree *>(this);
}

inline const Branch &Node::branch() const {
	assert(!is_leaf() && !is_subtree());
	return *static_cast<const Branch *>(this);
}

#endif
