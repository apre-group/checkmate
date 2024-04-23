#include <iostream>
#include <bitset>
#include <cassert>
#include <algorithm>
#include <unordered_set>
#include <bits/stdc++.h> 

#include "input.hpp"
#include "options.hpp"
#include "z3++.hpp"
#include "utils.hpp"

using z3::Bool;
using z3::Solver;

bool weak_immunity_rec(z3::Solver *solver, Node *node, unsigned player) {

	if (node->is_leaf()) {
		const auto &leaf = node->leaf();
		// known utility for us
		auto utility = leaf.utilities[player];
		auto condition = utility.operator>=({z3::Real::ZERO, z3::Real::ZERO});

		// std::cout << "condition " << condition << " for player " << player << std::endl;

		std::vector<Bool> assumptions;
		assumptions.push_back(!condition);
		if (solver->solve(assumptions) == z3::Result::UNSAT) {
			return true;
		}
		
		std::vector<Bool> assumptions2;
		assumptions2.push_back(condition);
		if (solver->solve(assumptions2) == z3::Result::UNSAT) {
			return false;
		}

		// todo set reason
		return false;
	}

	const auto &branch = node->branch();
	// else we deal with a branch
	if (player == branch.player) { 
		// player behaves honestly
		if (branch.honest) {
			// if we are along the honest history, we want to take an honest strategy
			auto &honest_choice = branch.get_honest_child();
			auto *subtree = honest_choice.node.get();

			// to do: set chosen action i.e. startegy for this note to be honest_choice->action
			// for this we need to add a property strategy to our nodes

			// the honest choice must be weak immune
			if (weak_immunity_rec(solver, subtree, player)) {
				return true;
			} 
			
			return false;
		}
		// otherwise we can take any strategy we please as long as it's weak immune
		for (const Choice &choice: branch.choices) {
			if (weak_immunity_rec(solver, choice.node.get(), player)) {
				return true;
			}			
		}
		return false;
	} else {
		// if we are not the honest player, we could do anything,
		// so all branches should be weak immune for the player
		for (const Choice &choice: branch.choices) {
			if (!weak_immunity_rec(solver, choice.node.get(), player)) {
				return false;
			}
		}
		return true;
	}

} 

 void weak_immunity(const Options &options, const Input &input) {

	std::cout << std::endl;
	std::cout << std::endl;
	std::cout << "WEAK IMMUNITY" << std::endl;

	// property is the same for all honest histories
	auto property_constraint = input.weak_immunity_constraint;

	Solver solver;
	solver.assert_(input.initial_constraint);
	// std::cout << "initial constraint(s) " << input.initial_constraint << std::endl;
	solver.assert_(property_constraint);
	// std::cout << "property constraint(s) " << property_constraint << std::endl;

	for (size_t history = 0; history < input.honest.size(); history++) {
		std::cout << std::endl;
		std::cout << "Is history " << input.honest[history] << " weak immune?" << std::endl;

		input.root.get()->reset_honest();
		input.root.get()->reset_reason();
		input.root.get()->mark_honest(input.honest[history]);	

		bool wi = true;	

		for (size_t player = 0; player < input.players.size(); player++) {
			// make a fresh frame for current player
			solver.push();
			bool weak_immune_for_player = weak_immunity_rec(&solver, input.root.get(), player);
			solver.pop();
			if (!weak_immune_for_player) {
				std::cout << "NO, it is not weak immune (or case splits needed !)." << std::endl;
				wi = false;
				break;
			}
		}

		if (wi)
			std::cout << "YES, it is weak immune." << std::endl;

	}
}

const Leaf& get_honest_leaf(Node *node, const std::vector<std::string> &history, int index) {
    if (node->is_leaf()) {
        return node->leaf();
    }
	int next_index = index + 1;
	return get_honest_leaf(node->branch().get_choice(history[index]).node.get(), history, next_index);
}

bool collusion_resilience_rec(z3::Solver *solver, Node *node, std::bitset<Input::MAX_PLAYERS> group, Utility honest_total, unsigned players) {
	
	if (node->is_leaf()) {

		// compute the total utility for the player group...
		Utility group_utility{z3::Real::ZERO, z3::Real::ZERO};
		const auto &leaf = node->leaf();
		for (size_t player = 0; player < players; player++)
			if (group[player])
				group_utility = group_utility + leaf.utilities[player];

		// ..and compare it to the honest total
		auto condition = group_utility.operator<=(honest_total);
		
		std::vector<Bool> assumptions;
		assumptions.push_back(!condition);
		if (solver->solve(assumptions) == z3::Result::UNSAT) {
			return true;
		}
		
		std::vector<Bool> assumptions2;
		assumptions2.push_back(condition);
		if (solver->solve(assumptions2) == z3::Result::UNSAT) {
			return false;
		}

		// todo set reason
		return false;
	}

	const auto &branch = node->branch();
	// else we deal with a branch
	if (!group[branch.player]) { 
		// player behaves honestly
		if (branch.honest) {
			// if we are along the honest history, we want to take an honest strategy
			auto &honest_choice = branch.get_honest_child();
			auto *subtree = honest_choice.node.get();

			// to do: set chosen action i.e. startegy for this note to be honest_choise->action
			// for this we need to add a property strategy to our nodes

			// the honest choice must be weak immune
			if (collusion_resilience_rec(solver, subtree, group, honest_total, players)) {
				return true;
			} 
			
			return false;
		}
		// otherwise we can take any strategy we please as long as it's weak immune
		for (const Choice &choice: branch.choices) {
			if (collusion_resilience_rec(solver, choice.node.get(), group, honest_total, players)) {
				return true;
			}			
		}
		return false;
	} else {
		// if we are not the honest player, we could do anything,
		// so all branches should be weak immune for the player
		for (const Choice &choice: branch.choices) {
			if (!collusion_resilience_rec(solver, choice.node.get(), group, honest_total, players)) {
				return false;
			}
		}
		return true;
	}
}

void collusion_resilience(const Options &options, const Input &input) {

	std::cout << std::endl;
	std::cout << std::endl;
	std::cout << "COLLUSION RESILIENCE" << std::endl;
	assert(input.players.size() < Input::MAX_PLAYERS);

	// property is the same for all honest histories
	auto property_constraint = input.collusion_resilience_constraint;

	Solver solver;
	solver.assert_(input.initial_constraint);
	// std::cout << "initial constraint(s) " << input.initial_constraint << std::endl;
	solver.assert_(property_constraint);
	// std::cout << "property constraint(s) " << property_constraint << std::endl;

	for (size_t history = 0; history < input.honest.size(); history++) {
		std::cout << std::endl;
		std::cout << "Is history " << input.honest[history] << " collusion resilient?" << std::endl;
		input.root.get()->reset_honest();
		input.root.get()->reset_reason();
		input.root.get()->mark_honest(input.honest[history]);	

		// lookup the leaf for this history
		const Leaf &honest_leaf = get_honest_leaf(input.root.get(), input.honest[history], 0);

		bool cr = true;

		// sneaky hack follows: all possible subgroups of n players can be implemented by counting through from 1 to (2^n - 2)
		// done this way more for concision than efficiency
		for (uint64_t binary_counter = 1; binary_counter < -1ull >> (64 - input.players.size()); binary_counter++) {
			std::bitset<Input::MAX_PLAYERS> group = binary_counter;
			Utility honest_total{z3::Real::ZERO, z3::Real::ZERO};
			// compute the honest total for the current group
			for (size_t player = 0; player < input.players.size(); player++)
				if (group[player])
					honest_total = honest_total + honest_leaf.utilities[player];

			// make a fresh frame for current group
			solver.push();
			bool collusion_resilient_for_group = collusion_resilience_rec(&solver, input.root.get(), group, honest_total, input.players.size());
			solver.pop();
			if (!collusion_resilient_for_group) {
				std::cout << "NO, it is not collusion resilient (or case splits needed !)." << std::endl;
				cr = false;
				break;
			}
		
		}

		if (cr)
			std::cout << "YES, it is collusion resilient." << std::endl;

	}

}

bool utility_tuples_eq(std::vector<Utility> tuple1, std::vector<Utility> tuple2) {
	
	if(tuple1.size() != tuple2.size()) {
		return false;
	} else {
		bool all_same = true;
		for (size_t i = 0; i < tuple1.size(); i++) {
			if (!tuple1[i].is(tuple2[i])) {
				all_same = false;
			}
		}
		return all_same;
	}
	return false;

}

std::unordered_set<std::vector<Utility>, std::hash<std::vector<Utility>>> practicality_rec(z3::Solver *solver, Node *node) {
	  if (node->is_leaf()) {
		// return the utility tuple of the leaf as a set (of one element)
		const Leaf &leaf = node->leaf();
		const std::vector<Utility> &utility_tuple = leaf.utilities;
		std::unordered_set<std::vector<Utility>, std::hash<std::vector<Utility>>> result;
		result.insert(utility_tuple);
		return result;
	}  

	// return std::unordered_set<std::vector<Utility>, std::hash<std::vector<Utility>>>();


 	const auto &branch = node->branch();
	// else we deal with a branch

	// get practical strategies and corresponding utilities recursively
	std::vector<std::unordered_set<std::vector<Utility>, std::hash<std::vector<Utility>>>> children;

	std::unordered_set<std::vector<Utility>, std::hash<std::vector<Utility>>> honest_utilities;


	for (const Choice &choice: branch.choices) {
		std::unordered_set<std::vector<Utility>, std::hash<std::vector<Utility>>> utilities = practicality_rec(solver, choice.node.get());

		// there is no practical child (propagate reason for case split, if any)
		if(utilities.empty()) {
			// TO do: set ´reason´
			// return empty set
			return std::unordered_set<std::vector<Utility>, std::hash<std::vector<Utility>>>(); 
		}

		if(choice.node.get()->honest) {
			honest_utilities = utilities;
		} else {
			children.push_back(utilities);
		}

	}


	if (branch.honest) {
		// if we are at an honest node, our strategy must be the honest strategy

		// to do: set chosen action i.e. startegy for this note to be honest_choice->action
		// for this we need to add a property strategy to our nodes
		
		assert(honest_utilities.size() == 1);
		// the utility at the leaf of the honest history
		std::vector<Utility> honest_utility = *honest_utilities.begin();
		// this should be maximal against other players, so...
		Utility maximum = honest_utility[branch.player];

		// for all other children
		for (const auto& utilities : children) {
			bool found = false;
			// does there exist a possible utility such that `maximum` is geq than it?
			 for (const auto& utility : utilities) {
				auto condition = maximum.operator<(utility[branch.player]);
				std::vector<Bool> assumptions;
				assumptions.push_back(condition);
				if (solver->solve(assumptions) == z3::Result::SAT) {
					std::vector<Bool> assumptions2;
					assumptions2.push_back(!condition);
					if (solver->solve(assumptions2) == z3::Result::SAT) {
						// might be maximal, just couldn't prove it
						// to do: set reason
					}
				} else {
					found = true;
				}
			}
			if (!found) {
				// return empty set
				return std::unordered_set<std::vector<Utility>, std::hash<std::vector<Utility>>>(); 
			}

		}

		// we return the maximal strategy 
		// honest choice is practical for current player
		return {honest_utility};

	} else {
		// not in the honest history
		// to do: we could do this more efficiently by working out the set of utilities for the player
		// but utilities can't be put in a set easily -> fix this here in the C++ version

		// compute the set of possible utilities by merging the set of children's utilities
		std::unordered_set<std::vector<Utility>, std::hash<std::vector<Utility>>> result;
		for (const auto& utilities : children) {
			for (const auto& utility : utilities) {
				result.insert(utility);
			}
		}

		// the set to drop
		std::unordered_set<std::vector<Utility>, std::hash<std::vector<Utility>>> remove;

		// work out whether to drop `candidate`
		for (const auto& candidate : result) {
			// this player's utility
			auto dominatee = candidate[branch.player];

			// check all other children
			// if any child has the property that all its utilities are bigger than `dominatee`
			// it can be dropped
			for (const auto& utilities : children) {
				// skip any where the cadidate is already contained

				// this logic can be factored out in an external function
				bool contained = false;
				for (const auto& utility : utilities) {
					if (utility_tuples_eq(utility, candidate)) {
						contained = true;
						break;
					}
				}

				if (contained) {
					continue;
				}

				// *all* utilities have to be bigger
				bool dominated = true;

				for (const auto& utility : utilities) {

					auto dominator = utility[branch.player];
					auto condition = dominator.operator<=(dominatee);
					std::vector<Bool> assumptions;
					assumptions.push_back(condition);
					if (solver->solve(assumptions) == z3::Result::SAT) {
						dominated = false;
						std::vector<Bool> assumptions2;
						assumptions2.push_back(!condition);
						if (solver->solve(assumptions2) == z3::Result::SAT) {
							// might be dominated, but can't prove it
							// todo: set reason
							// return empty set
							return std::unordered_set<std::vector<Utility>, std::hash<std::vector<Utility>>>(); 
						}

					}

				}  

				if (dominated) {
					remove.insert(candidate);
					break;
				}
			}

		}

		// result is all children's utilities inductively, minus those dropped
		std::unordered_set<std::vector<Utility>, std::hash<std::vector<Utility>>> difference_set;
		for(const auto& utility_tuple : result) {
			if(remove.find(utility_tuple) == remove.end()) {
				difference_set.insert(utility_tuple);
			}
		}

		return difference_set;

	} 

}

void practicality(const Options &options, const Input &input) {
	std::cout << std::endl;
	std::cout << std::endl;
	std::cout << "PRACTICALITY" << std::endl;

	// property is the same for all honest histories
	auto property_constraint = input.practicality_constraint;

	Solver solver;
	solver.assert_(input.initial_constraint);
	// std::cout << "initial constraint(s) " << input.initial_constraint << std::endl;
	solver.assert_(property_constraint);
	// std::cout << "property constraint(s) " << property_constraint << std::endl;

	for (size_t history = 0; history < input.honest.size(); history++) {
		std::cout << std::endl;
		std::cout << "Is history " << input.honest[history] << " practical?" << std::endl;
		input.root.get()->reset_honest();
		input.root.get()->reset_reason();
		input.root.get()->mark_honest(input.honest[history]);	

		solver.push();
		if(practicality_rec(&solver, input.root.get()).size() == 0) {
			std::cout << "NO, it is not practical (or case splits needed !)." << std::endl;
		} else {
			std::cout << "YES, it is practical." << std::endl;
		}
		
		solver.pop();

	}

}