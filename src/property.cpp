#include <iostream>
#include <bitset>
#include <cassert>
#include <algorithm>
#include <unordered_set>
#include <bits/stdc++.h> 
#include <string>

#include "input.hpp"
#include "options.hpp"
#include "z3++.hpp"
#include "utils.hpp"

using z3::Bool;
using z3::Solver;

using UtilityTuple = std::vector<Utility>;
using UtilityTuplesSet = std::unordered_set<UtilityTuple, std::hash<UtilityTuple>>;

std::vector<PotentialCase> practicality_rec(z3::Solver *solver, const Options &options, Node *node, std::vector<z3::Bool> current_case);
bool practicality_admin(z3::Solver *solver, const Options &options, Node *root, std::vector<z3::Bool> current_case);
bool all_end_new(std::vector<uint> it, std::vector<std::vector<RemoveSetStruct>> children);

bool weak_immunity_rec(z3::Solver *solver, Node *node, unsigned player, bool weaker) {

	if (node->is_leaf()) {
		const auto &leaf = node->leaf();
		// known utility for us
		auto utility = leaf.utilities[player];

		z3::Bool condition = weaker ? utility.real >= z3::Real::ZERO : utility >= Utility {z3::Real::ZERO, z3::Real::ZERO};

		if (solver->solve({!condition}) == z3::Result::UNSAT) {
			return true;
		}
		
		if (solver->solve({condition}) == z3::Result::UNSAT) {
			return false;
		}

		leaf.reason = condition;
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
			if (weak_immunity_rec(solver, subtree, player, weaker)) {
				return true;
			} 

			branch.reason = subtree->reason;
			return false;
		}
		// otherwise we can take any strategy we please as long as it's weak immune
		for (const Choice &choice: branch.choices) {
			if (weak_immunity_rec(solver, choice.node.get(), player, weaker)) {
				return true;
			}
			if (!choice.node->reason.null()) {
				branch.reason = choice.node->reason;
			}		
		}
		return false;
	} else {
		// if we are not the honest player, we could do anything,
		// so all branches should be weak immune for the player
		for (const Choice &choice: branch.choices) {
			if (!weak_immunity_rec(solver, choice.node.get(), player, weaker)) {
				branch.reason = choice.node->reason;
				return false;
			}
		}
		return true;
	}

} 

const Leaf& get_honest_leaf(Node *node, const std::vector<std::string> &history, uint index) {
    if (node->is_leaf()) {
        return node->leaf();
    }
	uint next_index = index + 1;
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
		auto condition = group_utility <= honest_total;
		
		if (solver->solve({!condition}) == z3::Result::UNSAT) {
			return true;
		}

		if (solver->solve({condition}) == z3::Result::UNSAT) {
			return false;
		}

		leaf.reason = condition;
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

			// the honest choice must be collusion resilient
			if (collusion_resilience_rec(solver, subtree, group, honest_total, players)) {
				return true;
			} 
			
			branch.reason = subtree->reason;
			return false;
		}
		// otherwise we can take any strategy we please as long as it's collusion resilient
		for (const Choice &choice: branch.choices) {
			if (collusion_resilience_rec(solver, choice.node.get(), group, honest_total, players)) {
				return true;
			}	
			if (!choice.node->reason.null()) {
				branch.reason = choice.node->reason;
			}		
		}
		return false;
	} else {
		// if we are not the honest player, we could do anything,
		// so all branches should be collusion resilient for the player
		for (const Choice &choice: branch.choices) {
			if (!collusion_resilience_rec(solver, choice.node.get(), group, honest_total, players)) {
				branch.reason = choice.node->reason;
				return false;
			}
		}
		return true;
	}
}

bool utility_tuples_eq(UtilityTuple tuple1, UtilityTuple tuple2) {
	
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

/*z3::Bool getSplitForPracticality(Utility a, Utility b) {
	if (a.real == b.real) 
		return a.infinitesimal >= b.infinitesimal
	else 
		return a.real > b.real
}*/

std::vector<RemoveSetStruct> do_magic_combining(z3::Solver *solver, std::vector<std::vector<RemoveSetStruct>> remove_sets, std::vector<z3::Bool> current_case) {
	z3::Bool tr = z3::Bool().True();
	if(remove_sets.size() == 0) 
		return {{{}, tr}};

	std::cout << remove_sets.size() << std::endl; 
	for (std::vector<RemoveSetStruct> vrs : remove_sets){
		std::cout << "do magic remove set: " << vrs[0].remove_tuple << std::endl;
	}

	std::vector<uint> it(remove_sets.size(), 0);
	std::vector<RemoveSetStruct> remove_sets_combined;
	while (!all_end_new(it, remove_sets)) {
		std::cout<< "we will not see this" << std::endl;
		// compute case
		z3::Bool comb_case = remove_sets[0][it[0]].case_split;
		UtilityTuplesSet comb_remove = remove_sets[0][it[0]].remove_tuple;
		for (uint k = 1; k < remove_sets.size(); k++){
			comb_case = comb_case && remove_sets[k][it[k]].case_split;
			for(auto element : remove_sets[k][it[k]].remove_tuple) {
				comb_remove.insert(element);
			}
			
		}
		std::vector<z3::Bool> check_case(current_case.begin(), current_case.end());
		check_case.push_back(comb_case);

		if (solver->solve(check_case)!= z3::Result::UNSAT) {
			remove_sets_combined.push_back({comb_remove, comb_case});
			std::cout << "pushed back" << std::endl;
		}
		uint n = remove_sets.size() -1;
		while (n > 0 && it[n] == remove_sets[n].size()-1) {
			it[n] = 0;
			n--;
		}
		it[n]++;
	}
	// compute last case
	z3::Bool comb_case = remove_sets[0][it[0]].case_split;
	UtilityTuplesSet comb_remove = remove_sets[0][it[0]].remove_tuple;
	for (uint k = 1; k < remove_sets.size(); k++){
		comb_case = comb_case && remove_sets[k][it[k]].case_split;
		for(auto element : remove_sets[k][it[k]].remove_tuple) {
			comb_remove.insert(element);
		}
		
	}
	std::cout << "comb case, supposed to be true " << comb_case << std::endl;
	std::vector<z3::Bool> check_case(current_case.begin(), current_case.end());
	check_case.push_back(comb_case);

	if(solver->solve(current_case)== z3::Result::UNSAT){
		std::cout << "WTF" << std::endl;
	} 
	// CONTINUE HERE!!!

	if (solver->solve(check_case)!= z3::Result::UNSAT) {
		remove_sets_combined.push_back({comb_remove, comb_case});
		std::cout << "pushed back" << std::endl;
	}

	return remove_sets_combined;
}


std::vector<PotentialCase> practicality_reasoning(z3::Solver *solver, const Options &options, Node *node, std::vector<z3::Bool> current_case, std::vector<UtilityTuplesSet> children, UtilityTuplesSet honest_utilities) {
		// std::cout << "Pear0" << std::endl;
		const auto &branch = node->branch();
		
		
		if (branch.honest) {
			// std::cout << "along honest" << std::endl;
			// if we are at an honest node, our strategy must be the honest strategy

			// to do: set chosen action i.e. startegy for this note to be honest_choice->action
			// for this we need to add a property strategy to our nodes
			
			assert(honest_utilities.size() == 1);
			// the utility at the leaf of the honest history
			UtilityTuple honest_utility = *honest_utilities.begin();
			// this should be maximal against other players, so...
			Utility maximum = honest_utility[branch.player];

			// for all other children
			for (const auto& utilities : children) {
				bool found = false;
				// does there exist a possible utility such that `maximum` is geq than it?
				for (const auto& utility : utilities) {
					auto condition = maximum < utility[branch.player];
					if (solver->solve({condition}) == z3::Result::SAT) {
						if (solver->solve({!condition}) == z3::Result::SAT) {
							// might be maximal, just couldn't prove it
							branch.reason = !condition;
						}
					} 
					else {
						found = true;
						break;
					}
				}
				if (!found) {
					// return empty set if no reason set
					if (branch.reason.null()) {
						return {}; 
					} else {
						// call this function for reason and !reason
						z3::Bool split = branch.reason;
						std::cout << "Splitting on: " << split << std::endl;

						for (const z3::Bool& condition : {split, !split}) {
							branch.reset_reason();

							solver->push();

							solver->assert_(condition);
							assert (solver->solve() != z3::Result::UNSAT);
							std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
							new_current_case.push_back(condition);
							bool attempt = practicality_admin(solver, options, node, new_current_case);
							
							solver->pop();
							if (!attempt) 
								return {};
						}

					}
				}

			}

			// we return the maximal strategy 
			// honest choice is practical for current player
			z3::Bool tr = z3::Bool().True();
			PotentialCase pot_case = {{honest_utility}, tr};
			return {pot_case};

	} else {
		// std::cout << "not along honest" << std::endl;

		// put inner two loops into magic fct, generate either worst case 2**n or 2n remove sets and splits


		// not in the honest history
		// to do: we could do this more efficiently by working out the set of utilities for the player
		// but utilities can't be put in a set easily -> fix this here in the C++ version

		// compute the set of possible utilities by merging the set of children's utilities
		UtilityTuplesSet result;
		for (const auto& utilities : children) {
			for (const auto& utility : utilities) {
				result.insert(utility);
			}
		}

		std::vector<std::vector<RemoveSetStruct>> remove_sets; //one per candidate in result, each candidate can have 1 or 2 RemoveSetStructs
		

		// work out whether to drop `candidate`
		for (const auto& candidate : result) {
			// ABC
			std::vector<RemoveSetStruct> remove_sets_of_candate;

			// this player's utility
			auto dominatee = candidate[branch.player];
			::new (&branch.reason) z3::Bool(); 

			bool dominated = true;
			z3::Bool split;

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
				dominated = true;

				for (const auto& utility : utilities) {
					auto dominator = utility[branch.player];
					auto condition = dominator <= dominatee;
					if (solver->solve({condition}) == z3::Result::SAT) {
						dominated = false;
						if (solver->solve({!condition}) == z3::Result::SAT) {
							if(split.null()) {
								split = !condition;
							} else {
								split = split || !condition;
							}
						}
					}
				}  

				if (dominated) {
					// ABC add to remove_sets
					z3::Bool tr = z3::Bool().True();
					RemoveSetStruct remove_struct = {{candidate}, tr};
					remove_sets_of_candate.push_back(remove_struct);
					break;

				} 
			}

			if (!dominated && !split.null()) {
					// ABC add to remove_sets same as above
					RemoveSetStruct remove_struct = {{candidate}, split};
					remove_sets_of_candate.push_back(remove_struct);

					RemoveSetStruct remove_struct2 = {{}, !split};
					remove_sets_of_candate.push_back(remove_struct2);

			}

			if(remove_sets_of_candate.size() > 0) {
				remove_sets.push_back(remove_sets_of_candate);
			}

		
		}

		// ABC combine remove sets to obtain O(2**n) remove sets
		std::vector<RemoveSetStruct> remove_sets_combined = do_magic_combining(solver, remove_sets, current_case);
		// std::cout << "remove sets size: " << remove_sets_combined.size() << std::endl;
		// for (auto rs : remove_sets_combined){
		//  std::cout << "elements in remove set: " << rs.remove_tuple.size() << std::endl;
		// } 

		// ABC continue here :)
		std::vector<PotentialCase> ret_result;

		for(auto remove_set : remove_sets_combined) {
			UtilityTuplesSet rec_result(result.begin(), result.end());
			for (const auto& elem : remove_set.remove_tuple) {
				rec_result.erase(elem);
			}
			ret_result.push_back({rec_result, remove_set.case_split});

		}

		return ret_result;

	} 

}


bool all_end(std::vector<uint> it, std::vector<std::vector<PotentialCase>> children) {

	for (uint i = 0; i < it.size(); i++){
		if (it[i] != children[i].size()-1){
			return false;
		}
	}
	return true;
}

bool all_end_new(std::vector<uint> it, std::vector<std::vector<RemoveSetStruct>> children) {

	for (uint i = 0; i < it.size(); i++){
		if (it[i] != children[i].size()-1){
			return false;
		}	
	}
	return true;
}

std::vector<PotentialCase> practicality_rec(z3::Solver *solver, const Options &options, Node *node, std::vector<z3::Bool> current_case) {
	  //std::cout << "Kiwi0" << std::endl;
	  //std::cout << node->is_leaf() << std::endl;
	  if (node->is_leaf()) {
		// return the utility tuple of the leaf as a set (of one element)
		const Leaf &leaf = node->leaf();
		//std::cout << "Apple" << std::endl;
		z3::Bool tr = z3::Bool().True();
		//std::cout << "Red Apple" << std::endl;
		PotentialCase ret = {{leaf.utilities}, tr};
		std::vector<PotentialCase> v = {ret};
		//std::cout << "Kiwi" << std::endl;
		return v;
	}  
	//std::cout << "Kiwi1" << std::endl;

	

	// else we deal with a branch
 	const auto &branch = node->branch();

	// get practical strategies and corresponding utilities recursively
	std::vector<std::vector<PotentialCase>> children;

	UtilityTuplesSet honest_utilities;
	z3::Bool honest_case;

	//std::cout << "Kiwi2" << std::endl;

	for (const Choice &choice: branch.choices) {
		//std::cout << "Kiwi3" << std::endl;
		std::vector<PotentialCase> potential_cases = practicality_rec(solver, options, choice.node.get(), current_case);

		//std::cout << "Kiwi4" << std::endl;
		// this child has no practical strategy (propagate reason for case split, if any) 
		// std::cout << potential_cases.size() << std::endl;
		if(potential_cases.empty()) {
			//std::cout << "---->" + choice.action << std::endl; 
			branch.reason = choice.node->reason;
			assert(choice.node->honest);
			assert(choice.node->reason.null());
			// return empty set
			// std::cout << "Kiwi5" << std::endl;
			return {};
		}
		

		if(choice.node->honest) {
			honest_utilities = potential_cases[0].utilities;
			honest_case = potential_cases[0]._case;
			// std::cout << "Kiwi6" << std::endl;
		} else {
			// std::cout << "Kiwi7" << std::endl;
			children.push_back(potential_cases);
		}

	}

	// compute all case combinations from the potential_case vector together with the corresponding utilities per child.
	//then iterate over it and call practicality_reasoning for each
	std::vector<z3::Bool> combined_cases;
	std::vector<std::vector<UtilityTuplesSet>> children_per_case;

	std::vector<uint> it(children.size(), 0);
	// std::cout << "Orange" << std::endl;
	while (!all_end(it, children)) {
		// compute case
		solver->push();
		z3::Bool comb_case = children[0][it[0]]._case;
		std::vector<UtilityTuplesSet> comb_case_children = {children[0][it[0]].utilities};
		for (uint k = 1; k < children.size(); k++){
			comb_case = comb_case && children[k][it[k]]._case;
			comb_case_children.push_back(children[k][it[k]].utilities);
		}
		// std::vector<z3::Bool> check_case(current_case.begin(), current_case.end());
		// check_case.push_back(comb_case);
		if (solver->solve({comb_case})!= z3::Result::UNSAT) {
			combined_cases.push_back(comb_case);
			children_per_case.push_back(comb_case_children);
		}
		solver->pop();
		uint n = children.size() -1;
		while (n > 0 && it[n] == children[n].size()-1) {
			it[n] = 0;
			n--;
		}
		it[n]++;
	}
	//std::cout << "Orange1" << std::endl;
	//std::cout << children.size() << std::endl;
	// compute last case
	std::vector<PotentialCase> children_at_zero = children[0];
	//std::cout << "Grape1" << std::endl;
	PotentialCase pot_case = children_at_zero[it[0]];
	//std::cout << "Grape2" << std::endl;
	z3::Bool comb_case = pot_case._case;
	//z3::Bool comb_case = children[0][it[0]]._case;
	//std::cout << "Orange1.1.1" << std::endl;
	std::vector<UtilityTuplesSet> comb_case_children = {children[0][it[0]].utilities};
	// std::cout << "Orange1.1" << std::endl;
	for (uint k = 1; k < children.size(); k++){
		comb_case = comb_case && children[k][it[k]]._case;
		comb_case_children.push_back(children[k][it[k]].utilities);
	}
	// std::cout << "Orange1.2" << std::endl;
	// std::vector<z3::Bool> check_case(current_case.begin(), current_case.end());
	// check_case.push_back(comb_case);
	// std::cout << "Orange1.3" << std::endl;
	solver->push();
	if (solver->solve({comb_case})!= z3::Result::UNSAT) {
		combined_cases.push_back(comb_case);
		children_per_case.push_back(comb_case_children);
	}
	solver->pop();
	// std::cout << "Orange2" << std::endl;


	std::vector<PotentialCase> result;
	// std::cout << "number of combined cases " << combined_cases.size() << std::endl;
	for (uint i=0; i < combined_cases.size(); i++){
		// std::cout << "Orange3" << std::endl;
		std::vector<z3::Bool> new_case = {};
		new_case.insert(new_case.begin(), current_case.begin(), current_case.end());
		new_case.insert(new_case.end(), combined_cases[i]);
		// std::cout << "Orange4" << std::endl;
		std::vector<PotentialCase> res_reasoning = practicality_reasoning(solver, options, node, new_case, children_per_case[i], honest_utilities);
		// std::cout << "number of potential cases per for the current combined case " << res_reasoning.size() << std::endl;
		// std::cout << "Orange4,5" << std::endl;
		for(auto pot_case : res_reasoning) {
			UtilityTuplesSet utilities = pot_case.utilities;
			if (utilities.empty()){
				// std::cout << "return size: 0" << std::endl;
				return {};
			}
			PotentialCase pot = {utilities, combined_cases[i] && pot_case._case};
			result.push_back(pot);
		}
		//std::cout << "Orange5" << std::endl;
		
		
	}
	//std::cout << "return size: " << result.size() << std::endl;
	return result;
}



bool property_under_split(z3::Solver *solver, const Input &input, const PropertyType property, size_t history) {
	/* determine if the input has some property for the current honest history under the current split */
	
	if (property == PropertyType::WeakImmunity || property == PropertyType::WeakerImmunity) {
		
		for (size_t player = 0; player < input.players.size(); player++) {
			
			bool weak_immune_for_player = weak_immunity_rec(solver, input.root.get(), player, property == PropertyType::WeakerImmunity);
			if (!weak_immune_for_player) {
				return false;
			}
		}
		return true;
	}

	else if (property == PropertyType::CollusionResilience) {
		// lookup the leaf for this history
		const Leaf &honest_leaf = get_honest_leaf(input.root.get(), input.honest[history], 0);
		// sneaky hack follows: all possible subgroups of n players can be implemented by counting through from 1 to (2^n - 2)
		// done this way more for concision than efficiency
		for (uint64_t binary_counter = 1; binary_counter < -1ull >> (64 - input.players.size()); binary_counter++) {
			std::bitset<Input::MAX_PLAYERS> group = binary_counter;
			Utility honest_total{z3::Real::ZERO, z3::Real::ZERO};
			// compute the honest total for the current group
			for (size_t player = 0; player < input.players.size(); player++) {
				if (group[player]) {
					honest_total = honest_total + honest_leaf.utilities[player];
				}
			}
					
			bool collusion_resilient_for_group = collusion_resilience_rec(solver, input.root.get(), group, honest_total, input.players.size());
			if (!collusion_resilient_for_group) {
				return false;
			}
		}
		return true;
	}

	/*
	else if (property == PropertyType::Practicality) {
		bool pr = practicality_rec(solver, input.root.get()).size() != 0;
		return pr;
	}
	*/
 
	assert(false);

}

bool property_rec(z3::Solver *solver, const Options &options, const Input &input, const PropertyType property, std::vector<z3::Bool> current_case, size_t history) {
	/* 
		actual case splitting engine
		determine if the input has some property for the current honest history, splitting recursively
	*/

	// property holds under current split
	if (property_under_split(solver, input, property, history)) {
		std::cout << "Property satisfied for current case: " << current_case << std::endl;
		return true;
	}

	// otherwise consider case split
	z3::Bool split = input.root->reason;
	// there is no case split
	if (split.null()) {
		std::cout << "Property violated in case: " << current_case << std::endl;
		return false;
	}

	std::cout << "Splitting on: " << split << std::endl;

	for (const z3::Bool& condition : {split, !split}) {
		input.root->reset_reason();

		solver->push();

		solver->assert_(condition);
		assert (solver->solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);
		bool attempt = property_rec(solver, options, input, property, new_current_case, history);
		
		solver->pop();
		if (!attempt) 
			return false;
	}

	return true;
}

bool practicality_admin(z3::Solver *solver, const Options &options, Node *root, std::vector<z3::Bool> current_case) {
	// std::cout << "Orange" << std::endl;
	if (practicality_rec(solver, options, root, current_case).size() != 0) {
		// std::cout << "Orange" << std::endl;
		std::cout << "Property satisfied for current case: " << current_case << std::endl;
		return true;
	}

	// std::cout << "Orange" << std::endl;

	// otherwise consider case split
	z3::Bool split = root->reason;
	// there is no case split
	assert(split.null());
	std::cout << "Property violated in case: " << current_case << std::endl;
	return false;


}

void property(const Options &options, const Input &input, PropertyType property, size_t history) {
	/* determine if the input has some property for the current honest history */
	std::cout << std::endl;
	std::cout << std::endl;
	std::cout << property << std::endl;

	Solver solver;
	solver.assert_(input.initial_constraint);

	switch (property)
	{
		case  PropertyType::WeakImmunity:
			solver.assert_(input.weak_immunity_constraint);
			break;
		case  PropertyType::WeakerImmunity:
			solver.assert_(input.weaker_immunity_constraint);
			break;
		case  PropertyType::CollusionResilience:
			solver.assert_(input.collusion_resilience_constraint);
			break;
		case  PropertyType::Practicality:
			solver.assert_(input.practicality_constraint);
			// std::cout << "Banana" << std::endl;
			break;
		default:
			std::cout << "Unknown property" << std::endl;
			return;
	}

	assert(solver.solve() == z3::Result::SAT);

	if (property == PropertyType::Practicality) {
		// std::cout << "Banana" << std::endl;
		if (practicality_admin(&solver, options, input.root.get(), std::vector<z3::Bool>()))
			std::cout << "YES, property " << property << " is satisfied" << std::endl;
		//std::cout << "Banana" << std::endl;
	} else {
		if (property_rec(&solver, options, input, property, std::vector<z3::Bool>(), history))
			std::cout << "YES, property " << property << " is satisfied" << std::endl;
	}
	
}

void analyse_properties(const Options &options, const Input &input) {
	/* iterate over all honest histories and check the properties for each of them */
	for (size_t history = 0; history < input.honest.size(); history++) { 
		std::cout << std::endl;
		std::cout << "Checking history " << input.honest[history] << std::endl; 

		input.root->reset_honest();
		input.root->reset_reason();
		input.root->mark_honest(input.honest[history]);

		if (options.weak_immunity)
			property(options, input, PropertyType::WeakImmunity, history);
		if (options.weaker_immunity)
			property(options, input, PropertyType::WeakerImmunity, history);
		if (options.collusion_resilience)
			property(options, input, PropertyType::CollusionResilience, history);
		if (options.practicality)
			property(options, input, PropertyType::Practicality, history);
	}
}