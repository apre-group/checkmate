#include <iostream>
#include <bitset>
#include <cassert>
#include <unordered_set>
#include <bits/stdc++.h> 
#include <string>

#include "input.hpp"
#include "options.hpp"
#include "z3++.hpp"
#include "utils.hpp"
#include "property.hpp"

using z3::Bool;
using z3::Solver;

bool all_at_end(std::vector<unsigned> it, std::vector<std::vector<PotentialCase>> children) {

	for (unsigned i = 0; i < it.size(); i++){
		if (it[i] != children[i].size()-1){
			return false;
		}
	}
	return true;
}

bool practicality_entry(z3::Solver &solver, const Options &options, const Input &input, Node *root, std::vector<z3::Bool> current_case);

template<typename Comparison>
z3::Bool get_split_approx(z3::Solver &solver, Utility a, Utility b, Comparison comp) {
	
	// if they have to be equal, consider infinitesimals
	if(solver.solve({a.real != b.real}) == z3::Result::UNSAT) {
		return comp(a.infinitesimal, b.infinitesimal);
	}	
	// if they cannot be equal, consider strict inequality
	else if (solver.solve({a.real == b.real}) == z3::Result::UNSAT) {
		//std::cout << "Case B" << std::endl;
		//std::cout << "-> " << a.real << ">" << b.real << std::endl;
		return a.real > b.real;
	}
	else {
		// if a.real has to be >= b.real, split on whether equal
		if (solver.solve({!comp(a.real, b.real)}) == z3::Result::UNSAT) {
			return a.real == b.real;
		}
		// we don't know whether their real parts are >=, assert it
		else {
			return comp(a.real, b.real);
		}
	} 	
}

template<typename Comparison>
z3::Bool get_split_approx_old(z3::Solver &solver, Utility a, Utility b, Comparison comp) {
	
	// if they have to be equal, consider infinitesimals
	if(solver.solve({a.real != b.real}) == z3::Result::UNSAT) {
		return comp(a.infinitesimal, b.infinitesimal);
	}	
	// if they cannot be equal, consider strict inequality
	else if (solver.solve({a.real == b.real}) == z3::Result::UNSAT) {
		//std::cout << "Case B" << std::endl;
		//std::cout << "-> " << a.real << ">" << b.real << std::endl;
		return a.real > b.real;
	}
	else {
		return a.real == b.real;
	} 	
}

bool weak_immunity_rec(const Input &input, z3::Solver &solver, Node *node, unsigned player, bool weaker) {

	if (node->is_leaf()) {
		const auto &leaf = node->leaf();
		// known utility for us
		auto utility = leaf.utilities[player];

		z3::Bool condition = weaker ? utility.real >= z3::Real::ZERO : utility >= Utility {z3::Real::ZERO, z3::Real::ZERO};

		if (solver.solve({!condition}) == z3::Result::UNSAT) {
			return true;
		}
		
		if (solver.solve({condition}) == z3::Result::UNSAT) {
			return false;
		}

		leaf.reason = weaker ? utility.real >= z3::Real::ZERO : get_split_approx(solver, utility, Utility {z3::Real::ZERO, z3::Real::ZERO}, [](z3::Real a, z3::Real b){return a >= b;});
		input.set_reset_point(leaf);
		return false;
	}

	

	const auto &branch = node->branch();

	

	// else we deal with a branch
	if (player == branch.player) { 

		if  (!branch.strategy.empty()){
		return true;
		}	

		// player behaves honestly
		if (branch.honest) {
			// if we are along the honest history, we want to take an honest strategy
			auto &honest_choice = branch.get_honest_child();
			auto *subtree = honest_choice.node.get();

			// set chosen action, needed for printing strategy
			branch.strategy = honest_choice.action;

			// the honest choice must be weak immune
			if (weak_immunity_rec(input, solver, subtree, player, weaker)) {
				return true;
			} 

			branch.reason = subtree->reason;
			input.set_reset_point(branch);
			return false;
		}
		// otherwise we can take any strategy we please as long as it's weak immune
		for (const Choice &choice: branch.choices) {
			if (weak_immunity_rec(input, solver, choice.node.get(), player, weaker)) {
				// set chosen action, needed for printing strategy
				branch.strategy = choice.action;
				return true;
			}
			if (!choice.node->reason.null()) {
				branch.reason = choice.node->reason;
				input.set_reset_point(branch);
			}		
		}
		return false;
	} else {
		// if we are not the honest player, we could do anything,
		// so all branches should be weak immune for the player
		for (const Choice &choice: branch.choices) {
			if (!weak_immunity_rec(input, solver, choice.node.get(), player, weaker)) {
				branch.reason = choice.node->reason;
				input.set_reset_point(branch);
				return false;
			}
		}
		return true;
	}

} 

const Leaf& get_honest_leaf(Node *node, const std::vector<std::string> &history, unsigned index) {
    if (node->is_leaf()) {
        return node->leaf();
    }
	unsigned next_index = index + 1;
	return get_honest_leaf(node->branch().get_choice(history[index]).node.get(), history, next_index);
}

bool collusion_resilience_rec(const Input &input, z3::Solver &solver, Node *node, std::bitset<Input::MAX_PLAYERS> group, Utility honest_total, unsigned players) {
	
	if (node->is_leaf()) {

		// compute the total utility for the player group...
		Utility group_utility{z3::Real::ZERO, z3::Real::ZERO};
		const auto &leaf = node->leaf();
		for (size_t player = 0; player < players; player++)
			if (group[player])
				group_utility = group_utility + leaf.utilities[player];

		// ..and compare it to the honest total
		auto condition = honest_total >= group_utility;		
		
		if (solver.solve({!condition}) == z3::Result::UNSAT) {
			return true;
		}

		if (solver.solve({condition}) == z3::Result::UNSAT) {
			return false;
		}

		leaf.reason = get_split_approx(solver, honest_total, group_utility, [](z3::Real a, z3::Real b){return a >= b;});
		input.set_reset_point(leaf);
		return false;
	}

	const auto &branch = node->branch();
	// else we deal with a branch
	if (!group[branch.player]) { 

		if  (!branch.strategy.empty()){
			return true;
		}


		// player behaves honestly
		if (branch.honest) {
			// if we are along the honest history, we want to take an honest strategy
			auto &honest_choice = branch.get_honest_child();
			auto *subtree = honest_choice.node.get();

			// set chosen action, needed for printing strategy
			branch.strategy = honest_choice.action;

			// the honest choice must be collusion resilient
			if (collusion_resilience_rec(input, solver, subtree, group, honest_total, players)) {
				return true;
			} 
			
			branch.reason = subtree->reason;
			input.set_reset_point(branch);
			return false;
		}
		// otherwise we can take any strategy we please as long as it's collusion resilient
		for (const Choice &choice: branch.choices) {
			if (collusion_resilience_rec(input, solver, choice.node.get(), group, honest_total, players)) {
				// set chosen action, needed for printing strategy
				branch.strategy = choice.action;
				return true;
			}	
			if (!choice.node->reason.null()) {
				branch.reason = choice.node->reason;
				input.set_reset_point(branch);
			}		
		}
		return false;
	} else {
		// if we are not the honest player, we could do anything,
		// so all branches should be collusion resilient for the player
		for (const Choice &choice: branch.choices) {
			if (!collusion_resilience_rec(input, solver, choice.node.get(), group, honest_total, players)) {
				branch.reason = choice.node->reason;
				input.set_reset_point(branch);
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

UtilityTuplesSet practicality_rec_old(z3::Solver &solver, Node *node) {
	if (node->is_leaf()) {
		// return the utility tuple of the leaf as a set (of one element)
		const Leaf &leaf = node->leaf();
		return {leaf.utilities};
	}  

	// else we deal with a branch
 	const auto &branch = node->branch();

	// get practical strategies and corresponding utilities recursively
	std::vector<UtilityTuplesSet> children;
	std::vector<std::string> children_actions;

	UtilityTuplesSet honest_utilities;

	for (const Choice &choice: branch.choices) {
		UtilityTuplesSet utilities = practicality_rec_old(solver, choice.node.get());

		// this child has no practical strategy (propagate reason for case split, if any) 
		if(utilities.empty()) {
			branch.reason = choice.node->reason;
			// return empty set
			return {};
		}

		if(choice.node->honest) {
			honest_utilities = utilities;
			branch.strategy = choice.action; // choose the honest action along the honest history
		} else {
			children.push_back(utilities);
			children_actions.push_back(choice.action);
		}

	}


	if (branch.honest) {
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
				auto condition =   maximum < utility[branch.player];
				if (solver.solve({condition}) == z3::Result::SAT) {
					if (solver.solve({!condition}) == z3::Result::SAT) {
						// might be maximal, just couldn't prove it
						branch.reason =  get_split_approx(solver, maximum, utility[branch.player], [](z3::Real a, z3::Real b){return a >= b;}); 
					}
				} 
				else {
					found = true;
					break;
				}
			}
			if (!found) {
				// return empty set
				return {}; 
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
		UtilityTuplesSet result;
		for (const auto& utilities : children) {
			for (const auto& utility : utilities) {
				result.insert(utility);
			}
		}

		// the set to drop
		UtilityTuplesSet remove;

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
					auto condition = dominator <= dominatee;
					if (solver.solve({condition}) == z3::Result::SAT) {
						dominated = false;
						if (solver.solve({!condition}) == z3::Result::SAT) {
							branch.reason = get_split_approx(solver, dominatee, dominator, [](z3::Real a, z3::Real b){return a >= b;}); 
							return {}; 
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
		for (const auto& elem : remove) {
			result.erase(elem);
		}

		// if strategy has not been set, we are not along the honest history
		// go over all children and pick the one that has a utility tuple which is contained in the returned result
		if (branch.strategy.empty()) {
			for (unsigned i = 0; i < children.size() && branch.strategy.empty(); i++) {
				auto& utilities = children[i];
				for (const auto& utility : utilities) {
					if(result.find(utility) != result.end()) {
						branch.strategy = children_actions[i];
						break;
					}
				}
			}
		}

		return result;

	} 

}

template<typename Comparison> // comparison either > or >=
z3::Bool get_split(z3::Solver &solver, Utility a, Utility b, Comparison comp) {
	// std::cout << solver << std::endl;
	if(solver.solve({a.real != b.real}) == z3::Result::UNSAT) {
		//std::cout << "Case A" << std::endl;
		//std::cout << "-> " << comp(a.infinitesimal, b.infinitesimal) << std::endl;
		return comp(a.infinitesimal, b.infinitesimal);
	}	
	else if (solver.solve({a.real == b.real}) == z3::Result::UNSAT) {
		//std::cout << "Case B" << std::endl;
		//std::cout << "-> " << a.real << ">" << b.real << std::endl;
		return a.real > b.real;
	}
	else {
		//std::cout << "Case C" << std::endl;
		//return comp(a.real, b.real);
		//return a.real == b.real;
		if (solver.solve({!comp(a.infinitesimal, b.infinitesimal)}) == z3::Result::UNSAT) {
			return comp(a.real, b.real);
		}
		else if (solver.solve({comp(a.infinitesimal, b.infinitesimal)}) == z3::Result::UNSAT) {
			return a.real > b.real;
		}
		else {
			return a.real > b.real || (a.real == b.real && comp(a.infinitesimal, b.infinitesimal));
		}
	} 	
}




std::vector<PotentialCase> compute_all_combinations(z3::Solver &solver, std::vector<std::vector<PotentialCase>> remove_sets, std::vector<z3::Bool> current_case) {
	if(remove_sets.size() == 0) 
		return {{{}, {}}};

	std::vector<unsigned> it(remove_sets.size(), 0);
	std::vector<PotentialCase> remove_sets_combined;
	bool last_case_computed = false;
	bool iterators_at_end = all_at_end(it, remove_sets);
	
	// I assume current case is asserted in solver;
	//solver.assert_(current_case);

	while (!iterators_at_end || !last_case_computed) {

		// compute case
		std::vector<z3::Bool> comb_case;
		UtilityTuplesSet comb_remove = remove_sets[0][it[0]].utilities;
		solver.push();
		for (unsigned k = 0; k < remove_sets.size(); k++){
			
			// comb_case.insert(comb_case.end(), remove_sets[k][it[k]]._case.begin(), remove_sets[k][it[k]]._case.end());
			for (auto constraint : remove_sets[k][it[k]]._case){
				// only add non trivial constriants
				if (solver.solve({!constraint})!= z3::Result::UNSAT){
					// std::cout << "constraint" << constraint << std::endl;
					comb_case.push_back(constraint);
					solver.assert_(constraint);
				}
			} 
			
			
			
			if(k != 0) {
				for (auto element : remove_sets[k][it[k]].utilities) {
					comb_remove.insert(element);
				}
			}
		}
		solver.pop();
		//std::cout << "comb case in comp_all_comb " << comb_case << std::endl;
		// might be unnecessary
		std::vector<z3::Bool> check_case(current_case.begin(), current_case.end());
		check_case.insert(check_case.end(), comb_case.begin(), comb_case.end());

		if (solver.solve(check_case)!= z3::Result::UNSAT) {
			// std::cout << "Combined case: " << comb_case << ", current case: " << current_case << std::endl;
			remove_sets_combined.push_back({comb_remove, comb_case});
		}

		if(iterators_at_end) {
			last_case_computed = true; 
		} else {
			unsigned n = remove_sets.size() -1;
			while (n > 0 && it[n] == remove_sets[n].size()-1) {
				it[n] = 0;
				n--;
			}
			it[n]++;
			iterators_at_end = all_at_end(it, remove_sets);
		}

	}

	return remove_sets_combined;
}


bool pr_case_split(z3::Solver &solver, const Options &options, const Input &input, UtilityTuple honest_utility, UtilityTuplesSet utilities, unsigned player, std::vector<z3::Bool> current_case){
// fake case splitting to find out if honest is geq for at least 1 utility[player] in  utilities for current_case"""

	bool need_to_split = false;
	z3::Bool split;
	for (auto utility : utilities){
		z3::Bool condition_to_check = get_split_approx_old(solver, utility[player], honest_utility[player], [](z3::Real a, z3::Real b){return a > b;}); 
		auto z3_result = solver.solve({condition_to_check});
		if (z3_result == z3::Result::UNSAT) {	
			if (!input.stop_log){
			std::cout << "\tProperty satisfied in case "<< current_case << std::endl;
			}
			return true;
			}
		else {
			assert(z3_result == z3::Result::SAT);
			auto z3_result = solver.solve({!condition_to_check});
			if (z3_result == z3::Result::SAT) {	
				need_to_split = true;
				split = condition_to_check;
			}
		} 		
	}

	if (need_to_split){
		bool result = true;
		if (!input.stop_log){
			std::cout << "\tSplitting on: " << split << std::endl;
		}

		for (const z3::Bool& condition : {split, split.invert()}) {
			solver.push();
			solver.assert_(condition);
			assert (solver.solve() != z3::Result::UNSAT);
			std::vector<z3::Bool> new_current_case = {};
			new_current_case.insert(new_current_case.begin(), current_case.begin(), current_case.end());
			new_current_case.push_back(condition);
			bool attempt = pr_case_split(solver, options, input, honest_utility, utilities, player, new_current_case);
			solver.pop();
			if (!attempt){
				if (options.preconditions){
					result = false;
				} else {
				return false;
				}
			}
		}
		return result;
	} else {
		if (!input.stop_log){
		std::cout << "\tProperty violated in case "<< current_case << std::endl;
		}
		if (options.preconditions){
				input.add_unsat_case(current_case);
				input.stop_logging();
			}
		return false;
	}


}


// refactoring try and avoid the copying here: each std::vector<T> (and UtilityTuplesSet) makes a new copy
std::vector<PotentialCase> practicality_reasoning(z3::Solver &solver, const Options &options, const Input &input, Node *node, std::vector<z3::Bool> current_case, std::vector<UtilityTuplesSet> children, UtilityTuplesSet honest_utilities) {
		const auto &branch = node->branch();
		bool ret_empty = false;
		
		if (branch.honest) {
			// if we are at an honest node, our strategy must be the honest strategy

			// TODO set chosen action i.e. startegy for this note to be honest_choice->action
			// for this we need to add a property strategy to our nodes
			
			assert(honest_utilities.size() == 1);
			// the utility at the leaf of the honest history
			const UtilityTuple &honest_utility = *honest_utilities.begin();
			// this should be maximal against other players, so...
			Utility maximum = honest_utility[branch.player];


			// if in the subsequent for loop never terminate:
			//	 	we return the maximal strategy 
			// 		honest choice is practical for current player
			PotentialCase pot_case = {{honest_utility}, {}};
			std::vector<PotentialCase> result = {pot_case};

			// for all other children
			for (const auto& utilities : children) {
				bool found = false;
				// does there exist a possible utility such that `maximum` is geq than it?
				for (const auto& utility : utilities) {
					//auto condition = maximum < utility[branch.player];
					//std::cout<<"Split needed: " << utility[branch.player] << "  " << maximum << std::endl;
					auto condition = get_split(solver, utility[branch.player], maximum, [](z3::Real a, z3::Real b){return a > b;});
					if (solver.solve({condition}) == z3::Result::SAT) {
						if (solver.solve({!condition}) == z3::Result::SAT) {
							// might be maximal, just couldn't prove it
							branch.reason = get_split_approx_old(solver, utility[branch.player], maximum, [](z3::Real a, z3::Real b){return a > b;});
						}
					} 
					else {
						found = true;

						break;
					}
				}
				
				if (!found) {
					// current_case_okay = false;
					
					// return empty set if no reason set
					if (branch.reason.null()) {
						if (!input.stop_log){
						std::cout << "\tProperty violated in case " << current_case << std::endl;
						}
						if (options.preconditions){
							input.add_unsat_case(current_case);
							input.stop_logging();
							ret_empty = true;
						} else {
							return {}; 
						}
					} else {

						// call this function for reason and !reason
						z3::Bool split = branch.reason;
						if (!input.stop_log){
							std::cout << "\tSplitting on: " << split << std::endl;
						}

						for (const z3::Bool& condition : {split, split.invert()}) {
							branch.reset_reason();

							solver.push();

							solver.assert_(condition);
							assert (solver.solve() != z3::Result::UNSAT);
							std::vector<z3::Bool> new_current_case = {};
							new_current_case.insert(new_current_case.begin(), current_case.begin(), current_case.end());
							new_current_case.push_back(condition);
							bool attempt = pr_case_split(solver, options, input, honest_utility, utilities, branch.player, new_current_case);
							
							solver.pop();
							if (!attempt) {
								if (options.preconditions){
									ret_empty = true;
								} else {
								return {};
								}
							} 
						}
						// std::cout << "\tSuccessful split on: " << split << "at history XXX" << std::endl;

					}
				}
			}

			if (ret_empty){
				assert(options.preconditions);
			} else {
				return result;
			}


	} else {
		// not in the honest history
		// TODO (maybe): we could do this more efficiently by working out the set of utilities for the player
		// but utilities can't be put in a set easily -> fix this here in the C++ version

		// compute the set of possible utilities by merging the set of children's utilities
		UtilityTuplesSet result;
		for (const auto& utilities : children) {
			for (const auto& utility : utilities) {
				result.insert(utility);
			}
		}

		std::vector<std::vector<PotentialCase>> remove_sets; //one per candidate in result, each candidate can have 1 or 2 PotentialCases
		
		// work out whether to drop `candidate`
		for (const auto& candidate : result) {
			std::vector<PotentialCase> remove_sets_of_candate;

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
					//auto condition = dominator <= dominatee;
					//std::cout<<"Split needed: " << dominatee << "  " << dominator << std::endl;
					auto condition = get_split(solver, dominatee, dominator, [](z3::Real a, z3::Real b){return a >= b;});
					if (solver.solve({condition}) == z3::Result::SAT) {
						dominated = false;
						if (solver.solve({!condition}) == z3::Result::SAT) {
							if(split.null()) {
								split = condition.invert();
							} else {
								split = split || condition.invert();
							}
						}
					}
				}  

				if (dominated) {
					PotentialCase remove_struct = {{candidate}, {}};
					remove_sets_of_candate.push_back(std::move(remove_struct));
					break;

				} 
			}

			if (!dominated && !split.null()) {

				PotentialCase remove_struct_first = {{candidate}, {split}};
				PotentialCase remove_struct_second = {{}, {split.invert()}};

				for(PotentialCase remove_struct : {remove_struct_first, remove_struct_second}) {
					remove_sets_of_candate.push_back(std::move(remove_struct));
				}

			}

			if(remove_sets_of_candate.size() > 0) {
				remove_sets.push_back(std::move(remove_sets_of_candate));
			}
		
		}

		// combine remove sets to obtain O(2**n) remove sets
		std::vector<PotentialCase> remove_sets_combined = compute_all_combinations(solver, remove_sets, current_case);
		for (auto elem : remove_sets_combined){
			// std::cout << "remove sets combined cases " << elem._case << std::endl;
		}
		std::vector<PotentialCase> ret_result;

		for(auto remove_set : remove_sets_combined) {
			UtilityTuplesSet rec_result(result.begin(), result.end()); // cannot use std::move here, we need a new copy in each iteration
			for (const auto& elem : remove_set.utilities) {
				rec_result.erase(elem);
			}
			ret_result.push_back({std::move(rec_result), remove_set._case});
		}

		return ret_result;

	} 
	assert(false);
	return {};
}


bool are_compatible(const PotentialCase &pc1, const PotentialCase &pc2) {
	bool compatible_utilities = true;

	for (const auto& utility : pc1.utilities) {
		if(pc2.utilities.find(utility) == pc2.utilities.end()) {
			compatible_utilities = false;
			break;
		}
	}

	bool compatible_cases = are_compatible_cases(pc1._case, pc2._case);

	return compatible_utilities && compatible_cases;
}

std::vector<PotentialCase> practicality_rec(z3::Solver &solver, const Options &options, const Input &input, Node *node, std::vector<z3::Bool> current_case) {
	std::cout << "in practicality_rec" << std::endl;

	if (node->is_leaf()) {
		// return the utility tuple of the leaf as a set (of one element)
		const Leaf &leaf = node->leaf();
		std::cout << "return 1 practicality_rec" << std::endl;
		return {{{leaf.utilities}, {}}};
	}  
	// keeps track on whether we have to return the empty set
	bool ret_empty = false;

	// else we deal with a branch
 	const auto &branch = node->branch();

	// get practical strategies and corresponding utilities recursively
	std::vector<std::vector<PotentialCase>> children;
	std::vector<std::string> children_actions;

	UtilityTuplesSet honest_utilities;
	std::vector<z3::Bool> honest_case;

	for (const Choice &choice: branch.choices) {
		std::vector<PotentialCase> potential_cases = practicality_rec(solver, options, input, choice.node.get(), current_case);

		// this child has no practical strategy (propagate reason for case split, if any) 
		if(potential_cases.empty()) {
			std::cout << "tada" << std::endl;
			branch.reason = choice.node->reason;
			assert(choice.node->honest);
			assert(choice.node->reason.null());
			std::cout << "what" << std::endl;


			// return empty set
			if (options.preconditions){
				ret_empty = true;
			} else {
				std::cout << "return 2 practicality_rec" << std::endl;
				return {};
			}
		}
		std::cout << "hmm" << std::endl;

		if(choice.node->honest) {
			std::cout << "visible" << std::endl;
			honest_utilities = potential_cases[0].utilities;
			std::cout << "invisible" << std::endl;
			honest_case = potential_cases[0]._case;

			//std::cout << "Before" << branch.pr_strategies_actions << std::endl;
			//std::cout << "---> add " << choice.action << " for case " << potential_cases[0]._case << std::endl;
			branch.pr_strategies_cases.push_back(potential_cases[0]._case); 
			branch.pr_strategies_actions.push_back(choice.action); // choose the honest action along the honest history
			//std::cout << "After" << branch.pr_strategies_actions << std::endl;
		} else {
			children.push_back(potential_cases);
			children_actions.push_back(choice.action);
		}
	}

	// compute all case combinations from the potential_case vector together with the corresponding utilities per child.
	// then iterate over it and call practicality_reasoning for each
	std::vector<std::vector<z3::Bool>> combined_cases;
	std::vector<std::vector<UtilityTuplesSet>> children_per_case;

	std::vector<unsigned> it(children.size(), 0);
	//std::cout << children.size() << std::endl;
	
	//TODO for debugging only -> remove afterwards
	/*unsigned big_product = 1; 
	for(auto something: children) {
		big_product *= something.size();
	}
	std::cout << "------------> "<< big_product<<std::endl;*/
	// until here to be removed

	bool last_case_computed = false;
	bool iterators_at_end = all_at_end(it, children);

	while (!iterators_at_end || !last_case_computed) {
		// compute case
		//solver.push(); -> TODO remove this, not needed, as we are not asserting anything
		
		//std::vector<z3::Bool> comb_case(children[0][it[0]]._case.begin(), children[0][it[0]]._case.end());
		//std::vector<UtilityTuplesSet> comb_case_children = {children[0][it[0]].utilities};
		std::vector<z3::Bool> comb_case;
		std::vector<UtilityTuplesSet> comb_case_children;

		solver.push();
		for (unsigned k = 0; k < children.size(); k++){
			//comb_case.insert(comb_case.end(), children[k][it[k]]._case.begin(), children[k][it[k]]._case.end());
			// add only non trivial constraints
			
			for (auto constraint : children[k][it[k]]._case) {
				if (solver.solve({!constraint}) != z3::Result::UNSAT){
					comb_case.push_back(constraint);
					solver.assert_(constraint);
				}
			}
			
			comb_case_children.push_back(children[k][it[k]].utilities);
		}
		solver.pop();
		if (solver.solve({comb_case})!= z3::Result::UNSAT) {
			combined_cases.push_back(comb_case);
			children_per_case.push_back(comb_case_children);
		}
		
		//solver.pop();
		if(iterators_at_end) {
			last_case_computed = true; 
		} else {
			unsigned n = children.size() -1;
			while (n > 0 && it[n] == children[n].size()-1) {
				it[n] = 0;
				n--;
			}
			it[n]++;
			iterators_at_end = all_at_end(it, children);
		}
		
	}


	std::vector<PotentialCase> result;
	for (unsigned i=0; i < combined_cases.size(); i++){
		std::vector<z3::Bool> new_case = {};
		new_case.insert(new_case.begin(), current_case.begin(), current_case.end());
		new_case.insert(new_case.end(), combined_cases[i].begin(), combined_cases[i].end());
		solver.push();
		for (auto asssertion : combined_cases[i]) {
			solver.assert_(asssertion);
		}
		std::cout << "pre practicality_reasoning" << std::endl;
		std::vector<PotentialCase> res_reasoning = practicality_reasoning(solver, options, input, node, new_case, children_per_case[i], honest_utilities);
		std::cout << "post practicality_reasoning" << std::endl;
		solver.pop();
		
		if (res_reasoning.size() == 0){
			// return empty set
			if (options.preconditions){
				ret_empty = true;
			} else {
			std::cout << "return 3 practicality_rec" << std::endl;
			return {};
			}
		}

		for(auto pot_case : res_reasoning) {
			UtilityTuplesSet utilities = pot_case.utilities;
			if (utilities.empty()){
				// return empty set
				if (options.preconditions){
					ret_empty = true;
				} else {
				std::cout << "return 4 practicality_rec" << std::endl;
				return {};
				}
			}
			// std::cout << "end of pr_rec potential case: " << pot_case._case << std::endl;
			// std::cout << "combined_cases[i]: " << combined_cases[i] << std::endl;
			// std::cout << "current case: " << current_case << std::endl;
			std::vector<z3::Bool> new_potential_case(combined_cases[i].begin(), combined_cases[i].end());
			new_potential_case.insert(new_potential_case.end(), pot_case._case.begin(), pot_case._case.end());
			PotentialCase pot = {utilities, new_potential_case};
			result.push_back(pot);
		}
		
	}

	// strategy extraction
	// for each potential case from result find the first child from children s.t.
	// child contains a potential case compatible with the potential case from result
	// a potential case (utilities1, case1) is compatible with potential case (utilities2, case2) iff.
	// utilities1 \subseteq utilities2 && case1 \subseteq case2
	if (!branch.honest) { // if strategy has not been set, we are not along the honest history
		for (unsigned i = 0; i < result.size(); i++) {
			PotentialCase &potential_case_from_result = result[i];
			bool found = false;
			for (unsigned j = 0; j < children.size() && !found; j++) {
				for (const auto& potential_case : children[j]) {
					if(are_compatible(potential_case, potential_case_from_result)) {
						branch.pr_strategies_cases.push_back(potential_case_from_result._case);
						branch.pr_strategies_actions.push_back(children_actions[j]);
						//std::cout << "---> add " << children_actions[j] << " for case " << potential_case_from_result._case << std::endl;
						found = true;
						break;
					}
				}
			}
		}
	} 

	if (ret_empty){
		assert(options.preconditions);
		std::cout << "return 5 practicality_rec" << std::endl;
		return {}; 
	} else {

		std::cout << "return 6 practicality_rec" << std::endl;
	return result;
	}
}

bool property_under_split(z3::Solver &solver, const Input &input, const PropertyType property, size_t history) {
	/* determine if the input has some property for the current honest history under the current split */
	
	if (property == PropertyType::WeakImmunity || property == PropertyType::WeakerImmunity) {
		for (size_t player = 0; player < input.players.size(); player++) {
			
			bool weak_immune_for_player = weak_immunity_rec(input, solver, input.root.get(), player, property == PropertyType::WeakerImmunity);
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
					
			bool collusion_resilient_for_group = collusion_resilience_rec(input, solver, input.root.get(), group, honest_total, input.players.size());
			if (!collusion_resilient_for_group) {
				return false;
			}
		}
		return true;
	}


	// Practicality new case splits -> this needs to be removed
	else if (property == PropertyType::Practicality) {
		bool pr = practicality_rec_old(solver, input.root.get()).size() != 0;
		return pr;
	}
	
 
	assert(false);
	UNREACHABLE
}

bool property_rec(z3::Solver &solver, const Options &options, const Input &input, const PropertyType property, std::vector<z3::Bool> current_case, size_t history) {
	/* 
		actual case splitting engine
		determine if the input has some property for the current honest history, splitting recursively
	*/

	// property holds under current split
	if (property_under_split(solver, input, property, history)) {
		if (!input.stop_log){
			std::cout << "\tProperty satisfied for case: " << current_case << std::endl; 
		}
		// if strategies, add a "potential case" to keep track of all strategies
		if (options.strategies){
			input.compute_strategy_case(current_case);
		}
		return true;
	}

	// otherwise consider case split
	z3::Bool split = input.root->reason;
	// there is no case split
	if (split.null()) {
		if (!input.stop_log){
			std::cout << "\tProperty violated in case: " << current_case << std::endl;
		}
		if (options.preconditions){
			input.add_unsat_case(current_case);
			input.stop_logging();
		}

		return false;
	}
	if (!input.stop_log){
		std::cout << "\tSplitting on: " << split << std::endl;
	}

	bool result = true;

	for (const z3::Bool& condition : {split, split.invert()}) {
		input.root->reset_reason();
		// strategy reset to be done in prev function
		input.reset_point->branch().reset_strategy();

		solver.push();

		solver.assert_(condition);
		assert (solver.solve() != z3::Result::UNSAT);
		std::vector<z3::Bool> new_current_case(current_case.begin(), current_case.end());
		new_current_case.push_back(condition);


		bool attempt = property_rec(solver, options, input, property, new_current_case, history);

		solver.pop();
		if (!attempt){
			if (!options.preconditions){
				return false;
			}
			else {
				result = false;
				input.stop_logging();
			}
		}
	}
	return result;
}

bool practicality_entry(z3::Solver &solver, const Options &options, const Input &input, Node *root, std::vector<z3::Bool> current_case) {
	std::vector<PotentialCase> result = practicality_rec(solver, options, input, root, current_case);
	std::cout << "after practicality_rec" << std::endl;
	if (result.size() != 0) {	
		// strategy computation to be adapted 
		// if (options.strategies) {
		// 	for (auto &pot_case: result) {
		// 		root->branch().print_strategy_pr(input, pot_case._case);
		// 	}
		// }
			
		return true;
	}

	// there is no case split
	assert(root->reason.null());
	return false;
}

void property(const Options &options, const Input &input, PropertyType property, size_t history) {
	/* determine if the input has some property for the current honest history */


	Solver solver;
	solver.assert_(input.initial_constraint);
	std::string prop_name;
	bool prop_holds;

	switch (property)
	{
		case  PropertyType::WeakImmunity:
			solver.assert_(input.weak_immunity_constraint);
			prop_name = "weak immune";
			break;
		case  PropertyType::WeakerImmunity:
			solver.assert_(input.weaker_immunity_constraint);
			prop_name = "weaker immune";
			break;
		case  PropertyType::CollusionResilience:
			solver.assert_(input.collusion_resilience_constraint);
			prop_name = "collusion resilient";
			break;
		case  PropertyType::Practicality:
			solver.assert_(input.practicality_constraint);
			prop_name = "practical";
			break;
		/*
		default:
			std::cout << "Unknown property" << std::endl;
			return;
		*/
	}

	std::cout << std::endl;
	std::cout << std::endl;
	std::cout << "Is history " << input.honest[history] << " " << prop_name << "?" << std::endl;

	assert(solver.solve() == z3::Result::SAT);

	if (property == PropertyType::Practicality) {
		// TODO: choose one of the 2 lines below depending on whether you want to use the new or
		// the old case splitting algorithm for practicality
		//if (practicality_entry(solver, options, input, input.root.get(), std::vector<z3::Bool>())) {
		if (property_rec(solver, options, input, property, std::vector<z3::Bool>(), history)) {
			std::cout << "YES, it is " << prop_name << "." << std::endl;
			prop_holds = true;
		} else { 
			std::cout << "NO, it is not " << prop_name << "." << std::endl;
			prop_holds = false;
		}
	} else {
		if (property_rec(solver, options, input, property, std::vector<z3::Bool>(), history)) {
			std::cout << "YES, it is " << prop_name << "." << std::endl;
			prop_holds = true;
		} else { 
			std::cout << "NO, it is not " << prop_name << "." << std::endl;
			prop_holds = false;
		}
	}
	
	// generate preconditions
	if (options.preconditions && !prop_holds) {
				std::cout << std::endl;
				std::vector<z3::Bool> conjuncts;
				std::vector<std::vector<z3::Bool>> simplified = input.precondition_simplify();

				for (const auto &unsat_case: simplified) {
					// negate each case (by disjoining the negated elements), then conjunct all - voila weakest prec to be added to the init constr
					std::vector<z3::Bool> neg_case;
					for (const auto &elem: unsat_case) {
						neg_case.push_back(elem.invert());
					}
					z3::Bool disj = disjunction(neg_case);
					conjuncts.push_back(disj);
				}
				z3::Bool raw_prec = conjunction(conjuncts);
				z3::Bool simpl_prec = raw_prec.simplify();
				std::cout << "Weakest Precondition: " << std::endl << "\t" << simpl_prec << std::endl;
	}
	
	// generate strategies
	if (options.strategies && prop_holds){
		// for each case a strategy
		input.print_strategies();
	}
	
}

void analyse_properties(const Options &options, const Input &input) {
	/* iterate over all honest histories and check the properties for each of them */
	for (size_t history = 0; history < input.honest.size(); history++) { 

		std::cout << std::endl;
		std::cout << std::endl;
		std::cout << "Checking history " << input.honest[history] << std::endl; 

		input.root->reset_honest();
		input.root->mark_honest(input.honest[history]);
		
		

		std::vector<bool> property_chosen = {options.weak_immunity, options.weaker_immunity, options.collusion_resilience, options.practicality};
		std::vector<PropertyType> property_types = {PropertyType::WeakImmunity, PropertyType::WeakerImmunity, PropertyType::CollusionResilience, PropertyType::Practicality};

		assert(property_chosen.size() == property_types.size());

		for (size_t i=0; i<property_chosen.size(); i++) {
			if(property_chosen[i]) {
				input.reset_logging();
				input.reset_unsat_cases();
				input.root->reset_reason();
				input.root->reset_strategy();
				input.reset_strategies(); 
				input.reset_reset_point();
				property(options, input, property_types[i], history);
			}
		}
	}
}
