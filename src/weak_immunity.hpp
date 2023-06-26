#ifndef __checkmate_weak_immunity__
#define __checkmate_weak_immunity__

#include "solver.hpp"

template<bool weaker>
class WeakImmunity: public Solver::PropertyBase {
public:
	WeakImmunity(const Input &input);
	using HonestHistoryBehaviour = Solver::InvariantToHonestHistory;

private:
	void collect_constraints(
		std::vector<z3::Bool> &constraints,
		const std::unique_ptr<Node> &input,
		const Player &player,
		z3::Bool *previous_player_decisions
	);
};

#endif
