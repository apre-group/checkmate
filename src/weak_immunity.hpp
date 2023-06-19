#ifndef __checkmate_weak_immunity__
#define __checkmate_weak_immunity__

#include "input.hpp"

class WeakImmunity {
public:
	WeakImmunity(const Input &input);
	z3::Bool computed;
private:
	void collect_constraints(std::vector<z3::Bool> &conjuncts, const std::unique_ptr<Node> &tree, const Player &player, z3::Bool *previous_player_decisions);
};

#endif
