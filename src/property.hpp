#ifndef __checkmate_property__
#define __checkmate_property__

struct Input;
struct Options;



struct PotentialCase {
	UtilityTuplesSet utilities;
	std::vector<z3::Bool> _case;
};

void analyse_properties(const Options &options, const Input &input);

void analyse_properties_subtree(const Options &options, const Input &input);

void analyse_properties_supertree(const Options &options, const Input &input);

std::vector<PotentialCase> practicality_rec(z3::Solver &solver, const Options &options, const Input &input, Node *node, std::vector<z3::Bool> current_case);

bool practicality_admin(z3::Solver *solver, const Options &options, Node *root, std::vector<z3::Bool> current_case);


#endif
