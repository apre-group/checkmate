#ifndef __checkmate_property__
#define __checkmate_property__

struct Input;
struct Options;

using UtilityTuple = std::vector<Utility>;
using UtilityTuplesSet = std::unordered_set<UtilityTuple, std::hash<UtilityTuple>>;

void analyse_properties(const Options &options, const Input &input);

UtilityTuplesSet practicality_rec(z3::Solver *solver, const Options &options, Node *node, std::vector<z3::Bool> current_case);

bool practicality_admin(z3::Solver *solver, const Options &options, Node *root, std::vector<z3::Bool> current_case);


#endif
