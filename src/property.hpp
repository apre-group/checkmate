#ifndef __checkmate_property__
#define __checkmate_property__

struct Input;
struct Options;


std::vector<std::string> index2player(const Input &input, unsigned index);

void analyse_properties(const Options &options, const Input &input);

void analyse_properties_subtree(const Options &options, const Input &input);


#endif
