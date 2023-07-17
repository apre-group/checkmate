#include "input.hpp"
#include "options.hpp"
#include "property.hpp"

#include <iostream>

int main(int, char **argv) {
	Options opts(argv);
	Input input(opts.input_path);

	if(opts.weak_immunity)
		weak_immunity<false>(input);
	if(opts.weaker_immunity)
		weak_immunity<true>(input);
	if(opts.collusion_resilience)
		collusion_resilience(input);
	if(opts.practicality)
		practicality(input);

	return EXIT_SUCCESS;
}
