#include "input.hpp"
#include "options.hpp"
#include "property.hpp"

#include <iostream>

int main(int, char **argv) {
	Options options(argv);
	Input input(options.input_path);

	if(options.weak_immunity)
		weak_immunity<false>(options, input);
	if(options.weaker_immunity)
		weak_immunity<true>(options, input);
	if(options.collusion_resilience)
		collusion_resilience(options, input);
	if(options.practicality)
		practicality(input);

	return EXIT_SUCCESS;
}
