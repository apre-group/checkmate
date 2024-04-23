#include "input.hpp"
#include "options.hpp"
#include "property.hpp"

int main(int, char **argv) {
	Options options(argv);
	Input input(options.input_path);

	if (options.weak_immunity)
		weak_immunity(options, input);
	if (options.collusion_resilience)
		collusion_resilience(options, input);
	if (options.practicality)
		practicality(options, input);

	return EXIT_SUCCESS;
}
