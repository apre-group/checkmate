#include "input.hpp"
#include "options.hpp"
#include "property.hpp"

#include <iostream>

int main(int, char **argv) {
	Options opts(argv);
	Input input(opts.input_path);

	std::cout << "weak immunity" << std::endl;
	weak_immunity<false>(input);
	std::cout << "weaker immunity" << std::endl;
	weak_immunity<true>(input);
	std::cout << "collusion resilience" << std::endl;
	collusion_resilience(input);
	std::cout << "practicality" << std::endl;
	practicality(input);

	return EXIT_SUCCESS;
}
