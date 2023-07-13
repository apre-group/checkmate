#include "input.hpp"
#include "options.hpp"
#include "solver.hpp"

#include <iostream>

int main(int, char **argv) {
	Options opts(argv);
	Input input(opts.input_path);
	Solver solver(input);

	std::cout << "weak immunity" << std::endl;
	solver.weak_immunity<false>();
	std::cout << "weaker immunity" << std::endl;
	solver.weak_immunity<true>();
	std::cout << "collusion resilience" << std::endl;
	solver.collusion_resilience();
	std::cout << "practicality" << std::endl;
	solver.practicality();

	return EXIT_SUCCESS;
}