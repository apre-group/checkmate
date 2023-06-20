#include "input.hpp"
#include "options.hpp"
#include "solver.hpp"
#include "weak_immunity.hpp"

int main(int argc, char **argv) {
	(void) argc;
	Options opts(argv);
	Input input(opts.input_path);
	Solver solver(input);

	std::cout << "weak immunity" << std::endl;
	solver.solve(weak_immunity<false>);
	std::cout << "weaker immunity" << std::endl;
	solver.solve(weak_immunity<true>);

	return EXIT_SUCCESS;
}
