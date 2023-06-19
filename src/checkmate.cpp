#include "input.hpp"
#include "options.hpp"
#include "solver.hpp"
#include "weak_immunity.hpp"

int main(int argc, char **argv) {
	(void) argc;
	Options opts(argv);
	Input input(opts.input_path);
	Solver<WeakImmunity> solver(input);
	solver.solve();
	return EXIT_SUCCESS;
}
