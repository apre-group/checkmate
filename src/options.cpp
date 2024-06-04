#include <cstring>
#include <iostream>
#include <sstream>

#include "options.hpp"

// usage message
const char *USAGE = R"(usage: checkmate PATH
	--weak_immunity
	--weaker_immunity
	--collusion_resilience
	--practicality
	--counterexamples
	--all_counterexamples
	--all_cases
	--preconditions
	--strategies
	--max_unsat N
)";

// print a message, the usage information and exit with failure code
[[noreturn]] static void bail(const char *msg) {
	std::cerr << "checkmate: " << msg << std::endl;
	std::cerr << USAGE;
	std::exit(EXIT_FAILURE);
}

Options::Options(char **argv) {
	using std::strcmp;

	// skip name of program, we don't care
	if (*argv) argv++;

	if (*argv && !strcmp(*argv, "--help")) {
		std::cerr << USAGE;
		std::exit(EXIT_SUCCESS);
	}

	if (!*argv)
		bail("expected an input path");
	input_path = *argv;
	argv++;

	// other flags
	while (*argv) {
		if (!strcmp(*argv, "--weak_immunity"))
			weak_immunity = true;
		else if (!strcmp(*argv, "--weaker_immunity"))
			weaker_immunity = true;
		else if (!strcmp(*argv, "--collusion_resilience"))
			collusion_resilience = true;
		else if (!strcmp(*argv, "--practicality"))
			practicality = true;
		else if (!strcmp(*argv, "--counterexamples"))
			counterexamples = true;
		else if (!strcmp(*argv, "--all_counterexamples"))
			counterexamples = all_counterexamples = true;
		else if (!strcmp(*argv, "--all_cases"))
			all_cases = true;
		else if (!strcmp(*argv, "--preconditions"))
			preconditions = true;
		else if (!strcmp(*argv, "--strategies"))
			strategies = true;
		else if (!strcmp(*argv, "--max_unsat")) {
			argv++; 
			if(!*argv) bail("max_unsat expects an argument");
			std::stringstream ss(*argv);
			if (!(ss >> max_unsat)){
				bail("max_unsat expects a positive integer");
			}
		}
		else
			bail("unknown option");
		argv++;
	}

	// analyze everything by default
	if (!weak_immunity && !weaker_immunity && !collusion_resilience && !practicality)
		weak_immunity = weaker_immunity = collusion_resilience = practicality = true;
}
