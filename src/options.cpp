#include <cstring>
#include <iostream>

#include "options.hpp"

// usage message
const char *USAGE = R"(usage: checkmate analyze PATH
	--weak_immunity
	--weaker_immunity
	--collusion_resilience
	--practicality
)";

// print a message, the usage information and exit with failure code
[[noreturn]] static void bail(const char *msg) {
	std::cerr << "checkmate: " << msg << std::endl;
	std::cerr << USAGE;
	std::exit(EXIT_FAILURE);
}

using std::strcmp;

Options::Options(char **argv) {
	// skip name of program, we don't care
	if(*argv) argv++;

	if(!strcmp(*argv, "--help")) {
		std::cerr << USAGE;
		std::exit(EXIT_SUCCESS);
	}

	if(!*argv)
		bail("expected a mode");
	if(strcmp(*argv, "analyze"))
		bail("expected mode to be 'analyze'");
	mode = Mode::ANALYZE;
	argv++;

	if(!*argv)
		bail("expected an input path");
	input_path = *argv;
	argv++;

	// other flags
	while(*argv) {
		if(!strcmp(*argv, "--weak_immunity"))
			weak_immunity = true;
		if(!strcmp(*argv, "--weaker_immunity"))
			weaker_immunity = true;
		if(!strcmp(*argv, "--collusion_resilience"))
			collusion_resilience = true;
		if(!strcmp(*argv, "--practicality"))
			practicality = true;
		argv++;
	}

	// analyze everything by default
	if(!weak_immunity && !weaker_immunity && !collusion_resilience && !practicality)
		weak_immunity = weaker_immunity = collusion_resilience = practicality = true;
}
