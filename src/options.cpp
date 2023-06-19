#include <cstring>
#include <iostream>
#include "options.hpp"

const char *USAGE = R"(usage: checkmate MODE PATH
)";

[[noreturn]] static void bail(const char *msg) {
	std::cerr << "checkmate: " << msg << std::endl;
	std::cerr << USAGE;
	std::exit(EXIT_FAILURE);
}

Options::Options(char **argv) {
	// skip name of program, we don't care
	if(*argv) argv++;

	if(!*argv)
		bail("expected a mode");
	if(std::strcmp(*argv, "analyze"))
		bail("expected mode to be 'analyze'");
	mode = Mode::ANALYZE;
	argv++;

	if(!*argv)
		bail("expected an input path");
	input_path = *argv;
}
