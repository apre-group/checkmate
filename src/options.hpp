#ifndef __checkmate_options__
#define __checkmate_options__

// program options
struct Options {
	// parse options from `argv` - exits the program on failure
	Options(char **argv);

	// input game we should load
	const char *input_path;

	// analyze weak immunity
	bool weak_immunity = false;
	// analyze weaker immunity
	bool weaker_immunity = false;
	// analyze collusion resilience
	bool collusion_resilience = false;
	// analyze practicality
	bool practicality = false;

	// compute counterexamples
	bool counterexamples = false;
	// compute all available counterexamples
	bool all_counterexamples = false;
	// continue to more cases even when one failed
	bool all_cases = false;
};

#endif
