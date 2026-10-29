#ifndef __checkmate_cefg_options__
#define __checkmate_cefg_options__

// imported from the cefg branch (c9c6e6f); wrapped in namespace cefg next to the EFG engine in src/
namespace cefg {

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

	// options for "compositionality feature"
	// reason over a subtree, to be plugged into a supertree later
	bool subtree = false;

	// write the results as JSON to this file: the verdicts in default mode, the subtree results in subtree mode
	const char *json_out = nullptr;

	// future options
	// compute counterexamples
	// bool counterexamples = false;
	// // compute all available counterexamples
	// bool all_counterexamples = false;
	// // continue to more cases even when one failed
	// bool all_cases = false;
	// // procude weakest precondition (implying the initial constraints) to make property satisfied
	// bool preconditions = false;
	// // provide witness strategy in case property satisfied
	// bool strategies = false;
	//
	// // used for experiments
	// bool count_nodes = false;
	// bool count_calls = false;
};

} // namespace cefg

#endif
