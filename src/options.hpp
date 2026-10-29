#ifndef __checkmate_options__
#define __checkmate_options__

// program options
struct Options {
	// parse options from `argv` - exits the program on failure
	Options(char **argv);

	// print a message, the usage information and exit with failure code
	[[noreturn]] static void bail(const char *msg);

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
	// procude weakest precondition (implying the initial constraints) to make property satisfied
	bool preconditions = false;
	// provide witness strategy in case property satisfied
	bool strategies = false;
	// write verdicts, cases, strategies and counterexamples as JSON to this file
	const char *json_out = nullptr;

	// options for "compositionality feature"
	// reason over a subtree, to be plugged into a supertree later
	bool subtree = false;

	// only for CEFGs: check that the conditions of condition nodes do not overlap and leave no gap (on by default)
	bool validate_conditions = true;

	// used for experiments
	bool count_nodes = false;
	bool count_calls = false;

	// disable optimizations/heuristics, for testing that they do not change results
	bool no_cr_node_cache = false;
	bool no_cr_leaf_cache = false;
	bool no_cr_implied_groups = false;
	bool no_cr_violated_lookup = false;
	bool no_problematic_groups = false;
	bool exact_splits = false;
	bool reset_from_root = false;
};

#endif
