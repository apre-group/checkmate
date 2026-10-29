#include <cstring>
#include <iostream>

#include "options.hpp"

// usage message
const char *USAGE = R"(usage: checkmate PATH
	--weak_immunity
	--weaker_immunity
	--collusion_resilience
	--practicality
	--subtree
	--json-out FILE
only for CEFGs (games with condition nodes), ignored for EFGs:
	--no_validate_conditions  do not check that the conditions of a condition node
	                          are mutually exclusive and leave no gap
not yet implemented for CEFGs (games with condition nodes), ignored for them:
	--counterexamples
	--all_counterexamples
	--preconditions
	--strategies
only for EFGs (games without condition nodes), ignored for CEFGs:
	--all_cases
	--count_nodes
	--count_calls
testing only, disable optimizations/heuristics (only for EFGs):
	--no-cr-node-cache
	--no-cr-leaf-cache
	--no-cr-implied-groups
	--no-cr-violated-lookup
	--no-problematic-groups
	--exact-splits
	--reset-from-root
)";

// print a message, the usage information and exit with failure code
[[noreturn]] void Options::bail(const char *msg) {
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
		else if (!strcmp(*argv, "--json-out")) {
			if (!argv[1])
				bail("--json-out expects a file name");
			json_out = *++argv;
		}
		else if (!strcmp(*argv, "--subtree"))
			subtree = true;
		else if (!strcmp(*argv, "--no_validate_conditions"))
			validate_conditions = false;
		else if (!strcmp(*argv, "--count_nodes"))
			count_nodes = true;
		else if (!strcmp(*argv, "--count_calls"))
			count_calls = true;
		else if (!strcmp(*argv, "--no-cr-node-cache"))
			no_cr_node_cache = true;
		else if (!strcmp(*argv, "--no-cr-leaf-cache"))
			no_cr_leaf_cache = true;
		else if (!strcmp(*argv, "--no-cr-implied-groups"))
			no_cr_implied_groups = true;
		else if (!strcmp(*argv, "--no-cr-violated-lookup"))
			no_cr_violated_lookup = true;
		else if (!strcmp(*argv, "--no-problematic-groups"))
			no_problematic_groups = true;
		else if (!strcmp(*argv, "--exact-splits"))
			exact_splits = true;
		else if (!strcmp(*argv, "--reset-from-root"))
			reset_from_root = true;
		else
			bail("unknown option");
		argv++;
	}

	// analyze everything by default
	if (!weak_immunity && !weaker_immunity && !collusion_resilience && !practicality)
		weak_immunity = weaker_immunity = collusion_resilience = practicality = true;
}
