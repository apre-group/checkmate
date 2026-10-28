#include <cstring>
#include <iostream>
#include <string>
#include <vector>

#include "game_type.hpp"
#include "input.hpp"
#include "options.hpp"
#include "property.hpp"
#include "cefg/run.hpp"

// analyse a CEFG with the analysis in src/cefg/, leaving out the options it does not support (with a warning)
static int run_cefg(char **argv) {
	// options the CEFG analysis understands
	static const char *SUPPORTED[] = {"--weak_immunity", "--weaker_immunity", "--collusion_resilience", "--practicality", "--subtree"};
	// options of the EFG analysis that the CEFG analysis does not have yet
	static const char *NOT_YET[] = {"--counterexamples", "--all_counterexamples", "--preconditions", "--strategies"};

	auto among = [](const char *option, const char *const *list, size_t size) {
		for (size_t i = 0; i < size; i++) {
			if (!std::strcmp(option, list[i])) {
				return true;
			}
		}
		return false;
	};

	// program name and input path, then the supported options
	std::vector<char *> arguments = {argv[0], argv[1]};
	for (char **option = argv + 2; *option; option++) {
		if (among(*option, SUPPORTED, sizeof SUPPORTED / sizeof *SUPPORTED)) {
			arguments.push_back(*option);
		} else if (among(*option, NOT_YET, sizeof NOT_YET / sizeof *NOT_YET)) {
			std::cerr << "checkmate: " << *option << " is not yet implemented for CEFGs and is ignored" << std::endl;
		} else {
			// Options already rejected unknown options, so this one is for EFGs only
			std::cerr << "checkmate: " << *option << " only applies to EFGs and is ignored" << std::endl;
			if (!std::strcmp(*option, "--json-out")) {
				option++;
			}
		}
	}
	arguments.push_back(nullptr);
	return cefg::run(arguments.data());
}

int main(int, char **argv) {
	// first, as for the EFG analysis before (its results may depend on where Z3 allocates its terms)
	z3::initialize();
	// checks all options, also those that are ignored for CEFGs
	Options options(argv);
	GameFile file = read_game(options.input_path);

	std::string reason;
	if (detect_game_type(file.document, reason) == GameType::CEFG) {
		if (!file.is_json) {
			std::cerr << "checkmate: " << options.input_path << ": games with " << reason
				<< " (CEFGs) are only supported in the JSON format for now" << std::endl;
			return EXIT_FAILURE;
		}
		std::cout << "Game type: CEFG (" << reason << ")" << std::endl;
		return run_cefg(argv);
	}

	if (options.subtree && (options.counterexamples || options.all_counterexamples || options.strategies || options.preconditions)) {
		Options::bail("cannot combine subtree with any other option");
	}

	Input input(options.input_path, std::move(file));

	if (options.subtree){
		// analyse properties in subtree mode
		analyse_properties_subtree(options, input);
	} else {
		// analyse properties in default mode (the tree may contain subtree results)
		analyse_properties(options, input);
		write_json_out(options);
	}

	return EXIT_SUCCESS;
}
