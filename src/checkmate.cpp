#include "input.hpp"
#include "options.hpp"
#include "default_mode.hpp"
#include "subtree_mode.hpp"

int main(int, char **argv) {
	Options options(argv);
	Input input(options.input_path);

	if (input.honest.empty() && input.honest_utilities.empty()) {
		std::cerr << "checkmate: the input has neither honest_histories nor honest_utilities, nothing to analyse" << std::endl;
		return EXIT_FAILURE;
	}

	// subtree mode: the results for every honest history and honest utility, written to INPUT.out in the end
	std::vector<SubtreeData> data;

	// analyse the properties chosen in `run_options` in default or subtree mode, with `ustar` the honest utilities;
	// in subtree mode, the result is stored in `data` under `key`,
	// with the honest utility at the end of `history` if the run is for an honest history
	auto run = [&](const Options &run_options, const UtilityTuplesSet &ustar, SubtreeEntryKey key, const HonestHistory *history) {
		if (!options.subtree) {
			default_mode(run_options, input, ustar);
			return;
		}
		Subtree result = subtree_mode(run_options, input, ustar);
		if (history) {
			// the supertree needs the honest utility if its honest history ends in this subtree
			result.honest_utility = honest_history2utility(input.root.get(), *history);
		}
		data.push_back({std::move(key), std::move(result)});
	};

	// first for every honest history...
	for (const HonestHistory &history : input.honest) {
		input.root->reset_honest();
		input.root->mark_honest(history);

		// one run for every honest history inside the subtree nodes the honest history ends in
		std::vector<const Subtree *> subtrees = honest_subtrees(input.root.get());
		for (const std::vector<const SubtreeEntry *> &subtrees_history : honest_subtree_histories(subtrees)) {
			mark_honest_subtree_histories(subtrees, subtrees_history);
			HonestHistory full_history = extend_honest_history(input.root.get(), history);
			std::cout << std::endl << std::endl << "Checking history " << full_history << std::endl;

			UtilityTuplesSet ustar;
			if (options.collusion_resilience) {
				ustar = compute_ustar(input.root.get(), history);
			}
			run(options, ustar, full_history, &history);
		}
	}

	// ...then for every honest utility given in the input (e.g. for a subtree off the honest history)
	if (!input.honest_utilities.empty()) {
		// no node is honest
		input.root->reset_honest();

		// weak(er) immunity and practicality do not depend on the honest utility: check them once
		Options other_options = options;
		other_options.collusion_resilience = false;
		if (other_options.weak_immunity || other_options.weaker_immunity || other_options.practicality) {
			std::cout << std::endl << std::endl << "Checking no honest history" << std::endl;
			run(other_options, UtilityTuplesSet(), std::monostate(), nullptr);
		}

		// collusion resilience: once for every honest utility
		Options cr_options = options;
		cr_options.weak_immunity = cr_options.weaker_immunity = cr_options.practicality = false;
		if (cr_options.collusion_resilience) {
			for (const HonestUtilityTuple &honest_utility : input.honest_utilities) {
				std::cout << std::endl << std::endl << "Checking honest utility " << honest_utility.element << std::endl;
				run(cr_options, compute_ustar(honest_utility.element), honest_utility.element, nullptr);
			}
		}
	}

	if (options.subtree) {
		data2json(input, data, options.input_path + std::string(".out"));
	}

	return EXIT_SUCCESS;
}
