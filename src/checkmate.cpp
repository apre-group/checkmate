#include "input.hpp"
#include "options.hpp"
#include "property.hpp"

int main(int, char **argv) {
	Options options(argv);
	Input input(options.input_path, options.supertree);

	if (options.subtree){
		analyse_properties_subtree(options, input);
	} else if (options.supertree) {
		analyse_properties_supertree(options, input);
	} else {
		analyse_properties(options, input);
	}

	return EXIT_SUCCESS;
}
