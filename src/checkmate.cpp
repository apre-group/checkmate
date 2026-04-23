#include "input.hpp"
#include "options.hpp"
#include "property.hpp"

int main(int, char **argv) {
	Options options(argv);
	Input input(options.input_path);

	if (options.subtree){
		// analyse properties in subtree mode
		analyse_properties_subtree(options, input);
	} else {
		// analyse properties in default mode 
		analyse_properties(options, input);
	}

	return EXIT_SUCCESS;
}
