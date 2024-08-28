#include "input.hpp"
#include "options.hpp"
#include "property.hpp"

int main(int, char **argv) {
	Options options(argv);
	Input input(options.input_path, options.supertree);

	std::cout << "size of wi: " << input.root.get()->branch().choices[1].node->subtree().weak_immunity.size() << std::endl;
	std::cout << "size of weri: " << input.root.get()->branch().choices[1].node->subtree().weaker_immunity.size() << std::endl;
	std::cout << "size of cr: " << input.root.get()->branch().choices[1].node->subtree().collusion_resilience.size() << std::endl;
	std::cout << "size of pr: " << input.root.get()->branch().choices[1].node->subtree().practicality.size() << std::endl;


	if (options.subtree){
		analyse_properties_subtree(options, input);
	} else {
		std::cout<< "before calling analyse_properties from main" << std::endl;
		analyse_properties(options, input);
		std::cout << "after calling analyse_properties from main" << std::endl;
	}

	std::cout << "before returning from main" << std::endl;
	return EXIT_SUCCESS;
}
