#include "input.hpp"
#include "options.hpp"
#include "property.hpp"

int main(int, char **argv) {
	Options options(argv);
	Input input(options.input_path, options.supertree);

	const Subtree &subtree = input.root.get()->branch().choices[1].node->subtree();
	std::cout << "size of wi: " << subtree.weak_immunity.size() << std::endl;
	// std::cout << "wi[0]: " << subtree.weak_immunity[0].player_group << " sat in " <<  subtree.weak_immunity[0].satisfied_in_case << std::endl;
	// std::cout << "wi[1]: " << subtree.weak_immunity[1].player_group << " sat in " <<  subtree.weak_immunity[1].satisfied_in_case << std::endl;
	// std::cout << "wi[2]: " << subtree.weak_immunity[2].player_group << " sat in " <<  subtree.weak_immunity[2].satisfied_in_case << std::endl;
	std::cout << "size of weri: " << subtree.weaker_immunity.size() << std::endl;
	std::cout << "size of cr: " << subtree.collusion_resilience.size() << std::endl;
	std::cout << "size of pr: " << subtree.practicality.size() << std::endl;


	if (options.subtree){
		analyse_properties_subtree(options, input);
	} else {
		//std::cout<< "before calling analyse_properties from main" << std::endl;
		analyse_properties(options, input);
		//std::cout << "after calling analyse_properties from main" << std::endl;
	}

	//std::cout << "before returning from main" << std::endl;
	return EXIT_SUCCESS;
}
