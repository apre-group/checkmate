#include "default_mode.hpp"

// TODO: placeholder, only reports what would be checked
void default_mode(const Options &options, [[maybe_unused]] const Input &input, const UtilityTuplesSet &ustar) {
	std::vector<std::pair<bool, std::string>> properties = {
		{options.weak_immunity, "weak immunity"},
		{options.weaker_immunity, "weaker immunity"},
		{options.collusion_resilience, "collusion resilience"},
		{options.practicality, "practicality"}
	};
	for (const auto &property : properties) {
		if (property.first) {
			std::cout << "\twould check " << property.second << std::endl;
		}
	}
	if (options.collusion_resilience) {
		std::cout << "\thonest utilities:" << std::endl;
		for (const UtilityTuple &utility : ustar) {
			std::cout << "\t\t" << utility.leaf << " if " << utility.condition << std::endl;
		}
	}
}
