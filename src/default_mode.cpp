#include "default_mode.hpp"
#include "property_checks.hpp"

void default_mode(const Options &options, const Input &input, const UtilityTuplesSet &ustar) {
	// the chosen properties, with how to name them in the result
	struct ChosenProperty {
		bool chosen;
		PropertyType property;
		const char *name;
	};
	std::vector<ChosenProperty> properties = {
		{options.weak_immunity, PropertyType::WeakImmunity, "weak immune"},
		{options.weaker_immunity, PropertyType::WeakerImmunity, "weaker immune"},
		{options.collusion_resilience, PropertyType::CollusionResilience, "collusion resilient"},
		{options.practicality, PropertyType::Practicality, "practical"}
	};

	for (const ChosenProperty &property : properties) {
		if (!property.chosen) {
			continue;
		}
		if (satisfiesProperty(input, ustar, property.property)) {
			std::cout << "YES, the game is " << property.name << " for the analyzed history." << std::endl;
		} else {
			std::cout << "NO, the game is not " << property.name << " for the analyzed history." << std::endl;
		}
	}
}


// Algorithm 3 (SatisfiesProperty), with IC the initial constraints together with the constraints of the property
bool satisfiesProperty(const Input &input, const UtilityTuplesSet &ustar, PropertyType property) {
	switch (property) {
		case PropertyType::WeakImmunity:
		case PropertyType::WeakerImmunity: {
			bool weaker = property == PropertyType::WeakerImmunity;
			z3::Bool ic = property_constraints(input, property);
			for (unsigned player = 0; player < input.players.size(); player++) {
				z3::Bool result = computeCWI(input, input.root.get(), ic, player, weaker);
				if (violated_somewhere(ic, result)) {
					return false;
				}
			}
			return true;
		}
		case PropertyType::CollusionResilience: {
			z3::Bool ic = property_constraints(input, property);
			// start with no conditions so far and the empty group
			z3::Bool result = computeCCR(input, ustar, z3::Bool(true), 0);
			return !violated_somewhere(ic, result);
		}
		case PropertyType::Practicality:
			return computeCPR(input);
	}
	assert(false);
	return false;
}
