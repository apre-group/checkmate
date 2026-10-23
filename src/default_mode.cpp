#include "default_mode.hpp"
#include "property_checks.hpp"
#include "selectors.hpp"

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
		std::string undecided;
		std::optional<bool> satisfied = satisfiesProperty(input, ustar, property.property, undecided);
		if (!satisfied) {
			std::cout << "UNKNOWN, could not decide whether the game is " << property.name << " for the analyzed history: "
				<< undecided << "." << std::endl;
		} else if (*satisfied) {
			std::cout << "YES, the game is " << property.name << " for the analyzed history." << std::endl;
		} else {
			std::cout << "NO, the game is not " << property.name << " for the analyzed history." << std::endl;
		}
	}
}


// Algorithm 3 (SatisfiesProperty), with IC the initial constraints together with the constraints of the property
std::optional<bool> satisfiesProperty(const Input &input, const UtilityTuplesSet &ustar, PropertyType property,
		std::string &undecided) {
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
			// start at the root with no conditions so far and the empty group
			CrCache cache;
			z3::Bool result = computeCCR(input, input.root.get(), ustar, ic, z3::Bool(true), 0, cache);
			return !violated_somewhere(ic, result);
		}
		case PropertyType::Practicality: {
			// without honest history there is no deviation from it to check
			// (and every subgame has a rationalizable utility set)
			if (!input.root->honest) {
				return true;
			}
			z3::Bool ic = property_constraints(input, property);
			z3::Bool result = computeCPR(input, input.root.get(), ustar, ic, z3::Bool(true));
			// with selectors: practical iff ∀ known (IC → result) is satisfiable with the selectors uninterpreted
			std::string how;
			Answer answer = check_practicality(input, ic, result, how);
			if (answer == Answer::UNKNOWN) {
				undecided = how;
				return std::nullopt;
			}
			return answer == Answer::YES;
		}
	}
	assert(false);
	return false;
}
