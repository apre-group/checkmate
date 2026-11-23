#include "default_mode.hpp"
#include "property_checks.hpp"
#include "selectors.hpp"
#include "../style.hpp"

// imported from the cefg branch (c9c6e6f); wrapped in namespace cefg next to the EFG engine in src/
namespace cefg {

void default_mode(const Options &options, const Input &input, const UtilityTuplesSet &ustar,
		nlohmann::json &results, const nlohmann::json &run) {
	// the chosen properties, with how to name them in the output and in the JSON result
	struct ChosenProperty {
		bool chosen;
		PropertyType property;
		const char *name;
		const char *json_name;
	};
	std::vector<ChosenProperty> properties = {
		{options.weak_immunity, PropertyType::WeakImmunity, "weak immunity", "weak_immunity"},
		{options.weaker_immunity, PropertyType::WeakerImmunity, "weaker immunity", "weaker_immunity"},
		{options.collusion_resilience, PropertyType::CollusionResilience, "collusion resilience", "collusion_resilience"},
		{options.practicality, PropertyType::Practicality, "practicality", "practicality"}
	};

	for (const ChosenProperty &property : properties) {
		if (!property.chosen) {
			continue;
		}
		std::string undecided;
		std::optional<bool> satisfied = satisfiesProperty(input, ustar, property.property, undecided);
		std::cout << "  " << property.name << ": " << (satisfied ? style::verdict(*satisfied) : style::unknown()) << std::endl;
		if (!satisfied)
			std::cout << "    could not decide it: " << undecided << std::endl;

		// as for EFGs, but `holds` is null if undecided (strategies and counterexamples are not implemented yet)
		nlohmann::json entry = run;
		entry["property"] = property.json_name;
		entry["holds"] = satisfied ? nlohmann::json(*satisfied) : nlohmann::json(nullptr);
		if (!satisfied) {
			entry["undecided"] = undecided;
		}
		entry["strategies"] = nlohmann::json::array();
		entry["counterexamples"] = nlohmann::json::array();
		results.push_back(entry);
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

} // namespace cefg
