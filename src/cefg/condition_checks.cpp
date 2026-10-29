#include <algorithm>
#include <iostream>
#include <iterator>
#include <optional>
#include <sstream>
#include <string>
#include <vector>

#include "condition_checks.hpp"
#include "property_checks.hpp"

namespace cefg {

// per satisfiability check; a check Z3 cannot decide in time is skipped with a warning
static const unsigned CONDITION_CHECK_TIMEOUT = 10000;

namespace {

struct ConditionChecker {
	const Options &options;
	// the constraints the conditions are checked under, and how to name them in messages
	z3::Bool constraints;
	std::string constraints_name;

	// where the node reached by `path` is: actions, and "condition N" (from 1) below condition nodes
	static std::string where(const std::vector<std::string> &path) {
		if (path.empty())
			return "at the root";
		std::string result = "after ";
		for (size_t i = 0; i < path.size(); i++)
			result += (i ? ", " : "") + path[i];
		return result;
	}

	static std::string condition_text(const ConditionChoice &choice, size_t index) {
		std::stringstream text;
		text << choice.condition;
		// comparisons are printed in brackets already
		std::string condition = text.str();
		if (condition.empty() || condition.front() != '(')
			condition = "(" + condition + ")";
		return "condition " + std::to_string(index + 1) + " " + condition;
	}

	[[noreturn]] void fail(const std::string &message) const {
		std::cerr << "checkmate: " << options.input_path << ": " << message
			<< " (turn this check off with --no_validate_conditions)" << std::endl;
		std::exit(EXIT_FAILURE);
	}

	// is `formula` satisfiable together with the constraints and `cond`? Warns with `what` if Z3 gives up
	std::optional<bool> satisfiable(const z3::Bool &cond, const z3::Bool &formula, const std::string &what) const {
		std::optional<bool> answer = holds_somewhere(all_of({constraints, cond}), formula, CONDITION_CHECK_TIMEOUT);
		if (!answer)
			std::cerr << "checkmate: warning: could not check whether " << what << ", Z3 gave up" << std::endl;
		return answer;
	}

	// check the condition nodes in the tree at `node`, reached by `path` under the conditions `cond`
	void check(const Node *node, const z3::Bool &cond, std::vector<std::string> &path) const {
		if (node->is_branch()) {
			for (const Choice &choice : node->branch().choices) {
				path.push_back(choice.action);
				check(choice.node.get(), cond, path);
				path.pop_back();
			}
			return;
		}
		if (!node->is_condition_node())
			// leaves, and subtrees, whose conditions were checked when they were analysed
			return;

		const std::vector<ConditionChoice> &conditions = node->condition_node().conditions;
		std::string at = "the condition node " + where(path);

		// relaxed (R3): the constraints may rule out some conditions, but not all of them
		std::vector<size_t> reachable, excluded;
		for (size_t i = 0; i < conditions.size(); i++) {
			std::optional<bool> possible = satisfiable(cond, conditions[i].condition,
				condition_text(conditions[i], i) + " of " + at + " can hold");
			(possible.value_or(true) ? reachable : excluded).push_back(i);
		}
		if (reachable.empty())
			fail("no condition of " + at + " can hold" + given());
		for (size_t i : excluded)
			std::cerr << "checkmate: note: " << condition_text(conditions[i], i) << " of " << at << " can never hold"
				<< given() << std::endl;

		// (R1) mutually exclusive
		for (size_t i = 0; i < reachable.size(); i++) {
			for (size_t j = i + 1; j < reachable.size(); j++) {
				const ConditionChoice &a = conditions[reachable[i]], &b = conditions[reachable[j]];
				std::string pair = condition_text(a, reachable[i]) + " and " + condition_text(b, reachable[j]) + " of " + at;
				if (satisfiable(cond, all_of({a.condition, b.condition}), pair + " overlap").value_or(false))
					fail(pair + " overlap: both hold for some values" + given());
			}
		}

		// (R2) collectively exhaustive
		std::vector<z3::Bool> all;
		for (const ConditionChoice &choice : conditions)
			all.push_back(choice.condition);
		if (satisfiable(cond, !any_of(all), "the conditions of " + at + " leave a gap").value_or(false))
			fail("the conditions of " + at + " leave a gap: no condition holds for some values" + given());

		for (size_t i : reachable) {
			path.push_back("condition " + std::to_string(i + 1));
			check(conditions[i].node.get(), all_of({cond, conditions[i].condition}), path);
			path.pop_back();
		}
	}

	std::string given() const {
		return " (given " + constraints_name + " and the conditions on the way)";
	}
};

} // namespace

void check_conditions(const Input &input, const Options &options) {
	struct Property {
		bool chosen;
		PropertyType type;
		const char *name;
	};
	const Property properties[] = {
		{options.weak_immunity, PropertyType::WeakImmunity, "weak immunity"},
		{options.weaker_immunity, PropertyType::WeakerImmunity, "weaker immunity"},
		{options.collusion_resilience, PropertyType::CollusionResilience, "collusion resilience"},
		{options.practicality, PropertyType::Practicality, "practicality"},
	};

	// the analysed properties grouped by the constraints they are analysed under: usually all share the initial constraints
	std::vector<std::pair<z3::Bool, std::vector<const char *>>> groups;
	for (const Property &property : properties) {
		if (!property.chosen)
			continue;
		z3::Bool constraints = property_constraints(input, property.type);
		auto group = std::find_if(groups.begin(), groups.end(), [&](const auto &g) { return g.first.is(constraints); });
		if (group == groups.end()) {
			groups.push_back({constraints, {}});
			group = std::prev(groups.end());
		}
		// name the properties that have constraints of their own
		if (!constraints.is(input.initial_constraint))
			group->second.push_back(property.name);
	}

	for (const auto &[constraints, names] : groups) {
		std::string name = "the initial constraints";
		if (!names.empty()) {
			name = "the initial and ";
			for (size_t i = 0; i < names.size(); i++)
				name += std::string(i ? (i + 1 == names.size() ? " and " : ", ") : "") + names[i];
			name += " constraints";
		}
		ConditionChecker checker{options, constraints, name};
		std::optional<bool> consistent = holds_somewhere(z3::Bool(true), constraints, CONDITION_CHECK_TIMEOUT);
		if (!consistent)
			std::cerr << "checkmate: warning: could not check whether " << name << " are satisfiable, Z3 gave up" << std::endl;
		else if (!*consistent)
			checker.fail(name + " are unsatisfiable");
		std::vector<std::string> path;
		checker.check(input.root.get(), z3::Bool(true), path);
	}
}

} // namespace cefg
