#ifndef __checkmate_report__
#define __checkmate_report__

#include <string>
#include <vector>

#include "style.hpp"
#include "utility.hpp"
#include "z3++.hpp"

// Pieces of checkmate's output for people to read.
namespace report {
	inline std::string join(const std::vector<std::string> &parts, const std::string &separator) {
		std::string result;
		for (size_t i = 0; i < parts.size(); i++)
			result += (i ? separator : "") + parts[i];
		return result;
	}

	// a, b and c
	inline std::string list(const std::vector<std::string> &parts) {
		if (parts.size() <= 1)
			return parts.empty() ? "" : parts[0];
		return join(std::vector<std::string>(parts.begin(), parts.end() - 1), ", ") + " and " + parts.back();
	}

	inline std::string history(const std::vector<std::string> &h) {
		std::vector<std::string> painted;
		for (const std::string &a : h)
			painted.push_back(style::play(a));
		return h.empty() ? style::play("(empty)") : join(painted, " → ");
	}

	inline std::string after(const std::vector<std::string> &h) {
		return h.empty() ? "at the start" : "after " + history(h);
	}

	// one of several actions: a or b
	inline std::string actions(const std::vector<std::string> &as) {
		std::vector<std::string> painted;
		for (const std::string &a : as)
			painted.push_back(style::play(a));
		return join(painted, " or ");
	}

	inline std::string conditions(const std::vector<z3::Bool> &c) {
		std::vector<std::string> parts;
		for (z3::Bool b : c)
			parts.push_back(z3::pretty(b));
		return style::condition(join(parts, " and "));
	}

	// "when a > 0: " for a case, nothing for the case without conditions
	inline std::string when(const std::vector<z3::Bool> &c) {
		return c.empty() ? "" : "when " + conditions(c) + ": ";
	}

	// Bob, or Alice and Bob together
	inline std::string group(const std::vector<std::string> &players) {
		return players.size() == 1 ? players[0] : list(players) + " together";
	}

	inline std::string utility(Utility u) {
		std::string real = z3::pretty(u.real), infinitesimal = z3::pretty(u.infinitesimal);
		if (infinitesimal == "0")
			return real;
		return real == "0" ? infinitesimal : real + " + " + infinitesimal;
	}

	// A: 1, B: x
	inline std::string utilities(const std::vector<std::string> &players, const std::vector<Utility> &leaf) {
		std::vector<std::string> parts;
		for (size_t i = 0; i < leaf.size() && i < players.size(); i++)
			parts.push_back(players[i] + ": " + utility(leaf[i]));
		return join(parts, ", ");
	}
}

#endif
