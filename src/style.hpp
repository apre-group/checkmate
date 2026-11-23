#ifndef __checkmate_style__
#define __checkmate_style__

#include <iostream>
#include <string>

// Terminal colours in checkmate's output, if style::on (see --color).
namespace style {
	inline bool on = false;

	inline std::string paint(const char *code, const std::string &text) {
		return on ? std::string("\033[") + code + "m" + text + "\033[0m" : text;
	}
	inline std::string bold(const std::string &text) { return paint("1", text); }
	inline std::string dim(const std::string &text) { return paint("2", text); }
	inline std::string yes() { return paint("1;32", "YES"); }
	inline std::string no() { return paint("1;31", "NO"); }
	inline std::string unknown() { return paint("1;33", "UNKNOWN"); }
	inline std::string verdict(bool holds) { return holds ? yes() : no(); }
	// conditions on the values (cases, preconditions)
	inline std::string condition(const std::string &text) { return paint("36", text); }
	// actions and histories
	inline std::string play(const std::string &text) { return paint("35", text); }

	// the line above the verdicts of a run, with a blank line between runs
	inline void heading(const std::string &title, const std::string &what) {
		static bool first = true;
		if (!first)
			std::cout << std::endl;
		first = false;
		std::cout << bold(title) << (what.empty() ? "" : " " + what) << std::endl;
	}
}

#endif
