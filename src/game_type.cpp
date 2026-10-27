#include <cerrno>
#include <cstring>
#include <fstream>
#include <iostream>
#include <iterator>

#include "compact.hpp"
#include "game_type.hpp"

using json = nlohmann::json;

GameFile read_game(const char *path) {
	std::ifstream input(path);
	GameFile file;
	try {
		input.exceptions(std::ifstream::failbit | std::ifstream::badbit);
		std::string text((std::istreambuf_iterator<char>(input)), std::istreambuf_iterator<char>());
		file.is_json = looks_like_json(text);
		file.document = file.is_json ? json::parse(text) : from_compact(text, &file.lines);
	}
	catch (const std::ifstream::failure &fail) {
		std::cerr << "checkmate: " << std::strerror(errno) << std::endl;
		std::exit(EXIT_FAILURE);
	}
	catch (const json::exception &err) {
		std::cerr << "checkmate: " << err.what() << std::endl;
		std::exit(EXIT_FAILURE);
	}
	catch (const CompactError &err) {
		std::cerr << "checkmate: " << path << ": " << err.what() << std::endl;
		std::exit(EXIT_FAILURE);
	}
	return file;
}

// the reason why the tree below `node` makes the game a CEFG, or the empty string
static std::string cefg_node(const json &node) {
	if (!node.is_object()) {
		return "";
	}
	// a list of conditions with their children (a string "True" is written by older versions of examples/dsl.py
	// on every node, and ignored)
	if (node.contains("condition") && node["condition"].is_array()) {
		return "condition nodes";
	}
	if (node.contains("subtree") && node["subtree"].is_array()) {
		return "subtree results of a CEFG";
	}
	if (node.contains("children") && node["children"].is_array()) {
		for (const json &child : node["children"]) {
			if (child.is_object() && child.contains("child")) {
				std::string reason = cefg_node(child["child"]);
				if (!reason.empty()) {
					return reason;
				}
			}
		}
	}
	return "";
}

// does `declarations` (constants or infinitesimals) declare unknown ones?
static bool declares_unknowns(const json &declarations) {
	return declarations.is_object() && declarations.contains("unknown") && declarations["unknown"].is_array()
		&& !declarations["unknown"].empty();
}

GameType detect_game_type(const json &game, std::string &reason) {
	if (game.contains("tree")) {
		reason = cefg_node(game["tree"]);
		if (!reason.empty()) {
			return GameType::CEFG;
		}
	}
	for (const char *key : {"constants", "infinitesimals"}) {
		if (game.contains(key) && declares_unknowns(game[key])) {
			reason = "unknown constants";
			return GameType::CEFG;
		}
	}
	// an honest utility with several utility tuples is a list of conditional branches instead of a list of utilities
	if (game.contains("honest_utilities") && game["honest_utilities"].is_array()) {
		for (const json &honest : game["honest_utilities"]) {
			if (!honest.is_object() || !honest.contains("utility") || !honest["utility"].is_array()) {
				continue;
			}
			for (const json &entry : honest["utility"]) {
				if (entry.is_object() && entry.contains("condition")) {
					reason = "an honest utility with several utility tuples";
					return GameType::CEFG;
				}
			}
		}
	}
	reason.clear();
	return GameType::EFG;
}
