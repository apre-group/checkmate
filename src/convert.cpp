// checkmate-convert: convert a game between JSON and the compact format.
#include <cstring>
#include <fstream>
#include <iostream>
#include <iterator>

#include "compact.hpp"
#include "game_type.hpp"

int main(int argc, char **argv) {
	if (argc < 2 || argc > 3 || !std::strcmp(argv[1], "--help")) {
		std::cerr << "usage: checkmate-convert GAME [OUTPUT]\n"
			"\tconverts a game in JSON to the compact format, and one in the compact format to JSON\n";
		return argc == 2 ? EXIT_SUCCESS : EXIT_FAILURE;
	}
	std::ifstream in(argv[1]);
	if (!in) {
		std::cerr << "checkmate-convert: cannot read " << argv[1] << std::endl;
		return EXIT_FAILURE;
	}
	std::string text((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
	std::string result;
	try {
		// CEFGs (games with condition nodes or unknown constants) are checked as checkmate checks them
		auto validate = [](const nlohmann::json &game, const LineMap *lines) {
			std::string reason;
			if (detect_game_type(game, reason) == GameType::CEFG)
				validate_cefg(game, lines);
			else
				validate_game(game, lines);
		};
		if (looks_like_json(text)) {
			nlohmann::json game = nlohmann::json::parse(text);
			validate(game, nullptr);
			result = to_compact(game);
		} else {
			LineMap lines;
			nlohmann::json game = from_compact(text, &lines);
			validate(game, &lines);
			result = game.dump(2) + "\n";
		}
	} catch (const nlohmann::json::exception &e) {
		std::cerr << "checkmate-convert: " << e.what() << std::endl;
		return EXIT_FAILURE;
	} catch (const CompactError &e) {
		std::cerr << "checkmate-convert: " << e.what() << std::endl;
		return EXIT_FAILURE;
	} catch (const GameError &e) {
		std::cerr << "checkmate-convert: " << e.what() << std::endl;
		return EXIT_FAILURE;
	}
	if (argc == 3) {
		std::ofstream out(argv[2]);
		if (!(out << result)) {
			std::cerr << "checkmate-convert: cannot write " << argv[2] << std::endl;
			return EXIT_FAILURE;
		}
	} else {
		std::cout << result;
	}
	return EXIT_SUCCESS;
}
