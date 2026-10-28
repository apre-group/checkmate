#ifndef __checkmate_game_type__
#define __checkmate_game_type__

#include <string>

#include "json.hpp"
#include "validate.hpp"

// a game as read from a file, in JSON or the compact format
struct GameFile {
	nlohmann::json document;
	bool is_json;
	// where things are in a compact file, for error messages
	LineMap lines;
};

// read the game at `path`, in JSON or the compact format - exits the program on failure
GameFile read_game(const char *path);

// which analysis a game needs: EFGs are analysed as before, conditional extensive form games (CEFGs) by src/cefg/
enum class GameType { EFG, CEFG };

// the type of `game`, with the reason in `reason` if it is a CEFG: a game is a CEFG if it has a condition node,
// declares unknown constants, contains subtree results written by the CEFG analysis, or has an honest utility with
// several utility tuples (if its honest history in a supergame passes a condition node)
GameType detect_game_type(const nlohmann::json &game, std::string &reason);

#endif
