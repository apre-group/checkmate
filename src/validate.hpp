#ifndef __checkmate_validate__
#define __checkmate_validate__

#include <map>
#include <stdexcept>
#include <string>

#include "json.hpp"

struct GameError : std::runtime_error {
	using std::runtime_error::runtime_error;
};

// Where things are in a compact file: "initial/0", "property/practicality/1", "honest/2",
// "honest_utility/0", "players", and "tree" or "tree/a/b" for the node reached by actions a, b.
using LineMap = std::map<std::string, size_t>;

// Check a game before it is analysed, so mistakes get a clear message (with a line number for the
// compact format) instead of a crash or a confusing error later. Throws GameError.
void validate_game(const nlohmann::json &game, const LineMap *lines = nullptr);

// The same for a CEFG (a game with condition nodes or unknown constants, see game_type.hpp), which is JSON only.
// Throws GameError.
void validate_cefg(const nlohmann::json &game);

#endif
