#ifndef __checkmate_compact__
#define __checkmate_compact__

#include <stdexcept>
#include <string>

#include "json.hpp"
#include "validate.hpp"

// The compact, human-readable game format (see README.md), and conversion to and from JSON.

struct CompactError : std::runtime_error {
	using std::runtime_error::runtime_error;
};

// throws CompactError if the game cannot be written compactly (e.g. names with spaces)
std::string to_compact(const nlohmann::json &game);

// throws CompactError with the line number of the problem; `lines` records where things are, for validate_game
nlohmann::json from_compact(const std::string &text, LineMap *lines = nullptr);

// does this file content look like JSON rather than the compact format?
bool looks_like_json(const std::string &text);

#endif
