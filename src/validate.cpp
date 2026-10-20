#include <cctype>
#include <set>
#include <vector>

#include "validate.hpp"

using json = nlohmann::json;

namespace {

struct Context {
	const LineMap *lines;
	std::set<std::string> players, symbols;

	// "line 7: ..." for the compact format, "in <what>: ..." for JSON
	[[noreturn]] void fail(const std::string &where, const std::string &what, const std::string &message) const {
		if (lines) {
			auto it = lines->find(where);
			if (it != lines->end())
				throw GameError("line " + std::to_string(it->second) + ": " + message);
		}
		throw GameError(what + ": " + message);
	}
};

std::string history_text(const std::vector<std::string> &history) {
	std::string s;
	for (const std::string &a : history)
		s += (s.empty() ? "" : " ") + a;
	return s.empty() ? "(the root)" : s;
}

std::string tree_key(const std::vector<std::string> &history) {
	std::string key = "tree";
	for (const std::string &a : history)
		key += "/" + a;
	return key;
}

// ---- expressions, following the grammar of Parser in input.cpp ---------------------

struct Expression {
	const Context &ctx;
	const std::string &text;
	std::string where, what;
	size_t pos = 0;

	enum Kind { NUMBER, NAME, OP, END };
	struct Token { Kind kind; std::string text; };
	std::vector<Token> tokens;
	size_t next = 0;

	Expression(const Context &ctx, const std::string &text, std::string where, std::string what)
		: ctx(ctx), text(text), where(std::move(where)), what(std::move(what)) {}

	[[noreturn]] void fail(const std::string &message) {
		ctx.fail(where, what, message + " in \"" + text + "\"");
	}

	void lex() {
		while (pos < text.size()) {
			char c = text[pos];
			if (std::isspace(static_cast<unsigned char>(c))) {
				pos++;
			} else if (std::isdigit(static_cast<unsigned char>(c)) || c == '.') {
				size_t start = pos;
				while (pos < text.size() && (std::isdigit(static_cast<unsigned char>(text[pos])) || text[pos] == '.'))
					pos++;
				tokens.push_back({NUMBER, text.substr(start, pos - start)});
			} else if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
				size_t start = pos;
				while (pos < text.size() && (std::isalnum(static_cast<unsigned char>(text[pos])) || text[pos] == '_'))
					pos++;
				std::string name = text.substr(start, pos - start);
				if (!ctx.symbols.count(name))
					fail("undeclared constant " + name);
				tokens.push_back({NAME, name});
			} else {
				std::string two = text.substr(pos, 2);
				if (two == "<=" || two == ">=" || two == "!=") {
					tokens.push_back({OP, two});
					pos += 2;
				} else if (std::string("+-*()=<>|&").find(c) != std::string::npos) {
					tokens.push_back({OP, std::string(1, c)});
					pos++;
				} else {
					fail(std::string("unexpected character '") + c + "'");
				}
			}
		}
		tokens.push_back({END, ""});
	}

	const Token &peek() const { return tokens[next]; }
	bool accept(const std::string &op) {
		if (peek().kind == OP && peek().text == op) {
			next++;
			return true;
		}
		return false;
	}
	static bool comparison(const Token &t) {
		return t.kind == OP && (t.text == "=" || t.text == "!=" || t.text == "<" || t.text == "<=" || t.text == ">" || t.text == ">=");
	}

	// term := product (('+' | '-') product)*, product := unary ('*' unary)*, unary := '-' unary | atom
	void term() {
		product();
		while (accept("+") || accept("-"))
			product();
	}
	void product() {
		unary();
		while (accept("*"))
			unary();
	}
	void unary() {
		if (accept("-"))
			return unary();
		if (peek().kind == NUMBER || peek().kind == NAME) {
			next++;
			return;
		}
		if (accept("(")) {
			term();
			if (!accept(")"))
				fail("missing )");
			return;
		}
		fail(peek().kind == END ? "expression ends too early" : "unexpected \"" + peek().text + "\"");
	}

	// constraint := conjunction ('|' conjunction)*, conjunction := atom ('&' atom)*,
	// atom := term comparison term | '(' constraint ')'
	void constraint() {
		conjunction();
		while (accept("|"))
			conjunction();
	}
	void conjunction() {
		atom();
		while (accept("&"))
			atom();
	}
	void atom() {
		// a parenthesis starts either a term or a constraint: try the term first
		size_t start = next;
		try {
			term();
			if (comparison(peek())) {
				next++;
				term();
				return;
			}
		} catch (const GameError &) {
			if (tokens[start].kind != OP || tokens[start].text != "(")
				throw;
		}
		next = start;
		if (accept("(")) {
			constraint();
			if (!accept(")"))
				fail("missing )");
			return;
		}
		fail("expected a comparison like a >= b");
	}

	void check_utility() {
		lex();
		term();
		if (peek().kind != END)
			fail("unexpected \"" + peek().text + "\"");
	}
	void check_constraint() {
		lex();
		constraint();
		if (peek().kind != END)
			fail("unexpected \"" + peek().text + "\"");
	}
};

void check_names(const Context &ctx, const json &game, const char *key, std::set<std::string> &into, bool required) {
	if (!game.contains(key) || !game[key].is_array()) {
		if (required)
			ctx.fail(key, key, "missing list of " + std::string(key));
		return;
	}
	for (const json &name : game[key]) {
		if (!name.is_string() || name.get<std::string>().empty())
			ctx.fail(key, key, "names must be non-empty strings");
		if (!into.insert(name.get<std::string>()).second)
			ctx.fail(key, key, name.get<std::string>() + " is declared twice");
	}
}

void check_utilities(const Context &ctx, const json &utilities, const std::string &where, const std::string &what) {
	if (!utilities.is_array())
		ctx.fail(where, what, "utilities must be a list");
	std::set<std::string> listed;
	for (const json &u : utilities) {
		if (!u.is_object() || !u.contains("player") || !u.contains("value") || !u["player"].is_string())
			ctx.fail(where, what, "a utility needs a player and a value");
		std::string player = u["player"];
		if (!ctx.players.count(player))
			ctx.fail(where, what, "unknown player " + player);
		if (!listed.insert(player).second)
			ctx.fail(where, what, "utility of " + player + " given twice");
		if (u["value"].is_string())
			Expression(ctx, u["value"].get_ref<const std::string &>(), where, what).check_utility();
		else if (!u["value"].is_number_unsigned())
			ctx.fail(where, what, "the utility of " + player + " must be an expression or a non-negative integer");
	}
	if (listed.size() != ctx.players.size())
		ctx.fail(where, what, "needs a utility for every player");
}

void check_tree(const Context &ctx, const json &node, std::vector<std::string> &history) {
	std::string where = tree_key(history), what = "node at " + history_text(history);
	if (!node.is_object())
		ctx.fail(where, what, "not a node");
	if (node.contains("children")) {
		if (!node.contains("player") || !node["player"].is_string() || !ctx.players.count(node["player"].get<std::string>()))
			ctx.fail(where, what, "the player of a node must be declared in players");
		if (!node["children"].is_array() || node["children"].empty())
			ctx.fail(where, what, "a node of " + node["player"].get<std::string>() + " needs at least one action");
		std::set<std::string> actions;
		for (const json &child : node["children"]) {
			if (!child.is_object() || !child.contains("action") || !child["action"].is_string() || !child.contains("child"))
				ctx.fail(where, what, "every child needs an action and a child");
			std::string action = child["action"];
			if (!actions.insert(action).second)
				ctx.fail(where, what, "action " + action + " appears twice");
			history.push_back(action);
			check_tree(ctx, child["child"], history);
			history.pop_back();
		}
	} else if (node.contains("utility")) {
		check_utilities(ctx, node["utility"], where, what);
	} else if (!node.contains("subtree")) {
		ctx.fail(where, what, "a node must have children, a utility, or a subtree result");
	}
}

void check_honest(const Context &ctx, const json &game, size_t index) {
	std::string where = "honest/" + std::to_string(index), what = "honest history " + std::to_string(index + 1);
	const json &history = game["honest_histories"][index];
	if (!history.is_array())
		ctx.fail(where, what, "must be a list of actions");
	const json *node = &game["tree"];
	std::vector<std::string> so_far;
	for (const json &a : history) {
		if (!a.is_string())
			ctx.fail(where, what, "actions must be strings");
		std::string action = a;
		if (!node->contains("children"))
			ctx.fail(where, what, history_text(so_far) + " already ends at a leaf, but the honest history continues with " + action);
		const json *found = nullptr;
		for (const json &child : (*node)["children"])
			if (child["action"] == action)
				found = &child["child"];
		if (!found)
			ctx.fail(where, what, "no action " + action + " after " + history_text(so_far));
		so_far.push_back(action);
		node = found;
		if (node->contains("subtree"))
			return;
	}
	if (node->contains("children"))
		ctx.fail(where, what, history_text(so_far) + " ends at a node of " + (*node)["player"].get<std::string>() +
			", not at a leaf");
}

}

void validate_game(const json &game, const LineMap *lines) {
	Context ctx{lines, {}, {}};
	if (!game.is_object())
		throw GameError("a game must be a JSON object");
	check_names(ctx, game, "players", ctx.players, true);
	if (ctx.players.empty())
		ctx.fail("players", "players", "the game needs at least one player");
	std::set<std::string> constants, infinitesimals;
	check_names(ctx, game, "constants", constants, false);
	check_names(ctx, game, "infinitesimals", infinitesimals, false);
	ctx.symbols = constants;
	for (const std::string &e : infinitesimals)
		if (!ctx.symbols.insert(e).second)
			ctx.fail("infinitesimals", "infinitesimals", e + " is declared as a constant and as an infinitesimal");

	if (!game.contains("tree"))
		throw GameError("the game has no tree");
	if (!game["tree"].is_object() || !game["tree"].contains("children"))
		ctx.fail("tree", "tree", "the root of the tree must be a node with actions");
	std::vector<std::string> history;
	check_tree(ctx, game["tree"], history);

	if (game.contains("initial_constraints")) {
		const json &cs = game["initial_constraints"];
		for (size_t i = 0; i < cs.size(); i++) {
			if (!cs[i].is_string())
				ctx.fail("initial/" + std::to_string(i), "initial constraint " + std::to_string(i + 1), "must be a string");
			Expression(ctx, cs[i].get_ref<const std::string &>(), "initial/" + std::to_string(i),
				"initial constraint " + std::to_string(i + 1)).check_constraint();
		}
	}
	if (!game.contains("property_constraints") || !game["property_constraints"].is_object())
		throw GameError("the game needs property_constraints, with a list for each property");
	for (const char *p : {"weak_immunity", "weaker_immunity", "collusion_resilience", "practicality"}) {
		if (!game["property_constraints"].contains(p) || !game["property_constraints"][p].is_array())
			throw GameError(std::string("property_constraints needs a list for ") + p);
		const json &cs = game["property_constraints"][p];
		for (size_t i = 0; i < cs.size(); i++) {
			std::string where = std::string("property/") + p + "/" + std::to_string(i);
			std::string what = std::string(p) + " constraint " + std::to_string(i + 1);
			if (!cs[i].is_string())
				ctx.fail(where, what, "must be a string");
			Expression(ctx, cs[i].get_ref<const std::string &>(), where, what).check_constraint();
		}
	}

	size_t honest = 0;
	if (game.contains("honest_histories")) {
		if (!game["honest_histories"].is_array())
			throw GameError("honest_histories must be a list of histories");
		for (size_t i = 0; i < game["honest_histories"].size(); i++)
			check_honest(ctx, game, i);
		honest += game["honest_histories"].size();
	}
	if (game.contains("honest_utilities")) {
		const json &us = game["honest_utilities"];
		for (size_t i = 0; i < us.size(); i++) {
			std::string where = "honest_utility/" + std::to_string(i), what = "honest utility " + std::to_string(i + 1);
			if (!us[i].is_object() || !us[i].contains("utility"))
				ctx.fail(where, what, "must have a utility");
			check_utilities(ctx, us[i]["utility"], where, what);
		}
		honest += us.size();
	}
	if (!honest)
		throw GameError("the game needs an honest history (honest: ...), or honest utilities for a subtree");
}
