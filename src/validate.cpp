#include <cctype>
#include <map>
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
// (with `cefg`, the grammar of Parser in cefg/input.cpp: also '/', '=>', '!' and true/false)

struct Expression {
	const Context &ctx;
	const std::string &text;
	std::string where, what;
	bool cefg;
	size_t pos = 0;

	enum Kind { NUMBER, NAME, BOOL, OP, END };
	struct Token { Kind kind; std::string text; };
	std::vector<Token> tokens;
	size_t next = 0;
	// the constants in the expression
	std::set<std::string> used;

	Expression(const Context &ctx, const std::string &text, std::string where, std::string what, bool cefg = false)
		: ctx(ctx), text(text), where(std::move(where)), what(std::move(what)), cefg(cefg) {}

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
				if (cefg && (name == "true" || name == "false")) {
					tokens.push_back({BOOL, name});
					continue;
				}
				if (cefg && name == "forall")
					fail("quantifiers are only allowed in the results of subtrees");
				if (!ctx.symbols.count(name))
					fail("undeclared constant " + name);
				used.insert(name);
				tokens.push_back({NAME, name});
			} else if (cefg && c == '@') {
				fail("selectors are only allowed in the results of subtrees");
			} else {
				std::string two = text.substr(pos, 2);
				if (two == "<=" || two == ">=" || two == "!=" || (cefg && two == "=>")) {
					tokens.push_back({OP, two});
					pos += 2;
				} else if (std::string("+-*()=<>|&").find(c) != std::string::npos || (cefg && (c == '/' || c == '!'))) {
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

	// term := product (('+' | '-') product)*, product := unary (('*' | '/') unary)*, unary := '-' unary | atom
	void term() {
		product();
		while (accept("+") || accept("-"))
			product();
	}
	void product() {
		unary();
		while (accept("*") || (cefg && accept("/")))
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
	// atom := term comparison term | '(' constraint ')';
	// for CEFGs, constraint := connected ('=>' constraint)?, connected := negation (('&' | '|') negation)*,
	// negation := '!' negation | atom, atom := 'true' | 'false' | term comparison term | '(' constraint ')'
	void constraint() {
		if (cefg) {
			negation();
			while (accept("&") || accept("|"))
				negation();
			if (accept("=>"))
				constraint();
			return;
		}
		conjunction();
		while (accept("|"))
			conjunction();
	}
	void negation() {
		if (accept("!"))
			return negation();
		atom();
	}
	void conjunction() {
		atom();
		while (accept("&"))
			atom();
	}
	void atom() {
		if (peek().kind == BOOL) {
			next++;
			return;
		}
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

	// the expression without whitespace and parentheses, to match the conditions of honest histories to those of
	// condition nodes: equal for the same condition (up to parentheses and spacing), but also for some different ones
	std::string normalised() {
		std::string result;
		for (const Token &t : tokens)
			if (t.kind != END && t.text != "(" && t.text != ")")
				result += t.text + " ";
		return result;
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

// for CEFGs (`known` not null): any number, and expressions only of the constants in `known`
void check_utilities(const Context &ctx, const json &utilities, const std::string &where, const std::string &what,
		const std::set<std::string> *known = nullptr) {
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
		if (u["value"].is_string()) {
			Expression e(ctx, u["value"].get_ref<const std::string &>(), where, what, known);
			e.check_utility();
			if (known)
				for (const std::string &name : e.used)
					if (!known->count(name))
						ctx.fail(where, what, "the utility of " + player + " uses " + name +
							", which is still unknown here (reveal it at a condition node on the way)");
		} else if (known && u["value"].is_number()) {
			continue;
		} else if (!u["value"].is_number_unsigned())
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


// ---- CEFGs (games with condition nodes or unknown constants), as read by cefg/input.cpp -----------

struct Cefg {
	Context ctx{nullptr, {}, {}};
	std::set<std::string> known, unknown;

	[[noreturn]] void fail(const std::string &what, const std::string &message) const {
		ctx.fail("", what, message);
	}

	// constants or infinitesimals: a list (all known) or {"known": [...], "unknown": [...]}
	void declarations(const json &game, const char *key) {
		if (!game.contains(key))
			return;
		const json &d = game[key];
		auto declare = [&](const json &names, std::set<std::string> &into, const std::string &what) {
			if (!names.is_array())
				fail(key, what + " must be a list of names");
			for (const json &name : names) {
				if (!name.is_string() || name.get<std::string>().empty())
					fail(key, "names must be non-empty strings");
				if (!ctx.symbols.insert(name.get<std::string>()).second)
					fail(key, name.get<std::string>() + " is declared twice");
				into.insert(name.get<std::string>());
			}
		};
		if (d.is_array()) {
			declare(d, known, key);
		} else if (d.is_object()) {
			for (const auto &item : d.items())
				if (item.key() != "known" && item.key() != "unknown")
					fail(key, "expected a list, or an object with known and unknown, not " + item.key());
			if (d.contains("known"))
				declare(d["known"], known, "known");
			if (d.contains("unknown"))
				declare(d["unknown"], unknown, "unknown");
		} else {
			fail(key, "must be a list, or an object with known and unknown");
		}
	}

	void constraints(const json &list, const std::string &what) {
		if (!list.is_array())
			fail(what, "must be a list of constraints");
		for (size_t i = 0; i < list.size(); i++) {
			std::string w = what + " " + std::to_string(i + 1);
			if (!list[i].is_string())
				fail(w, "must be a string");
			Expression(ctx, list[i].get_ref<const std::string &>(), "", w, true).check_constraint();
		}
	}

	// `path`: actions, and "condition N" (from 1) below condition nodes;
	// `known_here`: the constants known at `node`, i.e. the known ones and the unknowns revealed on the way
	void tree(const json &node, std::vector<std::string> &path, const std::set<std::string> &known_here) {
		std::string what = "node at " + history_text(path);
		if (!node.is_object())
			fail(what, "not a node");
		int kinds = node.contains("children") + node.contains("condition") + node.contains("utility") + node.contains("subtree");
		if (kinds != 1)
			fail(what, kinds ? "a node must have only one of children, condition, utility and subtree"
				: "a node must have children, a condition, a utility, or a subtree result");
		if (node.contains("children")) {
			if (!node.contains("player") || !node["player"].is_string() || !ctx.players.count(node["player"].get<std::string>()))
				fail(what, "the player of a node must be declared in players");
			if (!node["children"].is_array() || node["children"].empty())
				fail(what, "a node of " + node["player"].get<std::string>() + " needs at least one action");
			std::set<std::string> actions;
			for (const json &child : node["children"]) {
				if (!child.is_object() || !child.contains("action") || !child["action"].is_string() || !child.contains("child"))
					fail(what, "every child needs an action and a child");
				std::string action = child["action"];
				if (!actions.insert(action).second)
					fail(what, "action " + action + " appears twice");
				path.push_back(action);
				tree(child["child"], path, known_here);
				path.pop_back();
			}
		} else if (node.contains("condition")) {
			const json &conditions = node["condition"];
			if (!conditions.is_array() || conditions.empty())
				fail(what, "a condition node needs a list of at least one {constraint, child}");
			// unknowns in the conditions, and those in reveals, are known below the node
			std::set<std::string> below = known_here, texts;
			for (size_t i = 0; i < conditions.size(); i++) {
				const json &c = conditions[i];
				std::string w = "condition " + std::to_string(i + 1) + " of the " + what;
				if (!c.is_object() || !c.contains("constraint") || !c["constraint"].is_string() || !c.contains("child"))
					fail(w, "needs a constraint and a child");
				if (c.contains("name") && !c["name"].is_string())
					fail(w, "the name must be a string");
				Expression e(ctx, c["constraint"].get_ref<const std::string &>(), "", w, true);
				e.check_constraint();
				if (!texts.insert(e.normalised()).second)
					fail(w, "the condition " + c["constraint"].get<std::string>() + " appears twice");
				below.insert(e.used.begin(), e.used.end());
			}
			if (node.contains("reveals")) {
				if (!node["reveals"].is_array())
					fail(what, "reveals must be a list of constants");
				for (const json &name : node["reveals"]) {
					if (!name.is_string())
						fail(what, "reveals must be a list of constants, not " + name.dump());
					if (!ctx.symbols.count(name.get<std::string>()))
						fail(what, "reveals " + name.get<std::string>() + ", which is not declared");
					if (!unknown.count(name.get<std::string>()))
						fail(what, "reveals " + name.get<std::string>() + ", which is not declared unknown");
					below.insert(name.get<std::string>());
				}
			}
			for (size_t i = 0; i < conditions.size(); i++) {
				path.push_back("condition " + std::to_string(i + 1));
				tree(conditions[i]["child"], path, below);
				path.pop_back();
			}
		} else if (node.contains("utility")) {
			check_utilities(ctx, node["utility"], "", what, &known_here);
		} else if (node["subtree"].is_array()) {
			// written by --subtree for a CEFG; its expressions are checked when they are read
			for (const json &entry : node["subtree"])
				if (!entry.is_object() || !entry.contains("subtree") ||
						!(entry.contains("honest_history") || entry.contains("honest_utility") || entry.contains("no_honest_history")))
					fail(what, "every subtree entry needs a subtree result and one of honest_history, honest_utility and no_honest_history");
		} else if (!node["subtree"].is_object()) {
			fail(what, "a subtree result must be a list of entries (of a CEFG) or an object (of an EFG)");
		}
	}

	// the rest `history` of an honest history at `node`, reached by `path`
	void honest(const json &node, const json &history, std::vector<std::string> &path, const std::string &what) {
		if (!history.is_array())
			fail(what, "must be a list of actions, and of conditions at condition nodes");
		const json *at = &node;
		for (size_t i = 0; i < history.size(); i++) {
			const json &element = history[i];
			if (at->contains("subtree"))
				return;
			if (at->contains("utility"))
				fail(what, history_text(path) + " already ends at a leaf, but the honest history continues with " + element.dump());
			if (at->contains("children")) {
				if (!element.is_string())
					fail(what, "expected an action at the node of " + (*at)["player"].get<std::string>() + " after " +
						history_text(path) + ", not " + element.dump());
				const json *found = nullptr;
				for (const json &child : (*at)["children"])
					if (child["action"] == element)
						found = &child["child"];
				if (!found)
					fail(what, "no action " + element.get<std::string>() + " after " + history_text(path));
				path.push_back(element);
				at = found;
				continue;
			}
			// a condition node: the history continues in every condition, so it ends here
			const json &conditions = (*at)["condition"];
			if (!element.is_array())
				fail(what, "expected a list of {condition, path} at the condition node after " + history_text(path) + ", not " + element.dump());
			if (i + 1 != history.size())
				fail(what, "the conditions at the condition node after " + history_text(path) +
					" must be the last element, the history continues in their paths");
			if (element.size() != conditions.size())
				fail(what, "the condition node after " + history_text(path) + " has " + std::to_string(conditions.size()) +
					" conditions, but the honest history gives " + std::to_string(element.size()));
			std::map<std::string, size_t> index;
			for (size_t j = 0; j < conditions.size(); j++) {
				Expression e(ctx, conditions[j]["constraint"].get_ref<const std::string &>(), "", what, true);
				e.check_constraint();
				index[e.normalised()] = j;
			}
			std::set<size_t> given;
			for (const json &c : element) {
				if (!c.is_object() || !c.contains("condition") || !c["condition"].is_string() || !c.contains("path"))
					fail(what, "at the condition node after " + history_text(path) + ", every element needs a condition and a path");
				Expression e(ctx, c["condition"].get_ref<const std::string &>(), "", what, true);
				e.check_constraint();
				// a condition written differently is matched (or not) by CheckMate itself
				auto j = index.find(e.normalised());
				if (j == index.end())
					continue;
				if (!given.insert(j->second).second)
					fail(what, "the condition " + c["condition"].get<std::string>() + " after " + history_text(path) + " is given twice");
				path.push_back("condition " + std::to_string(j->second + 1));
				honest(conditions[j->second]["child"], c["path"], path, what);
				path.pop_back();
			}
			return;
		}
		if (at->contains("children"))
			fail(what, history_text(path) + " ends at a node of " + (*at)["player"].get<std::string>() + ", not at a leaf");
		if (at->contains("condition"))
			fail(what, history_text(path) + " ends at a condition node, not at a leaf (give the path for every condition)");
	}

	// an honest utility: a utility, or a list of {condition, utility}
	void honest_utility(const json &utility, const std::string &what) {
		if (utility.is_array() && !utility.empty() && utility[0].is_object() && utility[0].contains("condition")) {
			for (const json &c : utility) {
				if (!c.is_object() || !c.contains("condition") || !c["condition"].is_string() || !c.contains("utility"))
					fail(what, "every conditional honest utility needs a condition and a utility");
				Expression(ctx, c["condition"].get_ref<const std::string &>(), "", what, true).check_constraint();
				honest_utility(c["utility"], what);
			}
			return;
		}
		std::set<std::string> all = ctx.symbols;
		check_utilities(ctx, utility, "", what, &all);
	}
};
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


void validate_cefg(const json &game) {
	if (!game.is_object())
		throw GameError("a game must be a JSON object");
	Cefg cefg;
	check_names(cefg.ctx, game, "players", cefg.ctx.players, true);
	if (cefg.ctx.players.empty())
		throw GameError("players: the game needs at least one player");
	cefg.declarations(game, "constants");
	cefg.declarations(game, "infinitesimals");

	if (!game.contains("tree"))
		throw GameError("the game has no tree");
	if (!game["tree"].is_object() || !(game["tree"].contains("children") || game["tree"].contains("condition")))
		throw GameError("tree: the root of the tree must be a node with actions or conditions");
	std::vector<std::string> path;
	cefg.tree(game["tree"], path, cefg.known);

	if (game.contains("initial_constraints"))
		cefg.constraints(game["initial_constraints"], "initial constraint");
	// property constraints are optional for CEFGs, but must be lists if given
	if (game.contains("property_constraints")) {
		if (!game["property_constraints"].is_object())
			throw GameError("property_constraints must be an object with a list for each property");
		for (const char *p : {"weak_immunity", "weaker_immunity", "collusion_resilience", "practicality"})
			if (game["property_constraints"].contains(p))
				cefg.constraints(game["property_constraints"][p], std::string(p) + " constraint");
	}

	size_t honest = 0;
	if (game.contains("honest_histories")) {
		if (!game["honest_histories"].is_array())
			throw GameError("honest_histories must be a list of histories");
		for (size_t i = 0; i < game["honest_histories"].size(); i++) {
			path.clear();
			cefg.honest(game["tree"], game["honest_histories"][i], path, "honest history " + std::to_string(i + 1));
		}
		honest += game["honest_histories"].size();
	}
	if (game.contains("honest_utilities")) {
		const json &us = game["honest_utilities"];
		if (!us.is_array())
			throw GameError("honest_utilities must be a list");
		for (size_t i = 0; i < us.size(); i++) {
			std::string what = "honest utility " + std::to_string(i + 1);
			if (!us[i].is_object() || !us[i].contains("utility"))
				throw GameError(what + ": must have a utility");
			cefg.honest_utility(us[i]["utility"], what);
		}
		honest += us.size();
	}
	if (!honest)
		throw GameError("the game needs honest_histories, or honest_utilities for a subtree");
}
