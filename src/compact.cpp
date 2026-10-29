#include <algorithm>
#include <cctype>
#include <cstring>
#include <memory>
#include <set>
#include <sstream>
#include <utility>
#include <vector>

#include "compact.hpp"

using json = nlohmann::json;

namespace {

const char *PROPERTIES[] = {"weak_immunity", "weaker_immunity", "collusion_resilience", "practicality"};

std::string trim(const std::string &s) {
	size_t b = s.find_first_not_of(" \t\r");
	if (b == std::string::npos)
		return "";
	size_t e = s.find_last_not_of(" \t\r");
	return s.substr(b, e - b + 1);
}

std::vector<std::string> split(const std::string &s, const std::string &separators) {
	std::vector<std::string> parts;
	std::string part;
	for (char c : s) {
		if (separators.find(c) != std::string::npos) {
			parts.push_back(part);
			part.clear();
		} else {
			part += c;
		}
	}
	parts.push_back(part);
	return parts;
}

// player, action and constant names have to survive the separators of the format
bool plain_name(const std::string &name) {
	if (name.empty() || name.find("->") != std::string::npos)
		return false;
	for (char c : name)
		if (std::isspace(static_cast<unsigned char>(c)) || std::string(",:#?{};").find(c) != std::string::npos)
			return false;
	return true;
}

std::string join(const json &names, const std::string &separator) {
	std::string result;
	for (const json &name : names) {
		if (!result.empty())
			result += separator;
		result += name.get<std::string>();
	}
	return result;
}

std::string value_text(const json &value) {
	return value.is_string() ? value.get<std::string>() : value.dump();
}

// ---- writing ----------------------------------------------------------------

void check_name(const json &name, const char *what) {
	if (!name.is_string() || !plain_name(name.get<std::string>()))
		throw CompactError(std::string("cannot write ") + what + " " + name.dump() +
			" compactly: names must not contain spaces, any of , : # ? { } ; or ->");
}

void check_text(const std::string &text) {
	if (text.find('\n') != std::string::npos || text.find('#') != std::string::npos)
		throw CompactError("cannot write " + json(text).dump() + " compactly: it contains a newline or #");
}

std::string utilities_text(const json &utilities) {
	std::string result;
	for (const json &u : utilities) {
		check_name(u["player"], "player");
		std::string value = value_text(u["value"]);
		check_text(value);
		if (value.find_first_of(",;{}") != std::string::npos)
			throw CompactError("cannot write utility " + json(value).dump() + " compactly: it contains one of , ; { }");
		result += (result.empty() ? "" : ", ") + u["player"].get<std::string>() + ": " + value;
	}
	return result;
}

// conditions of CEFGs are written as "if CONDITION", up to "->", ";" or "}"
void check_condition(const std::string &condition) {
	check_text(condition);
	if (condition.find_first_of(":;{}") != std::string::npos || condition.find("->") != std::string::npos)
		throw CompactError("cannot write condition " + json(condition).dump() + " compactly: it contains one of : ; { } ->");
}

// constants or infinitesimals: a list, or {"known": [...], "unknown": [...]} in CEFGs
void write_declarations(std::ostringstream &out, const json &game, const std::string &key) {
	if (!game.contains(key))
		return;
	const json &d = game[key];
	json known = d.is_object() ? d.value("known", json::array()) : d;
	json unknown = d.is_object() ? d.value("unknown", json::array()) : json::array();
	for (const json &c : known)
		check_name(c, "constant");
	for (const json &c : unknown)
		check_name(c, "constant");
	if (!known.empty())
		out << key << ": " << join(known, ", ") << "\n";
	if (!unknown.empty())
		out << "unknown_" << key << ": " << join(unknown, ", ") << "\n";
}

// an honest history; in CEFGs, it continues at a condition node in every condition: {if CONDITION -> history; ...}
std::string honest_text(const json &history) {
	std::string result;
	for (const json &element : history) {
		if (!result.empty())
			result += " ";
		if (!element.is_array()) {
			check_name(element, "action");
			result += element.get<std::string>();
			continue;
		}
		std::string conditions;
		for (const json &c : element) {
			std::string condition = c["condition"], path = honest_text(c["path"]);
			check_condition(condition);
			conditions += (conditions.empty() ? "if " : "; if ") + condition + (path.empty() ? "" : " -> " + path);
		}
		result += "{" + conditions + "}";
	}
	return result;
}

// an honest utility; in CEFGs, it can depend on conditions: {if CONDITION -> utility; ...}
std::string honest_utility_text(const json &utility) {
	if (utility.empty() || !utility[0].contains("condition"))
		return utilities_text(utility);
	std::string conditions;
	for (const json &c : utility) {
		std::string condition = c["condition"];
		check_condition(condition);
		conditions += (conditions.empty() ? "if " : "; if ") + condition + " -> " + honest_utility_text(c["utility"]);
	}
	return "{" + conditions + "}";
}

// a condition node of a CEFG (older versions of examples/dsl.py write "condition": "True" on every node)
bool condition_node(const json &node) {
	return node.contains("condition") && node["condition"].is_array();
}

// a node with lines below it, as it is written after "->" (or at the root): its player, or ? for a condition node
std::string head(const json &node) {
	if (!condition_node(node)) {
		check_name(node["player"], "player");
		return node["player"];
	}
	if (!node.contains("reveals") || node["reveals"].empty())
		return "?";
	for (const json &c : node["reveals"])
		check_name(c, "constant");
	return "? reveals " + join(node["reveals"], ", ");
}

void write_node(std::ostringstream &out, const json &node, size_t indent);

// the rest of the line after "->", and the lines below it
void write_child(std::ostringstream &out, const json &c, size_t indent) {
	if (c.contains("children") || condition_node(c)) {
		out << head(c) << "\n";
		write_node(out, c, indent + 2);
	} else if (c.contains("utility")) {
		out << utilities_text(c["utility"]) << "\n";
	} else if (c.contains("subtree")) {
		out << "subtree " << c["subtree"].dump() << "\n";
	} else {
		throw CompactError("unexpected node " + c.dump());
	}
}

// the lines of the actions or conditions of `node`
void write_node(std::ostringstream &out, const json &node, size_t indent) {
	if (condition_node(node)) {
		for (const json &c : node["condition"]) {
			std::string condition = c["constraint"];
			check_condition(condition);
			out << std::string(indent, ' ') << "if ";
			if (c.contains("name")) {
				check_name(c["name"], "condition name");
				out << c["name"].get<std::string>() << ": ";
			}
			out << condition << " -> ";
			write_child(out, c["child"], indent);
		}
		return;
	}
	for (const json &child : node["children"]) {
		check_name(child["action"], "action");
		out << std::string(indent, ' ') << child["action"].get<std::string>() << " -> ";
		write_child(out, child["child"], indent);
	}
}

// ---- reading -----------------------------------------------------------------

struct Node {
	std::string player;                                            // branches
	json utility;                                                  // leaves
	json subtree;                                                  // subtree results
	std::vector<std::pair<std::string, std::unique_ptr<Node>>> children;
	// condition nodes of CEFGs
	bool is_condition = false;
	std::vector<std::string> reveals;
	struct Condition {
		std::string constraint, name;
		std::unique_ptr<Node> child;
	};
	std::vector<Condition> conditions;
	std::string key;                                               // "tree/a/condition 1/b", for the line map
};

[[noreturn]] void fail(size_t line, const std::string &message) {
	throw CompactError("line " + std::to_string(line) + ": " + message);
}

json node_json(const Node &node, std::vector<std::string> &actions, std::set<std::string> &seen) {
	if (!node.utility.is_null())
		return {{"utility", node.utility}};
	if (!node.subtree.is_null())
		return {{"subtree", node.subtree}};
	if (node.is_condition) {
		json conditions = json::array();
		for (const auto &c : node.conditions) {
			json condition = {{"constraint", c.constraint}, {"child", node_json(*c.child, actions, seen)}};
			if (!c.name.empty())
				condition["name"] = c.name;
			conditions.push_back(condition);
		}
		json result = {{"condition", conditions}};
		if (!node.reveals.empty())
			result["reveals"] = node.reveals;
		return result;
	}
	json children = json::array();
	for (const auto &child : node.children) {
		if (seen.insert(child.first).second)
			actions.push_back(child.first);
		children.push_back({{"action", child.first}, {"child", node_json(*child.second, actions, seen)}});
	}
	return {{"player", node.player}, {"children", children}};
}

json parse_utilities(size_t line, const std::string &text, const std::vector<std::string> &players) {
	json utility = json::array();
	std::set<std::string> listed;
	for (const std::string &entry : split(text, ",")) {
		size_t colon = entry.find(':');
		if (colon == std::string::npos)
			fail(line, "expected PLAYER: utility, got \"" + trim(entry) + "\"");
		std::string player = trim(entry.substr(0, colon)), value = trim(entry.substr(colon + 1));
		bool known = false;
		for (const std::string &p : players)
			known = known || p == player;
		if (!known)
			fail(line, "unknown player " + player);
		if (!listed.insert(player).second)
			fail(line, "utility of " + player + " given twice");
		if (value.empty())
			fail(line, "missing utility of " + player);
		utility.push_back({{"player", player}, {"value", value}});
	}
	if (listed.size() != players.size())
		fail(line, "a leaf needs a utility for every player");
	return utility;
}

// the node after "->" (or at the root) into `node`; returns whether lines below it follow (a branch or condition node)
bool parse_node(size_t line, const std::string &text, const std::vector<std::string> &players, Node &node) {
	if (text[0] == '?') {
		node.is_condition = true;
		std::string reveals = trim(text.substr(1));
		if (reveals.empty())
			return true;
		if (reveals.compare(0, 8, "reveals ") != 0)
			fail(line, "expected ? or ? reveals CONSTANT, ..., got \"" + text + "\"");
		for (const std::string &n : split(reveals.substr(8), ",")) {
			std::string name = trim(n);
			if (!plain_name(name))
				fail(line, "bad name \"" + name + "\" in reveals");
			node.reveals.push_back(name);
		}
		return true;
	}
	if (text.compare(0, 7, "subtree") == 0) {
		try {
			node.subtree = json::parse(text.substr(7));
		} catch (const json::exception &e) {
			fail(line, std::string("bad subtree result: ") + e.what());
		}
		return false;
	}
	if (text.find(':') != std::string::npos) {
		node.utility = parse_utilities(line, text, players);
		return false;
	}
	bool known = false;
	for (const std::string &p : players)
		known = known || p == text;
	if (!known)
		fail(line, "unknown player \"" + text + "\"");
	node.player = text;
	return true;
}

// the value of an honest: or honest_utility: line, with {if CONDITION -> ...; ...} for conditions in CEFGs
struct Value {
	size_t line;
	const std::string &text;
	size_t pos = 0;

	void skip(const char *chars) {
		while (pos < text.size() && std::strchr(chars, text[pos]))
			pos++;
	}
	bool at(const char *chars) const {
		return pos < text.size() && std::strchr(chars, text[pos]);
	}
	// the end, which a value that stops at ; or } has to reach
	void end() {
		skip(" ");
		if (pos < text.size())
			fail(line, std::string("unexpected '") + text[pos] + "'");
	}

	// a history, up to the end, ; or }
	json history() {
		json h = json::array();
		for (;;) {
			skip(" ,");
			if (pos == text.size() || at(";}"))
				return h;
			if (at("{")) {
				pos++;
				h.push_back(conditions(&Value::history_after, "path"));
				continue;
			}
			size_t start = pos;
			while (pos < text.size() && !at(" ,{};"))
				pos++;
			std::string action = text.substr(start, pos - start);
			if (!plain_name(action))
				fail(line, "bad action name \"" + action + "\"");
			h.push_back(action);
		}
	}
	json history_after(bool arrow) {
		return arrow ? history() : json::array();
	}

	// an honest utility, up to the end, ; or }
	json utility() {
		skip(" ");
		if (at("{")) {
			pos++;
			return conditions(&Value::utility_after, "utility");
		}
		size_t start = pos;
		while (pos < text.size() && !at(";}"))
			pos++;
		return parse_utilities(line, text.substr(start, pos - start), *players);
	}
	json utility_after(bool arrow) {
		if (!arrow)
			fail(line, "expected -> and the utility after the condition");
		return utility();
	}
	const std::vector<std::string> *players = nullptr;

	// after {: if CONDITION -> ...; ... }, with the ... read by `after` (told whether there was an arrow) under `key`
	json conditions(json (Value::*after)(bool), const char *key) {
		json result = json::array();
		for (;;) {
			skip(" ");
			if (text.compare(pos, 3, "if ") != 0)
				fail(line, "expected if CONDITION after { or ;");
			pos += 3;
			size_t stop = text.find_first_of(";}", pos), arrow = text.find("->", pos);
			bool has_arrow = arrow < stop;
			std::string condition = trim(text.substr(pos, (has_arrow ? arrow : stop) - pos));
			if (condition.empty())
				fail(line, "missing condition after if");
			pos = has_arrow ? arrow + 2 : std::min(stop, text.size());
			json rest = (this->*after)(has_arrow);
			result.push_back({{"condition", condition}, {key, rest}});
			if (pos == text.size())
				fail(line, "missing }");
			if (text[pos++] == '}')
				return result;
		}
	}
};

}

bool looks_like_json(const std::string &text) {
	size_t first = text.find_first_not_of(" \t\r\n");
	return first != std::string::npos && text[first] == '{';
}

std::string to_compact(const json &game) {
	std::ostringstream out;
	for (const json &p : game["players"])
		check_name(p, "player");
	out << "players: " << join(game["players"], ", ") << "\n";
	write_declarations(out, game, "constants");
	write_declarations(out, game, "infinitesimals");
	if (game.contains("initial_constraints"))
		for (const json &c : game["initial_constraints"]) {
			check_text(c.get<std::string>());
			out << "initial: " << c.get<std::string>() << "\n";
		}
	if (game.contains("property_constraints"))
		for (const char *p : PROPERTIES)
			if (game["property_constraints"].contains(p))
				for (const json &c : game["property_constraints"][p]) {
					check_text(c.get<std::string>());
					out << p << ": " << c.get<std::string>() << "\n";
				}
	if (game.contains("honest_histories"))
		for (const json &h : game["honest_histories"]) {
			std::string text = honest_text(h);
			out << "honest:" << (text.empty() ? "" : " " + text) << "\n";
		}
	if (game.contains("honest_utilities"))
		for (const json &u : game["honest_utilities"])
			out << "honest_utility: " << honest_utility_text(u["utility"]) << "\n";
	const json &tree = game["tree"];
	if (!tree.contains("children") && !condition_node(tree))
		throw CompactError("the root of the tree must be a node with actions or conditions");
	out << "\n" << head(tree) << "\n";
	write_node(out, tree, 2);
	return out.str();
}

json from_compact(const std::string &text, LineMap *lines) {
	LineMap ignored;
	LineMap &at = lines ? *lines : ignored;
	std::vector<std::string> players, constants, infinitesimals, unknown_constants, unknown_infinitesimals;
	json initial = json::array(), honest = json::array(), honest_utilities = json::array();
	json property = json::object();
	for (const char *p : PROPERTIES)
		property[p] = json::array();
	bool has_players = false;

	std::unique_ptr<Node> root;
	std::vector<std::pair<size_t, Node *>> stack;  // (indent, branch) of the open branches

	std::istringstream in(text);
	std::string raw;
	size_t line = 0;
	while (std::getline(in, raw)) {
		line++;
		size_t hash = raw.find('#');
		std::string content = raw.substr(0, hash);
		if (trim(content).empty())
			continue;
		if (content.find('\t') != std::string::npos)
			fail(line, "use spaces, not tabs");
		size_t indent = content.find_first_not_of(' ');
		std::string body = trim(content);
		size_t arrow = body.find("->");
		size_t colon = body.find(':');

		if (!root) {
			// header lines, until the root of the tree
			// (a conditional honest history or utility has -> after the colon)
			if (indent == 0 && colon != std::string::npos && colon < arrow) {
				std::string key = trim(body.substr(0, colon)), value = trim(body.substr(colon + 1));
				auto names = [&](std::vector<std::string> &into) {
					for (const std::string &n : split(value, ",")) {
						std::string name = trim(n);
						if (!plain_name(name))
							fail(line, "bad name \"" + name + "\" in " + key);
						into.push_back(name);
					}
				};
				if (key == "players" || key == "constants" || key == "infinitesimals" ||
						key == "unknown_constants" || key == "unknown_infinitesimals")
					at[key] = line;
				if (key == "players") {
					names(players);
					has_players = true;
				} else if (key == "constants") {
					names(constants);
				} else if (key == "infinitesimals") {
					names(infinitesimals);
				} else if (key == "unknown_constants") {
					names(unknown_constants);
				} else if (key == "unknown_infinitesimals") {
					names(unknown_infinitesimals);
				} else if (key == "initial") {
					at["initial/" + std::to_string(initial.size())] = line;
					initial.push_back(value);
				} else if (property.contains(key)) {
					at["property/" + key + "/" + std::to_string(property[key].size())] = line;
					property[key].push_back(value);
				} else if (key == "honest") {
					at["honest/" + std::to_string(honest.size())] = line;
					Value v{line, value};
					honest.push_back(v.history());
					v.end();
				} else if (key == "honest_utility") {
					if (!has_players)
						fail(line, "honest_utility before players");
					at["honest_utility/" + std::to_string(honest_utilities.size())] = line;
					Value v{line, value};
					v.players = &players;
					honest_utilities.push_back({{"utility", v.utility()}});
					v.end();
				} else {
					fail(line, "unknown setting \"" + key + "\"");
				}
				continue;
			}
			if (!has_players)
				fail(line, "the game needs a players: line before the tree");
			if (arrow != std::string::npos || indent != 0)
				fail(line, "the tree must start with the player (or ? for a condition node) at the root, without indentation");
			root.reset(new Node());
			if (!parse_node(line, body, players, *root))
				fail(line, "the root of the tree must be a node with actions or conditions");
			root->key = "tree";
			at["tree"] = line;
			stack.push_back({indent, root.get()});
			continue;
		}

		while (!stack.empty() && stack.back().first >= indent)
			stack.pop_back();
		if (stack.empty())
			fail(line, "this line must be indented below the root");
		Node *parent = stack.back().second;
		if (parent->is_condition) {
			// if [NAME:] CONDITION -> ...
			if (body.compare(0, 3, "if ") != 0 || arrow == std::string::npos)
				fail(line, "expected if CONDITION -> ... below a condition node, got \"" + body + "\"");
			std::string condition = trim(body.substr(3, arrow - 3)), name;
			size_t named = condition.find(':');
			if (named != std::string::npos) {
				name = trim(condition.substr(0, named));
				condition = trim(condition.substr(named + 1));
				if (!plain_name(name))
					fail(line, "bad condition name \"" + name + "\"");
			}
			if (condition.empty())
				fail(line, "missing condition after if");
			std::unique_ptr<Node> child(new Node());
			child->key = parent->key + "/condition " + std::to_string(parent->conditions.size() + 1);
			at[child->key] = line;
			std::string rest = trim(body.substr(arrow + 2));
			if (rest.empty())
				fail(line, "missing node after ->");
			Node *open = parse_node(line, rest, players, *child) ? child.get() : nullptr;
			parent->conditions.push_back({condition, name, std::move(child)});
			if (open)
				stack.push_back({indent, open});
			continue;
		}
		if (arrow == std::string::npos)
			fail(line, "expected ACTION -> ..., got \"" + body + "\"");
		std::string action = trim(body.substr(0, arrow)), rest = trim(body.substr(arrow + 2));
		if (!plain_name(action))
			fail(line, "bad action name \"" + action + "\"");
		for (const auto &c : parent->children)
			if (c.first == action)
				fail(line, "action " + action + " appears twice at the same node");

		std::unique_ptr<Node> child(new Node());
		child->key = parent->key + "/" + action;
		at[child->key] = line;
		if (rest.empty())
			fail(line, "missing node after ->");
		Node *open = parse_node(line, rest, players, *child) ? child.get() : nullptr;
		parent->children.push_back({action, std::move(child)});
		if (open)
			stack.push_back({indent, open});
	}

	if (!has_players)
		throw CompactError("the game has no players: line");
	if (!root)
		throw CompactError("the game has no tree");

	std::vector<std::string> actions;
	std::set<std::string> seen;
	json tree = node_json(*root, actions, seen);
	// in CEFGs, {"known": [...], "unknown": [...]}
	auto declarations = [](const std::vector<std::string> &known, const std::vector<std::string> &unknown) {
		return unknown.empty() ? json(known) : json{{"known", known}, {"unknown", unknown}};
	};
	json game = {
		{"players", players},
		{"actions", actions},
		{"infinitesimals", declarations(infinitesimals, unknown_infinitesimals)},
		{"constants", declarations(constants, unknown_constants)},
		{"initial_constraints", initial},
		{"property_constraints", property},
		{"honest_histories", honest},
	};
	if (!honest_utilities.empty())
		game["honest_utilities"] = honest_utilities;
	game["tree"] = tree;
	return game;
}
