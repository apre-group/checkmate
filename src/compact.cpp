#include <cctype>
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
		if (std::isspace(static_cast<unsigned char>(c)) || c == ',' || c == ':' || c == '#')
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
			" compactly: names must not contain spaces, any of , : # or ->");
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
		if (value.find(',') != std::string::npos)
			throw CompactError("cannot write utility " + json(value).dump() + " compactly: it contains a comma");
		result += (result.empty() ? "" : ", ") + u["player"].get<std::string>() + ": " + value;
	}
	return result;
}

void write_node(std::ostringstream &out, const json &node, size_t indent) {
	for (const json &child : node["children"]) {
		check_name(child["action"], "action");
		out << std::string(indent, ' ') << child["action"].get<std::string>() << " -> ";
		const json &c = child["child"];
		if (c.contains("children")) {
			check_name(c["player"], "player");
			out << c["player"].get<std::string>() << "\n";
			write_node(out, c, indent + 2);
		} else if (c.contains("utility")) {
			out << utilities_text(c["utility"]) << "\n";
		} else if (c.contains("subtree")) {
			out << "subtree " << c["subtree"].dump() << "\n";
		} else {
			throw CompactError("unexpected node " + c.dump());
		}
	}
}

// ---- reading -----------------------------------------------------------------

struct Node {
	std::string player;                                            // branches
	json utility;                                                  // leaves
	json subtree;                                                  // subtree results
	std::vector<std::pair<std::string, std::unique_ptr<Node>>> children;
	std::string key;                                               // "tree/a/b", for the line map
};

[[noreturn]] void fail(size_t line, const std::string &message) {
	throw CompactError("line " + std::to_string(line) + ": " + message);
}

json node_json(const Node &node, std::vector<std::string> &actions, std::set<std::string> &seen) {
	if (!node.utility.is_null())
		return {{"utility", node.utility}};
	if (!node.subtree.is_null())
		return {{"subtree", node.subtree}};
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
	for (const char *key : {"constants", "infinitesimals"}) {
		if (game.contains(key) && !game[key].empty()) {
			for (const json &c : game[key])
				check_name(c, "constant");
			out << key << ": " << join(game[key], ", ") << "\n";
		}
	}
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
			for (const json &a : h)
				check_name(a, "action");
			out << "honest:" << (h.empty() ? "" : " " + join(h, " ")) << "\n";
		}
	if (game.contains("honest_utilities"))
		for (const json &u : game["honest_utilities"])
			out << "honest_utility: " << utilities_text(u["utility"]) << "\n";
	const json &tree = game["tree"];
	if (!tree.contains("children"))
		throw CompactError("the root of the tree must be a branch");
	check_name(tree["player"], "player");
	out << "\n" << tree["player"].get<std::string>() << "\n";
	write_node(out, tree, 2);
	return out.str();
}

json from_compact(const std::string &text, LineMap *lines) {
	LineMap ignored;
	LineMap &at = lines ? *lines : ignored;
	std::vector<std::string> players, constants, infinitesimals;
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
			if (indent == 0 && colon != std::string::npos && arrow == std::string::npos) {
				std::string key = trim(body.substr(0, colon)), value = trim(body.substr(colon + 1));
				auto names = [&](std::vector<std::string> &into) {
					for (const std::string &n : split(value, ",")) {
						std::string name = trim(n);
						if (!plain_name(name))
							fail(line, "bad name \"" + name + "\" in " + key);
						into.push_back(name);
					}
				};
				if (key == "players" || key == "constants" || key == "infinitesimals")
					at[key] = line;
				if (key == "players") {
					names(players);
					has_players = true;
				} else if (key == "constants") {
					names(constants);
				} else if (key == "infinitesimals") {
					names(infinitesimals);
				} else if (key == "initial") {
					at["initial/" + std::to_string(initial.size())] = line;
					initial.push_back(value);
				} else if (property.contains(key)) {
					at["property/" + key + "/" + std::to_string(property[key].size())] = line;
					property[key].push_back(value);
				} else if (key == "honest") {
					at["honest/" + std::to_string(honest.size())] = line;
					json h = json::array();
					for (const std::string &a : split(value, " ,"))
						if (!trim(a).empty())
							h.push_back(trim(a));
					honest.push_back(h);
				} else if (key == "honest_utility") {
					if (!has_players)
						fail(line, "honest_utility before players");
					at["honest_utility/" + std::to_string(honest_utilities.size())] = line;
					honest_utilities.push_back({{"utility", parse_utilities(line, value, players)}});
				} else {
					fail(line, "unknown setting \"" + key + "\"");
				}
				continue;
			}
			if (!has_players)
				fail(line, "the game needs a players: line before the tree");
			if (arrow != std::string::npos || indent != 0)
				fail(line, "the tree must start with the player at the root, without indentation");
			root.reset(new Node());
			root->player = body;
			root->key = "tree";
			at["tree"] = line;
			stack.push_back({indent, root.get()});
			continue;
		}

		if (arrow == std::string::npos)
			fail(line, "expected ACTION -> ..., got \"" + body + "\"");
		while (!stack.empty() && stack.back().first >= indent)
			stack.pop_back();
		if (stack.empty())
			fail(line, "this line must be indented below the root");
		Node *parent = stack.back().second;
		std::string action = trim(body.substr(0, arrow)), rest = trim(body.substr(arrow + 2));
		if (!plain_name(action))
			fail(line, "bad action name \"" + action + "\"");
		for (const auto &c : parent->children)
			if (c.first == action)
				fail(line, "action " + action + " appears twice at the same node");

		std::unique_ptr<Node> child(new Node());
		child->key = parent->key + "/" + action;
		at[child->key] = line;
		Node *branch = nullptr;
		if (rest.compare(0, 7, "subtree") == 0) {
			try {
				child->subtree = json::parse(rest.substr(7));
			} catch (const json::exception &e) {
				fail(line, std::string("bad subtree result: ") + e.what());
			}
		} else if (rest.find(':') != std::string::npos) {
			child->utility = parse_utilities(line, rest, players);
		} else {
			bool known = false;
			for (const std::string &p : players)
				known = known || p == rest;
			if (!known)
				fail(line, "unknown player \"" + rest + "\"");
			child->player = rest;
			branch = child.get();
		}
		parent->children.push_back({action, std::move(child)});
		if (branch)
			stack.push_back({indent, branch});
	}

	if (!has_players)
		throw CompactError("the game has no players: line");
	if (!root)
		throw CompactError("the game has no tree");
	bool known = false;
	for (const std::string &p : players)
		known = known || p == root->player;
	if (!known)
		throw CompactError("unknown player \"" + root->player + "\" at the root");

	std::vector<std::string> actions;
	std::set<std::string> seen;
	json tree = node_json(*root, actions, seen);
	json game = {
		{"players", players},
		{"actions", actions},
		{"infinitesimals", infinitesimals},
		{"constants", constants},
		{"initial_constraints", initial},
		{"property_constraints", property},
		{"honest_histories", honest},
	};
	if (!honest_utilities.empty())
		game["honest_utilities"] = honest_utilities;
	game["tree"] = tree;
	return game;
}
