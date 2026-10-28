#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <unistd.h>
#include <sys/wait.h>

#include "property_checks.hpp"
#include "selectors.hpp"

// imported from the cefg branch (c9c6e6f); wrapped in namespace cefg next to the EFG engine in src/
namespace cefg {

using z3::CONTEXT;

namespace {

// milliseconds for Z3 on the final formula with selectors
const unsigned Z3_TIMEOUT = 10000;
// milliseconds for cvc5's synthesis, if Z3 cannot decide it (20 minutes)
const unsigned CVC5_TIMEOUT = 20 * 60 * 1000;

// all symbols introduced here contain '!', which cannot occur in identifiers of the input
// selectors are named sel!<number>!<number of candidates>
const std::string SELECTOR_PREFIX = "sel!";
unsigned selector_count = 0;
unsigned fresh_count = 0;

Z3_sort real_sort() {
	return Z3_mk_real_sort(CONTEXT);
}

std::string symbol_name(Z3_symbol symbol) {
	if (Z3_get_symbol_kind(CONTEXT, symbol) == Z3_INT_SYMBOL) {
		return std::to_string(Z3_get_symbol_int(CONTEXT, symbol));
	}
	return Z3_get_symbol_string(CONTEXT, symbol);
}

std::string decl_name(Z3_func_decl decl) {
	return symbol_name(Z3_get_decl_name(CONTEXT, decl));
}

std::string constant_name(Z3_ast constant) {
	return decl_name(Z3_get_app_decl(CONTEXT, Z3_to_app(CONTEXT, constant)));
}

// a fresh constant of sort `sort` (named after `name`, for readability)
Z3_ast fresh_constant(const std::string &name, Z3_sort sort) {
	std::string unique = "q!" + std::to_string(fresh_count++) + "!" + name;
	return Z3_mk_const(CONTEXT, Z3_mk_string_symbol(CONTEXT, unique.c_str()), sort);
}

Z3_ast numeral(unsigned k) {
	return Z3_mk_real(CONTEXT, k, 1);
}

bool is_app(Z3_ast ast) {
	return Z3_get_ast_kind(CONTEXT, ast) == Z3_APP_AST;
}

Z3_func_decl decl_of(Z3_ast ast) {
	return Z3_get_app_decl(CONTEXT, Z3_to_app(CONTEXT, ast));
}

bool is_selector(Z3_func_decl decl) {
	return Z3_get_decl_kind(CONTEXT, decl) == Z3_OP_UNINTERPRETED && decl_name(decl).rfind(SELECTOR_PREFIX, 0) == 0;
}

// the number of candidates a selector chooses among, from its name
unsigned selector_candidates(Z3_func_decl decl) {
	std::string name = decl_name(decl);
	return std::stoul(name.substr(name.rfind('!') + 1));
}

// call `visit` on every subterm of `ast` once, including quantifier bodies
template<typename Visit>
void visit_subterms(Z3_ast ast, Visit &&visit, std::set<unsigned> &seen) {
	if (!seen.insert(Z3_get_ast_id(CONTEXT, ast)).second) {
		return;
	}
	visit(ast);
	if (is_app(ast)) {
		Z3_app app = Z3_to_app(CONTEXT, ast);
		for (unsigned i = 0; i < Z3_get_app_num_args(CONTEXT, app); i++) {
			visit_subterms(Z3_get_app_arg(CONTEXT, app, i), visit, seen);
		}
	} else if (Z3_get_ast_kind(CONTEXT, ast) == Z3_QUANTIFIER_AST) {
		visit_subterms(Z3_get_quantifier_body(CONTEXT, ast), visit, seen);
	}
}

template<typename Visit>
void visit_subterms(Z3_ast ast, Visit &&visit) {
	std::set<unsigned> seen;
	visit_subterms(ast, visit, seen);
}

// the selectors occurring in `ast`
std::set<Z3_func_decl> selectors_in(Z3_ast ast) {
	std::set<Z3_func_decl> result;
	visit_subterms(ast, [&](Z3_ast term) {
		if (is_app(term) && is_selector(decl_of(term))) {
			result.insert(decl_of(term));
		}
	});
	return result;
}

// the uninterpreted constants occurring in `ast` (Z3 shares equal terms, so they can be compared as pointers)
void constants_in(Z3_ast ast, std::set<Z3_ast> &result) {
	visit_subterms(ast, [&](Z3_ast term) {
		if (is_app(term) && Z3_get_app_num_args(CONTEXT, Z3_to_app(CONTEXT, term)) == 0
				&& Z3_get_decl_kind(CONTEXT, decl_of(term)) == Z3_OP_UNINTERPRETED) {
			result.insert(term);
		}
	});
}

/*
 * The formula as a tree with quantifier blocks whose bound variables are unique constants,
 * so that variables can be followed to the block that binds them, and quantifiers can be moved around.
 */
struct FormulaNode {
	enum Kind { ATOM, NOT, AND, OR, IMPLIES, BLOCK } kind;
	std::vector<std::unique_ptr<FormulaNode>> children;
	// ATOM: a quantifier-free formula
	Z3_ast atom = nullptr;
	// BLOCK: ∀ (true) or ∃ (false) the `variables` (named after the original variables in `names`)
	bool forall = true;
	std::vector<Z3_ast> variables;
	std::vector<std::string> names;
};
using Tree = std::unique_ptr<FormulaNode>;

// the formula cannot be translated: a quantifier below another operator than ¬, ∧, ∨, →
struct Unsupported {};

Tree make(FormulaNode::Kind kind, std::vector<Tree> children) {
	Tree node(new FormulaNode());
	node->kind = kind;
	node->children = std::move(children);
	return node;
}

Tree make_atom(Z3_ast atom) {
	Tree node(new FormulaNode());
	node->kind = FormulaNode::ATOM;
	node->atom = atom;
	return node;
}

Tree make_unary(FormulaNode::Kind kind, Tree child) {
	std::vector<Tree> children;
	children.push_back(std::move(child));
	return make(kind, std::move(children));
}

Tree make_binary(FormulaNode::Kind kind, Tree left, Tree right) {
	std::vector<Tree> children;
	children.push_back(std::move(left));
	children.push_back(std::move(right));
	return make(kind, std::move(children));
}

Tree make_block(bool forall, std::vector<Z3_ast> variables, std::vector<std::string> names, Tree body) {
	Tree node = make_unary(FormulaNode::BLOCK, std::move(body));
	node->forall = forall;
	node->variables = std::move(variables);
	node->names = std::move(names);
	return node;
}

bool has_quantifier(Z3_ast ast) {
	bool found = false;
	visit_subterms(ast, [&](Z3_ast term) {
		found = found || Z3_get_ast_kind(CONTEXT, term) == Z3_QUANTIFIER_AST;
	});
	return found;
}

Tree convert(Z3_ast ast) {
	if (Z3_get_ast_kind(CONTEXT, ast) == Z3_QUANTIFIER_AST) {
		if (Z3_is_lambda(CONTEXT, ast)) {
			throw Unsupported();
		}
		unsigned count = Z3_get_quantifier_num_bound(CONTEXT, ast);
		std::vector<Z3_ast> variables;
		std::vector<std::string> names;
		for (unsigned i = 0; i < count; i++) {
			names.push_back(symbol_name(Z3_get_quantifier_bound_name(CONTEXT, ast, i)));
			variables.push_back(fresh_constant(names.back(), Z3_get_quantifier_bound_sort(CONTEXT, ast, i)));
		}
		// in the body, bound variable i has the de Bruijn index count - 1 - i
		std::vector<Z3_ast> replacements(variables.rbegin(), variables.rend());
		Z3_ast body = Z3_substitute_vars(CONTEXT, Z3_get_quantifier_body(CONTEXT, ast), count, replacements.data());
		return make_block(Z3_is_quantifier_forall(CONTEXT, ast), variables, names, convert(body));
	}
	if (is_app(ast)) {
		Z3_app app = Z3_to_app(CONTEXT, ast);
		std::vector<Tree> children;
		auto convert_arguments = [&]() {
			for (unsigned i = 0; i < Z3_get_app_num_args(CONTEXT, app); i++) {
				children.push_back(convert(Z3_get_app_arg(CONTEXT, app, i)));
			}
		};
		switch (Z3_get_decl_kind(CONTEXT, decl_of(ast))) {
			case Z3_OP_AND:
				convert_arguments();
				return make(FormulaNode::AND, std::move(children));
			case Z3_OP_OR:
				convert_arguments();
				return make(FormulaNode::OR, std::move(children));
			case Z3_OP_NOT:
				convert_arguments();
				return make(FormulaNode::NOT, std::move(children));
			case Z3_OP_IMPLIES:
				convert_arguments();
				return make(FormulaNode::IMPLIES, std::move(children));
			default:
				break;
		}
	}
	if (has_quantifier(ast)) {
		throw Unsupported();
	}
	return make_atom(ast);
}

Z3_ast build(const FormulaNode &node) {
	std::vector<Z3_ast> children;
	for (const Tree &child : node.children) {
		children.push_back(build(*child));
	}
	switch (node.kind) {
		case FormulaNode::ATOM:
			return node.atom;
		case FormulaNode::NOT:
			return Z3_mk_not(CONTEXT, children[0]);
		case FormulaNode::AND:
			return children.empty() ? Z3_mk_true(CONTEXT) : Z3_mk_and(CONTEXT, children.size(), children.data());
		case FormulaNode::OR:
			return children.empty() ? Z3_mk_false(CONTEXT) : Z3_mk_or(CONTEXT, children.size(), children.data());
		case FormulaNode::IMPLIES:
			return Z3_mk_implies(CONTEXT, children[0], children[1]);
		case FormulaNode::BLOCK: {
			if (node.variables.empty()) {
				return children[0];
			}
			std::vector<Z3_app> bound;
			for (Z3_ast variable : node.variables) {
				bound.push_back(Z3_to_app(CONTEXT, variable));
			}
			return node.forall
				? Z3_mk_forall_const(CONTEXT, 0, bound.size(), bound.data(), 0, nullptr, children[0])
				: Z3_mk_exists_const(CONTEXT, 0, bound.size(), bound.data(), 0, nullptr, children[0]);
		}
	}
	return nullptr;
}

// replace `from` by `to` in all atoms of `node`
void substitute(FormulaNode &node, const std::vector<Z3_ast> &from, const std::vector<Z3_ast> &to) {
	if (node.kind == FormulaNode::ATOM) {
		node.atom = Z3_substitute(CONTEXT, node.atom, from.size(), from.data(), to.data());
	}
	for (Tree &child : node.children) {
		substitute(*child, from, to);
	}
}

void atoms_of(const FormulaNode &node, std::vector<const FormulaNode *> &atoms) {
	if (node.kind == FormulaNode::ATOM) {
		atoms.push_back(&node);
	}
	for (const Tree &child : node.children) {
		atoms_of(*child, atoms);
	}
}

bool mentions_selector(const FormulaNode &node) {
	std::vector<const FormulaNode *> atoms;
	atoms_of(node, atoms);
	for (const FormulaNode *atom : atoms) {
		if (!selectors_in(atom->atom).empty()) {
			return true;
		}
	}
	return false;
}

std::set<Z3_ast> constants_of(const FormulaNode &node) {
	std::vector<const FormulaNode *> atoms;
	atoms_of(node, atoms);
	std::set<Z3_ast> result;
	for (const FormulaNode *atom : atoms) {
		constants_in(atom->atom, result);
	}
	return result;
}

// splice nested conjunctions (disjunctions) into `node`
void flatten(FormulaNode &node) {
	if (node.kind != FormulaNode::AND && node.kind != FormulaNode::OR) {
		return;
	}
	std::vector<Tree> children;
	for (Tree &child : node.children) {
		flatten(*child);
		if (child->kind == node.kind) {
			for (Tree &grandchild : child->children) {
				children.push_back(std::move(grandchild));
			}
		} else {
			children.push_back(std::move(child));
		}
	}
	node.children = std::move(children);
}

// ∀ x. A ∧ ∀ x. B ≡ ∀ x. (A ∧ B): merge universal blocks over the same variables in conjunctions,
// so that a selector occurring in both ends up under a single quantifier
void merge(FormulaNode &node) {
	for (Tree &child : node.children) {
		merge(*child);
	}
	if (node.kind != FormulaNode::AND) {
		return;
	}
	flatten(node);
	auto sorted = [](std::vector<std::string> names) {
		std::sort(names.begin(), names.end());
		return names;
	};
	for (size_t i = 0; i < node.children.size(); i++) {
		FormulaNode &first = *node.children[i];
		if (first.kind != FormulaNode::BLOCK || !first.forall || first.variables.empty()) {
			continue;
		}
		const std::vector<std::string> names = sorted(first.names);
		if (std::adjacent_find(names.begin(), names.end()) != names.end()) {
			continue;
		}
		bool merged = false;
		for (size_t j = i + 1; j < node.children.size(); ) {
			FormulaNode &second = *node.children[j];
			if (second.kind != FormulaNode::BLOCK || !second.forall || sorted(second.names) != names) {
				j++;
				continue;
			}
			// rename the variables of the second block to the ones of the first
			std::vector<Z3_ast> from, to;
			for (size_t a = 0; a < second.variables.size(); a++) {
				size_t b = std::find(first.names.begin(), first.names.end(), second.names[a]) - first.names.begin();
				from.push_back(second.variables[a]);
				to.push_back(first.variables[b]);
			}
			substitute(*second.children[0], from, to);
			first.children[0] = make_binary(FormulaNode::AND, std::move(first.children[0]), std::move(second.children[0]));
			node.children.erase(node.children.begin() + j);
			merged = true;
		}
		if (merged) {
			merge(first);
		}
	}
}

// ∀ V. (D1 ∨ D2) ≡ ∀ V \ V'. (∀ V'. D1) ∨ D2 if no variable in V' occurs in D2: move the variables that only occur in
// the parts without selectors (e.g. constants that are never revealed and only occur in IC) into a block of their own
Tree separate(Tree node) {
	if (node->kind == FormulaNode::BLOCK && node->forall && !node->variables.empty()) {
		FormulaNode &body = *node->children[0];
		std::vector<Tree> disjuncts;
		if (body.kind == FormulaNode::IMPLIES) {
			disjuncts.push_back(make_unary(FormulaNode::NOT, std::move(body.children[0])));
			disjuncts.push_back(std::move(body.children[1]));
		} else if (body.kind == FormulaNode::OR) {
			disjuncts = std::move(body.children);
		} else if (body.kind == FormulaNode::NOT && body.children[0]->kind == FormulaNode::AND) {
			for (Tree &conjunct : body.children[0]->children) {
				disjuncts.push_back(make_unary(FormulaNode::NOT, std::move(conjunct)));
			}
		}
		if (!disjuncts.empty()) {
			std::vector<Tree> with_selectors, without_selectors;
			std::set<Z3_ast> used;
			for (Tree &disjunct : disjuncts) {
				if (mentions_selector(*disjunct)) {
					std::set<Z3_ast> constants = constants_of(*disjunct);
					used.insert(constants.begin(), constants.end());
					with_selectors.push_back(std::move(disjunct));
				} else {
					without_selectors.push_back(std::move(disjunct));
				}
			}
			std::vector<Z3_ast> kept, moved;
			std::vector<std::string> kept_names, moved_names;
			for (size_t i = 0; i < node->variables.size(); i++) {
				bool use = used.count(node->variables[i]);
				(use ? kept : moved).push_back(node->variables[i]);
				(use ? kept_names : moved_names).push_back(node->names[i]);
			}
			std::vector<Tree> new_disjuncts;
			if (!without_selectors.empty()) {
				Tree rest = make(FormulaNode::OR, std::move(without_selectors));
				new_disjuncts.push_back(moved.empty() || with_selectors.empty()
					? std::move(rest) : make_block(true, moved, moved_names, std::move(rest)));
			}
			bool restructured = !moved.empty() && !with_selectors.empty() && !new_disjuncts.empty();
			for (Tree &disjunct : with_selectors) {
				new_disjuncts.push_back(std::move(disjunct));
			}
			node->children[0] = make(FormulaNode::OR, std::move(new_disjuncts));
			if (restructured) {
				node->variables = kept;
				node->names = kept_names;
			}
		}
	}
	for (Tree &child : node->children) {
		child = separate(std::move(child));
	}
	return node;
}

// the path from `root` to `target` (both included), if `target` is in the tree
bool find_path(FormulaNode *root, const FormulaNode *target, std::vector<FormulaNode *> &path) {
	path.push_back(root);
	if (root == target) {
		return true;
	}
	for (Tree &child : root->children) {
		if (find_path(child.get(), target, path)) {
			return true;
		}
	}
	path.pop_back();
	return false;
}

void binders(FormulaNode *node, std::map<Z3_ast, FormulaNode *> &result) {
	if (node->kind == FormulaNode::BLOCK) {
		for (Z3_ast variable : node->variables) {
			result[variable] = node;
		}
	}
	for (Tree &child : node->children) {
		binders(child.get(), result);
	}
}

// whether the subformula at the end of `path` occurs positively (not below an odd number of negations)
bool positive_at(const std::vector<FormulaNode *> &path) {
	bool positive = true;
	for (size_t i = 0; i + 1 < path.size(); i++) {
		if (path[i]->kind == FormulaNode::NOT || (path[i]->kind == FormulaNode::IMPLIES && path[i]->children[0].get() == path[i + 1])) {
			positive = !positive;
		}
	}
	return positive;
}

/*
 * Replace the selector `selector` by a quantifier over its value, if this is equivalent:
 * all its occurrences have the same arguments, all of them are below the block Q binding the innermost argument,
 * and every variable bound above Q is an argument (or the value of a selector replaced before, which only depends on
 * variables bound above it). Then the values of the selector for different arguments are independent choices
 * made below Q, i.e. ∃ selector. F ≡ F with Q. body replaced by Q. ∃ k. (k ∈ {1, ..., n} ∧ body[selector(args) := k])
 * (the variables of Q that are no arguments are moved below k; below a negation, ∃ k becomes ∀ k).
 */
bool eliminate(Tree &root, Z3_func_decl selector, std::set<Z3_ast> &transparent) {
	std::vector<const FormulaNode *> atoms, occurrences;
	atoms_of(*root, atoms);
	std::set<Z3_ast> applications;
	for (const FormulaNode *atom : atoms) {
		bool occurs = false;
		visit_subterms(atom->atom, [&](Z3_ast term) {
			if (is_app(term) && decl_of(term) == selector) {
				applications.insert(term);
				occurs = true;
			}
		});
		if (occurs) {
			occurrences.push_back(atom);
		}
	}
	if (applications.size() != 1) {
		return false;
	}
	Z3_ast application = *applications.begin();
	Z3_app app = Z3_to_app(CONTEXT, application);
	std::set<Z3_ast> arguments;
	for (unsigned i = 0; i < Z3_get_app_num_args(CONTEXT, app); i++) {
		arguments.insert(Z3_get_app_arg(CONTEXT, app, i));
	}

	// the block binding the innermost argument, and the path to it
	std::map<Z3_ast, FormulaNode *> binder;
	binders(root.get(), binder);
	std::vector<FormulaNode *> path_to_q = {root.get()};
	for (Z3_ast argument : arguments) {
		auto found = binder.find(argument);
		if (found == binder.end()) {
			return false;
		}
		std::vector<FormulaNode *> path;
		find_path(root.get(), found->second, path);
		if (path.size() > path_to_q.size()) {
			// the binders of all arguments are on one path
			if (!std::equal(path_to_q.begin(), path_to_q.end(), path.begin())) {
				return false;
			}
			path_to_q = path;
		} else if (!std::equal(path.begin(), path.end(), path_to_q.begin())) {
			return false;
		}
	}
	FormulaNode *q = path_to_q.back();
	if (q->kind != FormulaNode::BLOCK) {
		return false;
	}
	for (size_t i = 0; i + 1 < path_to_q.size(); i++) {
		if (path_to_q[i]->kind == FormulaNode::BLOCK) {
			for (Z3_ast variable : path_to_q[i]->variables) {
				if (!arguments.count(variable) && !transparent.count(variable)) {
					return false;
				}
			}
		}
	}
	for (const FormulaNode *atom : occurrences) {
		std::vector<FormulaNode *> path;
		find_path(q, atom, path);
		if (path.empty()) {
			return false;
		}
	}

	// below Q: the arguments of Q, then the value of the selector, then the other variables of Q
	std::vector<Z3_ast> outer, inner;
	std::vector<std::string> outer_names, inner_names;
	for (size_t i = 0; i < q->variables.size(); i++) {
		bool argument = arguments.count(q->variables[i]);
		(argument ? outer : inner).push_back(q->variables[i]);
		(argument ? outer_names : inner_names).push_back(q->names[i]);
	}
	Tree body = std::move(q->children[0]);
	if (!inner.empty()) {
		body = make_block(q->forall, inner, inner_names, std::move(body));
	}
	Z3_ast value = fresh_constant("selected", real_sort());
	substitute(*body, {application}, {value});
	std::vector<Z3_ast> options;
	for (unsigned k = 1; k <= selector_candidates(selector); k++) {
		options.push_back(Z3_mk_eq(CONTEXT, value, numeral(k)));
	}
	Tree range = make_atom(Z3_mk_or(CONTEXT, options.size(), options.data()));
	bool positive = positive_at(path_to_q);
	q->children[0] = positive
		? make_block(false, {value}, {"selected"}, make_binary(FormulaNode::AND, std::move(range), std::move(body)))
		: make_block(true, {value}, {"selected"}, make_binary(FormulaNode::IMPLIES, std::move(range), std::move(body)));
	q->variables = outer;
	q->names = outer_names;
	transparent.insert(value);
	return true;
}

// the selectors in `node`
std::set<Z3_func_decl> selectors_of(const FormulaNode &node) {
	std::vector<const FormulaNode *> atoms;
	atoms_of(node, atoms);
	std::set<Z3_func_decl> result;
	for (const FormulaNode *atom : atoms) {
		std::set<Z3_func_decl> found = selectors_in(atom->atom);
		result.insert(found.begin(), found.end());
	}
	return result;
}

/*
 * The SyGuS problem for cvc5: Skolemize the formula, i.e. every existentially quantified variable becomes a function
 * to synthesize, of the universally quantified variables around it, the universally quantified variables become
 * the variables of the constraint, and every selector becomes predicates to synthesize:
 * with n candidates, b_1, ..., b_{n-1}, where the k-th candidate is selected iff ¬b_1 ∧ ... ∧ ¬b_{k-1} ∧ b_k
 * (the n-th iff all are false)
 */
struct SyGuS {
	std::ostringstream functions, variables;
	unsigned skolems = 0;
	std::map<Z3_func_decl, std::vector<Z3_func_decl>> predicates;
	bool any_function = false;

	static std::string sort_name(Z3_sort sort) {
		return Z3_sort_to_string(CONTEXT, sort);
	}

	void synth_fun(const std::string &name, const std::vector<Z3_sort> &domain, Z3_sort range) {
		functions << "(synth-fun " << name << " (";
		for (size_t i = 0; i < domain.size(); i++) {
			functions << (i ? " " : "") << "(p" << i << ' ' << sort_name(domain[i]) << ')';
		}
		functions << ") " << sort_name(range) << ")\n";
		any_function = true;
	}

	Z3_ast skolemize(FormulaNode &node, bool positive, std::vector<Z3_ast> &universals, std::vector<Z3_ast> &from, std::vector<Z3_ast> &to) {
		switch (node.kind) {
			case FormulaNode::ATOM:
				return encode_selectors(Z3_substitute(CONTEXT, node.atom, from.size(), from.data(), to.data()));
			case FormulaNode::NOT:
				return Z3_mk_not(CONTEXT, skolemize(*node.children[0], !positive, universals, from, to));
			case FormulaNode::IMPLIES: {
				Z3_ast left = skolemize(*node.children[0], !positive, universals, from, to);
				Z3_ast right = skolemize(*node.children[1], positive, universals, from, to);
				return Z3_mk_implies(CONTEXT, left, right);
			}
			case FormulaNode::AND:
			case FormulaNode::OR: {
				std::vector<Z3_ast> children;
				for (Tree &child : node.children) {
					children.push_back(skolemize(*child, positive, universals, from, to));
				}
				if (children.empty()) {
					return node.kind == FormulaNode::AND ? Z3_mk_true(CONTEXT) : Z3_mk_false(CONTEXT);
				}
				return node.kind == FormulaNode::AND
					? Z3_mk_and(CONTEXT, children.size(), children.data())
					: Z3_mk_or(CONTEXT, children.size(), children.data());
			}
			case FormulaNode::BLOCK: {
				size_t universals_before = universals.size(), substitution_before = from.size();
				bool universal = node.forall == positive;
				for (Z3_ast variable : node.variables) {
					Z3_sort sort = Z3_get_sort(CONTEXT, variable);
					if (universal) {
						universals.push_back(variable);
						variables << "(declare-var " << constant_name(variable) << ' ' << sort_name(sort) << ")\n";
					} else {
						std::string name = "q!sk" + std::to_string(skolems++);
						std::vector<Z3_sort> domain;
						for (Z3_ast argument : universals) {
							domain.push_back(Z3_get_sort(CONTEXT, argument));
						}
						Z3_func_decl skolem = Z3_mk_func_decl(CONTEXT, Z3_mk_string_symbol(CONTEXT, name.c_str()),
							domain.size(), domain.data(), sort);
						synth_fun(name, domain, sort);
						from.push_back(variable);
						to.push_back(Z3_mk_app(CONTEXT, skolem, universals.size(), universals.data()));
					}
				}
				Z3_ast result = skolemize(*node.children[0], positive, universals, from, to);
				universals.resize(universals_before);
				from.resize(substitution_before);
				to.resize(substitution_before);
				return result;
			}
		}
		return nullptr;
	}

	// replace selector(args) = k by the predicates
	Z3_ast encode_selectors(Z3_ast ast) {
		std::vector<Z3_ast> from, to;
		visit_subterms(ast, [&](Z3_ast term) {
			if (!is_app(term) || Z3_get_decl_kind(CONTEXT, decl_of(term)) != Z3_OP_EQ) {
				return;
			}
			Z3_app app = Z3_to_app(CONTEXT, term);
			Z3_ast left = Z3_get_app_arg(CONTEXT, app, 0), right = Z3_get_app_arg(CONTEXT, app, 1);
			if (!is_app(left) || !is_selector(decl_of(left)) || Z3_get_ast_kind(CONTEXT, right) != Z3_NUMERAL_AST) {
				return;
			}
			Z3_func_decl selector = decl_of(left);
			unsigned candidates = selector_candidates(selector);
			unsigned k = std::stoul(Z3_get_numeral_string(CONTEXT, right));
			std::vector<Z3_func_decl> &bits = predicates_of(selector, candidates);
			Z3_app selector_app = Z3_to_app(CONTEXT, left);
			std::vector<Z3_ast> arguments;
			for (unsigned i = 0; i < Z3_get_app_num_args(CONTEXT, selector_app); i++) {
				arguments.push_back(Z3_get_app_arg(CONTEXT, selector_app, i));
			}
			std::vector<Z3_ast> conjuncts;
			for (unsigned j = 1; j < k && j < candidates; j++) {
				conjuncts.push_back(Z3_mk_not(CONTEXT, Z3_mk_app(CONTEXT, bits[j - 1], arguments.size(), arguments.data())));
			}
			if (k < candidates) {
				conjuncts.push_back(Z3_mk_app(CONTEXT, bits[k - 1], arguments.size(), arguments.data()));
			}
			from.push_back(term);
			to.push_back(k < 1 || k > candidates ? Z3_mk_false(CONTEXT)
				: conjuncts.empty() ? Z3_mk_true(CONTEXT) : Z3_mk_and(CONTEXT, conjuncts.size(), conjuncts.data()));
		});
		return from.empty() ? ast : Z3_substitute(CONTEXT, ast, from.size(), from.data(), to.data());
	}

	std::vector<Z3_func_decl> &predicates_of(Z3_func_decl selector, unsigned candidates) {
		auto found = predicates.find(selector);
		if (found != predicates.end()) {
			return found->second;
		}
		std::vector<Z3_func_decl> &bits = predicates[selector];
		std::vector<Z3_sort> domain;
		for (unsigned i = 0; i < Z3_get_domain_size(CONTEXT, selector); i++) {
			domain.push_back(Z3_get_domain(CONTEXT, selector, i));
		}
		std::string base = "q!b" + std::to_string(predicates.size());
		for (unsigned j = 1; j < candidates; j++) {
			std::string name = base + "!" + std::to_string(j);
			bits.push_back(Z3_mk_func_decl(CONTEXT, Z3_mk_string_symbol(CONTEXT, name.c_str()),
				domain.size(), domain.data(), Z3_mk_bool_sort(CONTEXT)));
			synth_fun(name, domain, Z3_mk_bool_sort(CONTEXT));
		}
		return bits;
	}
};

// Z3's general solver on `formula`, which (unlike the simple solver used elsewhere) chooses tactics for the formula,
// e.g. quantifier elimination; no answer if it cannot decide it within `timeout` milliseconds
std::optional<bool> z3_satisfiable(Z3_ast formula, unsigned timeout) {
	Z3_solver solver = Z3_mk_solver(CONTEXT);
	Z3_solver_inc_ref(CONTEXT, solver);
	Z3_params params = Z3_mk_params(CONTEXT);
	Z3_params_inc_ref(CONTEXT, params);
	Z3_params_set_uint(CONTEXT, params, Z3_mk_string_symbol(CONTEXT, "timeout"), timeout);
	Z3_solver_set_params(CONTEXT, solver, params);
	Z3_params_dec_ref(CONTEXT, params);
	Z3_solver_assert(CONTEXT, solver, formula);
	Z3_lbool result = Z3_solver_check(CONTEXT, solver);
	Z3_solver_dec_ref(CONTEXT, solver);
	z3::check_error();
	if (result == Z3_L_UNDEF) {
		return std::nullopt;
	}
	return result == Z3_L_TRUE;
}

std::string run_cvc5(const std::string &problem, std::string &how) {
#ifdef __EMSCRIPTEN__
	// no processes in the browser
	(void) problem;
	how = "cvc5 is not available in the web build";
	return "";
#else
	char path[] = "/tmp/checkmate-XXXXXX.sy";
	int descriptor = mkstemps(path, 3);
	if (descriptor < 0) {
		how = "could not write the problem for cvc5";
		return "";
	}
	FILE *file = fdopen(descriptor, "w");
	fputs(problem.c_str(), file);
	fclose(file);

	const char *configured = std::getenv("CHECKMATE_CVC5");
	std::string cvc5 = configured ? configured : "cvc5";
	std::string command = "'" + cvc5 + "' --lang sygus2 --tlimit=" + std::to_string(CVC5_TIMEOUT) + " '" + path + "' 2>&1";
	std::string output;
	FILE *pipe = popen(command.c_str(), "r");
	if (pipe) {
		char buffer[4096];
		size_t read;
		while ((read = fread(buffer, 1, sizeof buffer, pipe)) > 0) {
			output.append(buffer, read);
		}
		int status = pclose(pipe);
		if (WIFEXITED(status) && WEXITSTATUS(status) == 127) {
			how = "cvc5 not found (install cvc5 or set CHECKMATE_CVC5 to its path)";
			output.clear();
		}
	} else {
		how = "could not run cvc5";
	}
	unlink(path);
	return output;
#endif
}

// the SyGuS problem for cvc5 on a closed formula as it is, if it cannot be Skolemized: the selectors become functions
// to synthesize (with real values, as in the formula, which restricts them to the candidates), and the quantifiers stay
// in the constraint, which cvc5 accepts
std::string raw_sygus_problem(Z3_ast formula) {
	std::ostringstream problem;
	problem << "(set-logic ALL)\n";
	for (Z3_func_decl selector : selectors_in(formula)) {
		problem << "(synth-fun " << decl_name(selector) << " (";
		for (unsigned i = 0; i < Z3_get_domain_size(CONTEXT, selector); i++) {
			problem << (i ? " " : "") << "(p" << i << " Real)";
		}
		problem << ") Real)\n";
	}
	problem << "(constraint " << Z3_ast_to_string(CONTEXT, formula) << ")\n(check-synth)\n";
	return problem.str();
}

// run cvc5 on `problem` and read its answer: infeasible (no selectors exist), synthesized, or undecided
Answer solve_with_cvc5(const std::string &problem, const std::string &replaced_text, std::string &how) {
	std::string cvc5_how;
	std::string output = run_cvc5(problem, cvc5_how);
	std::istringstream lines(output);
	std::string first;
	while (std::getline(lines, first) && first.find_first_not_of(" \t\r") == std::string::npos) {
	}
	first.erase(0, first.find_first_not_of(" \t\r"));
	if (first.rfind("infeasible", 0) == 0) {
		how = "cvc5 (no selectors exist), " + replaced_text + ", after Z3 could not decide it";
		return Answer::NO;
	}
	if (first.rfind("(", 0) == 0) {
		how = "cvc5 (synthesized the selectors), " + replaced_text + ", after Z3 could not decide it";
		return Answer::YES;
	}
	how = "neither Z3 nor cvc5 could decide it (" + replaced_text + "; cvc5: "
		+ (cvc5_how.empty() ? (first.empty() ? std::string("no answer") : first) : cvc5_how) + ")";
	return Answer::UNKNOWN;
}

} // namespace

Z3_func_decl fresh_selector(unsigned arity, unsigned candidates) {
	std::string name = SELECTOR_PREFIX + std::to_string(selector_count++) + "!" + std::to_string(candidates);
	std::vector<Z3_sort> domain(arity, real_sort());
	Z3_func_decl decl = Z3_mk_func_decl(CONTEXT, Z3_mk_string_symbol(CONTEXT, name.c_str()), domain.size(), domain.data(), real_sort());
	z3::check_error();
	return decl;
}

Selector::Selector(const std::vector<z3::Real> &arguments, unsigned candidates) {
	Z3_func_decl decl = fresh_selector(arguments.size(), candidates);
	std::vector<Z3_ast> args;
	for (const z3::Real &argument : arguments) {
		args.push_back(argument.raw());
	}
	application = Z3_mk_app(CONTEXT, decl, args.size(), args.data());
	z3::check_error();
}

z3::Bool Selector::selects(unsigned k) const {
	return z3::Bool::wrap(Z3_mk_eq(CONTEXT, application, numeral(k)));
}

bool contains_selectors(const z3::Bool &formula) {
	return !selectors_in(formula.raw()).empty();
}

std::optional<bool> satisfiable_within(const z3::Bool &formula, unsigned timeout) {
	return z3_satisfiable(formula.raw(), timeout);
}

Answer check_practicality(const Input &input, const z3::Bool &ic, const z3::Bool &result, std::string &how) {
	if (!contains_selectors(result)) {
		how = "without selectors";
		return violated_somewhere(ic, result) ? Answer::NO : Answer::YES;
	}

	// ∀ known (IC → result) as ∀ known. (∀ unknown. ¬IC) ∨ result: the unknown constants only occur in IC,
	// as the result quantifies them wherever they occur
	std::vector<Z3_ast> known, unknown;
	std::vector<std::string> known_names, unknown_names;
	std::set<std::string> names;
	for (const auto &entry : input.utilities) {
		names.insert(entry.first);
	}
	for (const std::string &name : names) {
		Z3_ast constant = z3::Real::constant(name).raw();
		(input.unknowns.count(name) ? unknown : known).push_back(constant);
		(input.unknowns.count(name) ? unknown_names : known_names).push_back(name);
	}
	Tree tree;
	try {
		Tree not_ic = make_unary(FormulaNode::NOT, convert(ic.raw()));
		Tree body = make_binary(FormulaNode::OR, make_block(true, unknown, unknown_names, std::move(not_ic)), convert(result.raw()));
		tree = make_block(true, known, known_names, std::move(body));
	} catch (Unsupported &) {
		tree = nullptr;
	}

	// 1. replace selectors by quantifiers wherever possible
	unsigned replaced = 0, remaining = 0;
	Z3_ast formula;
	if (tree) {
		// first separate the variables without selectors from each block, then merge the blocks that bind the same
		// variables (merging first would turn the bodies into conjunctions, from which nothing can be separated)
		tree = separate(std::move(tree));
		merge(*tree);
		std::set<Z3_ast> transparent;
		bool progress = true;
		while (progress) {
			progress = false;
			for (Z3_func_decl selector : selectors_of(*tree)) {
				if (eliminate(tree, selector, transparent)) {
					replaced++;
					progress = true;
				}
			}
		}
		remaining = selectors_of(*tree).size();
		formula = build(*tree);
	} else {
		std::vector<Z3_app> bound;
		for (Z3_ast constant : known) {
			bound.push_back(Z3_to_app(CONTEXT, constant));
		}
		Z3_ast implication = Z3_mk_implies(CONTEXT, ic.raw(), result.raw());
		std::vector<Z3_app> all = bound;
		for (Z3_ast constant : unknown) {
			all.push_back(Z3_to_app(CONTEXT, constant));
		}
		formula = Z3_mk_forall_const(CONTEXT, 0, all.size(), all.data(), 0, nullptr, implication);
		remaining = selectors_in(result.raw()).size();
	}
	std::string replaced_text = std::to_string(replaced) + " of " + std::to_string(replaced + remaining)
		+ " selector" + (replaced + remaining == 1 ? "" : "s") + " replaced by quantifiers";

	// 2. Z3, with the remaining selectors as uninterpreted function symbols
	std::optional<bool> answer = z3_satisfiable(formula, Z3_TIMEOUT);
	if (answer) {
		how = "Z3, " + replaced_text;
		return *answer ? Answer::YES : Answer::NO;
	}
	// 3. cvc5: synthesize the remaining selectors, on the Skolemized formula if it could be restructured,
	// otherwise on the formula as it is
	if (!tree) {
		return solve_with_cvc5(raw_sygus_problem(formula), replaced_text + " (formula not restructured)", how);
	}
	SyGuS sygus;
	std::vector<Z3_ast> universals, from, to;
	Z3_ast matrix = sygus.skolemize(*tree, true, universals, from, to);
	if (!sygus.any_function) {
		sygus.synth_fun("q!unused", {}, Z3_mk_bool_sort(CONTEXT));
	}
	std::ostringstream problem;
	problem << "(set-logic ALL)\n" << sygus.functions.str() << sygus.variables.str()
		<< "(constraint " << Z3_ast_to_string(CONTEXT, matrix) << ")\n(check-synth)\n";
	return solve_with_cvc5(problem.str(), replaced_text, how);
}

} // namespace cefg
