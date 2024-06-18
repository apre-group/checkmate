#ifndef __checkmate_property__
#define __checkmate_property__

struct Input;
struct Options;

// reference to a utility tuple in a leaf
struct UtilityTuple {
	const std::vector<Utility> &leaf;
	UtilityTuple(decltype(leaf) leaf) : leaf(leaf) {}
	size_t size() const { return leaf.size(); }
	const Utility &operator[](size_t index) const { return leaf[index]; }
	std::vector<Utility>::const_iterator begin() const { return leaf.cbegin(); }
	std::vector<Utility>::const_iterator end() const { return leaf.cend(); }

	bool operator==(const UtilityTuple &other) const {
		// quick return for when you have the same reference
		if(this == &other)
			return true;
		if(size() != other.size())
			return false;
		for(size_t i = 0; i < size(); i++)
			if(!leaf[i].is(other.leaf[i]))
				return false;
		return true;
	}
};

// when hashing, hash its utilities sequentially
template<>
struct std::hash<UtilityTuple> {
	size_t operator()(UtilityTuple tuple) const {
		 size_t hash = 0;
		 for(const Utility &utility : tuple)
			 hash ^= std::hash<Utility>{}(utility);
		 return hash;
	}
};

using UtilityTuplesSet = std::unordered_set<UtilityTuple>;

struct PotentialCase {
	UtilityTuplesSet utilities;
	std::vector<z3::Bool> _case;
};

void analyse_properties(const Options &options, const Input &input);

std::vector<PotentialCase> practicality_rec(z3::Solver &solver, const Options &options, const Input &input, Node *node, std::vector<z3::Bool> current_case);

bool practicality_admin(z3::Solver *solver, const Options &options, Node *root, std::vector<z3::Bool> current_case);


#endif
