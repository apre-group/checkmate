#ifndef __checkmate_utility__
#define __checkmate_utility__

#include <climits>
#include <ostream>
// NB standard-library <utility>, not this file
#include <utility>

#include "z3++.hpp"

// a real/infinitesimal pair
struct Utility {
	// real and infinitesimal parts
	z3::Real real, infinitesimal;

	// is this exactly the same as `other`
	bool is(Utility other) const {
		return real.is(other.real) && infinitesimal.is(other.infinitesimal);
	}

	Utility operator+(Utility other) const {
		return {real + other.real, infinitesimal + other.infinitesimal};
	}

	Utility operator-(Utility other) const {
		return {real - other.real, infinitesimal - other.infinitesimal};
	}

	Utility operator*(Utility other) const {
		return {real * other.real, infinitesimal * other.infinitesimal};
	}

	Utility operator-() const {
		return {-real, -infinitesimal};
	}

	z3::Bool operator==(Utility other) const {
		if(real.is(other.real))
			return infinitesimal == other.infinitesimal;
		if(infinitesimal.is(other.infinitesimal))
			return real == other.real;
		return real == other.real && infinitesimal == other.infinitesimal;
	}

	z3::Bool operator!=(Utility other) const {
		if(real.is(other.real))
			return infinitesimal != other.infinitesimal;
		if(infinitesimal.is(other.infinitesimal))
			return real != other.real;
		return real != other.real || infinitesimal != other.infinitesimal;
	}

	z3::Bool operator>(Utility other) const {
		if(real.is(other.real))
			return infinitesimal > other.infinitesimal;
		if(infinitesimal.is(other.infinitesimal))
			return real > other.real;
		return real > other.real || (real == other.real && infinitesimal > other.infinitesimal);
	}

	z3::Bool operator<(Utility other) const {
		if(real.is(other.real))
			return infinitesimal < other.infinitesimal;
		if(infinitesimal.is(other.infinitesimal))
			return real < other.real;
		return real < other.real || (real == other.real && infinitesimal < other.infinitesimal);
	}

	z3::Bool operator>=(Utility other) const {
		if(real.is(other.real))
			return infinitesimal >= other.infinitesimal;
		if(infinitesimal.is(other.infinitesimal))
			return real >= other.real;
		return real > other.real || (real == other.real && infinitesimal >= other.infinitesimal);
	}

	z3::Bool operator<=(Utility other) const {
		if(real.is(other.real))
			return infinitesimal <= other.infinitesimal;
		if(infinitesimal.is(other.infinitesimal))
			return real <= other.real;
		return real < other.real || (real == other.real && infinitesimal <= other.infinitesimal);
	}
};

inline std::ostream &operator<<(std::ostream &out, Utility utility) {
	return out << utility.real << " + " << utility.infinitesimal;
}

// used in e.g. hash tables instead of operator==
template<>
struct std::equal_to<Utility> {
	bool operator()(Utility left, Utility right) const {
		return left.real.is(right.real) && left.infinitesimal.is(right.infinitesimal);
	}
};

// hash a utility by combining the bits of its constituent ids, then hash _that_
template<>
struct std::hash<Utility> {
	bool operator()(Utility utility) const {
		size_t real_id = utility.real.id();
		size_t infinitesimal_id = utility.infinitesimal.id();
		size_t combined = real_id << (CHAR_BIT * sizeof(unsigned)) | infinitesimal_id;
		return std::hash<size_t>{}(combined);
	}
};

#endif
