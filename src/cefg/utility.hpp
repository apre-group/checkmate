#ifndef __checkmate_cefg_utility__
#define __checkmate_cefg_utility__

#include <climits>
#include <iostream>
// NB standard-library <utility>, not this file
#include <utility>

#include "z3++.hpp"

// imported from the cefg branch (c9c6e6f); wrapped in namespace cefg next to the EFG engine in src/
namespace cefg {

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
		if (!(infinitesimal.is(z3::Real::ZERO)) && !(other.infinitesimal.is(z3::Real::ZERO))) {
			std::cerr << "mulitplication of two infinitesimals not supported" << std::endl;
			std::exit(EXIT_FAILURE);
		}
		return {real * other.real, infinitesimal * other.real + real * other.infinitesimal};
	}

	Utility operator/(Utility other) const {
		if (!other.infinitesimal.is(z3::Real::ZERO)) {
			std::cerr << "division by infinitesimals not supported" << std::endl;
			std::exit(EXIT_FAILURE);
		}
		return {real / other.real, infinitesimal / other.real};
	}

	Utility operator-() const {
		return {-real, -infinitesimal};
	}

	z3::Bool operator==(Utility other) const {
		if (real.is(other.real))
			return infinitesimal == other.infinitesimal;
		if (infinitesimal.is(other.infinitesimal))
			return real == other.real;
		return real == other.real && infinitesimal == other.infinitesimal;
	}

	z3::Bool operator!=(Utility other) const {
		if (real.is(other.real))
			return infinitesimal != other.infinitesimal;
		if (infinitesimal.is(other.infinitesimal))
			return real != other.real;
		return real != other.real || infinitesimal != other.infinitesimal;
	}

	z3::Bool operator>(Utility other) const {
		if (real.is(other.real))
			return infinitesimal > other.infinitesimal;
		if (infinitesimal.is(other.infinitesimal))
			return real > other.real;
		return real > other.real || (real == other.real && infinitesimal > other.infinitesimal);
	}

	z3::Bool operator<(Utility other) const {
		if (real.is(other.real))
			return infinitesimal < other.infinitesimal;
		if (infinitesimal.is(other.infinitesimal))
			return real < other.real;
		return real < other.real || (real == other.real && infinitesimal < other.infinitesimal);
	}

	z3::Bool operator>=(Utility other) const {
		if (real.is(other.real))
			return infinitesimal >= other.infinitesimal;
		if (infinitesimal.is(other.infinitesimal))
			return real >= other.real;
		return real > other.real || (real == other.real && infinitesimal >= other.infinitesimal);
	}

	z3::Bool operator<=(Utility other) const {
		if (real.is(other.real))
			return infinitesimal <= other.infinitesimal;
		if (infinitesimal.is(other.infinitesimal))
			return real <= other.real;
		return real < other.real || (real == other.real && infinitesimal <= other.infinitesimal);
	}
};



inline std::ostream &operator<<(std::ostream &out, Utility utility) {
	return out << utility.real << " + " << utility.infinitesimal;
}

// used in e.g. hash tables instead of operator==
} // namespace cefg
template<>
struct std::equal_to<cefg::Utility> {
	bool operator()(cefg::Utility left, cefg::Utility right) const {
		return left.real.is(right.real) && left.infinitesimal.is(right.infinitesimal);
	}
};
namespace cefg {

// hash a utility by combining the bits of its constituent ids, then hash _that_
} // namespace cefg
template<>
struct std::hash<cefg::Utility> {
	size_t operator()(cefg::Utility utility) const {
		size_t real_id = utility.real.id();
		size_t infinitesimal_id = utility.infinitesimal.id();
		size_t combined = real_id << (CHAR_BIT * sizeof(unsigned)) | infinitesimal_id;
		return std::hash<size_t>{}(combined);
	}
};
namespace cefg {

} // namespace cefg

#endif
