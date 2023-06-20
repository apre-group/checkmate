#ifndef __checkmate_utility__
#define __checkmate_utility__

#include <ostream>

#include "z3++.hpp"

struct Utility {
	z3::Real real, infinitesimal;

	Utility operator+(const Utility &other) const {
		return {real + other.real, infinitesimal + other.infinitesimal};
	}

	Utility operator-(const Utility &other) const {
		return {real + other.real, infinitesimal + other.infinitesimal};
	}

	Utility operator*(const Utility &other) const {
		return {real * other.real, infinitesimal * other.infinitesimal};
	}

	Utility operator-() const {
		return {-real, -infinitesimal};
	}

	z3::Bool operator==(const Utility &other) const {
		if(real.is(other.real))
			return infinitesimal == other.infinitesimal;
		if(infinitesimal.is(other.infinitesimal))
			return real == other.real;
		return real == other.real && infinitesimal == other.infinitesimal;
	}

	z3::Bool operator!=(const Utility &other) const {
		if(real.is(other.real))
			return infinitesimal != other.infinitesimal;
		if(infinitesimal.is(other.infinitesimal))
			return real != other.real;
		return real != other.real || infinitesimal != other.infinitesimal;
	}

	z3::Bool operator>(const Utility &other) const {
		if(real.is(other.real))
			return infinitesimal > other.infinitesimal;
		if(infinitesimal.is(other.infinitesimal))
			return real > other.real;
		return real > other.real || (real == other.real && infinitesimal > other.infinitesimal);
	}

	z3::Bool operator>=(const Utility &other) const {
		if(real.is(other.real))
			return infinitesimal >= other.infinitesimal;
		if(infinitesimal.is(other.infinitesimal))
			return real >= other.real;
		return real > other.real || (real == other.real && infinitesimal >= other.infinitesimal);
	}
};

inline std::ostream &operator<<(std::ostream &out, const Utility &utility) {
	return out << utility.real << " + " << utility.infinitesimal;
}

#endif
