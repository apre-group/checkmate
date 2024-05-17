#ifndef __checkmate_utils__
#define __checkmate_utils__

#include <ostream>
#include <vector>
#include <unordered_set>
#include <functional>

#ifdef __GNUC__
#define UNREACHABLE __builtin_unreachable();
#else
#define UNREACHABLE
#endif

enum class PropertyType {
	WeakImmunity,
	WeakerImmunity,
	CollusionResilience,
	Practicality
};

namespace std {
	template<typename T>
	ostream &operator<<(ostream &out, const vector<T> &vector) {
		out << '[';
		bool comma = false;
		for (const T &x: vector) {
			if (comma)
				out << ", ";
			comma = true;
			out << x;
		}
		out << ']';
		return out;
	}

	template<typename T>
	ostream &operator<<(ostream &out, const unordered_set<T> &vector) {
		out << '{';
		bool comma = false;
		for (const T &x: vector) {
			if (comma)
				out << ", ";
			comma = true;
			out << x;
		}
		out << '}';
		return out;
	}

	template<typename T>
	ostream &operator<<(ostream &out, const std::reference_wrapper<T> &wrapper) {
		return out << wrapper.get();
	}

	// overloading ostream for PropertyType
	inline ostream &operator<<(ostream &out, const PropertyType &type) {
		switch(type) {
			case PropertyType::WeakImmunity:
				out << "WEAK IMMUNITY";
				break;
			case PropertyType::WeakerImmunity:
				out << "WEAKER IMMUNITY";
				break;
			case PropertyType::CollusionResilience:
				out << "COLLUSION RESILIENCE";
				break;
			case PropertyType::Practicality:
				out << "PRACTICALITY";
				break;
			default:
				out << "UNKNOWN PROPERTY";
				break;
		}
		return out;
	}
}

#endif
