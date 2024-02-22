#ifndef __checkmate_utils__
#define __checkmate_utils__

#include <ostream>
#include <vector>
#include <unordered_set>

#ifdef __GNUC__
#define UNREACHABLE __builtin_unreachable();
#else
#define UNREACHABLE
#endif

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

}

#endif
