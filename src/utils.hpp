#ifndef __checkmate_utils__
#define __checkmate_utils__

#include <ostream>
#include <vector>

#ifdef __GNUC__
#define UNREACHABLE __builtin_unreachable();
#else
#define UNREACHABLE
#endif

template<typename T>
std::ostream &operator<<(std::ostream &out, const std::vector<T> &vector) {
	out << '[';
	bool comma = false;
	for (const T &x : vector) {
		if(comma)
			out << ", ";
		comma = true;
		out << x;
	}
	out << ']';
	return out;
}

#endif
