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

	template<typename Utility>
    struct hash<std::vector<Utility>> {
        size_t operator()(const std::vector<Utility> &v) const {
            size_t hashValue = 0;
			for (const auto& util : v) {
				// Combine the hash values of individual Utility objects in the vector
				hashValue ^= hash<Utility>()(util);
			}
        	return hashValue; 
        }
    };

	template<>
    struct equal_to<std::vector<Utility>> {
        size_t operator()(const std::vector<Utility> &left, const std::vector<Utility> &right) const {
			if (left.size() != right.size()) return false;
			for (size_t i = 0; i < left.size(); i++) {
                if(!(equal_to<Utility>()(left[i], right[i])))  
				    return false;
            }
            return true;
        }
    };

}

#endif
