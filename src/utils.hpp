#ifndef __checkmate_utils__
#define __checkmate_utils__

#include <vector>

#ifdef __GNUC__
#define UNREACHABLE __builtin_unreachable();
#else
#define UNREACHABLE
#endif

template<typename F>
struct Defer {
	Defer(F deferred) : deferred(deferred) {}
	~Defer() { deferred(); }
	F deferred;
};

template<typename F>
Defer<F> defer(F deferred) { return Defer<F>(deferred); }

class BinaryCounter {
public:
	BinaryCounter(size_t num_digits) : digits(num_digits, false) {}
	bool operator[](size_t i) const { return digits[i]; }

	operator bool() const {
		for(size_t i = 0; i < digits.size(); i++)
			if(digits[i])
				return true;
		return false;
	}

	void operator++(int) {
		for(size_t i = 0; i < digits.size(); i++)
			if((digits[i] = !digits[i]))
				break;
	}

private:
	std::vector<bool> digits;
};

#endif
