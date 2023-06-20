#ifndef __checkmate_utils__
#define __checkmate_utils__

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

#endif
