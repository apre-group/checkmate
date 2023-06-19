#ifndef __checkmate_utils__
#define __checkmate_utils__

#ifdef __GNUC__
#define UNREACHABLE __builtin_unreachable();
#else
#define UNREACHABLE
#endif

#endif
