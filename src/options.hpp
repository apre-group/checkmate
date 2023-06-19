#ifndef __checkmate_options__
#define __checkmate_options__

#include <string>

struct Options {
	enum class Mode {
		ANALYZE
	};
	Options(char **argv);
	Mode mode;
	const char *input_path;
};

#endif
