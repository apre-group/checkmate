#ifndef __checkmate_cefg_run__
#define __checkmate_cefg_run__

// the analysis of conditional extensive form games (CEFGs), imported from the cefg branch;
// the only part of src/cefg/ the rest of CheckMate uses
namespace cefg {

// analyse the game at the input path given in `argv` (as for the checkmate executable), returning an exit status;
// `argv` must not contain options for EFGs only or not supported for CEFGs (the caller removes them)
int run(char **argv);

}

#endif
