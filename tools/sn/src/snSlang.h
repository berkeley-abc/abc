/**CFile****************************************************************

  FileName    [snSlang.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Slang-to-SN RTL frontend.]

  Synopsis    [Public API for the Slang-based SystemVerilog-to-SN frontend.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snSlang.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_SLANG_H
#define SN_SLANG_H

#include "sn.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct sn_slang_timing_t
{
    double parse_seconds;
    double elaborate_seconds;
    double import_seconds;
} sn_slang_timing_t;

typedef enum sn_slang_assertion_policy_t
{
    SN_SLANG_ASSERT_WARN = 0,
    SN_SLANG_ASSERT_IGNORE,
    SN_SLANG_ASSERT_ERROR
} sn_slang_assertion_policy_t;

typedef enum sn_slang_unknown_module_policy_t
{
    SN_SLANG_UNKNOWN_DEFAULT = 0, // strict with Liberty, warn-and-drop for legacy RTL
    SN_SLANG_UNKNOWN_ERROR,
    SN_SLANG_UNKNOWN_WARN_DROP
} sn_slang_unknown_module_policy_t;

typedef struct sn_slang_options_t
{
    int define_count;
    const char* const* defines;
    int blackbox_count;
    const char* const* blackboxes;
    bool blackbox_empty_modules;
    bool memories_from_attributes_only;
    bool preserve_metadata;
    sn_slang_assertion_policy_t assertion_policy;
    // Optional first Liberty file (legacy single-file convenience). Scalar cells
    // become compact gates; vector cells remain opaque macro modules.
    const char* liberty_file;
    // Additional files in order, each retaining its own types, templates and units.
    int liberty_count;
    const char* const* liberty_files;
    sn_slang_unknown_module_policy_t unknown_module_policy;
    // Every Liberty argument may be a .lib text or an .snlib binary model
    // (chosen by the file's magic). With a cache directory, a text library is
    // loaded from <dir>/<basename>.snlib when that file matches the text's
    // size and hash, and written there after parsing otherwise.
    const char* liberty_cache_dir;
    // Ordered preprocessor search paths and lazy Verilog library source files.
    int include_directory_count;
    const char* const* include_directories;
    int library_source_count;
    const char* const* library_sources;
    // Optional, new JSON file describing elaborated top-port bit selectors and
    // normalized SN offsets. Packed integral input/output ports only; no unions.
    // Diagnostics only, not a correspondence proof. Existing files refuse.
    const char* port_layout_file;
} sn_slang_options_t;

// Parse, elaborate, and import SystemVerilog source files into a new SN design.
// Diagnostics are written to stderr. The caller owns a non-null result and must
// release it with sn_design_destroy().
sn_design_t* sn_slang_read_files(int file_count, const char* const* file_paths);

// As above, but ask Slang to elaborate the named module as the sole top.
sn_design_t* sn_slang_read_files_top(int file_count, const char* const* file_paths, const char* top_module);

// As above, and return wall-clock time spent in Slang parsing, Slang semantic
// elaboration, and conversion of the elaborated AST into hierarchical SN.
sn_design_t* sn_slang_read_files_top_timed(int file_count, const char* const* file_paths, const char* top_module,
                                           sn_slang_timing_t* timing);

// Complete the Slang-dependent side of the process boundary in one call. The
// resulting file is consumed by sn_design_read_binary_file(), normally through
// ABC's @read or @slang command. Returns false after frontend diagnostics on import failure.
bool sn_slang_write_binary_files_top_timed(int file_count, const char* const* file_paths, const char* top_module,
                                           const char* output_path, sn_slang_timing_t* timing);

// As above, with command-line-style preprocessor definitions such as "NAME" or "NAME=value".
bool sn_slang_write_binary_files_top_defines_timed(int file_count, const char* const* file_paths,
                                                   const char* top_module, int define_count,
                                                   const char* const* defines, const char* output_path,
                                                   sn_slang_timing_t* timing);

// General entry points for callers that need preprocessor definitions, metadata, memory, black-box, or formal
// statement policy. Module names in options->blackboxes are repeatable and take precedence over the source body.
sn_design_t* sn_slang_read_files_top_options_timed(int file_count, const char* const* file_paths,
                                                   const char* top_module, const sn_slang_options_t* options,
                                                   sn_slang_timing_t* timing);
bool sn_slang_write_binary_files_top_options_timed(int file_count, const char* const* file_paths,
                                                   const char* top_module, const sn_slang_options_t* options,
                                                   const char* output_path, sn_slang_timing_t* timing);

#ifdef __cplusplus
}
#endif

#endif
