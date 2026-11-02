#include "build.h"
#include "colors.h"
#include "kissat.h"
#include "print.h"

#include <stdio.h>

ABC_NAMESPACE_IMPL_START

const char *kissat_signature (void) { return "kissat-" VERSION; }

const char *kissat_id (void) { return ID; }

const char *kissat_compiler (void) { return COMPILER; }

static const char *copyright_lines[] = {
    "Copyright (c) 2021-2024 Armin Biere University of Freiburg",
    "Copyright (c) 2019-2021 Armin Biere Johannes Kepler University Linz",
    0};

const char **kissat_copyright (void) { return copyright_lines; }

const char *kissat_version (void) { return VERSION; }

#define PREFIX(COLORS) \
  do { \
    if (prefix) \
      fputs (prefix, Abc_FrameGlobalGetOut()); \
    COLOR (COLORS); \
  } while (0)

#define NL() \
  do { \
    fputs ("\n", Abc_FrameGlobalGetOut()); \
    COLOR (NORMAL); \
  } while (0)

void kissat_build (const char *prefix) {
  TERMINAL (stdout, 1);
  if (!prefix)
    connected_to_terminal = false;

  PREFIX (MAGENTA);
  if (ID)
    fprintf ( Abc_FrameGlobalGetOut(), "Version %s %s", VERSION, ID);
  else
    fprintf ( Abc_FrameGlobalGetOut(), "Version %s", VERSION);
  NL ();

  PREFIX (MAGENTA);
  fprintf ( Abc_FrameGlobalGetOut(), "%s", COMPILER);
  NL ();

  PREFIX (MAGENTA);
  fprintf ( Abc_FrameGlobalGetOut(), "%s", BUILD);
  NL ();
}

void kissat_banner (const char *prefix, const char *name) {
  TERMINAL (stdout, 1);
  if (!prefix)
    connected_to_terminal = false;

  PREFIX (BOLD MAGENTA);
  fprintf ( Abc_FrameGlobalGetOut(), "%s", name);
  NL ();

  PREFIX (BOLD MAGENTA);
  NL ();

  for (const char **p = kissat_copyright (), *line; (line = *p); p++) {
    PREFIX (BOLD MAGENTA);
    fputs (line, Abc_FrameGlobalGetOut());
    NL ();
  }

  if (prefix) {
    PREFIX ("");
    NL ();
  }

  kissat_build (prefix);
}

ABC_NAMESPACE_IMPL_END
