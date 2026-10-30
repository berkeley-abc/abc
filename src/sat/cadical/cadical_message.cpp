#include "global.h"

#include "internal.hpp"

ABC_NAMESPACE_IMPL_START

namespace CaDiCaL {

/*------------------------------------------------------------------------*/
#ifndef CADICAL_QUIET
/*------------------------------------------------------------------------*/

void Internal::print_prefix () { fputs (prefix.c_str (), Abc_FrameGlobalGetOut()); }

void Internal::vmessage (const char *fmt, va_list &ap) {
#ifdef LOGGING
  if (!opts.log)
#endif
    if (opts.quiet)
      return;
  print_prefix ();
  vfprintf ( Abc_FrameGlobalGetOut(), fmt, ap);
  fputc ('\n', Abc_FrameGlobalGetOut());
  fflush (Abc_FrameGlobalGetOut());
}

void Internal::message (const char *fmt, ...) {
#ifdef LOGGING
  if (!opts.log)
#endif
    if (opts.quiet)
      return;

  va_list ap;
  va_start (ap, fmt);
  vmessage (fmt, ap);
  va_end (ap);
}

void Internal::message () {
#ifdef LOGGING
  if (!opts.log)
#endif
    if (opts.quiet)
      return;
  print_prefix ();
  fputc ('\n', Abc_FrameGlobalGetOut());
  fflush (Abc_FrameGlobalGetOut());
}

/*------------------------------------------------------------------------*/

void Internal::vverbose (int level, const char *fmt, va_list &ap) {
#ifdef LOGGING
  if (!opts.log)
#endif
    if (opts.quiet || level > opts.verbose)
      return;
  print_prefix ();
  vfprintf ( Abc_FrameGlobalGetOut(), fmt, ap);
  fputc ('\n', Abc_FrameGlobalGetOut());
  fflush (Abc_FrameGlobalGetOut());
}

void Internal::verbose (int level, const char *fmt, ...) {
  va_list ap;
  va_start (ap, fmt);
  vverbose (level, fmt, ap);
  va_end (ap);
}

void Internal::verbose (int level) {
#ifdef LOGGING
  if (!opts.log)
#endif
    if (opts.quiet || level > opts.verbose)
      return;
  print_prefix ();
  fputc ('\n', Abc_FrameGlobalGetOut());
  fflush (Abc_FrameGlobalGetOut());
}

/*------------------------------------------------------------------------*/

void Internal::section (const char *title) {
#ifdef LOGGING
  if (!opts.log)
#endif
    if (opts.quiet)
      return;
  if (stats.sections++)
    MSG ();
  print_prefix ();
  tout.blue ();
  fputs ("--- [ ", Abc_FrameGlobalGetOut());
  tout.blue (true);
  fputs (title, Abc_FrameGlobalGetOut());
  tout.blue ();
  fputs (" ] ", Abc_FrameGlobalGetOut());
  for (int i = strlen (title) + strlen (prefix.c_str ()) + 9; i < 78; i++)
    fputc ('-', Abc_FrameGlobalGetOut());
  tout.normal ();
  fputc ('\n', Abc_FrameGlobalGetOut());
  MSG ();
}

/*------------------------------------------------------------------------*/

void Internal::phase (const char *phase, const char *fmt, ...) {
#ifdef LOGGING
  if (!opts.log)
#endif
    if (opts.quiet || (!force_phase_messages && opts.verbose < 2))
      return;
  print_prefix ();
  fprintf ( Abc_FrameGlobalGetOut(), "[%s] ", phase);
  va_list ap;
  va_start (ap, fmt);
  vfprintf ( Abc_FrameGlobalGetOut(), fmt, ap);
  va_end (ap);
  fputc ('\n', Abc_FrameGlobalGetOut());
  fflush (Abc_FrameGlobalGetOut());
}

void Internal::phase (const char *phase, int64_t count, const char *fmt,
                      ...) {
#ifdef LOGGING
  if (!opts.log)
#endif
    if (opts.quiet || (!force_phase_messages && opts.verbose < 2))
      return;
  print_prefix ();
  fprintf ( Abc_FrameGlobalGetOut(), "[%s-%" PRId64 "] ", phase, count);
  va_list ap;
  va_start (ap, fmt);
  vfprintf ( Abc_FrameGlobalGetOut(), fmt, ap);
  va_end (ap);
  fputc ('\n', Abc_FrameGlobalGetOut());
  fflush (Abc_FrameGlobalGetOut());
}

/*------------------------------------------------------------------------*/
#endif // ifndef CADICAL_QUIET
/*------------------------------------------------------------------------*/

void Internal::warning (const char *fmt, ...) {
  fflush (Abc_FrameGlobalGetOut());
  terr.bold ();
  fputs ("cadical: ", Abc_FrameGlobalGetErr());
  terr.red (1);
  fputs ("warning:", Abc_FrameGlobalGetErr());
  terr.normal ();
  fputc (' ', Abc_FrameGlobalGetErr());
  va_list ap;
  va_start (ap, fmt);
  vfprintf (Abc_FrameGlobalGetErr(), fmt, ap);
  va_end (ap);
  fputc ('\n', Abc_FrameGlobalGetErr());
  fflush (Abc_FrameGlobalGetErr());
}

/*------------------------------------------------------------------------*/

void Internal::error_message_start () {
  fflush (Abc_FrameGlobalGetOut());
  terr.bold ();
  fputs ("cadical: ", Abc_FrameGlobalGetErr());
  terr.red (1);
  fputs ("error:", Abc_FrameGlobalGetErr());
  terr.normal ();
  fputc (' ', Abc_FrameGlobalGetErr());
}

void Internal::error_message_end () {
  fputc ('\n', Abc_FrameGlobalGetErr());
  fflush (Abc_FrameGlobalGetErr());
  // TODO add possibility to use call back instead.
  exit (1);
}

void Internal::verror (const char *fmt, va_list &ap) {
  error_message_start ();
  vfprintf (Abc_FrameGlobalGetErr(), fmt, ap);
  error_message_end ();
}

void Internal::error (const char *fmt, ...) {
  va_list ap;
  va_start (ap, fmt);
  verror (fmt, ap);
  va_end (ap); // unreachable
}

/*------------------------------------------------------------------------*/

void fatal_message_start () {
  fflush (Abc_FrameGlobalGetOut());
  terr.bold ();
  fputs ("cadical: ", Abc_FrameGlobalGetErr());
  terr.red (1);
  fputs ("fatal error:", Abc_FrameGlobalGetErr());
  terr.normal ();
  fputc (' ', Abc_FrameGlobalGetErr());
}

void fatal_message_end () {
  fputc ('\n', Abc_FrameGlobalGetErr());
  fflush (Abc_FrameGlobalGetErr());
  abort ();
}

void fatal (const char *fmt, ...) {
  fatal_message_start ();
  va_list ap;
  va_start (ap, fmt);
  vfprintf (Abc_FrameGlobalGetErr(), fmt, ap);
  va_end (ap);
  fatal_message_end ();
  abort ();
}

} // namespace CaDiCaL

ABC_NAMESPACE_IMPL_END
