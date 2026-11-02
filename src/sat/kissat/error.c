#include "error.h"
#include "colors.h"
#include "cover.h"

#include <stdarg.h>
#include <stdlib.h>

ABC_NAMESPACE_IMPL_START

static void (*kissat_abort_function) (void);

void kissat_call_function_instead_of_abort (void (*f) (void)) {
  kissat_abort_function = f;
}

// clang-format off

void
kissat_abort (void)
{
  if (kissat_abort_function)
    { FLUSH_COVERAGE (); kissat_abort_function (); } // Keep all in this line.
  else
    { FLUSH_COVERAGE (); abort (); }                 // Keep all in this line.
}

// clang-format on

static void typed_error_message_start (const char *type) {
  fflush( Abc_FrameGlobalGetOut() );
  TERMINAL (stderr, 2);
  COLOR (BOLD);
  fputs ("kissat: ", Abc_FrameGlobalGetErr());
  COLOR (RED);
  fputs (type, Abc_FrameGlobalGetErr());
  fputs (": ", Abc_FrameGlobalGetErr());
  COLOR (NORMAL);
}

void kissat_fatal_message_start (void) {
  typed_error_message_start ("fatal error");
}

static void vprint_error (const char *type, const char *fmt, va_list *ap) {
  typed_error_message_start (type);
  vfprintf( Abc_FrameGlobalGetErr(),  fmt, *ap);
  fputc( '\n', Abc_FrameGlobalGetErr() );
  fflush( Abc_FrameGlobalGetErr() );
}

void kissat_error (const char *fmt, ...) {
  va_list ap;
  va_start (ap, fmt);
  vprint_error ("error", fmt, &ap);
  va_end (ap);
}

void kissat_fatal (const char *fmt, ...) {
  va_list ap;
  va_start (ap, fmt);
  vprint_error ("fatal error", fmt, &ap);
  va_end (ap);
  kissat_abort ();
}

ABC_NAMESPACE_IMPL_END
