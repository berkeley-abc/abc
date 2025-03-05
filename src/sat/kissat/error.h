#ifndef _error_h_INCLUDED
#define _error_h_INCLUDED

#include "attribute.h"

// clang-format off

void kissat_error (const char *fmt, ...) ATTRIBUTE_FORMAT (1, 2);
void kissat_fatal (const char *fmt, ...) ATTRIBUTE_FORMAT (1, 2);

void kissat_fatal_message_start (void);

void kissat_call_function_instead_of_abort (void (*)(void));
void kissat_abort (void);

// clang-format on

#endif
