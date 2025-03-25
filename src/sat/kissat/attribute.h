#ifndef _attribute_h_INCLUDED
#define _attribute_h_INCLUDED

#define ATTRIBUTE_FORMAT(FORMAT_POSITION, VARIADIC_ARGUMENT_POSITION) \
  __attribute__ (( \
      format (printf, FORMAT_POSITION, VARIADIC_ARGUMENT_POSITION)))

#define ATTRIBUTE_ALWAYS_INLINE __attribute__ ((always_inline))

#endif
