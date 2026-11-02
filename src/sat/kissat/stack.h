#ifndef _stack_h_INCLUDED
#define _stack_h_INCLUDED

#include <stdlib.h>

#include "global.h"
ABC_NAMESPACE_HEADER_START

#define STACK(TYPE) \
  struct { \
    TYPE *begin; \
    TYPE *end; \
    TYPE *allocated; \
  }

#define FULL_STACK(S) ((S).end == (S).allocated)
#define EMPTY_STACK(S) ((S).begin == (S).end)
#define SIZE_STACK(S) ((size_t) ((S).end - (S).begin))
#define CAPACITY_STACK(S) ((size_t) ((S).allocated - (S).begin))

#define INIT_STACK(S) \
  do { \
    (S).begin = (S).end = (S).allocated = 0; \
  } while (0)

#define TOP_STACK(S) (END_STACK (S)[KISSAT_assert (!EMPTY_STACK (S)), -1])

#define PEEK_STACK(S, N) \
  (BEGIN_STACK (S)[KISSAT_assert ((N) < SIZE_STACK (S)), (N)])

#define POKE_STACK(S, N, E) \
  do { \
    PEEK_STACK (S, N) = (E); \
  } while (0)

#define POP_STACK(S) (KISSAT_assert (!EMPTY_STACK (S)), *--(S).end)

// Preserve the pointer type when ABC is compiled as C++.
#ifdef __cplusplus
#define KISSAT_STACK_CAST(S) (decltype((S).begin))
#else
#define KISSAT_STACK_CAST(S)
#endif

#define ENLARGE_STACK(S) \
  do { \
    const size_t BYTES_PER_ELEMENT = sizeof *(S).begin; \
    const size_t OLD_SIZE = SIZE_STACK (S); \
    const size_t OLD_CAPACITY = CAPACITY_STACK (S); \
    size_t NEW_CAPACITY = \
        OLD_CAPACITY ? 2 * OLD_CAPACITY : BYTES_PER_ELEMENT; \
    const size_t OLD_BYTES = OLD_CAPACITY * BYTES_PER_ELEMENT; \
    const size_t NEW_BYTES = NEW_CAPACITY * BYTES_PER_ELEMENT; \
    (S).begin = KISSAT_STACK_CAST(S) \
        kissat_realloc (solver, (S).begin, OLD_BYTES, NEW_BYTES); \
    (S).allocated = (S).begin + NEW_CAPACITY; \
    (S).end = (S).begin + OLD_SIZE; \
    KISSAT_assert ((S).end <= (S).allocated); \
  } while (0)

#define SHRINK_STACK(S) \
  do { \
    if (FULL_STACK (S)) \
      break; \
    const size_t BYTES_PER_ELEMENT = sizeof *(S).begin; \
    const size_t OLD_CAPACITY = CAPACITY_STACK (S); \
    const size_t OLD_BYTES = OLD_CAPACITY * BYTES_PER_ELEMENT; \
    const size_t OLD_SIZE = SIZE_STACK (S); \
    if (!OLD_SIZE) { \
      kissat_free (solver, (S).begin, OLD_BYTES); \
      (S).begin = (S).end = (S).allocated = 0; \
      break; \
    } \
    if (OLD_BYTES <= sizeof (void *)) \
      break; \
    KISSAT_assert (OLD_CAPACITY); \
    const unsigned LD_OLD_SIZE = kissat_log2_ceiling_of_word (OLD_SIZE); \
    const size_t NEW_CAPACITY = ((size_t) 1) << LD_OLD_SIZE; \
    size_t NEW_BYTES = NEW_CAPACITY * BYTES_PER_ELEMENT; \
    if (NEW_BYTES == OLD_BYTES) \
      break; \
    KISSAT_assert (NEW_BYTES < OLD_BYTES); \
    (S).begin = KISSAT_STACK_CAST(S) \
        kissat_realloc (solver, (S).begin, OLD_BYTES, NEW_BYTES); \
    (S).allocated = (S).begin + NEW_CAPACITY; \
    (S).end = (S).begin + OLD_SIZE; \
    KISSAT_assert ((S).end <= (S).allocated); \
  } while (0)

#define PUSH_STACK(S, E) \
  do { \
    if (FULL_STACK (S)) \
      ENLARGE_STACK (S); \
    *(S).end++ = (E); \
  } while (0)

#define BEGIN_STACK(S) (S).begin

#define END_STACK(S) (S).end

#define CLEAR_STACK(S) \
  do { \
    (S).end = (S).begin; \
  } while (0)

#define RESIZE_STACK(S, NEW_SIZE) \
  do { \
    const size_t TMP_NEW_SIZE = (NEW_SIZE); \
    KISSAT_assert (TMP_NEW_SIZE <= SIZE_STACK (S)); \
    (S).end = (S).begin + TMP_NEW_SIZE; \
  } while (0)

#define SET_END_OF_STACK(S, P) \
  do { \
    KISSAT_assert (BEGIN_STACK (S) <= (P)); \
    KISSAT_assert ((P) <= END_STACK (S)); \
    if ((P) == END_STACK (S)) \
      break; \
    (S).end = (P); \
  } while (0)

#define RELEASE_STACK(S) \
  do { \
    DEALLOC ((S).begin, CAPACITY_STACK (S)); \
    INIT_STACK (S); \
  } while (0)

#define REMOVE_STACK(T, S, E) \
  do { \
    KISSAT_assert (!EMPTY_STACK (S)); \
    T *END_REMOVE_STACK = END_STACK (S); \
    T *P_REMOVE_STACK = BEGIN_STACK (S); \
    while (*P_REMOVE_STACK != (E)) { \
      P_REMOVE_STACK++; \
      KISSAT_assert (P_REMOVE_STACK != END_REMOVE_STACK); \
    } \
    P_REMOVE_STACK++; \
    while (P_REMOVE_STACK != END_REMOVE_STACK) { \
      P_REMOVE_STACK[-1] = *P_REMOVE_STACK; \
      P_REMOVE_STACK++; \
    } \
    (S).end--; \
  } while (0)

#define REVERSE_STACK(T, S) \
  do { \
    if (SIZE_STACK (S) < 2) \
      break; \
    T *HEAD = (S).begin, *TAIL = (S).end - 1; \
    while (HEAD < TAIL) { \
      T TMP = *HEAD; \
      *HEAD++ = *TAIL; \
      *TAIL-- = TMP; \
    } \
  } while (0)

#define all_stack(T, E, S) \
  T E, *E##_PTR = BEGIN_STACK (S), *const E##_END = END_STACK (S); \
  E##_PTR != E##_END && (E = *E##_PTR, true); \
  ++E##_PTR

#define all_pointers(T, E, S) \
  T *E, *const *E##_PTR = BEGIN_STACK (S), \
               *const *const E##_END = END_STACK (S); \
  E##_PTR != E##_END && (E = *E##_PTR, true); \
  ++E##_PTR

// clang-format off

typedef STACK (char) chars;
typedef STACK (int) ints;
typedef STACK (size_t) sizes;
typedef STACK (unsigned) unsigneds;

// clang-format on

struct kissat;

ABC_NAMESPACE_HEADER_END

#endif
