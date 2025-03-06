#include "kitten.h"
#include "random.h"
#include "stack.h"

#include <assert.h>
#include <inttypes.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef signed char value;

static void die (const char *fmt, ...) {
  fputs ("kitten: error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static inline void *kitten_calloc (size_t n, size_t size) {
  void *res = calloc (n, size);
  if (n && size && !res)
    die ("out of memory allocating '%zu * %zu' bytes", n, size);
  return res;
}

#define CALLOC(P, N) \
  do { \
    (P) = kitten_calloc (N, sizeof *(P)); \
  } while (0)
#define DEALLOC(P, N) free (P)

#undef ENLARGE_STACK

#define ENLARGE_STACK(S) \
  do { \
    assert (FULL_STACK (S)); \
    const size_t SIZE = SIZE_STACK (S); \
    const size_t OLD_CAPACITY = CAPACITY_STACK (S); \
    const size_t NEW_CAPACITY = OLD_CAPACITY ? 2 * OLD_CAPACITY : 1; \
    const size_t BYTES = NEW_CAPACITY * sizeof *(S).begin; \
    (S).begin = realloc ((S).begin, BYTES); \
    if (!(S).begin) \
      die ("out of memory reallocating '%zu' bytes", BYTES); \
    (S).allocated = (S).begin + NEW_CAPACITY; \
    (S).end = (S).begin + SIZE; \
  } while (0)

// Beside allocators above also use stand alone statistics counters.

#define INC(NAME) \
  do { \
    statistics *statistics = &kitten->statistics; \
    assert (statistics->NAME < UINT64_MAX); \
    statistics->NAME++; \
  } while (0)

#define ADD(NAME, DELTA) \
  do { \
    statistics *statistics = &kitten->statistics; \
    assert (statistics->NAME <= UINT64_MAX - (DELTA)); \
    statistics->NAME += (DELTA); \
  } while (0)

#define KITTEN_TICKS (kitten->statistics.kitten_ticks)

#define INVALID UINT_MAX
#define MAX_VARS ((1u << 31) - 1)

#define CORE_FLAG (1u)
#define LEARNED_FLAG (2u)

// clang-format off

typedef struct kar kar;
typedef struct kink kink;
typedef struct klause klause;
typedef STACK (unsigned) klauses;
typedef unsigneds katches;

// clang-format on

struct kar {
  unsigned level;
  unsigned reason;
};

struct kink {
  unsigned next;
  unsigned prev;
  uint64_t stamp;
};

struct klause {
  unsigned aux;
  unsigned size;
  unsigned flags;
  unsigned lits[1];
};

typedef struct statistics statistics;

struct statistics {
  uint64_t learned;
  uint64_t original;
  uint64_t kitten_flip;
  uint64_t kitten_flipped;
  uint64_t kitten_sat;
  uint64_t kitten_solved;
  uint64_t kitten_conflicts;
  uint64_t kitten_decisions;
  uint64_t kitten_propagations;
  uint64_t kitten_ticks;
  uint64_t kitten_unknown;
  uint64_t kitten_unsat;
};

typedef struct kimits kimits;

struct kimits {
  uint64_t ticks;
};

struct kitten {
  // First zero initialized field in 'clear_kitten' is 'status'.
  //
  int status;

#if defined(LOGGING)
  bool logging;
#endif
  bool antecedents;
  bool learned;

  unsigned level;
  unsigned propagated;
  unsigned unassigned;
  unsigned inconsistent;
  unsigned failing;

  uint64_t generator;

  size_t lits;
  size_t evars;

  size_t end_original_ref;

  struct {
    unsigned first, last;
    uint64_t stamp;
    unsigned search;
  } queue;

  // The 'size' field below is the first not zero reinitialized field
  // by 'memset' in 'clear_kitten' (after 'kissat').

  size_t size;
  size_t esize;

  kar *vars;
  kink *links;
  value *marks;
  value *values;
  bool *failed;
  unsigned char *phases;
  unsigned *import;
  katches *watches;

  unsigneds analyzed;
  unsigneds assumptions;
  unsigneds core;
  unsigneds rcore;
  unsigneds eclause;
  unsigneds export;
  unsigneds klause;
  unsigneds klauses;
  unsigneds resolved;
  unsigneds trail;
  unsigneds units;
  unsigneds prime[2];

  kimits limits;
  int (*terminator) (void *);
  void *terminator_data;
  unsigneds clause;
  uint64_t initialized;
  statistics statistics;
};

/*------------------------------------------------------------------------*/

static inline bool is_core_klause (klause *c) {
  return c->flags & CORE_FLAG;
}

static inline bool is_learned_klause (klause *c) {
  return c->flags & LEARNED_FLAG;
}

static inline void set_core_klause (klause *c) { c->flags |= CORE_FLAG; }

static inline void unset_core_klause (klause *c) { c->flags &= ~CORE_FLAG; }

static inline klause *dereference_klause (kitten *kitten, unsigned ref) {
  unsigned *res = BEGIN_STACK (kitten->klauses) + ref;
  assert (res < END_STACK (kitten->klauses));
  return (klause *) res;
}

static inline unsigned reference_klause (kitten *kitten, const klause *c) {
  const unsigned *const begin = BEGIN_STACK (kitten->klauses);
  const unsigned *p = (const unsigned *) c;
  assert (begin <= p);
  assert (p < END_STACK (kitten->klauses));
  const unsigned res = p - begin;
  return res;
}

/*------------------------------------------------------------------------*/

#define KATCHES(KIT) (kitten->watches[assert ((KIT) < kitten->lits), (KIT)])

#define all_klauses(C) \
  klause *C = begin_klauses (kitten), *end_##C = end_klauses (kitten); \
  (C) != end_##C; \
  (C) = next_klause (kitten, C)

#define all_original_klauses(C) \
  klause *C = begin_klauses (kitten), \
         *end_##C = end_original_klauses (kitten); \
  (C) != end_##C; \
  (C) = next_klause (kitten, C)

#define all_learned_klauses(C) \
  klause *C = begin_learned_klauses (kitten), \
         *end_##C = end_klauses (kitten); \
  (C) != end_##C; \
  (C) = next_klause (kitten, C)

#define all_kits(KIT) \
  size_t KIT = 0, KIT_##END = kitten->lits; \
  KIT != KIT_##END; \
  KIT++

#define BEGIN_KLAUSE(C) (C)->lits

#define END_KLAUSE(C) (BEGIN_KLAUSE (C) + (C)->size)

#define all_literals_in_klause(KIT, C) \
  unsigned KIT, *KIT##_PTR = BEGIN_KLAUSE (C), \
                *KIT##_END = END_KLAUSE (C); \
  KIT##_PTR != KIT##_END && ((KIT = *KIT##_PTR), true); \
  ++KIT##_PTR

#define all_antecedents(REF, C) \
  unsigned REF, *REF##_PTR = antecedents (C), \
                *REF##_END = REF##_PTR + (C)->aux; \
  REF##_PTR != REF##_END && ((REF = *REF##_PTR), true); \
  ++REF##_PTR

#ifdef LOGGING

#define logging (kitten->logging)

static void log_basic (kitten *, const char *, ...)
    __attribute__ ((format (printf, 2, 3)));

static void log_basic (kitten *kitten, const char *fmt, ...) {
  assert (logging);
  printf ("c KITTEN %u ", kitten->level);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void log_reference (kitten *, unsigned, const char *, ...)
    __attribute__ ((format (printf, 3, 4)));

static void log_reference (kitten *kitten, unsigned ref, const char *fmt,
                           ...) {
  klause *c = dereference_klause (kitten, ref);
  assert (logging);
  printf ("c KITTEN %u ", kitten->level);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (is_learned_klause (c)) {
    fputs (" learned", stdout);
    if (c->aux)
      printf ("[%u]", c->aux);
  } else {
    fputs (" original", stdout);
    if (c->aux != INVALID)
      printf ("[%u]", c->aux);
  }
  printf (" size %u clause[%u]", c->size, ref);
  value *values = kitten->values;
  kar *vars = kitten->vars;
  for (all_literals_in_klause (lit, c)) {
    printf (" %u", lit);
    const value value = values[lit];
    if (value)
      printf ("@%u=%d", vars[lit / 2].level, (int) value);
  }
  fputc ('\n', stdout);
  fflush (stdout);
}

static void log_literals (kitten *, unsigned *, unsigned, const char *, ...)
    __attribute__ ((format (printf, 4, 5)));

static void log_literals (kitten *kitten, unsigned *lits, unsigned size,
                          const char *fmt, ...) {
  assert (logging);
  printf ("c KITTEN %u ", kitten->level);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  value *values = kitten->values;
  kar *vars = kitten->vars;
  for (unsigned i = 0; i < size; i++) {
    const unsigned lit = lits[i];
    printf (" %u", lit);
    const value value = values[lit];
    if (value)
      printf ("@%u=%d", vars[lit / 2].level, (int) value);
  }
  fputc ('\n', stdout);
  fflush (stdout);
}

#define LOG(...) \
  do { \
    if (logging) \
      log_basic (kitten, __VA_ARGS__); \
  } while (0)

#define ROG(...) \
  do { \
    if (logging) \
      log_reference (kitten, __VA_ARGS__); \
  } while (0)

#define LOGLITS(...) \
  do { \
    if (logging) \
      log_literals (kitten, __VA_ARGS__); \
  } while (0)

#else

#define LOG(...) \
  do { \
  } while (0)
#define ROG(...) \
  do { \
  } while (0)
#define LOGLITS(...) \
  do { \
  } while (0)

#endif

static void check_queue (kitten *kitten) {
#ifdef CHECK_KITTEN
  const unsigned vars = kitten->lits / 2;
  unsigned found = 0, prev = INVALID;
  kink *links = kitten->links;
  uint64_t stamp = 0;
  for (unsigned idx = kitten->queue.first, next; idx != INVALID;
       idx = next) {
    kink *link = links + idx;
    assert (link->prev == prev);
    assert (!found || stamp < link->stamp);
    assert (link->stamp < kitten->queue.stamp);
    stamp = link->stamp;
    next = link->next;
    prev = idx;
    found++;
  }
  assert (found == vars);
  unsigned next = INVALID;
  found = 0;
  for (unsigned idx = kitten->queue.last, prev; idx != INVALID;
       idx = prev) {
    kink *link = links + idx;
    assert (link->next == next);
    prev = link->prev;
    next = idx;
    found++;
  }
  assert (found == vars);
  value *values = kitten->values;
  bool first = true;
  for (unsigned idx = kitten->queue.search, next; idx != INVALID;
       idx = next) {
    kink *link = links + idx;
    next = link->next;
    const unsigned lit = 2 * idx;
    assert (first || values[lit]);
    first = false;
  }
#else
  (void) kitten;
#endif
}

static void update_search (kitten *kitten, unsigned idx) {
  if (kitten->queue.search == idx)
    return;
  kitten->queue.search = idx;
  LOG ("search updated to %u stamped %" PRIu64, idx,
       kitten->links[idx].stamp);
}

static void enqueue (kitten *kitten, unsigned idx) {
  LOG ("enqueue %u", idx);
  kink *links = kitten->links;
  kink *l = links + idx;
  const unsigned last = kitten->queue.last;
  if (last == INVALID)
    kitten->queue.first = idx;
  else
    links[last].next = idx;
  l->prev = last;
  l->next = INVALID;
  kitten->queue.last = idx;
  l->stamp = kitten->queue.stamp++;
  LOG ("stamp %" PRIu64, l->stamp);
}

static void dequeue (kitten *kitten, unsigned idx) {
  LOG ("dequeue %u", idx);
  kink *links = kitten->links;
  kink *l = links + idx;
  const unsigned prev = l->prev;
  const unsigned next = l->next;
  if (prev == INVALID)
    kitten->queue.first = next;
  else
    links[prev].next = next;
  if (next == INVALID)
    kitten->queue.last = prev;
  else
    links[next].prev = prev;
}

static void init_queue (kitten *kitten, size_t old_vars, size_t new_vars) {
  for (size_t idx = old_vars; idx < new_vars; idx++) {
    assert (!kitten->values[2 * idx]);
    assert (kitten->unassigned < UINT_MAX);
    kitten->unassigned++;
    enqueue (kitten, idx);
  }
  LOG ("initialized decision queue from %zu to %zu", old_vars, new_vars);
  update_search (kitten, kitten->queue.last);
  check_queue (kitten);
}

static void initialize_kitten (kitten *kitten) {
  kitten->queue.first = INVALID;
  kitten->queue.last = INVALID;
  kitten->inconsistent = INVALID;
  kitten->failing = INVALID;
  kitten->queue.search = INVALID;
  kitten->terminator = 0;
  kitten->terminator_data = 0;
  kitten->limits.ticks = UINT64_MAX;
  kitten->generator = kitten->initialized++;
}

static void clear_kitten (kitten *kitten) {
  size_t bytes = (char *) &kitten->size - (char *) &kitten->status;
  memset (&kitten->status, 0, bytes);
  memset (&kitten->statistics, 0, sizeof (statistics));
  initialize_kitten (kitten);
}

#define RESIZE1(P) \
  do { \
    void *OLD_PTR = (P); \
    CALLOC ((P), new_size / 2); \
    const size_t BYTES = old_vars * sizeof *(P); \
    memcpy ((P), OLD_PTR, BYTES); \
    void *NEW_PTR = (P); \
    (P) = OLD_PTR; \
    DEALLOC ((P), old_size / 2); \
    (P) = NEW_PTR; \
  } while (0)

#define RESIZE2(P) \
  do { \
    void *OLD_PTR = (P); \
    CALLOC ((P), new_size); \
    const size_t BYTES = old_lits * sizeof *(P); \
    memcpy ((P), OLD_PTR, BYTES); \
    void *NEW_PTR = (P); \
    (P) = OLD_PTR; \
    DEALLOC ((P), old_size); \
    (P) = NEW_PTR; \
  } while (0)

static void enlarge_internal (kitten *kitten, size_t lit) {
  const size_t new_lits = (lit | 1) + 1;
  const size_t old_lits = kitten->lits;
  assert (old_lits <= lit);
  assert (old_lits < new_lits);
  assert ((lit ^ 1) < new_lits);
  assert (lit < new_lits);
  const size_t old_size = kitten->size;
  const unsigned new_vars = new_lits / 2;
  const unsigned old_vars = old_lits / 2;
  if (old_size < new_lits) {
    size_t new_size = old_size ? 2 * old_size : 2;
    while (new_size <= lit)
      new_size *= 2;
    LOG ("internal literals resized to %zu from %zu (requested %zu)",
         new_size, old_size, new_lits);

    RESIZE1 (kitten->marks);
    RESIZE1 (kitten->phases);
    RESIZE2 (kitten->values);
    RESIZE2 (kitten->failed);
    RESIZE1 (kitten->vars);
    RESIZE1 (kitten->links);
    RESIZE2 (kitten->watches);

    kitten->size = new_size;
  }
  kitten->lits = new_lits;
  init_queue (kitten, old_vars, new_vars);
  LOG ("internal literals activated until %zu literals", new_lits);
  return;
}

static const char *status_to_string (int status) {
  switch (status) {
  case 10:
    return "formula satisfied";
  case 11:
    return "formula satisfied and prime implicant computed";
  case 20:
    return "formula inconsistent";
  case 21:
    return "formula inconsistent and core computed";
  default:
    assert (!status);
    return "formula unsolved";
  }
}

static void invalid_api_usage (const char *fun, const char *fmt, ...) {
  fprintf (stderr, "kitten: fatal error: invalid API usage in '%s': ", fun);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  abort ();
}

#define INVALID_API_USAGE(...) invalid_api_usage (__func__, __VA_ARGS__)

#define REQUIRE_INITIALIZED() \
  do { \
    if (!kitten) \
      INVALID_API_USAGE ("solver argument zero"); \
  } while (0)

#define REQUIRE_STATUS(EXPECTED) \
  do { \
    REQUIRE_INITIALIZED (); \
    if (kitten->status != (EXPECTED)) \
      INVALID_API_USAGE ("invalid status '%s' (expected '%s')", \
                         status_to_string (kitten->status), \
                         status_to_string (EXPECTED)); \
  } while (0)

#define UPDATE_STATUS(STATUS) \
  do { \
    if (kitten->status != (STATUS)) \
      LOG ("updating status from '%s' to '%s'", \
           status_to_string (kitten->status), status_to_string (STATUS)); \
    else \
      LOG ("keeping status at '%s'", status_to_string (STATUS)); \
    kitten->status = (STATUS); \
  } while (0)

kitten *kitten_init (void) {
  kitten *kitten;
  CALLOC (kitten, 1);
  initialize_kitten (kitten);
  return kitten;
}

#ifdef LOGGING
void kitten_set_logging (kitten *kitten) { logging = true; }
#endif

void kitten_track_antecedents (kitten *kitten) {
  REQUIRE_STATUS (0);

  if (kitten->learned)
    INVALID_API_USAGE ("can not start tracking antecedents after learning");

  LOG ("enabling antecedents tracking");
  kitten->antecedents = true;
}

void kitten_randomize_phases (kitten *kitten) {
  REQUIRE_INITIALIZED ();

  LOG ("randomizing phases");

  unsigned char *phases = kitten->phases;
  const unsigned vars = kitten->size / 2;

  uint64_t random = kissat_next_random64 (&kitten->generator);

  unsigned i = 0;
  const unsigned rest = vars & ~63u;

  while (i != rest) {
    uint64_t *p = (uint64_t *) (phases + i);
    p[0] = (random >> 0) & 0x0101010101010101;
    p[1] = (random >> 1) & 0x0101010101010101;
    p[2] = (random >> 2) & 0x0101010101010101;
    p[3] = (random >> 3) & 0x0101010101010101;
    p[4] = (random >> 4) & 0x0101010101010101;
    p[5] = (random >> 5) & 0x0101010101010101;
    p[6] = (random >> 6) & 0x0101010101010101;
    p[7] = (random >> 7) & 0x0101010101010101;
    random = kissat_next_random64 (&kitten->generator);
    i += 64;
  }

  unsigned shift = 0;
  while (i != vars)
    phases[i++] = (random >> shift++) & 1;
}

void kitten_flip_phases (kitten *kitten) {
  REQUIRE_INITIALIZED ();

  LOG ("flipping phases");

  unsigned char *phases = kitten->phases;
  const unsigned vars = kitten->size / 2;

  unsigned i = 0;
  const unsigned rest = vars & ~7u;

  while (i != rest) {
    uint64_t *p = (uint64_t *) (phases + i);
    *p ^= 0x0101010101010101;
    i += 8;
  }

  while (i != vars)
    phases[i++] ^= 1;
}

void kitten_no_ticks_limit (kitten *kitten) {
  REQUIRE_INITIALIZED ();
  LOG ("forcing no ticks limit");
  kitten->limits.ticks = UINT64_MAX;
}

uint64_t kitten_current_ticks (kitten *kitten) {
  REQUIRE_INITIALIZED ();
  const uint64_t current = KITTEN_TICKS;
  return current;
}

void kitten_set_ticks_limit (kitten *kitten, uint64_t delta) {
  REQUIRE_INITIALIZED ();
  const uint64_t current = KITTEN_TICKS;
  uint64_t limit;
  if (UINT64_MAX - delta <= current) {
    LOG ("forcing unlimited ticks limit");
    limit = UINT64_MAX;
  } else {
    limit = current + delta;
    LOG ("new limit of %" PRIu64 " ticks after %" PRIu64, limit, delta);
  }

  kitten->limits.ticks = limit;
}

void kitten_no_terminator (kitten *kitten) {
  REQUIRE_INITIALIZED ();
  LOG ("removing terminator");
  kitten->terminator = 0;
  kitten->terminator_data = 0;
}

void kitten_set_terminator (kitten *kitten, void *data,
                            int (*terminator) (void *)) {
  REQUIRE_INITIALIZED ();
  LOG ("setting terminator");
  kitten->terminator = terminator;
  kitten->terminator_data = data;
}

static void shuffle_unsigned_array (kitten *kitten, size_t size,
                                    unsigned *a) {
  for (size_t i = 0; i < size; i++) {
    const size_t j = kissat_pick_random (&kitten->generator, 0, i);
    if (j == i)
      continue;
    const unsigned first = a[i];
    const unsigned second = a[j];
    a[i] = second;
    a[j] = first;
  }
}

static void shuffle_unsigned_stack (kitten *kitten, unsigneds *stack) {
  const size_t size = SIZE_STACK (*stack);
  unsigned *a = BEGIN_STACK (*stack);
  shuffle_unsigned_array (kitten, size, a);
}

static void shuffle_katches (kitten *kitten) {
  LOG ("shuffling watch lists");
  for (size_t lit = 0; lit < kitten->lits; lit++)
    shuffle_unsigned_stack (kitten, &KATCHES (lit));
}

static void shuffle_queue (kitten *kitten) {
  LOG ("shuffling variable decision order");

  const unsigned vars = kitten->lits / 2;
  for (unsigned i = 0; i < vars; i++) {
    const unsigned idx = kissat_pick_random (&kitten->generator, 0, vars);
    dequeue (kitten, idx);
    enqueue (kitten, idx);
  }
  update_search (kitten, kitten->queue.last);
}

static void shuffle_units (kitten *kitten) {
  LOG ("shuffling units");
  shuffle_unsigned_stack (kitten, &kitten->units);
}

void kitten_shuffle_clauses (kitten *kitten) {
  REQUIRE_STATUS (0);
  shuffle_queue (kitten);
  shuffle_katches (kitten);
  shuffle_units (kitten);
}

static inline unsigned *antecedents (klause *c) {
  assert (is_learned_klause (c));
  return c->lits + c->size;
}

static inline void watch_klause (kitten *kitten, unsigned lit,
                                 unsigned ref) {
  ROG (ref, "watching %u in", lit);
  katches *watches = &KATCHES (lit);
  PUSH_STACK (*watches, ref);
}

static inline void connect_new_klause (kitten *kitten, unsigned ref) {
  ROG (ref, "new");

  klause *c = dereference_klause (kitten, ref);

  if (!c->size) {
    if (kitten->inconsistent == INVALID) {
      ROG (ref, "registering inconsistent empty");
      kitten->inconsistent = ref;
    } else
      ROG (ref, "ignoring inconsistent empty");
  } else if (c->size == 1) {
    ROG (ref, "watching unit");
    PUSH_STACK (kitten->units, ref);
  } else {
    watch_klause (kitten, c->lits[0], ref);
    watch_klause (kitten, c->lits[1], ref);
  }
}

static unsigned new_reference (kitten *kitten) {
  size_t ref = SIZE_STACK (kitten->klauses);
  if (ref >= INVALID) {
    die ("maximum number of literals exhausted");
  }
  const unsigned res = (unsigned) ref;
  assert (res != INVALID);
  INC (kitten_ticks);
  return res;
}

static void new_original_klause (kitten *kitten, unsigned id) {
  unsigned res = new_reference (kitten);
  unsigned size = SIZE_STACK (kitten->klause);
  unsigneds *klauses = &kitten->klauses;
  PUSH_STACK (*klauses, id);
  PUSH_STACK (*klauses, size);
  PUSH_STACK (*klauses, 0);
  for (all_stack (unsigned, lit, kitten->klause))
    PUSH_STACK (*klauses, lit);
  connect_new_klause (kitten, res);
  kitten->end_original_ref = SIZE_STACK (*klauses);
  kitten->statistics.original++;
}

static void enlarge_external (kitten *kitten, size_t eidx) {
  const size_t old_size = kitten->esize;
  const unsigned old_evars = kitten->evars;
  assert (old_evars <= eidx);
  const unsigned new_evars = eidx + 1;
  if (old_size <= eidx) {
    size_t new_size = old_size ? 2 * old_size : 1;
    while (new_size <= eidx)
      new_size *= 2;
    LOG ("external resizing to %zu variables from %zu (requested %u)",
         new_size, old_size, new_evars);
    unsigned *old_import = kitten->import;
    CALLOC (kitten->import, new_size);
    const size_t bytes = old_evars * sizeof *kitten->import;
    memcpy (kitten->import, old_import, bytes);
    DEALLOC (old_import, old_size);
    kitten->esize = new_size;
  }
  kitten->evars = new_evars;
  LOG ("external variables enlarged to %u", new_evars);
}

static unsigned import_literal (kitten *kitten, unsigned elit) {
  const unsigned eidx = elit / 2;
  if (eidx >= kitten->evars)
    enlarge_external (kitten, eidx);

  unsigned iidx = kitten->import[eidx];
  if (!iidx) {
    iidx = SIZE_STACK (kitten->export);
    PUSH_STACK (kitten->export, eidx);
    kitten->import[eidx] = iidx + 1;
  } else
    iidx--;
  unsigned ilit = 2 * iidx + (elit & 1);
  LOG ("imported external literal %u as internal literal %u", elit, ilit);
  if (ilit >= kitten->lits)
    enlarge_internal (kitten, ilit);
  return ilit;
}

static unsigned export_literal (kitten *kitten, unsigned ilit) {
  const unsigned iidx = ilit / 2;
  assert (iidx < SIZE_STACK (kitten->export));
  const unsigned eidx = PEEK_STACK (kitten->export, iidx);
  const unsigned elit = 2 * eidx + (ilit & 1);
  return elit;
}

unsigned new_learned_klause (kitten *kitten) {
  unsigned res = new_reference (kitten);
  unsigneds *klauses = &kitten->klauses;
  const size_t size = SIZE_STACK (kitten->klause);
  assert (size <= UINT_MAX);
  const size_t aux =
      kitten->antecedents ? SIZE_STACK (kitten->resolved) : 0;
  assert (aux <= UINT_MAX);
  PUSH_STACK (*klauses, (unsigned) aux);
  PUSH_STACK (*klauses, (unsigned) size);
  PUSH_STACK (*klauses, LEARNED_FLAG);
  for (all_stack (unsigned, lit, kitten->klause))
    PUSH_STACK (*klauses, lit);
  if (aux)
    for (all_stack (unsigned, ref, kitten->resolved))
      PUSH_STACK (*klauses, ref);
  connect_new_klause (kitten, res);
  kitten->learned = true;
  kitten->statistics.learned++;
  return res;
}

void kitten_clear (kitten *kitten) {
  LOG ("clear kitten of size %zu", kitten->size);

  assert (EMPTY_STACK (kitten->analyzed));
  assert (EMPTY_STACK (kitten->eclause));
  assert (EMPTY_STACK (kitten->resolved));

  CLEAR_STACK (kitten->assumptions);
  CLEAR_STACK (kitten->core);
  CLEAR_STACK (kitten->klause);
  CLEAR_STACK (kitten->klauses);
  CLEAR_STACK (kitten->trail);
  CLEAR_STACK (kitten->units);
  CLEAR_STACK (kitten->clause);
  CLEAR_STACK (kitten->prime[0]);
  CLEAR_STACK (kitten->prime[1]);

  for (all_kits (kit))
    CLEAR_STACK (KATCHES (kit));

  while (!EMPTY_STACK (kitten->export))
    kitten->import[POP_STACK (kitten->export)] = 0;

  const size_t lits = kitten->size;
  const unsigned vars = lits / 2;

#ifndef NDEBUG
  for (unsigned i = 0; i < vars; i++)
    assert (!kitten->marks[i]);
#endif

  memset (kitten->phases, 0, vars);
  memset (kitten->values, 0, lits);
  memset (kitten->failed, 0, lits);
  memset (kitten->vars, 0, vars);

  clear_kitten (kitten);
}

void kitten_release (kitten *kitten) {
  RELEASE_STACK (kitten->analyzed);
  RELEASE_STACK (kitten->assumptions);
  RELEASE_STACK (kitten->core);
  RELEASE_STACK (kitten->eclause);
  RELEASE_STACK (kitten->export);
  RELEASE_STACK (kitten->klause);
  RELEASE_STACK (kitten->klauses);
  RELEASE_STACK (kitten->resolved);
  RELEASE_STACK (kitten->trail);
  RELEASE_STACK (kitten->units);
  RELEASE_STACK (kitten->clause);
  RELEASE_STACK (kitten->prime[0]);
  RELEASE_STACK (kitten->prime[1]);

  for (size_t lit = 0; lit < kitten->size; lit++)
    RELEASE_STACK (kitten->watches[lit]);

  const size_t lits = kitten->size;
  const unsigned vars = lits / 2;
  DEALLOC (kitten->marks, vars);
  DEALLOC (kitten->phases, vars);
  DEALLOC (kitten->values, lits);
  DEALLOC (kitten->failed, lits);
  DEALLOC (kitten->vars, vars);
  DEALLOC (kitten->links, vars);
  DEALLOC (kitten->watches, lits);
  DEALLOC (kitten->import, kitten->esize);
  (void) vars;

  free (kitten);
}

static inline void move_to_front (kitten *kitten, unsigned idx) {
  if (idx == kitten->queue.last)
    return;
  LOG ("move to front variable %u", idx);
  dequeue (kitten, idx);
  enqueue (kitten, idx);
  assert (kitten->values[2 * idx]);
}

static inline void assign (kitten *kitten, unsigned lit, unsigned reason) {
#ifdef LOGGING
  if (reason == INVALID)
    LOG ("assign %u as decision", lit);
  else
    ROG (reason, "assign %u reason", lit);
#endif
  value *values = kitten->values;
  const unsigned not_lit = lit ^ 1;
  assert (!values[lit]);
  assert (!values[not_lit]);
  values[lit] = 1;
  values[not_lit] = -1;
  const unsigned idx = lit / 2;
  const unsigned sign = lit & 1;
  kitten->phases[idx] = sign;
  PUSH_STACK (kitten->trail, lit);
  kar *v = kitten->vars + idx;
  v->level = kitten->level;
  if (!v->level) {
    assert (reason != INVALID);
    klause *c = dereference_klause (kitten, reason);
    if (c->size > 1) {
      if (kitten->antecedents) {
        PUSH_STACK (kitten->resolved, reason);
        for (all_literals_in_klause (other, c))
          if (other != lit) {
            const unsigned other_idx = other / 2;
            const unsigned other_ref = kitten->vars[other_idx].reason;
            assert (other_ref != INVALID);
            PUSH_STACK (kitten->resolved, other_ref);
          }
      }
      PUSH_STACK (kitten->klause, lit);
      reason = new_learned_klause (kitten);
      CLEAR_STACK (kitten->resolved);
      CLEAR_STACK (kitten->klause);
    }
  }
  v->reason = reason;
  assert (kitten->unassigned);
  kitten->unassigned--;
}

static inline unsigned propagate_literal (kitten *kitten, unsigned lit) {
  LOG ("propagating %u", lit);
  value *values = kitten->values;
  assert (values[lit] > 0);
  const unsigned not_lit = lit ^ 1;
  katches *watches = kitten->watches + not_lit;
  unsigned conflict = INVALID;
  unsigned *q = BEGIN_STACK (*watches);
  const unsigned *const end_watches = END_STACK (*watches);
  unsigned const *p = q;
  uint64_t ticks = (((char *) end_watches - (char *) q) >> 7) + 1;
  while (p != end_watches) {
    const unsigned ref = *q++ = *p++;
    klause *c = dereference_klause (kitten, ref);
    assert (c->size > 1);
    unsigned *lits = c->lits;
    const unsigned other = lits[0] ^ lits[1] ^ not_lit;
    const value other_value = values[other];
    ticks++;
    if (other_value > 0)
      continue;
    value replacement_value = -1;
    unsigned replacement = INVALID;
    const unsigned *const end_lits = lits + c->size;
    unsigned *r;
    for (r = lits + 2; r != end_lits; r++) {
      replacement = *r;
      replacement_value = values[replacement];
      if (replacement_value >= 0)
        break;
    }
    if (replacement_value >= 0) {
      assert (replacement != INVALID);
      ROG (ref, "unwatching %u in", not_lit);
      lits[0] = other;
      lits[1] = replacement;
      *r = not_lit;
      watch_klause (kitten, replacement, ref);
      q--;
    } else if (other_value < 0) {
      ROG (ref, "conflict");
      INC (kitten_conflicts);
      conflict = ref;
      break;
    } else {
      assert (!other_value);
      assign (kitten, other, ref);
    }
  }
  while (p != end_watches)
    *q++ = *p++;
  SET_END_OF_STACK (*watches, q);
  ADD (kitten_ticks, ticks);
  return conflict;
}

static inline unsigned propagate (kitten *kitten) {
  assert (kitten->inconsistent == INVALID);
  unsigned propagated = 0;
  unsigned conflict = INVALID;
  while (conflict == INVALID &&
         kitten->propagated < SIZE_STACK (kitten->trail)) {
    if (kitten->terminator &&
        kitten->terminator (kitten->terminator_data)) {
      break;
    }
    const unsigned lit = PEEK_STACK (kitten->trail, kitten->propagated);
    conflict = propagate_literal (kitten, lit);
    kitten->propagated++;
    propagated++;
  }
  ADD (kitten_propagations, propagated);
  return conflict;
}

static void bump (kitten *kitten) {
  value *marks = kitten->marks;
  for (all_stack (unsigned, idx, kitten->analyzed)) {
    marks[idx] = 0;
    move_to_front (kitten, idx);
  }
  check_queue (kitten);
}

static inline void unassign (kitten *kitten, value *values, unsigned lit) {
  const unsigned not_lit = lit ^ 1;
  assert (values[lit]);
  assert (values[not_lit]);
  const unsigned idx = lit / 2;
#ifdef LOGGING
  kar *var = kitten->vars + idx;
  kitten->level = var->level;
  LOG ("unassign %u", lit);
#endif
  values[lit] = values[not_lit] = 0;
  assert (kitten->unassigned < kitten->lits / 2);
  kitten->unassigned++;
  kink *links = kitten->links;
  kink *link = links + idx;
  if (link->stamp > links[kitten->queue.search].stamp)
    update_search (kitten, idx);
}

static void backtrack (kitten *kitten, unsigned jump) {
  check_queue (kitten);
  assert (jump < kitten->level);
  LOG ("back%s to level %u",
       (kitten->level == jump + 1 ? "tracking" : "jumping"), jump);
  kar *vars = kitten->vars;
  value *values = kitten->values;
  unsigneds *trail = &kitten->trail;
  while (!EMPTY_STACK (*trail)) {
    const unsigned lit = TOP_STACK (*trail);
    const unsigned idx = lit / 2;
    const unsigned level = vars[idx].level;
    if (level == jump)
      break;
    (void) POP_STACK (*trail);
    unassign (kitten, values, lit);
  }
  kitten->propagated = SIZE_STACK (*trail);
  kitten->level = jump;
  check_queue (kitten);
}

void completely_backtrack_to_root_level (kitten *kitten) {
  check_queue (kitten);
  LOG ("completely backtracking to level 0");
  value *values = kitten->values;
  unsigneds *trail = &kitten->trail;
  unsigneds *units = &kitten->units;
#ifndef NDEBUG
  kar *vars = kitten->vars;
#endif
  for (all_stack (unsigned, lit, *trail)) {
    assert (vars[lit / 2].level);
    unassign (kitten, values, lit);
  }
  CLEAR_STACK (*trail);
  for (all_stack (unsigned, ref, *units)) {
    klause *c = dereference_klause (kitten, ref);
    assert (c->size == 1);
    const unsigned unit = c->lits[0];
    const value value = values[unit];
    if (value <= 0)
      continue;
    unassign (kitten, values, unit);
  }
  kitten->propagated = 0;
  kitten->level = 0;
  check_queue (kitten);
}

static void analyze (kitten *kitten, unsigned conflict) {
  assert (kitten->level);
  assert (kitten->inconsistent == INVALID);
  assert (EMPTY_STACK (kitten->analyzed));
  assert (EMPTY_STACK (kitten->resolved));
  assert (EMPTY_STACK (kitten->klause));
  PUSH_STACK (kitten->klause, INVALID);
  unsigned reason = conflict;
  value *marks = kitten->marks;
  const kar *const vars = kitten->vars;
  const unsigned level = kitten->level;
  unsigned const *p = END_STACK (kitten->trail);
  unsigned open = 0, jump = 0, size = 1, uip;
  for (;;) {
    assert (reason != INVALID);
    klause *c = dereference_klause (kitten, reason);
    assert (c);
    ROG (reason, "analyzing");
    PUSH_STACK (kitten->resolved, reason);
    for (all_literals_in_klause (lit, c)) {
      const unsigned idx = lit / 2;
      if (marks[idx])
        continue;
      assert (kitten->values[lit] < 0);
      LOG ("analyzed %u", lit);
      marks[idx] = true;
      PUSH_STACK (kitten->analyzed, idx);
      const kar *const v = vars + idx;
      const unsigned tmp = v->level;
      if (tmp < level) {
        if (tmp > jump) {
          jump = tmp;
          if (size > 1) {
            const unsigned other = PEEK_STACK (kitten->klause, 1);
            POKE_STACK (kitten->klause, 1, lit);
            lit = other;
          }
        }
        PUSH_STACK (kitten->klause, lit);
        size++;
      } else
        open++;
    }
    unsigned idx;
    do {
      assert (BEGIN_STACK (kitten->trail) < p);
      uip = *--p;
    } while (!marks[idx = uip / 2]);
    assert (open);
    if (!--open)
      break;
    reason = vars[idx].reason;
  }
  const unsigned not_uip = uip ^ 1;
  LOG ("first UIP %u jump level %u size %u", not_uip, jump, size);
  POKE_STACK (kitten->klause, 0, not_uip);
  bump (kitten);
  CLEAR_STACK (kitten->analyzed);
  const unsigned learned_ref = new_learned_klause (kitten);
  CLEAR_STACK (kitten->resolved);
  CLEAR_STACK (kitten->klause);
  backtrack (kitten, jump);
  assign (kitten, not_uip, learned_ref);
}

static void failing (kitten *kitten) {
  assert (kitten->inconsistent == INVALID);
  assert (!EMPTY_STACK (kitten->assumptions));
  assert (EMPTY_STACK (kitten->analyzed));
  assert (EMPTY_STACK (kitten->resolved));
  assert (EMPTY_STACK (kitten->klause));
  LOG ("analyzing failing assumptions");
  const value *const values = kitten->values;
  const kar *const vars = kitten->vars;
  unsigned failed_clashing = INVALID;
  unsigned first_failed = INVALID;
  unsigned failed_unit = INVALID;
  for (all_stack (unsigned, lit, kitten->assumptions)) {
    if (values[lit] >= 0)
      continue;
    if (first_failed == INVALID)
      first_failed = lit;
    const unsigned failed_idx = lit / 2;
    const kar *const failed_var = vars + failed_idx;
    if (!failed_var->level) {
      failed_unit = lit;
      break;
    }
    if (failed_clashing == INVALID && failed_var->reason == INVALID)
      failed_clashing = lit;
  }
  unsigned failed;
  if (failed_unit != INVALID)
    failed = failed_unit;
  else if (failed_clashing != INVALID)
    failed = failed_clashing;
  else
    failed = first_failed;
  assert (failed != INVALID);
  const unsigned failed_idx = failed / 2;
  const kar *const failed_var = vars + failed_idx;
  const unsigned failed_reason = failed_var->reason;
  LOG ("first failed assumption %u", failed);
  kitten->failed[failed] = true;

  if (failed_unit != INVALID) {
    assert (dereference_klause (kitten, failed_reason)->size == 1);
    LOG ("root-level falsified assumption %u", failed);
    kitten->failing = failed_reason;
    ROG (kitten->failing, "failing reason");
    return;
  }

  const unsigned not_failed = failed ^ 1;
  if (failed_clashing != INVALID) {
    LOG ("clashing with negated assumption %u", not_failed);
    kitten->failed[not_failed] = true;
    assert (kitten->failing == INVALID);
    return;
  }

  value *marks = kitten->marks;
  assert (!marks[failed_idx]);
  marks[failed_idx] = true;
  PUSH_STACK (kitten->analyzed, failed_idx);
  PUSH_STACK (kitten->klause, not_failed);

  unsigneds work;
  INIT_STACK (work);

  LOGLITS (BEGIN_STACK (kitten->trail), SIZE_STACK (kitten->trail),
           "trail");

  assert (SIZE_STACK (kitten->trail));
  unsigned const *p = END_STACK (kitten->trail);
  unsigned open = 1;
  for (;;) {
    if (!open)
      break;
    open--;
    unsigned idx, uip;
    do {
      assert (BEGIN_STACK (kitten->trail) < p);
      uip = *--p;
    } while (!marks[idx = uip / 2]);

    const kar *var = vars + idx;
    const unsigned reason = var->reason;
    if (reason == INVALID) {
      unsigned lit = 2 * idx;
      if (values[lit] < 0)
        lit ^= 1;
      LOG ("failed assumption %u", lit);
      assert (!kitten->failed[lit]);
      kitten->failed[lit] = true;
      const unsigned not_lit = lit ^ 1;
      PUSH_STACK (kitten->klause, not_lit);
    } else {
      ROG (reason, "analyzing");
      PUSH_STACK (kitten->resolved, reason);
      klause *c = dereference_klause (kitten, reason);
      for (all_literals_in_klause (other, c)) {
        const unsigned other_idx = other / 2;
        if (marks[other_idx])
          continue;
        assert (other_idx != idx);
        marks[other_idx] = true;
        assert (values[other]);
        if (vars[other_idx].level)
          open++;
        else
          PUSH_STACK (work, other_idx);
        PUSH_STACK (kitten->analyzed, other_idx);

        LOG ("analyzing final literal %u", other ^ 1);
      }
    }
  }
  for (size_t next = 0; next < SIZE_STACK (work); next++) {
    const unsigned idx = PEEK_STACK (work, next);
    const kar *var = vars + idx;
    const unsigned reason = var->reason;
    if (reason == INVALID) {
      unsigned lit = 2 * idx;
      if (values[lit] < 0)
        lit ^= 1;
      LOG ("failed assumption %u", lit);
      assert (!kitten->failed[lit]);
      kitten->failed[lit] = true;
      const unsigned not_lit = lit ^ 1;
      PUSH_STACK (kitten->klause, not_lit);
    } else {
      ROG (reason, "analyzing unit");
      PUSH_STACK (kitten->resolved, reason);
    }
  }

  // this is bfs not dfs so it does not work for lrat :/
  /*
  for (size_t next = 0; next < SIZE_STACK (kitten->analyzed); next++) {
    const unsigned idx = PEEK_STACK (kitten->analyzed, next);
    assert (marks[idx]);
    const kar *var = vars + idx;
    const unsigned reason = var->reason;
    if (reason == INVALID) {
      unsigned lit = 2 * idx;
      if (values[lit] < 0)
        lit ^= 1;
      LOG ("failed assumption %u", lit);
      assert (!kitten->failed[lit]);
      kitten->failed[lit] = true;
      const unsigned not_lit = lit ^ 1;
      PUSH_STACK (kitten->klause, not_lit);
    } else {
      ROG (reason, "analyzing");
      PUSH_STACK (kitten->resolved, reason);
      klause *c = dereference_klause (kitten, reason);
      for (all_literals_in_klause (other, c)) {
        const unsigned other_idx = other / 2;
        if (other_idx == idx)
          continue;
        if (marks[other_idx])
          continue;
        marks[other_idx] = true;
        PUSH_STACK (kitten->analyzed, other_idx);
        LOG ("analyzing final literal %u", other ^ 1);
      }
    }
  }
  */

  for (all_stack (unsigned, idx, kitten->analyzed))
    assert (marks[idx]), marks[idx] = 0;
  CLEAR_STACK (kitten->analyzed);

  RELEASE_STACK (work);

  const size_t resolved = SIZE_STACK (kitten->resolved);
  assert (resolved);

  if (resolved == 1) {
    kitten->failing = PEEK_STACK (kitten->resolved, 0);
    ROG (kitten->failing, "reusing as core");
  } else {
    kitten->failing = new_learned_klause (kitten);
    ROG (kitten->failing, "new core");
  }

  CLEAR_STACK (kitten->resolved);
  CLEAR_STACK (kitten->klause);
}

static void flush_trail (kitten *kitten) {
  unsigneds *trail = &kitten->trail;
  LOG ("flushing %zu root-level literals from trail", SIZE_STACK (*trail));
  assert (!kitten->level);
  kitten->propagated = 0;
  CLEAR_STACK (*trail);
}

static int decide (kitten *kitten) {
  if (!kitten->level && !EMPTY_STACK (kitten->trail))
    flush_trail (kitten);

  const value *const values = kitten->values;
  unsigned decision = INVALID;
  const size_t assumptions = SIZE_STACK (kitten->assumptions);
  while (kitten->level < assumptions) {
    unsigned assumption = PEEK_STACK (kitten->assumptions, kitten->level);
    value value = values[assumption];
    if (value < 0) {
      LOG ("found failing assumption %u", assumption);
      failing (kitten);
      return 20;
    } else if (value > 0) {

      kitten->level++;
      LOG ("pseudo decision level %u for already satisfied assumption %u",
           kitten->level, assumption);
    } else {
      decision = assumption;
      LOG ("using assumption %u as decision", decision);
      break;
    }
  }

  if (!kitten->unassigned)
    return 10;

  if (KITTEN_TICKS >= kitten->limits.ticks) {
    LOG ("ticks limit %" PRIu64 " hit after %" PRIu64 " ticks",
         kitten->limits.ticks, KITTEN_TICKS);
    return -1;
  }

  if (kitten->terminator && kitten->terminator (kitten->terminator_data)) {
    LOG ("terminator requested termination");
    return -1;
  }

  if (decision == INVALID) {
    unsigned idx = kitten->queue.search;
    const kink *const links = kitten->links;
    for (;;) {
      assert (idx != INVALID);
      if (!values[2 * idx])
        break;
      idx = links[idx].prev;
    }
    update_search (kitten, idx);
    const unsigned phase = kitten->phases[idx];
    decision = 2 * idx + phase;
    LOG ("decision %u variable %u phase %u", decision, idx, phase);
  }
  INC (kitten_decisions);
  kitten->level++;
  assign (kitten, decision, INVALID);
  return 0;
}

static void inconsistent (kitten *kitten, unsigned ref) {
  assert (ref != INVALID);
  assert (kitten->inconsistent == INVALID);

  if (!kitten->antecedents) {
    kitten->inconsistent = ref;
    ROG (ref, "registering inconsistent virtually empty");
    return;
  }

  unsigneds *analyzed = &kitten->analyzed;
  unsigneds *resolved = &kitten->resolved;

  assert (EMPTY_STACK (*analyzed));
  assert (EMPTY_STACK (*resolved));

  value *marks = kitten->marks;
  const kar *const vars = kitten->vars;
  unsigned next = 0;

  for (;;) {
    assert (ref != INVALID);
    klause *c = dereference_klause (kitten, ref);
    assert (c);
    ROG (ref, "analyzing inconsistent");
    PUSH_STACK (*resolved, ref);
    for (all_literals_in_klause (lit, c)) {
      const unsigned idx = lit / 2;
      assert (!vars[idx].level);
      if (marks[idx])
        continue;
      assert (kitten->values[lit] < 0);
      LOG ("analyzed %u", lit);
      marks[idx] = true;
      PUSH_STACK (kitten->analyzed, idx);
    }
    if (next == SIZE_STACK (kitten->analyzed))
      break;
    const unsigned idx = PEEK_STACK (kitten->analyzed, next);
    next++;
    const kar *const v = vars + idx;
    assert (!v->level);
    ref = v->reason;
  }
  assert (EMPTY_STACK (kitten->klause));
  ref = new_learned_klause (kitten);
  ROG (ref, "registering final inconsistent empty");
  kitten->inconsistent = ref;

  for (all_stack (unsigned, idx, *analyzed))
    marks[idx] = 0;

  CLEAR_STACK (*analyzed);
  CLEAR_STACK (*resolved);
}

static int propagate_units (kitten *kitten) {
  if (kitten->inconsistent != INVALID)
    return 20;

  if (EMPTY_STACK (kitten->units)) {
    LOG ("no root level unit clauses");
    return 0;
  }

  LOG ("propagating %zu root level unit clauses",
       SIZE_STACK (kitten->units));

  const value *const values = kitten->values;

  for (size_t next = 0; next < SIZE_STACK (kitten->units); next++) {
    const unsigned ref = PEEK_STACK (kitten->units, next);
    assert (ref != INVALID);
    klause *c = dereference_klause (kitten, ref);
    assert (c->size == 1);
    ROG (ref, "propagating unit");
    const unsigned unit = c->lits[0];
    const value value = values[unit];
    if (value > 0)
      continue;
    if (value < 0) {
      inconsistent (kitten, ref);
      return 20;
    }
    assign (kitten, unit, ref);
  }
  const unsigned conflict = propagate (kitten);
  if (conflict == INVALID)
    return 0;
  inconsistent (kitten, conflict);
  return 20;
}

/*------------------------------------------------------------------------*/

static klause *begin_klauses (kitten *kitten) {
  return (klause *) BEGIN_STACK (kitten->klauses);
}

static klause *end_original_klauses (kitten *kitten) {
  return (klause *) (BEGIN_STACK (kitten->klauses) +
                     kitten->end_original_ref);
}

static klause *end_klauses (kitten *kitten) {
  return (klause *) END_STACK (kitten->klauses);
}

static klause *next_klause (kitten *kitten, klause *c) {
  assert (begin_klauses (kitten) <= c);
  assert (c < end_klauses (kitten));
  unsigned *res = c->lits + c->size;
  if (kitten->antecedents && is_learned_klause (c))
    res += c->aux;
  return (klause *) res;
}

/*------------------------------------------------------------------------*/

static void reset_core (kitten *kitten) {
  LOG ("resetting core clauses");
  size_t reset = 0;
  for (all_klauses (c))
    if (is_core_klause (c))
      unset_core_klause (c), reset++;
  LOG ("reset %zu core clauses", reset);
  CLEAR_STACK (kitten->core);
}

static void reset_assumptions (kitten *kitten) {
  LOG ("reset %zu assumptions", SIZE_STACK (kitten->assumptions));
  while (!EMPTY_STACK (kitten->assumptions)) {
    const unsigned assumption = POP_STACK (kitten->assumptions);
    kitten->failed[assumption] = false;
  }
#ifndef NDEBUG
  for (size_t i = 0; i < kitten->size; i++)
    assert (!kitten->failed[i]);
#endif
  CLEAR_STACK (kitten->assumptions);
  if (kitten->failing != INVALID) {
    ROG (kitten->failing, "reset failed assumption reason");
    kitten->failing = INVALID;
  }
}

static void reset_incremental (kitten *kitten) {
  // if (kitten->level)
  completely_backtrack_to_root_level (kitten);
  if (!EMPTY_STACK (kitten->assumptions))
    reset_assumptions (kitten);
  else
    assert (kitten->failing == INVALID);
  if (kitten->status == 21)
    reset_core (kitten);
  UPDATE_STATUS (0);
}

/*------------------------------------------------------------------------*/

static bool flip_literal (kitten *kitten, unsigned lit) {
  INC (kitten_flip);
  signed char *values = kitten->values;
  if (values[lit] < 0)
    lit ^= 1;
  LOG ("trying to flip value of satisfied literal %u", lit);
  assert (values[lit] > 0);
  katches *watches = kitten->watches + lit;
  unsigned *q = BEGIN_STACK (*watches);
  const unsigned *const end_watches = END_STACK (*watches);
  unsigned const *p = q;
  uint64_t ticks = (((char *) end_watches - (char *) q) >> 7) + 1;
  bool res = true;
  while (p != end_watches) {
    const unsigned ref = *q++ = *p++;
    klause *c = dereference_klause (kitten, ref);
    unsigned *lits = c->lits;
    const unsigned other = lits[0] ^ lits[1] ^ lit;
    const value other_value = values[other];
    ticks++;
    if (other_value > 0)
      continue;
    value replacement_value = -1;
    unsigned replacement = INVALID;
    const unsigned *const end_lits = lits + c->size;
    unsigned *r;
    for (r = lits + 2; r != end_lits; r++) {
      replacement = *r;
      assert (replacement != lit);
      replacement_value = values[replacement];
      assert (replacement_value);
      if (replacement_value > 0)
        break;
    }
    if (replacement_value > 0) {
      assert (replacement != INVALID);
      ROG (ref, "unwatching %u in", lit);
      lits[0] = other;
      lits[1] = replacement;
      *r = lit;
      watch_klause (kitten, replacement, ref);
      q--;
    } else {
      assert (replacement_value < 0);
      ROG (ref, "single satisfied");
      res = false;
      break;
    }
  }
  while (p != end_watches)
    *q++ = *p++;
  SET_END_OF_STACK (*watches, q);
  ADD (kitten_ticks, ticks);
  if (res) {
    LOG ("flipping value of %u", lit);
    values[lit] = -1;
    const unsigned not_lit = lit ^ 1;
    values[not_lit] = 1;
    INC (kitten_flipped);
  } else
    LOG ("failed to flip value of %u", lit);
  return res;
}

/*------------------------------------------------------------------------*/

// this cadical specific clause addition avoids copying clauses multiple
// times just to convert literals to unsigned representation.
//
static unsigned int2u (int lit) {
  assert (lit != 0);
  int idx = abs (lit) - 1;
  return (lit < 0) + 2u * (unsigned) idx;
}

void kitten_assume (kitten *kitten, unsigned elit) {
  REQUIRE_INITIALIZED ();
  if (kitten->status)
    reset_incremental (kitten);
  const unsigned ilit = import_literal (kitten, elit);
  LOG ("registering assumption %u", ilit);
  PUSH_STACK (kitten->assumptions, ilit);
}

void kitten_assume_signed (kitten *kitten, int elit) {
  unsigned kelit = int2u (elit);
  kitten_assume (kitten, kelit);
}

void kitten_clause_with_id_and_exception (kitten *kitten, unsigned id,
                                          size_t size,
                                          const unsigned *elits,
                                          unsigned except) {
  REQUIRE_INITIALIZED ();
  if (kitten->status)
    reset_incremental (kitten);
  assert (EMPTY_STACK (kitten->klause));
  const unsigned *const end = elits + size;
  for (const unsigned *p = elits; p != end; p++) {
    const unsigned elit = *p;
    if (elit == except)
      continue;
    const unsigned ilit = import_literal (kitten, elit);
    assert (ilit < kitten->lits);
    const unsigned iidx = ilit / 2;
    if (kitten->marks[iidx])
      INVALID_API_USAGE ("variable '%u' of literal '%u' occurs twice",
                         elit / 2, elit);
    kitten->marks[iidx] = true;
    PUSH_STACK (kitten->klause, ilit);
  }
  for (unsigned *p = kitten->klause.begin; p != kitten->klause.end; p++)
    kitten->marks[*p / 2] = false;
  new_original_klause (kitten, id);
  CLEAR_STACK (kitten->klause);
}

void citten_clause_with_id_and_exception (kitten *kitten, unsigned id,
                                          size_t size, const int *elits,
                                          unsigned except) {
  REQUIRE_INITIALIZED ();
  if (kitten->status)
    reset_incremental (kitten);
  assert (EMPTY_STACK (kitten->klause));
  const int *const end = elits + size;
  for (const int *p = elits; p != end; p++) {
    const unsigned elit = int2u (*p); // this is the conversion
    if (elit == except)
      continue;
    const unsigned ilit = import_literal (kitten, elit);
    assert (ilit < kitten->lits);
    const unsigned iidx = ilit / 2;
    if (kitten->marks[iidx])
      INVALID_API_USAGE ("variable '%u' of literal '%u' occurs twice",
                         elit / 2, elit);
    kitten->marks[iidx] = true;
    PUSH_STACK (kitten->klause, ilit);
  }
  for (unsigned *p = kitten->klause.begin; p != kitten->klause.end; p++)
    kitten->marks[*p / 2] = false;
  new_original_klause (kitten, id);
  CLEAR_STACK (kitten->klause);
}

void citten_clause_with_id_and_equivalence (kitten *kitten, unsigned id,
                                            size_t size, const int *elits,
                                            unsigned lit, unsigned other) {
  REQUIRE_INITIALIZED ();
  if (kitten->status)
    reset_incremental (kitten);
  assert (EMPTY_STACK (kitten->klause));
  bool sat = false;
  const int *const end = elits + size;
  for (const int *p = elits; p != end; p++) {
    const unsigned elit = int2u (*p); // this is the conversion
    if (elit == (lit ^ 1u) || elit == (other ^ 1u))
      continue;
    if (elit == lit || elit == other) {
      sat = true;
      break;
    }
    const unsigned ilit = import_literal (kitten, elit);
    assert (ilit < kitten->lits);
    const unsigned iidx = ilit / 2;
    if (kitten->marks[iidx])
      INVALID_API_USAGE ("variable '%u' of literal '%u' occurs twice",
                         elit / 2, elit);
    kitten->marks[iidx] = true;
    PUSH_STACK (kitten->klause, ilit);
  }
  for (unsigned *p = kitten->klause.begin; p != kitten->klause.end; p++)
    kitten->marks[*p / 2] = false;
  if (!sat)
    new_original_klause (kitten, id);
  CLEAR_STACK (kitten->klause);
}

void kitten_clause (kitten *kitten, size_t size, unsigned *elits) {
  kitten_clause_with_id_and_exception (kitten, INVALID, size, elits,
                                       INVALID);
}

void citten_clause_with_id (kitten *kitten, unsigned id, size_t size,
                            int *elits) {
  citten_clause_with_id_and_exception (kitten, id, size, elits, INVALID);
}

void kitten_unit (kitten *kitten, unsigned lit) {
  kitten_clause (kitten, 1, &lit);
}

void kitten_binary (kitten *kitten, unsigned a, unsigned b) {
  unsigned clause[2] = {a, b};
  kitten_clause (kitten, 2, clause);
}

int kitten_solve (kitten *kitten) {
  REQUIRE_INITIALIZED ();
  if (kitten->status)
    reset_incremental (kitten);
  else // if (kitten->level)
    completely_backtrack_to_root_level (kitten);

  LOG ("starting solving under %zu assumptions",
       SIZE_STACK (kitten->assumptions));

  INC (kitten_solved);

  int res = propagate_units (kitten);
  while (!res) {
    const unsigned conflict = propagate (kitten);
    if (kitten->terminator &&
        kitten->terminator (kitten->terminator_data)) {
      LOG ("terminator requested termination");
      res = -1;
      break;
    }
    if (conflict != INVALID) {
      if (kitten->level)
        analyze (kitten, conflict);
      else {
        inconsistent (kitten, conflict);
        res = 20;
      }
    } else
      res = decide (kitten);
  }

  if (res < 0)
    res = 0;

  if (!res && !EMPTY_STACK (kitten->assumptions))
    reset_assumptions (kitten);

  UPDATE_STATUS (res);

  if (res == 10)
    INC (kitten_sat);
  else if (res == 20)
    INC (kitten_unsat);
  else
    INC (kitten_unknown);

  LOG ("finished solving with result %d", res);

  return res;
}

int kitten_status (kitten *kitten) { return kitten->status; }

unsigned kitten_compute_clausal_core (kitten *kitten,
                                      uint64_t *learned_ptr) {
  REQUIRE_STATUS (20);

  if (!kitten->antecedents)
    INVALID_API_USAGE ("antecedents not tracked");

  LOG ("computing clausal core");

  unsigneds *resolved = &kitten->resolved;
  assert (EMPTY_STACK (*resolved));

  unsigned original = 0;
  uint64_t learned = 0;

  unsigned reason_ref = kitten->inconsistent;

  if (reason_ref == INVALID) {
    assert (!EMPTY_STACK (kitten->assumptions));
    reason_ref = kitten->failing;
    if (reason_ref == INVALID) {
      LOG ("assumptions mutually inconsistent");
      goto DONE;
    }
  }

  PUSH_STACK (*resolved, reason_ref);
  unsigneds *core = &kitten->core;
  assert (EMPTY_STACK (*core));

  while (!EMPTY_STACK (*resolved)) {
    const unsigned c_ref = POP_STACK (*resolved);
    if (c_ref == INVALID) {
      const unsigned d_ref = POP_STACK (*resolved);
      ROG (d_ref, "core[%zu]", SIZE_STACK (*core));
      PUSH_STACK (*core, d_ref);
      klause *d = dereference_klause (kitten, d_ref);
      assert (!is_core_klause (d));
      set_core_klause (d);
      if (is_learned_klause (d))
        learned++;
      else
        original++;
    } else {
      klause *c = dereference_klause (kitten, c_ref);
      if (is_core_klause (c))
        continue;
      PUSH_STACK (*resolved, c_ref);
      PUSH_STACK (*resolved, INVALID);
      ROG (c_ref, "analyzing antecedent core");
      if (!is_learned_klause (c))
        continue;
      for (all_antecedents (d_ref, c)) {
        klause *d = dereference_klause (kitten, d_ref);
        if (!is_core_klause (d))
          PUSH_STACK (*resolved, d_ref);
      }
    }
  }

DONE:

  if (learned_ptr)
    *learned_ptr = learned;

  LOG ("clausal core of %u original clauses", original);
  LOG ("clausal core of %" PRIu64 " learned clauses", learned);
  kitten->statistics.original = original;
  kitten->statistics.learned = 0;
  UPDATE_STATUS (21);

  return original;
}

void kitten_traverse_core_ids (kitten *kitten, void *state,
                               void (*traverse) (void *, unsigned)) {
  REQUIRE_STATUS (21);

  LOG ("traversing core of original clauses");

  unsigned traversed = 0;

  for (all_original_klauses (c)) {
    // only happens for 'true' incremental calls, i.e. if add happens after
    // solve
    if (is_learned_klause (c))
      continue;
    if (!is_core_klause (c))
      continue;
    ROG (reference_klause (kitten, c), "traversing");
    traverse (state, c->aux);
    traversed++;
  }

  LOG ("traversed %u original core clauses", traversed);
  (void) traversed;

  assert (kitten->status == 21);
}

void kitten_traverse_core_clauses (kitten *kitten, void *state,
                                   void (*traverse) (void *, bool, size_t,
                                                     const unsigned *)) {
  REQUIRE_STATUS (21);

  LOG ("traversing clausal core");

  unsigned traversed = 0;

  for (all_stack (unsigned, c_ref, kitten->core)) {
    klause *c = dereference_klause (kitten, c_ref);
    assert (is_core_klause (c));
    const bool learned = is_learned_klause (c);
    unsigneds *eclause = &kitten->eclause;
    assert (EMPTY_STACK (*eclause));
    for (all_literals_in_klause (ilit, c)) {
      const unsigned elit = export_literal (kitten, ilit);
      PUSH_STACK (*eclause, elit);
    }
    const size_t size = SIZE_STACK (*eclause);
    const unsigned *elits = eclause->begin;
    ROG (reference_klause (kitten, c), "traversing");
    traverse (state, learned, size, elits);
    CLEAR_STACK (*eclause);
    traversed++;
  }

  LOG ("traversed %u core clauses", traversed);
  (void) traversed;

  assert (kitten->status == 21);
}

void kitten_traverse_core_clauses_with_id (
    kitten *kitten, void *state,
    void (*traverse) (void *state, unsigned, bool learned, size_t,
                      const unsigned *)) {
  REQUIRE_STATUS (21);

  LOG ("traversing clausal core");

  unsigned traversed = 0;

  for (all_stack (unsigned, c_ref, kitten->core)) {
    klause *c = dereference_klause (kitten, c_ref);
    assert (is_core_klause (c));
    const bool learned = is_learned_klause (c);
    unsigneds *eclause = &kitten->eclause;
    assert (EMPTY_STACK (*eclause));
    for (all_literals_in_klause (ilit, c)) {
      const unsigned elit = export_literal (kitten, ilit);
      PUSH_STACK (*eclause, elit);
    }
    const size_t size = SIZE_STACK (*eclause);
    const unsigned *elits = eclause->begin;
    ROG (reference_klause (kitten, c), "traversing");
    unsigned ctag = learned ? 0 : c->aux;
    traverse (state, ctag, learned, size, elits);
    CLEAR_STACK (*eclause);
    traversed++;
  }

  LOG ("traversed %u core clauses", traversed);
  (void) traversed;

  assert (kitten->status == 21);
}

void kitten_trace_core (kitten *kitten, void *state,
                        void (*trace) (void *, unsigned, unsigned, bool,
                                       size_t, const unsigned *, size_t,
                                       const unsigned *)) {
  REQUIRE_STATUS (21);

  LOG ("tracing clausal core");

  unsigned traced = 0;

  for (all_stack (unsigned, c_ref, kitten->core)) {
    klause *c = dereference_klause (kitten, c_ref);
    assert (is_core_klause (c));
    const bool learned = is_learned_klause (c);
    unsigneds *eclause = &kitten->eclause;
    assert (EMPTY_STACK (*eclause));
    for (all_literals_in_klause (ilit, c)) {
      const unsigned elit = export_literal (kitten, ilit);
      PUSH_STACK (*eclause, elit);
    }
    const size_t size = SIZE_STACK (*eclause);
    const unsigned *elits = eclause->begin;

    unsigneds *resolved = &kitten->resolved;
    assert (EMPTY_STACK (*resolved));
    if (learned) {
      for (all_antecedents (ref, c)) {
        PUSH_STACK (*resolved, ref);
      }
    }
    const size_t rsize = SIZE_STACK (*resolved);
    const unsigned *rids = resolved->begin;

    unsigned cid = reference_klause (kitten, c);
    unsigned ctag = learned ? 0 : c->aux;
    ROG (cid, "tracing");
    trace (state, cid, ctag, learned, size, elits, rsize, rids);
    CLEAR_STACK (*eclause);
    CLEAR_STACK (*resolved);
    traced++;
  }

  LOG ("traced %u core clauses", traced);
  (void) traced;

  assert (kitten->status == 21);
}

void kitten_shrink_to_clausal_core (kitten *kitten) {
  REQUIRE_STATUS (21);

  LOG ("shrinking formula to core of original clauses");

  CLEAR_STACK (kitten->trail);

  kitten->unassigned = kitten->lits / 2;
  kitten->propagated = 0;
  kitten->level = 0;

  update_search (kitten, kitten->queue.last);

  memset (kitten->values, 0, kitten->lits);

  for (all_kits (lit))
    CLEAR_STACK (KATCHES (lit));

  assert (kitten->inconsistent != INVALID);
  klause *inconsistent = dereference_klause (kitten, kitten->inconsistent);
  if (is_learned_klause (inconsistent) || inconsistent->size) {
    ROG (kitten->inconsistent, "resetting inconsistent");
    kitten->inconsistent = INVALID;
  } else
    ROG (kitten->inconsistent, "keeping inconsistent");

  CLEAR_STACK (kitten->units);

  klause *begin = begin_klauses (kitten), *q = begin;
  klause const *const end = end_original_klauses (kitten);
#ifdef LOGGING
  unsigned original = 0;
#endif
  for (klause *c = begin, *next; c != end; c = next) {
    next = next_klause (kitten, c);
    // assert (!is_learned_klause (c)); not necessarily true
    if (is_learned_klause (c))
      continue;
    if (!is_core_klause (c))
      continue;
    unset_core_klause (c);
    const unsigned dst = (unsigned *) q - (unsigned *) begin;
    const unsigned size = c->size;
    if (!size) {
      if (kitten->inconsistent != INVALID)
        kitten->inconsistent = dst;
    } else if (size == 1) {
      PUSH_STACK (kitten->units, dst);
      ROG (dst, "keeping");
    } else {
      watch_klause (kitten, c->lits[0], dst);
      watch_klause (kitten, c->lits[1], dst);
    }
    if (c == q)
      q = next;
    else {
      const size_t bytes = (char *) next - (char *) c;
      memmove (q, c, bytes);
      q = (klause *) ((char *) q + bytes);
    }
#ifdef LOGGING
    original++;
#endif
  }
  SET_END_OF_STACK (kitten->klauses, (unsigned *) q);
  kitten->end_original_ref = SIZE_STACK (kitten->klauses);
  LOG ("end of original clauses at %zu", kitten->end_original_ref);
  LOG ("%u original clauses left", original);

  CLEAR_STACK (kitten->core);

  UPDATE_STATUS (0);
}

signed char kitten_signed_value (kitten *kitten, int selit) {
  REQUIRE_STATUS (10);
  const unsigned elit = int2u (selit);
  const unsigned eidx = elit / 2;
  if (eidx >= kitten->evars)
    return 0;
  unsigned iidx = kitten->import[eidx];
  if (!iidx)
    return 0;
  const unsigned ilit = 2 * (iidx - 1) + (elit & 1);
  return kitten->values[ilit];
}

signed char kitten_value (kitten *kitten, unsigned elit) {
  REQUIRE_STATUS (10);
  const unsigned eidx = elit / 2;
  if (eidx >= kitten->evars)
    return 0;
  unsigned iidx = kitten->import[eidx];
  if (!iidx)
    return 0;
  const unsigned ilit = 2 * (iidx - 1) + (elit & 1);
  return kitten->values[ilit];
}

signed char kitten_fixed (kitten *kitten, unsigned elit) {
  const unsigned eidx = elit / 2;
  if (eidx >= kitten->evars)
    return 0;
  unsigned iidx = kitten->import[eidx];
  if (!iidx)
    return 0;
  iidx--;
  const unsigned ilit = 2 * iidx + (elit & 1);
  signed char res = kitten->values[ilit];
  if (!res)
    return 0;
  kar *v = kitten->vars + iidx;
  if (v->level)
    return 0;
  return res;
}

signed char kitten_fixed_signed (kitten *kitten, int elit) {
  unsigned kelit = int2u (elit);
  return kitten_fixed (kitten, kelit);
}

bool kitten_flip_literal (kitten *kitten, unsigned elit) {
  REQUIRE_STATUS (10);
  const unsigned eidx = elit / 2;
  if (eidx >= kitten->evars)
    return false;
  unsigned iidx = kitten->import[eidx];
  if (!iidx)
    return false;
  const unsigned ilit = 2 * (iidx - 1) + (elit & 1);
  if (kitten_fixed (kitten, elit))
    return false;
  return flip_literal (kitten, ilit);
}

bool kitten_flip_signed_literal (kitten *kitten, int elit) {
  REQUIRE_STATUS (10);
  unsigned kelit = int2u (elit);
  return kitten_flip_literal (kitten, kelit);
}

bool kitten_failed (kitten *kitten, unsigned elit) {
  REQUIRE_STATUS (20);
  const unsigned eidx = elit / 2;
  if (eidx >= kitten->evars)
    return false;
  unsigned iidx = kitten->import[eidx];
  if (!iidx)
    return false;
  const unsigned ilit = 2 * (iidx - 1) + (elit & 1);
  return kitten->failed[ilit];
}

// checks both watches for clauses with only one literal positively
// assigned. if such a clause is found, return false. Otherwise fix watch
// invariant and return true
static bool prime_propagate (kitten *kitten, const unsigned idx,
                             void *state, const bool ignoring,
                             bool (*ignore) (void *, unsigned)) {
  unsigned lit = 2 * idx;
  unsigned conflict = INVALID;
  value *values = kitten->values;
  for (int i = 0; i < 2; i++) {
    if (conflict != INVALID)
      break;
    lit = lit ^ i;
    const unsigned not_lit = lit ^ 1;
    katches *watches = kitten->watches + not_lit;
    unsigned *q = BEGIN_STACK (*watches);
    const unsigned *const end_watches = END_STACK (*watches);
    unsigned const *p = q;
    uint64_t ticks = (((char *) end_watches - (char *) q) >> 7) + 1;
    while (p != end_watches) {
      const unsigned ref = *q++ = *p++;
      klause *c = dereference_klause (kitten, ref);
      if (is_learned_klause (c) || ignore (state, c->aux) == ignoring)
        continue;
      assert (c->size > 1);
      unsigned *lits = c->lits;
      const unsigned other = lits[0] ^ lits[1] ^ not_lit;
      const value other_value = values[other];
      ticks++;
      if (other_value > 0)
        continue;
      value replacement_value = -1;
      unsigned replacement = INVALID;
      const unsigned *const end_lits = lits + c->size;
      unsigned *r;
      for (r = lits + 2; r != end_lits; r++) {
        replacement = *r;
        replacement_value = values[replacement];
        if (replacement_value > 0)
          break;
      }
      if (replacement_value > 0) {
        assert (replacement != INVALID);
        ROG (ref, "unwatching %u in", not_lit);
        lits[0] = other;
        lits[1] = replacement;
        *r = not_lit;
        watch_klause (kitten, replacement, ref);
        q--;
      } else {
        ROG (ref, "idx %u forced prime by", idx);
        conflict = ref;
        break;
      }
    }
    while (p != end_watches)
      *q++ = *p++;
    SET_END_OF_STACK (*watches, q);
    ADD (kitten_ticks, ticks);
  }
  return conflict == INVALID;
}

void kitten_add_prime_implicant (kitten *kitten, void *state, int side,
                                 void (*add_implicant) (void *, int, size_t,
                                                        const unsigned *)) {
  REQUIRE_STATUS (11);
  // might be possible in some edge cases
  unsigneds *prime = &kitten->prime[side];
  unsigneds *prime2 = &kitten->prime[!side];
  assert (!EMPTY_STACK (*prime) || !EMPTY_STACK (*prime2));
  CLEAR_STACK (*prime2);

  for (all_stack (unsigned, lit, *prime)) {
    const unsigned not_lit = lit ^ 1;
    const unsigned elit = export_literal (kitten, not_lit);
    PUSH_STACK (*prime2, elit);
  }

  // adds a clause which will reset kitten status and backtrack
  add_implicant (state, side, SIZE_STACK (*prime2), BEGIN_STACK (*prime2));
  CLEAR_STACK (*prime);
  CLEAR_STACK (*prime2);
}

// computes two prime implicants, only considering clauses based on ignore
// return -1 if no prime implicant has been computed, otherwise returns
// index of shorter implicant.
// TODO does not work if flip has been called beforehand
int kitten_compute_prime_implicant (kitten *kitten, void *state,
                                    bool (*ignore) (void *, unsigned)) {
  REQUIRE_STATUS (10);

  value *values = kitten->values;
  kar *vars = kitten->vars;
  unsigneds unassigned;
  INIT_STACK (unassigned);
  bool limit_hit = 0;
  assert (EMPTY_STACK (kitten->prime[0]) && EMPTY_STACK (kitten->prime[1]));
  for (int i = 0; i < 2; i++) {
    const bool ignoring = i;
    for (all_stack (unsigned, lit, kitten->trail)) {
      if (KITTEN_TICKS >= kitten->limits.ticks) {
        LOG ("ticks limit %" PRIu64 " hit after %" PRIu64 " ticks",
             kitten->limits.ticks, KITTEN_TICKS);
        limit_hit = 1;
        break;
      }
      assert (values[lit] > 0);
      const unsigned idx = lit / 2;
      const unsigned ref = vars[idx].reason;
      assert (vars[idx].level);
      klause *c = 0;
      if (ref != INVALID)
        c = dereference_klause (kitten, ref);
      if (ref == INVALID || is_learned_klause (c) ||
          ignore (state, c->aux) == ignoring) {
        LOG ("non-prime candidate var %d", idx);
        if (prime_propagate (kitten, idx, state, ignoring, ignore)) {
          values[lit] = 0;
          values[lit ^ 1] = 0;
          PUSH_STACK (unassigned, lit);
        } else
          assert (values[lit] > 0);
      }
    }
    unsigneds *prime = &kitten->prime[i];
    // push on prime implicant stack.
    for (all_kits (lit)) {
      if (values[lit] > 0)
        PUSH_STACK (*prime, lit);
    }
    // reassign all literals on
    for (all_stack (unsigned, lit, unassigned)) {
      assert (!values[lit]);
      values[lit] = 1;
      values[lit ^ 1] = -1;
    }
    CLEAR_STACK (unassigned);
  }
  RELEASE_STACK (unassigned);

  if (limit_hit) {
    CLEAR_STACK (kitten->prime[0]);
    CLEAR_STACK (kitten->prime[1]);
    return -1;
  }
  // the only case when one of the prime implicants is allowed to be empty
  // is if ignore returns always true or always false.
  assert (!EMPTY_STACK (kitten->prime[0]) ||
          !EMPTY_STACK (kitten->prime[1]));
  UPDATE_STATUS (11);

  int res = SIZE_STACK (kitten->prime[0]) > SIZE_STACK (kitten->prime[1]);
  return res;
}

static bool contains_blit (kitten *kitten, klause *c, const unsigned blit) {
  for (all_literals_in_klause (lit, c)) {
    if (lit == blit)
      return true;
  }
  return false;
}

static bool prime_propagate_blit (kitten *kitten, const unsigned idx,
                                  const unsigned blit) {
  unsigned lit = 2 * idx;
  unsigned conflict = INVALID;
  value *values = kitten->values;
  LOG ("prime propagating idx %u for blit %u", idx, blit);
  for (int i = 0; i < 2; i++) {
    if (conflict != INVALID)
      break;
    lit = lit ^ i;
    if (lit == blit)
      continue;
    const unsigned not_lit = lit ^ 1;
    katches *watches = kitten->watches + not_lit;
    unsigned *q = BEGIN_STACK (*watches);
    const unsigned *const end_watches = END_STACK (*watches);
    unsigned const *p = q;
    uint64_t ticks = (((char *) end_watches - (char *) q) >> 7) + 1;
    while (p != end_watches) {
      const unsigned ref = *q++ = *p++;
      klause *c = dereference_klause (kitten, ref);
      if (is_learned_klause (c))
        continue;
      ROG (ref, "checking with blit %u", blit);
      assert (c->size > 1);
      unsigned *lits = c->lits;
      const unsigned other = lits[0] ^ lits[1] ^ not_lit;
      const value other_value = values[other];
      ticks++;
      bool use = other == blit || not_lit == blit;
      if (other_value > 0)
        continue;
      value replacement_value = -1;
      unsigned replacement = INVALID;
      const unsigned *const end_lits = lits + c->size;
      unsigned *r;
      for (r = lits + 2; r != end_lits; r++) {
        replacement = *r;
        replacement_value = values[replacement];
        use = use || replacement == blit;
        if (replacement_value > 0)
          break;
      }
      if (replacement_value > 0) {
        assert (replacement != INVALID);
        ROG (ref, "unwatching %u in", not_lit);
        lits[0] = other;
        lits[1] = replacement;
        *r = not_lit;
        watch_klause (kitten, replacement, ref);
        q--;
      } else if (!use) {
        continue;
      } else {
        ROG (ref, "idx %u forced prime by", idx);
        conflict = ref;
        break;
      }
    }
    while (p != end_watches)
      *q++ = *p++;
    SET_END_OF_STACK (*watches, q);
    ADD (kitten_ticks, ticks);
  }
  return conflict == INVALID;
}

static int compute_prime_implicant_for (kitten *kitten, unsigned blit) {
  value *values = kitten->values;
  kar *vars = kitten->vars;
  unsigneds unassigned;
  INIT_STACK (unassigned);
  bool limit_hit = false;
  assert (EMPTY_STACK (kitten->prime[0]) && EMPTY_STACK (kitten->prime[1]));
  for (int i = 0; i < 2; i++) {
    const unsigned block = blit ^ i;
    const bool ignoring = i;
    if (prime_propagate_blit (kitten, block / 2, block)) {
      value tmp = values[blit];
      assert (tmp);
      values[blit] = 0;
      values[blit ^ 1] = 0;
      PUSH_STACK (unassigned, tmp > 0 ? blit : blit ^ 1);
      PUSH_STACK (kitten->prime[i], block); // will be negated!
    } else
      assert (false);
    for (all_stack (unsigned, lit, kitten->trail)) {
      if (KITTEN_TICKS >= kitten->limits.ticks) {
        LOG ("ticks limit %" PRIu64 " hit after %" PRIu64 " ticks",
             kitten->limits.ticks, KITTEN_TICKS);
        limit_hit = true;
        break;
      }
      if (!values[lit])
        continue;
      assert (values[lit]); // not true when flipping is involved
      const unsigned idx = lit / 2;
      const unsigned ref = vars[idx].reason;
      assert (vars[idx].level);
      LOG ("non-prime candidate var %d", idx);
      if (prime_propagate_blit (kitten, idx, block)) {
        value tmp = values[lit];
        assert (tmp);
        values[lit] = 0;
        values[lit ^ 1] = 0;
        PUSH_STACK (unassigned, tmp > 0 ? lit : lit ^ 1);
      }
    }
    unsigneds *prime = &kitten->prime[i];
    // push on prime implicant stack.
    for (all_kits (lit)) {
      if (values[lit] > 0)
        PUSH_STACK (*prime, lit);
    }
    // reassign all literals on
    for (all_stack (unsigned, lit, unassigned)) {
      assert (!values[lit]);
      values[lit] = 1;
      values[lit ^ 1] = -1;
    }
    CLEAR_STACK (unassigned);
  }
  RELEASE_STACK (unassigned);

  if (limit_hit) {
    CLEAR_STACK (kitten->prime[0]);
    CLEAR_STACK (kitten->prime[1]);
    return -1;
  }
  // the only case when one of the prime implicants is allowed to be empty
  // is if ignore returns always true or always false.
  assert (!EMPTY_STACK (kitten->prime[0]) ||
          !EMPTY_STACK (kitten->prime[1]));
  LOGLITS (BEGIN_STACK (kitten->prime[0]), SIZE_STACK (kitten->prime[0]),
           "first implicant %u", blit);
  LOGLITS (BEGIN_STACK (kitten->prime[1]), SIZE_STACK (kitten->prime[1]),
           "second implicant %u", blit ^ 1);
  UPDATE_STATUS (11);

  int res = SIZE_STACK (kitten->prime[0]) > SIZE_STACK (kitten->prime[1]);
  return res;
}

int kitten_flip_and_implicant_for_signed_literal (kitten *kitten,
                                                  int elit) {
  REQUIRE_STATUS (10);
  unsigned kelit = int2u (elit);
  if (!kitten_flip_literal (kitten, kelit)) {
    return -2;
  }
  const unsigned eidx = kelit / 2;
  unsigned iidx = kitten->import[eidx];
  assert (iidx);
  const unsigned ilit = 2 * (iidx - 1) + (kelit & 1);
  return compute_prime_implicant_for (kitten, ilit);
}
