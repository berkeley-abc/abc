#ifndef _kitten_h_INCLUDED
#define _kitten_h_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct kitten kitten;

kitten *kitten_init (void);
void kitten_clear (kitten *);
void kitten_release (kitten *);

#ifdef LOGGING
void kitten_set_logging (kitten *kitten);
#endif

void kitten_track_antecedents (kitten *);

void kitten_shuffle_clauses (kitten *);
void kitten_flip_phases (kitten *);
void kitten_randomize_phases (kitten *);

void kitten_assume (kitten *, unsigned lit);
void kitten_assume_signed (kitten *, int lit);

void kitten_clause (kitten *, size_t size, unsigned *);
void citten_clause_with_id (kitten *, unsigned id, size_t size, int *);
void kitten_unit (kitten *, unsigned);
void kitten_binary (kitten *, unsigned, unsigned);

void kitten_clause_with_id_and_exception (kitten *, unsigned id,
                                          size_t size, const unsigned *,
                                          unsigned except);

void citten_clause_with_id_and_exception (kitten *, unsigned id,
                                          size_t size, const int *,
                                          unsigned except);
void citten_clause_with_id_and_equivalence (kitten *, unsigned id,
                                            size_t size, const int *,
                                            unsigned, unsigned);
void kitten_no_ticks_limit (kitten *);
void kitten_set_ticks_limit (kitten *, uint64_t);
uint64_t kitten_current_ticks (kitten *);

void kitten_no_terminator (kitten *);
void kitten_set_terminator (kitten *, void *, int (*) (void *));

int kitten_solve (kitten *);
int kitten_status (kitten *);

signed char kitten_value (kitten *, unsigned);
signed char kitten_signed_value (kitten *, int); // converts second argument
signed char kitten_fixed (kitten *, unsigned);
signed char kitten_fixed_signed (kitten *, int); // converts
bool kitten_failed (kitten *, unsigned);
bool kitten_flip_literal (kitten *, unsigned);
bool kitten_flip_signed_literal (kitten *, int);

unsigned kitten_compute_clausal_core (kitten *, uint64_t *learned);
void kitten_shrink_to_clausal_core (kitten *);

void kitten_traverse_core_ids (kitten *, void *state,
                               void (*traverse) (void *state, unsigned id));

void kitten_traverse_core_clauses (kitten *, void *state,
                                   void (*traverse) (void *state,
                                                     bool learned, size_t,
                                                     const unsigned *));
void kitten_traverse_core_clauses_with_id (
    kitten *, void *state,
    void (*traverse) (void *state, unsigned, bool learned, size_t,
                      const unsigned *));
void kitten_trace_core (kitten *, void *state,
                        void (*trace) (void *, unsigned, unsigned, bool,
                                       size_t, const unsigned *, size_t,
                                       const unsigned *));

int kitten_compute_prime_implicant (kitten *kitten, void *state,
                                    bool (*ignore) (void *, unsigned));

void kitten_add_prime_implicant (kitten *kitten, void *state, int side,
                                 void (*add_implicant) (void *, int, size_t,
                                                        const unsigned *));

int kitten_flip_and_implicant_for_signed_literal (kitten *kitten, int elit);

#ifdef __cplusplus
}
#endif

#endif
