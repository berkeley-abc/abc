#ifndef _proof_h_INCLUDED
#define _proof_h_INCLUDED

#include "global.h"

#include "tracer.hpp"
#include <stdint.h>

ABC_NAMESPACE_CXX_HEADER_START

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

class File;
struct Clause;
struct Internal;
class Tracer;
class FileTracer;

/*------------------------------------------------------------------------*/

// Provides proof checking and writing.

class Proof {

  Internal *internal;

  std::vector<int> clause;          // of external literals
  std::vector<int64_t> proof_chain; // LRAT style proof chain of clause
  int64_t clause_id;                // id of added clause
  bool redundant;
  int witness;

  // the 'tracers'
  std::vector<Tracer *> tracers;          // tracers (ie checker)
  std::vector<FileTracer *> file_tracers; // file tracers (ie LRAT tracer)

  void add_literal (int internal_lit); // add to 'clause'
  void add_literals (Clause *);        // add to 'clause'

  void add_literals (const std::vector<int> &); // ditto

  void add_original_clause (
      bool restore = false); // notify observers of original clauses
  void add_derived_clause ();
  void add_assumption_clause ();
  void delete_clause ();
  void demote_clause ();
  void weaken_minus ();
  void strengthen ();
  void finalize_clause ();
  void add_assumption ();
  void add_constraint ();

public:
  Proof (Internal *);
  ~Proof ();

  void connect (Tracer *t) { tracers.push_back (t); }
  void disconnect (Tracer *t);
  // Add original clauses to the proof (for online proof checking).
  //
  void add_original_clause (int64_t, bool, const std::vector<int> &);

  void add_assumption_clause (int64_t, const std::vector<int> &,
                              const std::vector<int64_t> &);
  void add_assumption_clause (int64_t, int, const std::vector<int64_t> &);
  void add_assumption (int);
  void add_constraint (const std::vector<int> &);
  void reset_assumptions ();

  // Add/delete original clauses to/from the proof using their original
  //  external literals (from external->eclause)
  //
  void add_external_original_clause (int64_t, bool,
                                     const std::vector<int> &,
                                     bool restore = false);
  void delete_external_original_clause (int64_t, bool,
                                        const std::vector<int> &);

  // Add derived (such as learned) clauses to the proof.
  //
  void add_derived_empty_clause (int64_t, const std::vector<int64_t> &);
  void add_derived_unit_clause (int64_t, int unit,
                                const std::vector<int64_t> &);
  void add_derived_clause (Clause *c, const std::vector<int64_t> &);
  void add_derived_clause (int64_t, bool, const std::vector<int> &,
                           const std::vector<int64_t> &);
  void add_derived_rat_clause (int64_t, bool, int, const std::vector<int> &,
                               const std::vector<int64_t> &);
  void add_derived_rat_clause (Clause *c, int w,
                               const std::vector<int64_t> &);

  // deletion of clauses. It comes in several variants, depending if the
  // clause should be restored or not
  void delete_clause (int64_t, bool, const std::vector<int> &);
  void weaken_minus (int64_t, const std::vector<int> &);
  void weaken_plus (int64_t, const std::vector<int> &);
  void delete_unit_clause (int64_t id, const int lit);
  void delete_clause (Clause *);
  void weaken_minus (Clause *);
  void weaken_plus (Clause *);
  void strengthen (int64_t);

  void finalize_unit (int64_t, int);
  void finalize_external_unit (int64_t, int);
  void finalize_clause (int64_t, const std::vector<int> &c);
  void finalize_clause (Clause *);

  void report_status (int, int64_t);
  void begin_proof (int64_t);
  void conclude_unsat (ConclusionType, const std::vector<int64_t> &);
  void conclude_sat (const std::vector<int> &model);
  void conclude_unknown (const std::vector<int> &trace);
  void solve_query ();
  // These two actually pretend to add and remove a clause.
  //
  void flush_clause (Clause *); // remove falsified literals
  void strengthen_clause (Clause *, int, const std::vector<int64_t> &);
  void otfs_strengthen_clause (Clause *, const std::vector<int> &,
                               const std::vector<int64_t> &);

  void flush ();
};

} // namespace CaDiCaL

ABC_NAMESPACE_CXX_HEADER_END

#endif
