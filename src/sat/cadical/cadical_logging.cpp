#include "global.h"

#ifdef LOGGING

#include "internal.hpp"

ABC_NAMESPACE_IMPL_START

namespace CaDiCaL {

void Logger::print_log_prefix (Internal *internal) {
  internal->print_prefix ();
  tout.magenta ();
  fputs ("LOG ", Abc_FrameGlobalGetOut());
  tout.magenta (true);
  fprintf ( Abc_FrameGlobalGetOut(), "%d ", internal->level);
  tout.normal ();
}

void Logger::log_empty_line (Internal *internal) {
  internal->print_prefix ();
  tout.magenta ();
  const int len = internal->prefix.size (), max = 78 - len;
  for (int i = 0; i < max; i++)
    fputc( '-', Abc_FrameGlobalGetOut() );
  fputc( '\n', Abc_FrameGlobalGetOut() );
  tout.normal ();
  fflush( Abc_FrameGlobalGetOut() );
}

void Logger::log (Internal *internal, const char *fmt, ...) {
  print_log_prefix (internal);
  tout.magenta ();
  va_list ap;
  va_start (ap, fmt);
  vfprintf ( Abc_FrameGlobalGetOut(), fmt, ap);
  va_end (ap);
  fputc( '\n', Abc_FrameGlobalGetOut() );
  tout.normal ();
  fflush( Abc_FrameGlobalGetOut() );
}

// It is hard to factor out the common part between the two clause loggers,
// since they are also used in slightly different contexts.  Our attempt to
// do so were not more readable than the current version.  See the header
// for an explanation of the difference between the following two functions.

void Logger::log (Internal *internal, const Clause *c, const char *fmt,
                  ...) {
  print_log_prefix (internal);
  tout.magenta ();
  va_list ap;
  va_start (ap, fmt);
  vfprintf ( Abc_FrameGlobalGetOut(), fmt, ap);
  va_end (ap);
  if (c) {
    if (c->redundant)
      fprintf ( Abc_FrameGlobalGetOut(), " glue %d redundant", c->glue);
    else
      fprintf ( Abc_FrameGlobalGetOut(), " irredundant");
    fprintf ( Abc_FrameGlobalGetOut(), " size %d clause[%" PRId64 "]", c->size, c->id);
    if (c->moved)
      fprintf ( Abc_FrameGlobalGetOut(), " ... (moved)");
    else {
      if (internal->opts.logsort) {
        vector<int> s;
        for (const auto &lit : *c)
          s.push_back (lit);
        sort (s.begin (), s.end (), clause_lit_less_than ());
        for (const auto &lit : s)
          fprintf ( Abc_FrameGlobalGetOut(), " %d", lit);
      } else {
        for (const auto &lit : *c) {
          fprintf ( Abc_FrameGlobalGetOut(), " %s", loglit (internal, lit).c_str ());
        }
      }
    }
  } else if (internal->level)
    fprintf ( Abc_FrameGlobalGetOut(), " decision");
  else
    fprintf ( Abc_FrameGlobalGetOut(), " unit");
  fputc( '\n', Abc_FrameGlobalGetOut() );
  tout.normal ();
  fflush( Abc_FrameGlobalGetOut() );
}

void Logger::log (Internal *internal, const Gate *g, const char *fmt, ...) {
  print_log_prefix (internal);
  tout.magenta ();
  va_list ap;
  va_start (ap, fmt);
  vfprintf ( Abc_FrameGlobalGetOut(), fmt, ap);
  va_end (ap);
  if (g) {
    fprintf ( Abc_FrameGlobalGetOut(), "%s%s gate[%" PRIu64 "] (arity: %zu) %s := %s",
            special_gate_str (g->degenerated_gate).c_str (),
            g->garbage ? " garbage" : "", g->id, g->arity (),
            loglit (internal, g->lhs).c_str (),
            string_of_gate (g->tag).c_str ());
    for (const auto &lit : g->rhs) {
      fprintf ( Abc_FrameGlobalGetOut(), " %s", loglit (internal, lit).c_str ());
    }
  } else
    fprintf ( Abc_FrameGlobalGetOut(), " null gate");
  fputc( '\n', Abc_FrameGlobalGetOut() );
  tout.normal ();
  fflush( Abc_FrameGlobalGetOut() );
}

// Same as above, but for the global clause 'c' (which is not a reason).

void Logger::log (Internal *internal, const vector<int> &c, const char *fmt,
                  ...) {
  print_log_prefix (internal);
  tout.magenta ();
  va_list ap;
  va_start (ap, fmt);
  vfprintf ( Abc_FrameGlobalGetOut(), fmt, ap);
  va_end (ap);
  if (internal->opts.logsort) {
    vector<int> s;
    for (const auto &lit : c)
      s.push_back (lit);
    sort (s.begin (), s.end (), clause_lit_less_than ());
    for (const auto &lit : s)
      fprintf ( Abc_FrameGlobalGetOut(), " %d", lit);
  } else {
    for (const auto &lit : c)
      fprintf ( Abc_FrameGlobalGetOut(), " %d", lit);
  }
  fputc( '\n', Abc_FrameGlobalGetOut() );
  tout.normal ();
  fflush( Abc_FrameGlobalGetOut() );
}

// Now for 'restore_clause' to avoid copying (without logging).

void Logger::log (Internal *internal,
                  const vector<int>::const_iterator &begin,
                  const vector<int>::const_iterator &end, const char *fmt,
                  ...) {
  print_log_prefix (internal);
  tout.magenta ();
  va_list ap;
  va_start (ap, fmt);
  vfprintf ( Abc_FrameGlobalGetOut(), fmt, ap);
  va_end (ap);
  if (internal->opts.logsort) {
    vector<int> s;
    for (auto p = begin; p != end; p++)
      s.push_back (*p);
    sort (s.begin (), s.end (), clause_lit_less_than ());
    for (const auto &lit : s)
      fprintf ( Abc_FrameGlobalGetOut(), " %d", lit);
  } else {
    for (auto p = begin; p != end; p++)
      fprintf ( Abc_FrameGlobalGetOut(), " %d", *p);
  }
  fputc( '\n', Abc_FrameGlobalGetOut() );
  tout.normal ();
  fflush( Abc_FrameGlobalGetOut() );
}

// for LRAT proof chains

void Logger::log (Internal *internal, const vector<int64_t> &c,
                  const char *fmt, ...) {
  print_log_prefix (internal);
  tout.magenta ();
  va_list ap;
  va_start (ap, fmt);
  vfprintf ( Abc_FrameGlobalGetOut(), fmt, ap);
  va_end (ap);
  for (const auto &id : c)
    fprintf ( Abc_FrameGlobalGetOut(), " %" PRId64, id);
  fputc( '\n', Abc_FrameGlobalGetOut() );
  tout.normal ();
  fflush( Abc_FrameGlobalGetOut() );
}

// for LRAT proof clauses

void Logger::log (Internal *internal, const int *literals,
                  const unsigned size, const char *fmt, ...) {
  print_log_prefix (internal);
  tout.magenta ();
  va_list ap;
  va_start (ap, fmt);
  vfprintf ( Abc_FrameGlobalGetOut(), fmt, ap);
  va_end (ap);
  for (unsigned i = 0; i < size; i++) {
    const int lit = literals[i];
    fprintf ( Abc_FrameGlobalGetOut(), " %d", lit);
  }
  fputc( '\n', Abc_FrameGlobalGetOut() );
  tout.normal ();
  fflush( Abc_FrameGlobalGetOut() );
}

string Logger::loglit (Internal *internal, int lit) {
  std::string v = std::to_string (lit);
  if (lit && -internal->max_var <= lit && internal->max_var >= lit) {
    const int va = internal->val (lit);
    if (va) {
      v = v + "@" + std::to_string (internal->var (lit).level);
      if (!internal->var (lit).reason)
        v = v + "+";
    }
    if (va > 0)
      v += "=1";
    else if (va < 0)
      v += "=-1";
  }
  return v;
}
} // namespace CaDiCaL

ABC_NAMESPACE_IMPL_END

#endif
