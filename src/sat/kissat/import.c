#include "internal.h"
#include "logging.h"
#include "resize.h"

static void adjust_imports_for_external_literal (kissat *solver,
                                                 unsigned eidx) {
  while (eidx >= SIZE_STACK (solver->import)) {
    struct import import;
    import.lit = 0;
    import.extension = false;
    import.imported = false;
    import.eliminated = false;
    PUSH_STACK (solver->import, import);
  }
}

static void adjust_exports_for_external_literal (kissat *solver,
                                                 unsigned eidx,
                                                 bool extension) {
  struct import *import = &PEEK_STACK (solver->import, eidx);
  unsigned iidx = solver->vars;
  kissat_enlarge_variables (solver, iidx + 1);
  unsigned ilit = 2 * iidx;
  import->extension = extension;
  import->imported = true;
  if (extension)
    INC (variables_extension);
  else
    INC (variables_original);
  assert (!import->eliminated);
  import->lit = ilit;
  LOG ("importing %s external variable %u as internal literal %u",
       extension ? "extension" : "original", eidx, ilit);
  while (iidx >= SIZE_STACK (solver->export))
    PUSH_STACK (solver->export, 0);
  POKE_STACK (solver->export, iidx, (int) eidx);
  LOG ("exporting internal variable %u as external literal %u", iidx, eidx);
}

static inline unsigned import_literal (kissat *solver, int elit,
                                       bool extension) {
  const unsigned eidx = ABS (elit);
  adjust_imports_for_external_literal (solver, eidx);
  struct import *import = &PEEK_STACK (solver->import, eidx);
  if (import->eliminated)
    return INVALID_LIT;
  unsigned ilit;
  if (!import->imported)
    adjust_exports_for_external_literal (solver, eidx, extension);
  assert (import->imported);
  ilit = import->lit;
  if (elit < 0)
    ilit = NOT (ilit);
  assert (VALID_INTERNAL_LITERAL (ilit));
  return ilit;
}

unsigned kissat_import_literal (kissat *solver, int elit) {
  assert (VALID_EXTERNAL_LITERAL (elit));
  if (GET_OPTION (tumble))
    return import_literal (solver, elit, false);
  const unsigned eidx = ABS (elit);
  assert (SIZE_STACK (solver->import) <= UINT_MAX);
  unsigned other = SIZE_STACK (solver->import);
  if (eidx < other)
    return import_literal (solver, elit, false);
  if (!other)
    adjust_imports_for_external_literal (solver, other++);

  unsigned ilit = 0;
  do {
    assert (VALID_EXTERNAL_LITERAL ((int) other));
    ilit = import_literal (solver, other, false);
  } while (other++ < eidx);

  if (elit < 0)
    ilit = NOT (ilit);

  return ilit;
}

unsigned kissat_fresh_literal (kissat *solver) {
  size_t imported = SIZE_STACK (solver->import);
  assert (imported <= EXTERNAL_MAX_VAR);
  if (imported == EXTERNAL_MAX_VAR) {
    LOG ("can not get another external variable");
    return INVALID_LIT;
  }
  assert (imported <= (unsigned) INT_MAX);
  int eidx = (int) imported;
  unsigned res = import_literal (solver, eidx, true);
#ifndef NDEBUG
  struct import *import = &PEEK_STACK (solver->import, imported);
  assert (import->imported);
  assert (import->extension);
#endif
  INC (fresh);
  kissat_activate_literal (solver, res);
  return res;
}
