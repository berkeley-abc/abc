#include "internal.hpp"

namespace CaDiCaL {

Terminal::Terminal (FILE *f) : file (f), reset_on_exit (false) {
  assert (file);
  int fd = fileno (f);
  assert (fd == 1 || fd == 2);
  use_colors = connected = isatty (fd);
}

void Terminal::force_colors () { use_colors = connected = true; }
void Terminal::force_no_colors () { use_colors = false; }
void Terminal::force_reset_on_exit () { reset_on_exit = true; }

void Terminal::reset () {
  if (!connected)
    return;
  erase_until_end_of_line ();
  cursor (true);
  normal ();
  fflush (file);
}

void Terminal::disable () {
  reset ();
  connected = use_colors = false;
}

Terminal::~Terminal () {
  if (reset_on_exit)
    reset ();
}

Terminal tout (stdout);
Terminal terr (stderr);

} // namespace CaDiCaL
