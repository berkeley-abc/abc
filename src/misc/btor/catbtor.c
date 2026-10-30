/**
 *  Btor2Tools: A tool package for the BTOR format.
 *
 *  Copyright (c) 2012-2015 Armin Biere.
 *  Copyright (c) 2017 Mathias Preiner.
 *  Copyright (c) 2017-2018 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of the Btor2Tools package.
 *  See LICENSE.txt for more information on using this software.
 */

#include "btor2parser.h"

#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

ABC_NAMESPACE_IMPL_START

/* Parse BTOR2 file and print to stdout. */

int32_t
Abc_BtorCat (char* input_name, int verbosity)
{
  FILE* input_file;

  Btor2Parser* reader;
  Btor2LineIterator it;
  Btor2Line* l;
  uint32_t j;
  const char* err;
  
  input_file = fopen (input_name, "r");
  if (!input_file)
  {
    fprintf( Abc_FrameGlobalGetErr(), "*** catbtor: can not open '%s' for reading\n", input_name);
    return 1;
  }

  if (verbosity)
  {
    fprintf( Abc_FrameGlobalGetErr(), "; [catbor] simple CAT for BTOR files\n"
             "; [catbor] reading '%s'\n",
             input_name);
    fflush( Abc_FrameGlobalGetErr() );
  }
  reader = btor2parser_new ();
  if (!btor2parser_read_lines (reader, input_file))
  {
    err = btor2parser_error (reader);
    assert (err);
    fprintf( Abc_FrameGlobalGetErr(), "*** catbtor: parse error in '%s' %s\n", input_name, err);
    btor2parser_delete (reader);
    fclose (input_file);
    return 1;
  }
  fclose (input_file);
  if (verbosity)
  {
    fprintf( Abc_FrameGlobalGetErr(), "; [catbor] finished parsing '%s'\n", input_name);
    fflush( Abc_FrameGlobalGetErr() );
  }
  if (verbosity)
  {
    fprintf( Abc_FrameGlobalGetErr(), "; [catbor] starting to dump BTOR model to '<stdout>'\n");
    fflush( Abc_FrameGlobalGetErr() );
  }
  it = btor2parser_iter_init (reader);
  while ((l = btor2parser_iter_next (&it)))
  {
    fprintf ( Abc_FrameGlobalGetOut(), "%" PRId64 " %s", l->id, l->name);
    if (l->tag == BTOR2_TAG_sort)
    {
      fprintf ( Abc_FrameGlobalGetOut(), " %s", l->sort.name);
      switch (l->sort.tag)
      {
        case BTOR2_TAG_SORT_bitvec: fprintf ( Abc_FrameGlobalGetOut(), " %u", l->sort.bitvec.width); break;
        case BTOR2_TAG_SORT_array:
          fprintf ( Abc_FrameGlobalGetOut(), " %" PRId64 " %" PRId64, l->sort.array.index, l->sort.array.element);
          break;
        default:
          fprintf( Abc_FrameGlobalGetErr(), "*** catbtor: invalid sort encountered\n");
          btor2parser_delete (reader);
          return 1;
      }
    }
    else if (l->sort.id)
      fprintf ( Abc_FrameGlobalGetOut(), " %" PRId64, l->sort.id);
    for (j = 0; j < l->nargs; j++) fprintf ( Abc_FrameGlobalGetOut(), " %" PRId64, l->args[j]);
    if (l->tag == BTOR2_TAG_slice) fprintf ( Abc_FrameGlobalGetOut(), " %" PRId64 " %" PRId64, l->args[1], l->args[2]);
    if (l->tag == BTOR2_TAG_sext || l->tag == BTOR2_TAG_uext)
      fprintf ( Abc_FrameGlobalGetOut(), " %" PRId64, l->args[1]);
    if (l->constant) fprintf ( Abc_FrameGlobalGetOut(), " %s", l->constant);
    if (l->symbol) fprintf ( Abc_FrameGlobalGetOut(), " %s", l->symbol);
    fputc( '\n', Abc_FrameGlobalGetOut() );
  }
  btor2parser_delete (reader);
  if (verbosity)
  {
    fprintf( Abc_FrameGlobalGetErr(), "; [catbor] finished dumping BTOR model to '<stdout>'\n");
    fflush( Abc_FrameGlobalGetErr() );
  }
  return 0;
}

ABC_NAMESPACE_IMPL_END
