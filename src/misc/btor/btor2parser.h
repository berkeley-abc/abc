/**
 *  Btor2Tools: A tool package for the BTOR2 format.
 *
 *  Copyright (c) 2012-2018 Armin Biere.
 *  Copyright (c) 2017 Mathias Preiner
 *  Copyright (c) 2017 Aina Niemetz
 *
 *  All rights reserved.
 *
 *  This file is part of the Btor2Tools package.
 *  See LICENSE.txt for more information on using this software.
 */

#ifndef btor2parser_h_INCLUDED
#define btor2parser_h_INCLUDED

/*------------------------------------------------------------------------*/
/* The BTOR2 format is described in                                       */
/* "BTOR2, BtorMC and Boolector 3.0" by A. Niemetz, M. Preiner, C. Wolf   */
/* and A. Biere at CAV 2018.                                              */
/*------------------------------------------------------------------------*/

#include <stdint.h>
#include <stdio.h>

#include "misc/util/abc_global.h"

ABC_NAMESPACE_HEADER_START

/*------------------------------------------------------------------------*/

#define BTOR2_FORMAT_MAXID (((int64_t) 1) << 40)
#define BTOR2_FORMAT_MAXBITWIDTH ((1l << 30) + ((1l << 30) - 1))

/*------------------------------------------------------------------------*/

typedef struct Btor2Parser Btor2Parser;
typedef struct Btor2Line Btor2Line;
typedef struct Btor2Sort Btor2Sort;
typedef struct Btor2LineIterator Btor2LineIterator;

/*------------------------------------------------------------------------*/

/**
 * BTOR2 tags can be used for fast(er) traversal and operations on BTOR2
 * format lines, e.g., in a switch statement in client code.
 * Alternatively, client code can use the name of the BTOR2 tag, which is a C
 * string (redundantly) contained in the format line. Note that this requires
 * string comparisons and is therefore slower even if client code uses an
 * additional hash table.
 */
enum Btor2Tag
{
  BTOR2_TAG_add,
  BTOR2_TAG_and,
  BTOR2_TAG_bad,
  BTOR2_TAG_concat,
  BTOR2_TAG_const,
  BTOR2_TAG_constraint,
  BTOR2_TAG_constd,
  BTOR2_TAG_consth,
  BTOR2_TAG_dec,
  BTOR2_TAG_eq,
  BTOR2_TAG_fair,
  BTOR2_TAG_iff,
  BTOR2_TAG_implies,
  BTOR2_TAG_inc,
  BTOR2_TAG_init,
  BTOR2_TAG_input,
  BTOR2_TAG_ite,
  BTOR2_TAG_justice,
  BTOR2_TAG_mul,
  BTOR2_TAG_nand,
  BTOR2_TAG_neq,
  BTOR2_TAG_neg,
  BTOR2_TAG_next,
  BTOR2_TAG_nor,
  BTOR2_TAG_not,
  BTOR2_TAG_one,
  BTOR2_TAG_ones,
  BTOR2_TAG_or,
  BTOR2_TAG_output,
  BTOR2_TAG_read,
  BTOR2_TAG_redand,
  BTOR2_TAG_redor,
  BTOR2_TAG_redxor,
  BTOR2_TAG_rol,
  BTOR2_TAG_ror,
  BTOR2_TAG_saddo,
  BTOR2_TAG_sdiv,
  BTOR2_TAG_sdivo,
  BTOR2_TAG_sext,
  BTOR2_TAG_sgt,
  BTOR2_TAG_sgte,
  BTOR2_TAG_slice,
  BTOR2_TAG_sll,
  BTOR2_TAG_slt,
  BTOR2_TAG_slte,
  BTOR2_TAG_sort,
  BTOR2_TAG_smod,
  BTOR2_TAG_smulo,
  BTOR2_TAG_sra,
  BTOR2_TAG_srem,
  BTOR2_TAG_srl,
  BTOR2_TAG_ssubo,
  BTOR2_TAG_state,
  BTOR2_TAG_sub,
  BTOR2_TAG_uaddo,
  BTOR2_TAG_udiv,
  BTOR2_TAG_uext,
  BTOR2_TAG_ugt,
  BTOR2_TAG_ugte,
  BTOR2_TAG_ult,
  BTOR2_TAG_ulte,
  BTOR2_TAG_umulo,
  BTOR2_TAG_urem,
  BTOR2_TAG_usubo,
  BTOR2_TAG_write,
  BTOR2_TAG_xnor,
  BTOR2_TAG_xor,
  BTOR2_TAG_zero,
};
typedef enum Btor2Tag Btor2Tag;

enum Btor2SortTag
{
  BTOR2_TAG_SORT_array,
  BTOR2_TAG_SORT_bitvec,
};
typedef enum Btor2SortTag Btor2SortTag;

/*------------------------------------------------------------------------*/

struct Btor2Sort
{
  int64_t id;
  Btor2SortTag tag;
  const char *name;
  union
  {
    struct
    {
      int64_t index;
      int64_t element;
    } array;
    struct
    {
      uint32_t width;
    } bitvec;
  };
};

struct Btor2Line
{
  int64_t id;       /* positive id (non zero)                 */
  int64_t lineno;   /* line number in original file           */
  const char *name; /* name in ASCII: "and", "add", ...       */
  Btor2Tag tag;     /* same as name but encoded as integer    */
  Btor2Sort sort;
  int64_t init, next; /* non zero if initialized or has next    */
  char *constant;     /* non zero for const, constd, consth     */
  char *symbol;       /* optional for: var array state input    */
  uint32_t nargs;     /* number of arguments                    */
  int64_t *args;      /* non zero ids up to nargs               */
};

struct Btor2LineIterator
{
  Btor2Parser *reader;
  int64_t next;
};

/*------------------------------------------------------------------------*/
/* Constructor, setting options and destructor:
 */
Btor2Parser *btor2parser_new ();
void btor2parser_delete (Btor2Parser *);

/*------------------------------------------------------------------------*/
/* The 'btor2parser_read_lines' function returns zero on failure.  In this
 * case you can call 'btor2parser_error' to obtain a description of
 * the actual read or parse error, which includes the line number where
 * the error occurred.
 */
int32_t btor2parser_read_lines (Btor2Parser *, FILE *);
const char *btor2parser_error (Btor2Parser *);

/*------------------------------------------------------------------------*/
/* Iterate over all read format lines:
 *
 *   Btor2LineIterator it = btor2parser_iter_init (bfr);
 *   Btor2Line * l;
 *   while ((l = btor2parser_iter_next (&it)))
 *     do_something_with_btor_format_line (l);
 */
Btor2LineIterator btor2parser_iter_init (Btor2Parser *bfr);
Btor2Line *btor2parser_iter_next (Btor2LineIterator *);

/*------------------------------------------------------------------------*/
/* The reader maintains a mapping of ids to format lines.  This mapping
 * can be retrieved with the following function.  Note, however, that
 * ids might be negative and denote the negation of the actual node.
 */
int64_t btor2parser_max_id (Btor2Parser *);
Btor2Line *btor2parser_get_line_by_id (Btor2Parser *, int64_t id);

/*------------------------------------------------------------------------*/

ABC_NAMESPACE_HEADER_END

#endif
