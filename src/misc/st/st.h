/*
 * Revision Control Information
 *
 * /projects/hsis/CVS/utilities/st/st.h,v
 * serdar
 * 1.1
 * 1993/07/29 01:00:21
 *
 */
/* LINTLIBRARY */

/* /projects/hsis/CVS/utilities/st/st.h,v 1.1 1993/07/29 01:00:21 serdar Exp */

#ifndef ABC__misc__st__st_h
#define ABC__misc__st__st_h
#define ST_INCLUDED

#include "misc/util/abc_global.h"

ABC_NAMESPACE_HEADER_START


/* These are potential duplicates. */
#ifndef EXTERN
#   ifdef __cplusplus
#       ifdef ABC_NAMESPACE
#           define EXTERN extern
#       else
#           define EXTERN extern "C"
#       endif
#   else
#       define EXTERN extern
#   endif
#endif

#ifndef ARGS
#define ARGS(protos) protos
#endif


typedef int (*st_compare_func_type)(const char*, const char*);
typedef int (*st_hash_func_type)(const char*, int);

typedef struct st_table_entry st_table_entry;
struct st_table_entry {
    char *key;
    char *record;
    st_table_entry *next;
};

typedef struct st_table st_table;
struct st_table {
    st_compare_func_type compare;
    st_hash_func_type hash;
    int num_bins;
    int num_entries;
    int max_density;
    int reorder_flag;
    double grow_factor;
    st_table_entry **bins;
};

typedef struct st_generator st_generator;
struct st_generator {
    st_table *table;
    st_table_entry *entry;
    int index;
};

#define st_is_member(table,key) st_lookup(table,key,(char **) 0)
#define st_count(table) ((table)->num_entries)

enum st_retval {ST_CONTINUE, ST_STOP, ST_DELETE};

typedef enum st_retval (*ST_PFSR)(char *, char *, char *);
typedef int (*ST_PFI)();

extern st_table *st_init_table_with_params (st_compare_func_type compare, st_hash_func_type hash, int size, int density, double grow_factor, int reorder_flag);
extern st_table *st_init_table (st_compare_func_type, st_hash_func_type);
extern void st_free_table (st_table *);
extern int st_lookup (st_table *, const char *, char **);
extern int st_lookup_int (st_table *, char *, int *);
extern int st_insert (st_table *, const char *, char *);
extern int st_add_direct (st_table *, char *, char *);
extern int st_find_or_add (st_table *, char *, char ***);
extern int st_find (st_table *, char *, char ***);
extern st_table *st_copy (st_table *);
extern int st_delete (st_table *, const char **, char **);
extern int st_delete_int (st_table *, long *, char **);
extern int st_foreach (st_table *, ST_PFSR, char *);
extern int st_strhash (const char *, int);
extern int st_numhash (const char *, int);
extern int st_ptrhash (const char *, int);
extern int st_numcmp (const char *, const char *);
extern int st_ptrcmp (const char *, const char *);
extern st_generator *st_init_gen (st_table *);
extern int st_gen (st_generator *, const char **, char **);
extern int st_gen_int (st_generator *, const char **, long *);
extern void st_free_gen (st_generator *);


#define ST_DEFAULT_MAX_DENSITY 5
#define ST_DEFAULT_INIT_TABLE_SIZE 11
#define ST_DEFAULT_GROW_FACTOR 2.0
#define ST_DEFAULT_REORDER_FLAG 0

#define st_foreach_item(table, gen, key, value) \
    for(gen=st_init_gen(table); st_gen(gen,key,value) || (st_free_gen(gen),0);)

#define st_foreach_item_int(table, gen, key, value) \
    for(gen=st_init_gen(table); st_gen_int(gen,key,value) || (st_free_gen(gen),0);)

#define ST_OUT_OF_MEM -10000



ABC_NAMESPACE_HEADER_END



#endif /* ST_INCLUDED */
