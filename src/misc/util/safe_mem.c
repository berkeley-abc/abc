/*
 * Revision Control Information
 *
 * /projects/hsis/CVS/utilities/util/safe_mem.c,v
 * rajeev
 * 1.3
 * 1995/08/08 22:41:29
 *
 */
/* LINTLIBRARY */

#include "util.h"

/*
 *  These are interface routines to be placed between a program and the
 *  system memory allocator.  
 *
 *  It forces well-defined semantics for several 'borderline' cases:
 *
 *    malloc() of a 0 size object is guaranteed to return something
 *        which is not 0, and can safely be freed (but not dereferenced)
 *    free() accepts (silently) an 0 pointer
 *    realloc of a 0 pointer is allowed, and is equiv. to malloc()
 *    For the IBM/PC it forces no object > 64K; note that the size argument
 *        to malloc/realloc is a 'long' to catch this condition
 *
 *  The function pointer MMoutOfMemory() contains a vector to handle a
 *  'out-of-memory' error (which, by default, points at a simple wrap-up 
 *  and exit routine).
 */

extern char *MMalloc();
extern void MMout_of_memory();
extern char *MMrealloc();


void (*MMoutOfMemory)() = MMout_of_memory;


/* MMout_of_memory -- out of memory for lazy people, flush and exit */
void 
MMout_of_memory(size)
long size;
{
    (void) fflush(stdout);
    (void) fprintf(stderr, "\nout of memory allocating %u bytes\n",
           (unsigned) size);
    assert( 0 );
    exit(1);
}


char *
MMalloc(size)
long size;
{
    char *p;

#ifdef IBMPC
    if (size > 65000L) {
    if (MMoutOfMemory != (void (*)()) 0 ) (*MMoutOfMemory)(size);
    return NIL(char);
    }
#endif
    if (size == 0) size = sizeof(long);
    if ((p = (char *) malloc((unsigned) size)) == NIL(char)) {
    if (MMoutOfMemory != (void (*)()) 0 ) (*MMoutOfMemory)(size);
    return NIL(char);
    }
    return p;
}


char *
MMrealloc(obj, size)
char *obj;
long size;
{
    char *p;

#ifdef IBMPC
    if (size > 65000L) {
    if (MMoutOfMemory != (void (*)()) 0 ) (*MMoutOfMemory)(size);
    return NIL(char);
    }
#endif
    if (obj == NIL(char)) return MMalloc(size);
    if (size <= 0) size = sizeof(long);
    if ((p = (char *) realloc(obj, (unsigned) size)) == NIL(char)) {
    if (MMoutOfMemory != (void (*)()) 0 ) (*MMoutOfMemory)(size);
    return NIL(char);
    }
    return p;
}


void
MMfree(obj)
char *obj;
{
    if (obj != 0) {
    free(obj);
    }
}
