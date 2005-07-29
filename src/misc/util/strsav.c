/*
 * Revision Control Information
 *
 * /projects/hsis/CVS/utilities/util/strsav.c,v
 * shiple
 * 1.4
 * 1995/08/30 17:37:58
 *
 */
/* LINTLIBRARY */

#include <stdio.h>
#include "util.h"


/*
 *  util_strsav -- save a copy of a string
 */
char *
util_strsav(s)
char *s;
{
    if(s == NIL(char)) {  /* added 7/95, for robustness */
       return s;
    }
    else {
       return strcpy(ALLOC(char, strlen(s)+1), s);
    }
}

/*
 * util_inttostr -- converts an integer into a string
 */
char *
util_inttostr(i)
  int i;
{
  unsigned int mod, len;
  char *s;
  
  if (i == 0)
    len = 1;
  else {
    if (i < 0) {
      len = 1;
      mod = -i;
    }
    else {
      len = 0;
      mod = i;
    }
    len += (unsigned)floor(log10(mod)) + 1;
  }

  s = ALLOC(char, len + 1);
  sprintf(s, "%d", i);
  
  return s;
}

/*
 * util_strcat3 -- Creates a new string which is the concatenation of 3
 *    strings. It is the responsibility of the caller to free this string
 *    using FREE.
 */
char *
util_strcat3(
  char * str1,
  char * str2,
  char * str3)
{
  char *str = ALLOC(char, strlen(str1) + strlen(str2) + strlen(str3) + 1);
  
  (void) strcpy(str, str1);
  (void) strcat(str, str2);
  (void) strcat(str, str3);

  return (str);
}

/*
 * util_strcat4 -- Creates a new string which is the concatenation of 4
 *    strings. It is the responsibility of the caller to free this string
 *    using FREE.
 */
char *
util_strcat4(
  char * str1,
  char * str2,
  char * str3,
  char * str4)
{
  char *str = ALLOC(char, strlen(str1) + strlen(str2) + strlen(str3) +
                    strlen(str4) + 1);
  
  (void) strcpy(str, str1);
  (void) strcat(str, str2);
  (void) strcat(str, str3);
  (void) strcat(str, str4);

  return (str);
}


#if !HAVE_STRSTR
/**Function********************************************************************

  Synopsis    [required]

  Description [optional]

  SideEffects [required]

  SeeAlso     [optional]

******************************************************************************/
char *
strstr(
  const char * s,
  const char * pat)
{
  int len;

  len = strlen(pat);
  for (; *s != '\0'; ++s)
    if (*s == *pat && memcmp(s, pat, len) ==  0) {
      return (char *)s; /* UGH */
    }
  return NULL;
}
#endif /* !HAVE_STRSTR */

#if !HAVE_STRCHR
/**Function********************************************************************

  Synopsis    [required]

  Description [optional]

  SideEffects [required]

  SeeAlso     [optional]

******************************************************************************/
char *
strchr(const char * s,
       int c)
{
   for (; *s != '\0'; s++) {
     if (*s == c) {
       return (char *)s;
     }
   }
   return NULL;
   
}
#endif /* !HAVE_STRCHR */
