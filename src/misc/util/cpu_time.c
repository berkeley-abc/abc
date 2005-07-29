/**CFile***********************************************************************

  FileName    [ cpu_time.c ]

  PackageName [ util ]

  Synopsis    [ System time calls ]

  Description [ The problem is that all unix systems have a different notion
        of how fast time goes (i.e., the units returned by).  This
        returns a consistent result. ]

  Author      [ Stephen Edwards <sedwards@eecs.berkeley.edu> and others ]

  Copyright   [Copyright (c) 1994-1996 The Regents of the Univ. of California.
  All rights reserved.

  Permission is hereby granted, without written agreement and without license
  or royalty fees, to use, copy, modify, and distribute this software and its
  documentation for any purpose, provided that the above copyright notice and
  the following two paragraphs appear in all copies of this software.

  IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY FOR
  DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT
  OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF
  CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

  THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES,
  INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR A PARTICULAR PURPOSE.  THE SOFTWARE PROVIDED HEREUNDER IS ON AN
  "AS IS" BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO PROVIDE
  MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.]

******************************************************************************/

#include "util.h"

#if HAVE_SYS_TYPES_H
#  include<sys/types.h>
#endif

#if HAVE_SYS_TIMES_H
#  include<sys/times.h>
#endif

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

/**AutomaticEnd***************************************************************/

/**Function********************************************************************

  Synopsis           [ Return elapsed time in milliseconds ]

  Description        [ Return a long which represents the elapsed time in
               milliseconds since some constant reference. <P>

               There are two possibilities:
               <OL>
               <LI> The system is non-POSIX compliant, so unistd.h
                    and hence sysconf() can't tell us the clock tick
                speed.  At this point, we have to resort to
                using the user-settable CLOCK_RESOLUTION definition
                to get the right speed
               <LI> The system is POSIX-compliant.  unistd.h gives
                    us sysconf(), which tells us the clock rate.
               </OL>
 ]

  SideEffects        [ none ]

******************************************************************************/

/*
long 
util_cpu_time()
{
    long t = 0;

#if HAVE_SYSCONF == 1

    // Code for POSIX systems 

    struct tms buffer;
    long nticks;                // number of clock ticks per second 

    nticks = sysconf(_SC_CLK_TCK);
    times(&buffer);
    t = buffer.tms_utime * (1000.0/nticks);

#else
#  ifndef vms

    // Code for non-POSIX systems 

    struct tms buffer;

    time(&buffer);
    t = buffer.tms_utime * 1000.0 / CLOCK_RESOLUTION;

#  else

    // Code for VMS (?) 

    struct {int p1, p2, p3, p4;} buffer;
    static long ref_time;
    times(&buffer);
    t = buffer.p1 * 10;
    if (ref_time == 0)
      ref_time = t;
    t = t - ref_time;

#  endif // vms 
#endif // _POSIX_VERSION 

    return t;
}
*/


long 
util_cpu_time()
{
    return clock();
}
