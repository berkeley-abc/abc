/**CFilextern e****************************************************************

  FileName    [nm.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Name manager.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: nm.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __NM_H__
#define __NM_H__

#ifdef __cplusplus
extern "C" {
#endif

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Nm_Man_t_ Nm_Man_t;

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== nmApi.c ==========================================================*/
extern Nm_Man_t *   Nm_ManCreate( int nSize );
extern void         Nm_ManFree( Nm_Man_t * p );
extern int          Nm_ManNumEntries( Nm_Man_t * p );
extern char *       Nm_ManStoreIdName( Nm_Man_t * p, int ObjId, char * pName, char * pSuffix );
extern char *       Nm_ManCreateUniqueName( Nm_Man_t * p, int ObjId );
extern char *       Nm_ManFindNameById( Nm_Man_t * p, int ObjId );
extern int          Nm_ManFindIdByName( Nm_Man_t * p, char * pName, int * pSecond );
extern void         Nm_ManPrintTables( Nm_Man_t * p );

#ifdef __cplusplus
}
#endif

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

