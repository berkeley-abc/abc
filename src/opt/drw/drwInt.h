/**CFile****************************************************************

  FileName    [drwInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Compact DAG-aware AIG rewriting.]

  Synopsis    [Internal declarations and immutable rewriting library.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: drwInt.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__opt__drw__drwInt_h
#define ABC__opt__drw__drwInt_h

#include "drw.h"

ABC_NAMESPACE_HEADER_START

typedef struct Drw_LibClass_t_ Drw_LibClass_t;
struct Drw_LibClass_t_
{
    int iNodes;
    int nNodes;
    int iRoots;
    int nRoots;
    int MinSize;
    int iPairs;
    int nPairs;
};

extern const unsigned Drw_Transforms[65536];
extern const unsigned char Drw_MinSizes[65536];
extern const int Drw_LibMaxSize;
extern const Drw_LibClass_t Drw_Classes[222];
extern const unsigned short Drw_LibNodes[][2];
extern const unsigned short Drw_LibRoots[];
extern const unsigned char Drw_LibSizes[];
extern const signed char Drw_LibDepths[][4];
extern const unsigned char Drw_LibPairs[];

ABC_NAMESPACE_HEADER_END

#endif
