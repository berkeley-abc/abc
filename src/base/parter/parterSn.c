/**CFile****************************************************************

  FileName    [parterSn.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Acyclic word-level partitioning.]

  Synopsis    [Static SN hypergraphs with complete state/control grouping.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: parterSn.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#include "parterSn.h"
#include <math.h>
#include <stdarg.h>

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Reports an adapter error without modifying the input.]

***********************************************************************/
static int Prt_SnError( char * pError, unsigned nError, const char * pFormat, ... )
{
    va_list Args;
    va_start(Args,pFormat);
    if ( pError && nError ) vsnprintf(pError,nError,pFormat,Args);
    va_end(Args);
    return 0;
}

/**Function*************************************************************

  Synopsis    [Allocates a checked array, including an empty-array sentinel.]

***********************************************************************/
static void * Prt_SnAlloc( size_t Count, size_t Size )
{
    if ( Count > SIZE_MAX / Size ) return NULL;
    return calloc(Count ? Count : 1,Size);
}

/**Function*************************************************************

  Synopsis    [Recognizes constants which can be copied to every part.]

***********************************************************************/
static int Prt_SnConstant( unsigned Type )
{
    return Type == SN_CONST0 || Type == SN_CONST1 || Type == SN_CONST;
}

/**Function*************************************************************

  Synopsis    [Recognizes the objects that belong to partition vertices.]

***********************************************************************/
static int Prt_SnMovable( unsigned Type )
{
    return Type != SN_PI && Type != SN_PO && !Prt_SnConstant(Type);
}

/**Function*************************************************************

  Synopsis    [Finds a mandatory-group root with path compression.]

***********************************************************************/
static unsigned Prt_SnFind( unsigned * pParent, unsigned Object )
{
    unsigned Root = Object, Next;
    while ( Root != pParent[Root] ) Root = pParent[Root];
    while ( Object != Root )
    {
        Next = pParent[Object]; pParent[Object] = Root; Object = Next;
    }
    return Root;
}

/**Function*************************************************************

  Synopsis    [Joins mandatory groups with a deterministic minimum-ID root.]

***********************************************************************/
static void Prt_SnUnion( unsigned * pParent, unsigned A, unsigned B )
{
    A = Prt_SnFind(pParent,A); B = Prt_SnFind(pParent,B);
    if ( A < B ) pParent[B] = A;
    else pParent[A] = B;
}

/**Function*************************************************************

  Synopsis    [Checks array spans before reading object attributes and fanins.]

***********************************************************************/
static int Prt_SnCore( const sn_module_t * p, char * pError, unsigned nError )
{
    size_t i, j, n = p->obj_types.size;
    if ( n >= PRT_NONE || p->width_signed.size != n || p->fanin_counts.size != n ||
         p->fanin_offsets.size != n || p->obj_data.size != n ||
         (n && (!p->obj_types.data || !p->width_signed.data || !p->fanin_counts.data ||
                !p->fanin_offsets.data || !p->obj_data.data)) || (p->fanins.size && !p->fanins.data) )
        return Prt_SnError(pError,nError,"invalid SN object arrays");
    for ( i = 0; i < n; ++i )
    {
        unsigned Type = sn_obj_type(p,(unsigned)i);
        unsigned Count = sn_obj_fanin_count(p,(unsigned)i);
        unsigned Offset = sn_vec_at(uint32_t,&p->fanin_offsets,i);
        if ( Type <= SN_NONE || Type >= SN_OBJ_TYPE_COUNT || Offset > p->fanins.size ||
             Count > p->fanins.size-Offset )
            return Prt_SnError(pError,nError,"invalid SN object %u fanin span",(unsigned)i);
        for ( j = 0; j < Count; ++j )
        {
            unsigned Fanin = sn_obj_fanin(p,(unsigned)i,(unsigned)j);
            if ( Fanin != SN_INVALID_ID && Fanin >= n )
                return Prt_SnError(pError,nError,"invalid SN object %u fanin %u",(unsigned)i,Fanin);
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Contracts owners, pairs, and all ports of each memory first.]

***********************************************************************/
static int Prt_SnGroups( const sn_module_t * p, unsigned * pParent, char * pError, unsigned nError )
{
    unsigned i, k, Fanin, Type, OtherType, n = (unsigned)p->obj_types.size;
    for ( i = 0; i < n; ++i ) pParent[i] = i;
    for ( i = 0; i < n; ++i )
    {
        Type = sn_obj_type(p,i);
        if ( Type == SN_FAN || Type == SN_REG_OUT || Type == SN_MEM_OUT || Type == SN_LOOP_OUT ||
             Type == SN_MEM_READ )
        {
            if ( !sn_obj_fanin_count(p,i) )
                return Prt_SnError(pError,nError,"missing owner/pair for object %u",i);
            Fanin = sn_obj_fanin(p,i,0);
            if ( Fanin == SN_INVALID_ID )
                return Prt_SnError(pError,nError,"missing owner/pair for object %u",i);
            OtherType = sn_obj_type(p,Fanin);
            if ( (Type == SN_FAN && OtherType != SN_INST && OtherType != SN_GATE) ||
                 (Type == SN_REG_OUT && OtherType != SN_REG_IN) ||
                 (Type == SN_MEM_OUT && OtherType != SN_MEM_IN) ||
                 (Type == SN_LOOP_OUT && OtherType != SN_LOOP_IN) ||
                 (Type == SN_MEM_READ && OtherType != SN_MEM_OUT) )
                return Prt_SnError(pError,nError,"invalid owner/pair for object %u",i);
            Prt_SnUnion(pParent,i,Fanin);
        }
        if ( Type != SN_MEM_IN ) continue;
        if ( sn_obj_fanin_count(p,i) < SN_MEM_IN_FIXED_FANIN_COUNT )
            return Prt_SnError(pError,nError,"missing memory initialization slots for object %u",i);
        for ( k = SN_MEM_IN_FIXED_FANIN_COUNT; k < sn_obj_fanin_count(p,i); ++k )
        {
            Fanin = sn_obj_fanin(p,i,k);
            if ( Fanin == SN_INVALID_ID || sn_obj_type(p,Fanin) != SN_MEM_WRITE )
                return Prt_SnError(pError,nError,"invalid memory write for object %u",i);
            Prt_SnUnion(pParent,i,Fanin);
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Releases the independent graph and its SN correspondence.]

***********************************************************************/
void Prt_SnFree( Prt_SnModel_t * p )
{
    if ( !p ) return;
    Prt_GraphFree(p->pGraph);
    free(p->pObjToGroup); free(p->pObjToVertex); free(p->pVertexObject); free(p);
}

/**Function*************************************************************

  Synopsis    [Builds mandatory groups, then SCCs, preserving original nets.]

***********************************************************************/
int Prt_SnBuild( const sn_module_t * pModule, const Sn_AigCostModule_t * pCosts,
    Prt_SnModel_t ** ppModel, char * pError, unsigned nError )
{
    Prt_SnModel_t * p = NULL;
    Prt_Graph_t * pGrouped = NULL;
    unsigned * pParent = NULL, * pRootGroup = NULL, * pDriver = NULL, * pStart = NULL;
    unsigned * pNext = NULL, * pSinks = NULL, * pScc = NULL, * pOrder = NULL;
    double * pWeights = NULL, * pNetWeights = NULL;
    unsigned n, i, k, Root, Group, Fanin, Pins = 0;
    int Ok = 0;
    if ( ppModel ) *ppModel = NULL;
    if ( pError && nError ) pError[0] = 0;
    if ( !ppModel || !pModule || !pCosts ) return Prt_SnError(pError,nError,"missing SN partition input");
    if ( !pCosts->Known ) return Prt_SnError(pError,nError,"unknown local cost: %s",pCosts->UnknownReason);
    if ( !Prt_SnCore(pModule,pError,nError) ) return 0;
    n = (unsigned)pModule->obj_types.size;
    if ( pCosts->nObjects != n || (n && !pCosts->pObjectAreas) )
        return Prt_SnError(pError,nError,"characterization does not match SN object count");
    p = (Prt_SnModel_t *)Prt_SnAlloc(1,sizeof(*p));
    pParent = (unsigned *)Prt_SnAlloc(n,sizeof(unsigned));
    pRootGroup = (unsigned *)Prt_SnAlloc(n,sizeof(unsigned));
    pDriver = (unsigned *)Prt_SnAlloc(n,sizeof(unsigned));
    pStart = (unsigned *)Prt_SnAlloc((size_t)n+1,sizeof(unsigned));
    pNext = (unsigned *)Prt_SnAlloc(n,sizeof(unsigned));
    pWeights = (double *)Prt_SnAlloc(n,sizeof(double));
    pNetWeights = (double *)Prt_SnAlloc(n,sizeof(double));
    if ( !p || !pParent || !pRootGroup || !pDriver || !pStart || !pNext || !pWeights || !pNetWeights ) goto Memory;
    p->nObjects = n; p->MaxGroupObject = p->MaxSccObject = PRT_NONE;
    p->pObjToGroup = (unsigned *)Prt_SnAlloc(n,sizeof(unsigned));
    p->pObjToVertex = (unsigned *)Prt_SnAlloc(n,sizeof(unsigned));
    if ( !p->pObjToGroup || !p->pObjToVertex ) goto Memory;
    if ( !Prt_SnGroups(pModule,pParent,pError,nError) ) goto Cleanup;
    for ( i = 0; i < n; ++i ) pRootGroup[i] = PRT_NONE;
    for ( i = 0; i < n; ++i )
    {
        p->pObjToGroup[i] = p->pObjToVertex[i] = pDriver[i] = PRT_NONE;
        if ( !isfinite(pCosts->pObjectAreas[i]) || pCosts->pObjectAreas[i] < 0 )
        { Prt_SnError(pError,nError,"invalid cost for object %u",i); goto Cleanup; }
        if ( !Prt_SnMovable(sn_obj_type(pModule,i)) ) continue;
        ++p->nMovable;
        Root = Prt_SnFind(pParent,i);
        if ( pRootGroup[Root] == PRT_NONE ) pRootGroup[Root] = p->nGroups++;
        Group = pRootGroup[Root];
        p->pObjToGroup[i] = pDriver[i] = Group;
        pWeights[Group] += pCosts->pObjectAreas[i];
        if ( !isfinite(pWeights[Group]) ) { Prt_SnError(pError,nError,"group cost overflow"); goto Cleanup; }
    }
    for ( i = 0; i < n; ++i )
    {
        Group = p->pObjToGroup[i];
        if ( Group != PRT_NONE && (p->MaxGroupObject == PRT_NONE || pWeights[Group] > p->MaxGroupWeight) )
        { p->MaxGroupWeight = pWeights[Group]; p->MaxGroupObject = i; }
        if ( !Prt_SnConstant(sn_obj_type(pModule,i)) ) pNetWeights[i] = sn_obj_width(pModule,i);
        if ( Group == PRT_NONE ) continue;
        for ( k = 0; k < sn_obj_fanin_count(pModule,i); ++k )
        {
            Fanin = sn_obj_fanin(pModule,i,k);
            if ( Fanin == SN_INVALID_ID || Prt_SnConstant(sn_obj_type(pModule,Fanin)) || pDriver[Fanin] == Group ) continue;
            if ( Pins == PRT_NONE ) { Prt_SnError(pError,nError,"too many SN partition pins"); goto Cleanup; }
            ++Pins; ++pStart[Fanin+1];
        }
    }
    for ( i = 0; i < n; ++i ) pStart[i+1] += pStart[i];
    memcpy(pNext,pStart,(size_t)n*sizeof(unsigned));
    pSinks = (unsigned *)Prt_SnAlloc(Pins,sizeof(unsigned));
    pScc = (unsigned *)Prt_SnAlloc(p->nGroups,sizeof(unsigned));
    if ( !pSinks || !pScc ) goto Memory;
    for ( i = 0; i < n; ++i )
    {
        Group = p->pObjToGroup[i];
        if ( Group == PRT_NONE ) continue;
        for ( k = 0; k < sn_obj_fanin_count(pModule,i); ++k )
        {
            Fanin = sn_obj_fanin(pModule,i,k);
            if ( Fanin == SN_INVALID_ID || Prt_SnConstant(sn_obj_type(pModule,Fanin)) || pDriver[Fanin] == Group ) continue;
            pSinks[pNext[Fanin]++] = Group;
        }
    }
    if ( !Prt_GraphCreate(p->nGroups,n,pDriver,pStart,pSinks,pWeights,pNetWeights,&pGrouped,pError,nError) ||
         !Prt_GraphScc(pGrouped,pScc,&p->nScc,pError,nError) ||
         !Prt_GraphContract(pGrouped,p->nScc,pScc,&p->pGraph,pError,nError) ) goto Cleanup;
    p->pVertexObject = (unsigned *)Prt_SnAlloc(p->nScc,sizeof(unsigned));
    pOrder = (unsigned *)Prt_SnAlloc(p->nScc,sizeof(unsigned));
    if ( !p->pVertexObject || !pOrder ) goto Memory;
    for ( i = 0; i < p->nScc; ++i ) p->pVertexObject[i] = PRT_NONE;
    for ( i = 0; i < n; ++i )
    {
        Group = p->pObjToGroup[i];
        if ( Group == PRT_NONE ) continue;
        p->pObjToVertex[i] = pScc[Group];
        if ( p->pVertexObject[pScc[Group]] == PRT_NONE ) p->pVertexObject[pScc[Group]] = i;
    }
    for ( i = 0; i < p->nScc; ++i )
        if ( p->MaxSccObject == PRT_NONE || p->pGraph->pObjWeight[i] > p->MaxSccWeight )
        { p->MaxSccWeight = p->pGraph->pObjWeight[i]; p->MaxSccObject = p->pVertexObject[i]; }
    if ( !Prt_GraphTopo(p->pGraph,pOrder,pError,nError) ) goto Cleanup;
    *ppModel = p; p = NULL; Ok = 1; goto Cleanup;
Memory:
    Prt_SnError(pError,nError,"out of memory building SN partition graph");
Cleanup:
    Prt_SnFree(p); Prt_GraphFree(pGrouped);
    free(pParent); free(pRootGroup); free(pDriver); free(pStart); free(pNext);
    free(pSinks); free(pScc); free(pOrder); free(pWeights); free(pNetWeights);
    return Ok;
}

ABC_NAMESPACE_IMPL_END
