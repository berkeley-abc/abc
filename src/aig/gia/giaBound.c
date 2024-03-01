#include "gia.h"
#include "misc/tim/tim.h"
#include "misc/vec/vecWec.h"
#include "proof/cec/cec.h"


ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Bnd_Man_t_  Bnd_Man_t;

struct Bnd_Man_t_
{
    int nBI;
    int nBO;
    int nBI_miss;
    int nBO_miss;
    int nInternal;
    int nExtra;
    int nMerged_spec;
    int nMerged_impl;
    
    int nNode_spec;
    int nNode_impl;
    int nNode_patch;
    int nNode_patched;

    int status; // 0: init 1: boundary found 2: out generated 3: patched generated

    int combLoop_spec;
    int combLoop_impl;
    int eq_out;
    int eq_res;
    int nChoice;

    Vec_Ptr_t* vBmiter2Spec;
    Vec_Ptr_t* vBmiter2Impl;
    Vec_Int_t* vSpec2Impl;
    Vec_Bit_t* vSpec2Impl_phase;
    
    Vec_Int_t* vBI;
    Vec_Int_t* vBO;
    Vec_Int_t* vEI_spec;
    Vec_Int_t* vEO_spec;
    Vec_Int_t* vEI_impl;
    Vec_Int_t* vEO_impl;
    Vec_Bit_t* vEI_phase;
    Vec_Bit_t* vEO_phase;

    Vec_Int_t* vSpec2Impl_diff;

};

Bnd_Man_t* pBnd;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

void Bnd_ManSetEqOut( int eq ) { pBnd -> eq_out = eq;}
void Bnd_ManSetEqRes( int eq ) { pBnd -> eq_res = eq;}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/

Bnd_Man_t* Bnd_ManStart( Gia_Man_t *pSpec, Gia_Man_t *pImpl )
{
    int i;
    Bnd_Man_t* p = ABC_CALLOC( Bnd_Man_t, 1 );

    p -> vBmiter2Spec = Vec_PtrAlloc( Gia_ManObjNum(pSpec) + Gia_ManObjNum(pImpl) );
    p -> vBmiter2Impl = Vec_PtrAlloc( Gia_ManObjNum(pSpec) + Gia_ManObjNum(pImpl) );
    Vec_PtrFill( p -> vBmiter2Spec, (Gia_ManObjNum(pSpec) + Gia_ManObjNum(pImpl)), 0 );
    Vec_PtrFill( p -> vBmiter2Impl, (Gia_ManObjNum(pSpec) + Gia_ManObjNum(pImpl)), 0 );
    for( i = 0; i <  Vec_PtrSize( p -> vBmiter2Impl ); i ++ )
    {
        Vec_PtrSetEntry( p -> vBmiter2Spec, i, Vec_IntAlloc(1) );
        Vec_PtrSetEntry( p -> vBmiter2Impl, i, Vec_IntAlloc(1) );
    }

    p -> vSpec2Impl = Vec_IntAlloc( Gia_ManObjNum(pSpec) );
    p -> vSpec2Impl_phase = Vec_BitAlloc( Gia_ManObjNum(pSpec) );
    Vec_IntFill( p -> vSpec2Impl, Gia_ManObjNum(pSpec), -1 );
    Vec_BitFill( p -> vSpec2Impl_phase, Gia_ManObjNum(pSpec), 0 );
    
    p -> vBI = Vec_IntAlloc(16);
    p -> vBO = Vec_IntAlloc(16);
    p -> vEI_spec = Vec_IntAlloc(16);
    p -> vEO_spec = Vec_IntAlloc(16);
    p -> vEI_impl = Vec_IntAlloc(16);
    p -> vEO_impl = Vec_IntAlloc(16);
    p -> vEI_phase = Vec_BitAlloc(16);
    p -> vEO_phase = Vec_BitAlloc(16);

    p -> nNode_spec = Gia_ManAndNum(pSpec)  - Gia_ManBufNum(pSpec);
    p -> nNode_impl = Gia_ManAndNum(pImpl);
    p -> nNode_patch = 0;
    p -> nNode_patched = 0;

    p -> status = 0;
    p -> combLoop_spec = 0;
    p -> combLoop_impl = 0;
    p -> eq_out = 0;
    p -> eq_res = 0;

    p -> nChoice = 0;

    p -> vSpec2Impl_diff = Vec_IntAlloc( Gia_ManObjNum(pSpec) );
    Vec_IntFill( p -> vSpec2Impl_diff, Gia_ManObjNum(pSpec), 0 );

    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bnd_ManStop()
{
    assert(pBnd);

    Vec_PtrFree( pBnd-> vBmiter2Spec );
    Vec_PtrFree( pBnd-> vBmiter2Impl );
    Vec_IntFree( pBnd-> vSpec2Impl );
    Vec_BitFree( pBnd-> vSpec2Impl_phase );

    Vec_IntFree( pBnd->vBI );
    Vec_IntFree( pBnd->vBO );
    Vec_IntFree( pBnd->vEI_spec );
    Vec_IntFree( pBnd->vEO_spec );
    Vec_IntFree( pBnd->vEI_impl );
    Vec_IntFree( pBnd->vEO_impl );
    Vec_BitFree( pBnd->vEI_phase );
    Vec_BitFree( pBnd->vEO_phase );

    Vec_IntFree( pBnd-> vSpec2Impl_diff );

    ABC_FREE( pBnd );
}


void Bnd_ManMap( int iLit, int id, int spec )
{

    if ( spec )
    {
        Vec_IntPush( Vec_PtrEntry( pBnd -> vBmiter2Spec, iLit >> 1), id ); 
        Vec_BitSetEntry( pBnd -> vSpec2Impl_phase, id, iLit & 1 );
    }
    else 
    {
        assert( (iLit & 1) == 0 );
        Vec_IntPush( Vec_PtrEntry( pBnd -> vBmiter2Impl, iLit >> 1), id ); 
    }
}

void Bnd_ManMerge( int id_repr, int id_obj, int phaseDiff )
{


    Vec_Ptr_t* vBmiter2Spec = pBnd -> vBmiter2Spec;
    Vec_Ptr_t* vBmiter2Impl = pBnd -> vBmiter2Impl;
    Vec_Bit_t* vSpec2Impl_phase = pBnd -> vSpec2Impl_phase;
    int id, i;

    Vec_Int_t *vIds_spec_repr, *vIds_impl_repr, *vIds_spec_obj, *vIds_impl_obj;

    vIds_spec_repr = Vec_PtrEntry( vBmiter2Spec, id_repr );
    vIds_impl_repr = Vec_PtrEntry( vBmiter2Impl, id_repr );
    vIds_spec_obj = Vec_PtrEntry( vBmiter2Spec, id_obj );
    vIds_impl_obj = Vec_PtrEntry( vBmiter2Impl, id_obj );

    Vec_IntForEachEntry( vIds_spec_obj, id, i )
    {
        Vec_IntPush(vIds_spec_repr, id);
    }
    Vec_IntForEachEntry( vIds_impl_obj, id, i )
    {
        Vec_IntPush(vIds_impl_repr, id);
    }

    // handle spec2impl phase
    if ( phaseDiff )
    {
        Vec_IntForEachEntry( vIds_spec_obj, id, i )
        {
            Vec_BitSetEntry( vSpec2Impl_phase, id, !Vec_BitEntry(vSpec2Impl_phase, id) );
            // printf( "spec id %d's phase set to %d\n", id, Vec_BitEntry(vSpec2Impl_phase, id) );
        }
    }

    // handle impl2spec phase
    /*
    if ( Vec_IntSize(vIds_spec_repr) == 0  )    // no match
    {
        if ( pObj->fPhase ^ pRepr -> fPhase )
        {
            Vec_IntForEachEntry( vIds_impl_obj, eId, j )
            {
                Vec_BitSetEntry( vImpl2Spec_phase, eId, !Vec_BitEntry(vImpl2Spec_phase, eId) );
                printf( "impl id %d's phase set to %d\n", eId, Vec_BitEntry(vImpl2Spec_phase, eId) );
            }
        }
    }
    else if ( Vec_IntSize( vIds_spec_repr ) == Vec_IntSize( vIds_spec_obj) && Vec_IntSize( vIds_impl_obj ) == 0 ) // new match
    {
        if ( pObj->fPhase ^ pRepr -> fPhase )
        {
            Vec_IntForEachEntry( vIds_impl_repr, eId, j )
            {
                Vec_BitSetEntry( vImpl2Spec_phase, eId, !Vec_BitEntry(vImpl2Spec_phase, eId) );
                printf( "impl id %d's phase set to %d\n", eId, Vec_BitEntry(vImpl2Spec_phase, eId) );
            }
            printf("new match flip\n");
        }
    }
    else if ( Vec_IntSize( vIds_spec_repr ) > 0 && Vec_IntSize( vIds_impl_obj ) > 0 ) // matched, merge impl
    {
        if ( ( pObj->fPhase ^ pRepr -> fPhase) ^ ( Vec_BitEntry( vImpl2Spec_phase, Vec_IntEntry(vIds_impl_repr, 0)) ^ Vec_BitEntry( vImpl2Spec_phase, Vec_IntEntry(vIds_impl_obj, 0)) ) )
        {
            if ( Vec_IntSize( vIds_spec_repr ) == Vec_IntSize( vIds_spec_obj) ) // unmatched repr, matched obj, set repr bits
            {
                Vec_IntForEachEntry( vIds_impl_repr, eId, j )
                {
                    if ( j >= Vec_IntSize( vIds_impl_repr)-Vec_IntSize(vIds_impl_obj)  ) break;
                    Vec_BitSetEntry( vImpl2Spec_phase, eId, !Vec_BitEntry(vImpl2Spec_phase, eId) );
                    printf( "impl id %d's phase set to %d\n", eId, Vec_BitEntry(vImpl2Spec_phase, eId) );
                }
            }
            else // set obj bits
            {
                Vec_IntForEachEntry( vIds_impl_obj, eId, j )
                {
                    Vec_BitSetEntry( vImpl2Spec_phase, eId, !Vec_BitEntry(vImpl2Spec_phase, eId) );
                    printf( "impl id %d's phase set to %d\n", eId, Vec_BitEntry(vImpl2Spec_phase, eId) );
                }
            }
        }
    }
    */

    Vec_IntClear(vIds_spec_obj);
    Vec_IntClear(vIds_impl_obj);

}
void Bnd_ManFinalizeMappings()
{

    Vec_Ptr_t* vBmiter2Spec = pBnd -> vBmiter2Spec;
    Vec_Ptr_t* vBmiter2Impl = pBnd -> vBmiter2Impl;
    Vec_Int_t* vSpec2Impl = pBnd -> vSpec2Impl;

    Vec_Int_t *vSpec, *vImpl;
    int i, j, id;

    pBnd -> nMerged_impl = 0;
    pBnd -> nMerged_spec = 0;


    for( i = 0; i < Vec_PtrSize(vBmiter2Spec); i++ )
    {
        vSpec = Vec_PtrEntry( vBmiter2Spec, i );
        vImpl = Vec_PtrEntry( vBmiter2Impl, i );

        // create spec2impl
        if ( Vec_IntSize(vSpec) != 0 && Vec_IntSize(vImpl) != 0 )
        {
            Vec_IntForEachEntry( vSpec, id, j )
            {
                Vec_IntSetEntry( vSpec2Impl, id, Vec_IntEntry(vImpl, 0) );

                // record the number of different choice of vEI_impl, vEO_impl
                Vec_IntSetEntry( pBnd->vSpec2Impl_diff, id, Vec_IntSize(vImpl)-1 );
            }


        }

        // count number of nodes merged into the same circuit
        if ( Vec_IntSize(vSpec) != 0 )
        {
            pBnd->nMerged_spec += Vec_IntSize(vSpec) - 1;
        }
        if ( Vec_IntSize(vImpl) != 0 )
        {
            pBnd->nMerged_impl += Vec_IntSize(vImpl) - 1;
        }




    }


}
void Bnd_ManPrintMappings()
{
    Vec_Ptr_t* vBmiter2Spec = pBnd -> vBmiter2Spec;
    Vec_Ptr_t* vBmiter2Impl = pBnd -> vBmiter2Impl;
    Vec_Int_t* vIds_spec, *vIds_impl;
    int k, id;
    for( int j=0; j < Vec_PtrSize(vBmiter2Spec); j++ )
    {
        printf("node %d: ", j);
        vIds_spec = Vec_PtrEntry( vBmiter2Spec, j);
        vIds_impl = Vec_PtrEntry( vBmiter2Impl, j);
        Vec_IntForEachEntry(vIds_spec, id, k)
            printf("%d ", id);
        printf("| ");
        Vec_IntForEachEntry(vIds_impl, id, k)
            printf("%d ", id);
        printf("\n");
    }

}

void Bnd_ManPrintBound()
{

    printf("%d nodes merged in spec\n", pBnd ->nMerged_spec - Vec_IntSize(pBnd->vBI) - Vec_IntSize(pBnd->vBO) );
    printf("%d nodes merged in impl\n", pBnd ->nMerged_impl );

    printf("BI spec:"); Vec_IntPrint(pBnd -> vBI);
    printf("BO spec:"); Vec_IntPrint(pBnd -> vBO);
    printf("\nEI spec:"); Vec_IntPrint(pBnd -> vEI_spec);
    printf("EI impl:"); Vec_IntPrint(pBnd -> vEI_impl);
    printf("EI phase:"); Vec_BitPrint(pBnd -> vEI_phase);
    printf("\nEO spec:"); Vec_IntPrint(pBnd -> vEO_spec);
    printf("EO impl:"); Vec_IntPrint(pBnd -> vEO_impl);
    printf("EO phase:"); Vec_BitPrint(pBnd -> vEO_phase);
}

void Bnd_ManPrintStats()
{
    Bnd_Man_t* p = pBnd;

    // #internal
    // nBI, nBO
    // nBI_miss, nBO_miss
    // nAI, nAO, nExtra
    // #spec, #impl, #patched 

    // combLoop_spec, combLoop_impl

    // eq_out, eq_res
    // status

    // #different choice of impl on boundary

    printf("\nRESULT\n");
    printf("%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d\n",
        p->nInternal,
        p->nBI, p->nBO,
        p->nBI_miss, p->nBO_miss,
        Vec_IntSize(p->vEI_spec), Vec_IntSize(p->vEO_spec), p->nExtra,
        p->nNode_spec, p->nNode_impl, p->nNode_patched,
        p->combLoop_spec, p->combLoop_impl,
        p->eq_out, p->eq_res,
        p->status,
        p->nChoice
    );
}

/**Function*************************************************************

  Synopsis    []

  Description [check if the given boundary is valid. Return 0 if
  the boundary is invalid. Return k if the boundary is valid and
  there're k boundary inputs. ]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bnd_ManCheckBound( Gia_Man_t * p )
{
    int i;
    Gia_Obj_t *pObj;
    int valid = 1;
    pBnd -> nBI = 0;
    pBnd -> nBO = 0;
    pBnd -> nInternal = 0;

    printf( "Checking boundary... \n");

    Vec_Int_t *vPath;
    vPath = Vec_IntAlloc( Gia_ManObjNum(p) );
    Vec_IntFill( vPath, Gia_ManObjNum(p), 0 );
    int path;

    Gia_ManForEachObjReverse1( p , pObj, i )
    {
        if ( Gia_ObjIsCo( pObj ) )
        {
            Vec_IntSetEntry( vPath, Gia_ObjId( p, pObj ), 1 );
        }

        path = Vec_IntEntry( vPath, Gia_ObjId(p, pObj) );
        // printf("path = %d\n", path);

        if ( path >= 8 )
        {
            valid = 0;
            printf("there're more than 2 bufs in a path\n");
            break;
        }


        if( Gia_ObjIsBuf( pObj ) )
        {
            Vec_IntSetEntry( vPath, Gia_ObjId( p, Gia_ObjFanin0( pObj ) ), Vec_IntEntry( vPath, Gia_ObjId(p, Gia_ObjFanin0( pObj ) ) ) | path << 1 );
            if ( path == 1 )  // boundary input
            {
                // TODO: record BIs here since they may not be in the first n buffers
                pBnd -> nBO ++;
            }
        }
        else if ( Gia_ObjFaninNum( p, pObj ) >= 1 )
        {
            Vec_IntSetEntry( vPath, Gia_ObjId( p, Gia_ObjFanin0( pObj ) ), Vec_IntEntry( vPath, Gia_ObjId(p, Gia_ObjFanin0( pObj ) ) ) | path );
            if ( Gia_ObjFaninNum( p, pObj ) >= 2 )
            {
                assert( Gia_ObjFaninNum( p, pObj ) <= 2  );
                Vec_IntSetEntry( vPath, Gia_ObjId( p, Gia_ObjFanin1( pObj ) ), Vec_IntEntry( vPath, Gia_ObjId(p, Gia_ObjFanin1( pObj ) ) ) | path );
            }
            if ( path == 2 )  // inside boundary
            {
                // TODO: record BIs here since they may not be in the first n buffers
                pBnd -> nInternal ++;
            }
        }
        else // PI or const, check validity
        {
            if ( (Vec_IntEntry( vPath, Gia_ObjId(p, pObj) ) | 5) != 5 )
            {
                valid = 0;
                printf("incorrect buf number at pi %d\n", Vec_IntEntry(vPath, Gia_ObjId(p, pObj)) );
                break;
            }
        }
    }

    pBnd -> nBI = Gia_ManBufNum(p) - pBnd -> nBO;

    if ( !valid ) 
    {
        printf("invalid boundary\n");
        return 0;
    }
    else 
    {
        printf("valid boundary (");
        printf("#BI = %d\t#BO = %d\t", pBnd -> nBI, Gia_ManBufNum(p)- pBnd -> nBI);
        printf("#Internal = %d)\n", pBnd -> nInternal );
        assert( pBnd -> nBI > 0 );
        return pBnd -> nBI;
    }
}


int Bnd_CheckFlagRec( Gia_Man_t *p, Gia_Obj_t *pObj, Vec_Int_t* vFlag )
{
    int id = Gia_ObjId(p, pObj);
    if ( Vec_IntEntry(vFlag, id) == 1 ) return 1;
    if ( Vec_IntEntry(vFlag, id) == 2 ) return 0;

    Vec_IntSetEntry(vFlag, id, 1);

    int ret = 1;
    for( int i = 0; i < Gia_ObjFaninNum(p, pObj); i++ )
    {
        if ( !Bnd_CheckFlagRec( p, Gia_ObjFanin(pObj, i), vFlag ) )
        {
            ret = 0;
            break;
        }
    }
    return ret;

}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Bnd_ManCheckExtBound( Gia_Man_t * p, Vec_Int_t *vEI, Vec_Int_t *vEO )
{
    Vec_Int_t *vFlag = Vec_IntAlloc( Gia_ManObjNum(p) );
    Vec_IntFill( vFlag, Gia_ManObjNum(p), 0 );
    int success = 1;
    int i, id;

    Vec_IntForEachEntry( vEO, id, i )
    {
        Vec_IntSetEntry( vFlag, id, 2 );
    }

    Vec_IntForEachEntry( vEI, id, i )
    {
        if ( Vec_IntEntry(vFlag, id) == 2 ) continue; // BI connected to BO directly

        if ( !Bnd_CheckFlagRec( p, Gia_ManObj(p, id), vFlag ) )
        {
            success = 0;
            break;
        }
    }


    Vec_IntFree(vFlag);
    return success;
}



/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/

void Bnd_ManFindBound( Gia_Man_t * p )
{
    Vec_Int_t  *vFlag;
    Vec_Ptr_t *vQ;
    Gia_Obj_t *pObj;
    int i, j, id, cnt;

    Vec_Int_t *vAI = Vec_IntAlloc(16);
    Vec_Int_t *vAO = Vec_IntAlloc(16);

    Vec_Int_t *vSpec2Impl = pBnd -> vSpec2Impl;
    Vec_Bit_t *vSpec2Impl_phase = pBnd -> vSpec2Impl_phase;
    Vec_Int_t *vBI = pBnd -> vBI;
    Vec_Int_t *vBO = pBnd -> vBO;
    Vec_Int_t *vEI_spec = pBnd -> vEI_spec;
    Vec_Int_t *vEO_spec = pBnd -> vEO_spec;
    Vec_Int_t *vEI_impl = pBnd -> vEI_impl;
    Vec_Int_t *vEO_impl = pBnd -> vEO_impl;
    Vec_Bit_t *vEI_phase = pBnd -> vEI_phase;
    Vec_Bit_t *vEO_phase = pBnd -> vEO_phase;


    // prepare to compute extended boundary
    vQ = Vec_PtrAlloc(16);
    vFlag = Vec_IntAlloc( Gia_ManObjNum(p) );
    Vec_IntFill( vFlag, Gia_ManObjNum(p), 0 );

    Gia_ManStaticFanoutStart(p);

    // save bo, bi
    cnt = 0;
    Gia_ManForEachBuf(p, pObj, i)
    {
        if ( cnt < pBnd -> nBI ) 
        {
            Vec_IntPush( vBI, Gia_ObjId(p, pObj) );
        }
        else 
        {
            Vec_IntPush( vBO, Gia_ObjId(p, pObj) );
        }
        cnt++;
    }
    printf("#BI = %d #BO = %d\n", Vec_IntSize(vBI), Vec_IntSize(vBO) );

    // compute EO, travse with flag 1
    Vec_IntForEachEntry( vBO, id, i )
    {
        if ( Vec_IntEntry( vSpec2Impl, id ) == -1 ) // BO not matched 
        {
            Vec_PtrPush( vQ, Gia_ManObj(p, id) );
        }
        else
        {
            Vec_IntPush(vEO_spec, id);
        }
    }
    printf("%d BO doesn't match\n", Vec_PtrSize(vQ) );
    pBnd -> nBO_miss = Vec_PtrSize(vQ);

    int cnt_extra = - Vec_PtrSize(vQ);
    while( Vec_PtrSize(vQ) > 0 )
    {
        pObj = Vec_PtrPop(vQ);
        id = Gia_ObjId( p, pObj );

        if ( Vec_IntEntry( vFlag, id  ) == 1 ) continue;
        Vec_IntSetEntry( vFlag, id, 1 );

        // printf("%d\n", id);

        if ( Vec_IntEntry( vSpec2Impl, id ) != -1 )    // matched
        {
            Vec_IntPush( vEO_spec, id );
            Vec_IntPush( vAO, id );
        }
        else
        {
            for( j = 0; j < Gia_ObjFanoutNum(p, pObj); j++ )
            {
                Vec_PtrPush( vQ, Gia_ObjFanout(p, pObj, j) );
                // printf("\t%d\n", Gia_ObjId( p1, Gia_ObjFanout(p1, pObj, j) ) );
            }
        }
    }
    // printf("%d AO found with %d extra nodes\n", Vec_IntSize(vAO) , cnt_extra );
     printf("%d AO found\n", Vec_IntSize(vAO) );


    // mark TFOC of BO with flag 1 to prevent them from being selected into EI
    // stop at CO
    Vec_IntForEachEntry( pBnd -> vBO, id, i )
    {
        Vec_PtrPush( vQ, Gia_ManObj(p, id) );
    }
    Vec_IntForEachEntry( vFlag, id, i )
    {
        Vec_IntSetEntry( vFlag, id, 0 );
    }
    while( Vec_PtrSize(vQ) > 0 )
    {
        pObj = Vec_PtrPop(vQ);
        id = Gia_ObjId( p, pObj );

        if ( Vec_IntEntry( vFlag, id  ) == 1 ) continue;
        Vec_IntSetEntry( vFlag, id, 1 );

        for( j = 0; j < Gia_ObjFanoutNum(p, pObj); j++ )
        {
            Vec_PtrPush( vQ, Gia_ObjFanout(p, pObj, j) );
        }
    }



    // compute EI,  traverse with flag 2

    // add unmatched BI to queue
    Vec_IntForEachEntry( vBI, id, i )
    {
        if ( Vec_IntEntry( vSpec2Impl, id ) == -1 ) // BO not matched 
        {
            Vec_PtrPush( vQ, Gia_ManObj(p, id) );
        }
        else
        {
            Vec_IntPush(vEI_spec, id);
        }
    }
    printf("%d BI doesn't match\n", Vec_PtrSize(vQ) );
    pBnd -> nBI_miss = Vec_PtrSize(vQ);
    cnt_extra -= Vec_PtrSize(vQ);

    // add AO to queue
    Vec_IntForEachEntry( vAO, id, i )
    {
        Vec_PtrPush( vQ, Gia_ManObj(p, id) );
    }

    // set flag 2 for BO
    Vec_IntForEachEntry( vBO, id, i )
    {
        Vec_IntSetEntry( vFlag, id, 2 );
    }

    // traverse down from AI and unmatched BI
    while( Vec_PtrSize(vQ) > 0 )
    {
        pObj = Vec_PtrPop(vQ);
        id = Gia_ObjId( p, pObj );

        if ( Vec_IntEntry( vFlag, id  ) == 2 ) continue;
        cnt_extra ++;

        // printf("%d\n", id);

        if ( Vec_IntEntry(vFlag, id) != 1 && Vec_IntEntry( vSpec2Impl, id ) != -1 )    // matched
        {
            Vec_IntPush( vEI_spec, id );
            Vec_IntPush( vAI, id );
        }
        else
        {
            for( j = 0; j < Gia_ObjFaninNum(p, pObj); j++ )
            {
                Vec_PtrPush( vQ, Gia_ObjFanin(pObj, j) );
                // printf("\t%d\n", Gia_ObjId( p1, Gia_ObjFanout(p1, pObj, j) ) );
            }
        }

        Vec_IntSetEntry( vFlag, id, 2 );
    }
    printf("%d AI found with %d extra nodes in total\n", Vec_IntSize(vAI) , cnt_extra );
    pBnd -> nExtra = cnt_extra;


    // gen vEI_impl, vEO_impl, vEI_phase, vEO_phase
    Vec_IntForEachEntry( vEI_spec, id, i )
    {
        Vec_IntPush( vEI_impl, Vec_IntEntry( vSpec2Impl, id ) );
        Vec_BitPush( vEI_phase, Vec_BitEntry( vSpec2Impl_phase, id ) );
    }
    Vec_IntForEachEntry( vEO_spec, id, i )
    {
        Vec_IntPush( vEO_impl, Vec_IntEntry( vSpec2Impl, id ) );
        Vec_BitPush( vEO_phase, Vec_BitEntry( vSpec2Impl_phase, id ) );
    }


    // count number of choice of boundary in impl
    Vec_IntForEachEntry( vEI_spec, id, i )
    {
        pBnd -> nChoice += Vec_IntEntry( pBnd -> vSpec2Impl_diff, id );
    }
    Vec_IntForEachEntry( vEO_spec, id, i )
    {
        pBnd -> nChoice += Vec_IntEntry( pBnd -> vSpec2Impl_diff, id );
    }


    // print
    pBnd -> status = 1;
    printf("#EI = %d\t#EO = %d\t#Extra Node = %d\n", Vec_IntSize(vEI_spec) , Vec_IntSize(vEO_spec), cnt_extra );
    Bnd_ManPrintBound();

    // check boundary has comb loop
    if ( !Bnd_ManCheckExtBound( p, vEI_spec, vEO_spec ) )
    {
        printf("Combinational loop exist\n");
        pBnd -> combLoop_spec = 1;
    }


    // clean up
    Vec_IntFree(vAI);
    Vec_IntFree(vAO);
}




/**Function*************************************************************

  Synopsis    []

  Description [create circuit with the boundary changed to CI/CO]

  SideEffects []

  SeeAlso     []

***********************************************************************/

Gia_Man_t* Bnd_ManCutBoundary( Gia_Man_t *p, Vec_Int_t* vEI, Vec_Int_t* vEO, Vec_Bit_t* vEI_phase, Vec_Bit_t* vEO_phase )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, id, lit;

    // check if the boundary has loop (EO cannot be in the TFC of EI )
    if ( !Bnd_ManCheckExtBound( p, vEI, vEO ) )
    {
        printf("Combinational loop exist\n");
        pBnd -> combLoop_impl = 1;
        return 0;
    }


    // initialize
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew -> pName = ABC_ALLOC( char, strlen(p->pName)+10);
    sprintf( pNew -> pName, "%s_out", p -> pName );
    Gia_ManHashStart( pNew );
    Gia_ManConst0(p) -> Value = 0;
    Gia_ManCleanValue(p);


    // create ci for ci and eo
    Gia_ManForEachCi( p, pObj, i )
    {
        pObj -> Value = Gia_ManAppendCi( pNew );
    }
    Vec_IntForEachEntry( vEO, id, i )
    {
        Gia_ManObj( p, id ) -> Value = Gia_ManAppendCi(pNew);
        if ( vEO_phase && Vec_BitEntry( vEO_phase, i ) )
        {
            Gia_ManObj( p, id ) -> Value ^= 1;
        }
    }

    // TODO: consider where EI and EO share the same node

    // add aig nodes
    Gia_ManForEachAnd(p, pObj, i)
    {
        if ( pObj -> Value ) continue;
        pObj -> Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    }

    // create co for co and ei
    Gia_ManForEachCo(p, pObj, i)
    {
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    }
    Vec_IntForEachEntry( vEI, id, i )
    {
        lit = Gia_ManObj(p, id)->Value;
        // lit = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        if ( vEI_phase && Vec_BitEntry( vEI_phase, i ) ) lit ^= 1;
        Gia_ManAppendCo( pNew, lit );
    }

    // clean up
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;

}

Gia_Man_t* Bnd_ManGenSpecOut( Gia_Man_t* p )
{
    printf("Generating spec_out with given boundary.\n");
    Gia_Man_t *pNew = Bnd_ManCutBoundary( p, pBnd->vEI_spec, pBnd->vEO_spec, 0, 0 );
    return pNew;
}
Gia_Man_t* Bnd_ManGenImplOut( Gia_Man_t* p )
{
    printf("Generating impl_out with given boundary.\n");
    Gia_Man_t *pNew = Bnd_ManCutBoundary( p, pBnd->vEI_impl, pBnd->vEO_impl, pBnd->vEI_phase, pBnd->vEO_phase );
    if ( pNew ) pBnd -> status = 2;
    else pBnd -> combLoop_impl = 1;
    return pNew;
}

void Bnd_AddNodeRec( Gia_Man_t *p, Gia_Man_t *pNew, Gia_Obj_t *pObj )
{
    // TODO does this mean constant zero node?
    if ( pObj -> Value != 0 || Gia_ObjIsConst0(pObj) ) return;

    for( int i = 0; i < Gia_ObjFaninNum(p, pObj); i++  )
    {
        Bnd_AddNodeRec( p, pNew, Gia_ObjFanin(pObj, i) );
    }

    if ( Gia_ObjIsAnd(pObj) ) 
    {
        pObj -> Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    }
    else 
    {
        if ( Gia_ObjIsCi(pObj) )
        {
            printf("Ci with value 0 encountered (id = %d)\n", Gia_ObjId(p, pObj) );
        }
        assert( Gia_ObjIsCo(pObj) );
        pObj -> Value = Gia_ObjFanin0Copy(pObj);
    }
}

Gia_Man_t* Bnd_ManGenPatched( Gia_Man_t *pOut, Gia_Man_t *pSpec, Gia_Man_t *pPatch )
{

    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i, id, cnt;
    Vec_Int_t *vBI_patch, *vBO_patch;

    printf("Generating patched implementation\n");
    pBnd -> nNode_patch = Gia_ManAndNotBufNum( pPatch );

    pNew = Gia_ManStart( Gia_ManObjNum(pOut) + Gia_ManObjNum( pSpec ) + Gia_ManObjNum(pPatch) );
    pNew -> pName = ABC_ALLOC( char, strlen(pOut->pName)+3);
    sprintf( pNew -> pName, "%s_p", pOut -> pName );
    Gia_ManHashStart( pNew );
    Gia_ManCleanValue(pOut);
    Gia_ManCleanValue(pSpec);
    Gia_ManCleanValue(pPatch);

    // get bi and bo in patch
    cnt = 0;
    vBI_patch = Vec_IntAlloc(16);
    vBO_patch = Vec_IntAlloc(16);
    Gia_ManForEachBuf( pPatch, pObj, i )
    {
        if ( cnt < pBnd -> nBI )
        {
            Vec_IntPush( vBI_patch, Gia_ObjId( pPatch, pObj ) );
        }
        else
        {

            Vec_IntPush( vBO_patch, Gia_ObjId( pPatch, pObj ) );
        }
        cnt ++;
    }
    assert( Vec_IntSize( vBI_patch ) == Vec_IntSize(pBnd->vBI) );
    assert( Vec_IntSize( vBO_patch ) == Vec_IntSize(pBnd->vBO) );
    assert( Bnd_ManCheckBound(pPatch) != 0 );


    // add Impl (real) PI
    for ( i = 0; i < Gia_ManCiNum(pSpec); i++ )
    {
        pObj = Gia_ManCi(pOut, i);
        pObj -> Value = Gia_ManAppendCi( pNew );
    }

    // add Impl EI to CI
    printf("adding EI to CI in Impl\n");
    for ( i = 0; i < Vec_IntSize( pBnd -> vEI_spec ); i++ )
    {
        pObj = Gia_ManCo(pOut, i + Gia_ManCoNum(pSpec) );
        Bnd_AddNodeRec( pOut, pNew, pObj );

        // set Spec EI
        Gia_ManObj( pSpec, Vec_IntEntry(pBnd -> vEI_spec, i) ) -> Value = pObj -> Value;
        printf("%d ", pObj->Value);
    }
    printf("\n");

    // add Spec BI to EI
    printf("adding BI to EI in Spec\n");
    Vec_IntForEachEntry( pBnd -> vBI, id, i )
    {
        pObj = Gia_ManObj( pSpec, id );
        Bnd_AddNodeRec( pSpec, pNew, pObj );

        // set patch bi
        Gia_ManObj( pPatch, Vec_IntEntry( vBI_patch, i) ) -> Value = pObj -> Value;
        printf("%d ", pObj->Value);
    }
    printf("\n");

    // check
    // cnt = 0;
    // Gia_ManForEachBuf( pPatch, pObj, i )
    // {
    //     if ( cnt < pBnd -> nBI )
    //     {
    //         assert(pObj -> Value != 0);
    //     }
    //     cnt++;
    // }

    // add Patch BO to BI
    printf("adding BO to BI in Patch\n");
    Vec_IntForEachEntry( vBO_patch, id, i )
    {
        pObj = Gia_ManObj( pPatch, id );
        Bnd_AddNodeRec( pPatch, pNew, pObj );

        // set spec bo
        Gia_ManObj( pSpec, Vec_IntEntry( pBnd -> vBO, i) ) -> Value = pObj -> Value;
        printf("%d ", pObj->Value);
    }
    printf("\n");

    // add Spec EO to BO
    printf("adding EO to BO in Spec\n");
    Vec_IntForEachEntry( pBnd -> vEO_spec, id, i )
    {
        pObj = Gia_ManObj( pSpec, id );
        Bnd_AddNodeRec( pSpec, pNew, pObj );

        // set impl EO (PI)
        Gia_ManCi( pOut, i + Gia_ManCiNum(pSpec) ) -> Value = pObj -> Value;
        printf("%d ", pObj->Value);
    }
    printf("\n");

    // add Impl (real) PO to EO
    printf("adding CO to EO in Impl\n");
    for ( i = 0; i < Gia_ManCoNum(pSpec); i++ )
    {
        pObj = Gia_ManCo( pOut, i );
        Bnd_AddNodeRec( pOut, pNew, pObj );
        Gia_ManAppendCo( pNew, pObj->Value );
        printf("%d ", pObj->Value);
    }
    printf("\n");


    // clean up
    Vec_IntFree( vBI_patch );
    Vec_IntFree( vBO_patch );
    Gia_ManHashStop( pNew );

    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );

    pBnd -> nNode_patched = Gia_ManAndNum( pNew );
    pBnd -> status = 3;

    return pNew;
}





////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END