#include <stdio.h>
#include "main.h"
#include "aig.h"
#include "saig.h"
#include <string.h>

ABC_NAMESPACE_IMPL_START


#define PROPAGATE_NAMES

#define FULL_BIERE_MODE 0
#define IGNORE_LIVENESS_KEEP_SAFETY_MODE 1
#define IGNORE_SAFETY_KEEP_LIVENESS_MODE 2
#define IGNORE_SAFETY_KEEP_LIVENESS_ONE_LOOP_MODE 3
#define FULL_BIERE_ONE_LOOP_MODE 4
//#define DUPLICATE_CKT_DEBUG

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
//char *strdup(const char *string);

 
/*******************************************************************
LAYOUT OF PI VECTOR:

+------------------------------------------------------------------------------------------------------------------------------------+
| TRUE ORIGINAL PI (n) | SAVE(PI) (1) | ORIGINAL LO (k) | SAVED(LO) (1) | SHADOW_ORIGINAL LO (k) | LIVENESS LO (l) | FAIRNESS LO (f) |
+------------------------------------------------------------------------------------------------------------------------------------+
<------------True PI----------------->|<----------------------------LO--------------------------------------------------------------->

LAYOUT OF PO VECTOR:

+-----------------------------------------------------------------------------------------------------------+
| SOLE PO (1) | ORIGINAL LI (k) | SAVED LI (1) | SHADOW_ORIGINAL LI (k) | LIVENESS LI (l) | FAIRNESS LI (f) |
+-----------------------------------------------------------------------------------------------------------+
<--True PO--->|<--------------------------------------LI---------------------------------------------------->

********************************************************************/


static int nodeName_starts_with( Abc_Obj_t *pNode, const char *prefix )
{
    if( strstr( Abc_ObjName( pNode ), prefix ) == Abc_ObjName( pNode ) )
        return 1;
    else
        return 0;
}

void printVecPtrOfString( Vec_Ptr_t *vec )
{
    int i;

    for( i=0; i< Vec_PtrSize( vec ); i++ )
    {
        printf("vec[%d] = %s\n", i, (char *)Vec_PtrEntry(vec, i) );
    }
}

int getPoIndex( Aig_Man_t *pAig, Aig_Obj_t *pPivot )
{
    int i;
    Aig_Obj_t *pObj;

    Saig_ManForEachPo( pAig, pObj, i )
    {
        if( pObj == pPivot )
            return i;
    }
    return -1;
}

char * retrieveTruePiName( Abc_Ntk_t *pNtkOld, Aig_Man_t *pAigOld, Aig_Man_t *pAigNew, Aig_Obj_t *pObjPivot )
{
    Aig_Obj_t *pObjOld, *pObj;
    Abc_Obj_t *pNode;
    int index;

    assert( Saig_ObjIsPi( pAigNew, pObjPivot ) );
    Aig_ManForEachPi( pAigNew, pObj, index )
        if( pObj == pObjPivot )
            break;
    assert( index < Aig_ManPiNum( pAigNew ) - Aig_ManRegNum( pAigNew ) );
    if( index == Saig_ManPiNum( pAigNew ) - 1 )
        return "SAVE_BIERE";
    else
    {
        pObjOld = Aig_ManPi( pAigOld, index );
        pNode = Abc_NtkPi( pNtkOld, index );
        assert( pObjOld->pData == pObjPivot );
        return Abc_ObjName( pNode );
    }
}

char * retrieveLOName( Abc_Ntk_t *pNtkOld, Aig_Man_t *pAigOld, Aig_Man_t *pAigNew, Aig_Obj_t *pObjPivot, Vec_Ptr_t *vLive, Vec_Ptr_t * vFair )
{
    Aig_Obj_t *pObjOld, *pObj;
    Abc_Obj_t *pNode;
    int index, oldIndex, originalLatchNum = Saig_ManRegNum(pAigOld), strMatch, i;
    char *dummyStr = (char *)malloc( sizeof(char) * 50 );

    assert( Saig_ObjIsLo( pAigNew, pObjPivot ) );
    Saig_ManForEachLo( pAigNew, pObj, index )
        if( pObj == pObjPivot )
            break;
    if( index < originalLatchNum )
    {
        oldIndex = Saig_ManPiNum( pAigOld ) + index;
        pObjOld = Aig_ManPi( pAigOld, oldIndex );
        pNode = Abc_NtkCi( pNtkOld, oldIndex );
        assert( pObjOld->pData == pObjPivot );
        return Abc_ObjName( pNode );
    }
    else if( index == originalLatchNum )
        return "SAVED_LO";
    else if( index > originalLatchNum && index < 2 * originalLatchNum + 1 )
    {
        oldIndex = Saig_ManPiNum( pAigOld ) + index - originalLatchNum - 1;
        pObjOld = Aig_ManPi( pAigOld, oldIndex );
        pNode = Abc_NtkCi( pNtkOld, oldIndex );
        sprintf( dummyStr, "%s__%s", Abc_ObjName( pNode ), "SHADOW");
        return dummyStr;
    }
    else if( index >= 2 * originalLatchNum + 1 && index < 2 * originalLatchNum + 1 + Vec_PtrSize( vLive ) )
    {
        oldIndex = index - 2 * originalLatchNum - 1;
        strMatch = 0;
        dummyStr[0] = '\0';
        Saig_ManForEachPo( pAigOld, pObj, i )
        {
            pNode = Abc_NtkPo( pNtkOld, i );
            //if( strstr( Abc_ObjName( pNode ), "assert_fair" ) != NULL )
            if(    nodeName_starts_with( pNode, "assert_fair" ) )
            {
                if( strMatch == oldIndex )
                {
                    sprintf( dummyStr, "%s__%s", Abc_ObjName( pNode ), "LIVENESS");
                    //return dummyStr;
                    break;
                }
                else
                    strMatch++;
            }
        }
        assert( dummyStr[0] != '\0' );
        return dummyStr;
    }
    else if( index >= 2 * originalLatchNum + 1 + Vec_PtrSize( vLive ) && index < 2 * originalLatchNum + 1 + Vec_PtrSize( vLive ) + Vec_PtrSize( vFair ) )
    {
        oldIndex = index - 2 * originalLatchNum - 1 - Vec_PtrSize( vLive );
        strMatch = 0;
        dummyStr[0] = '\0';
        Saig_ManForEachPo( pAigOld, pObj, i )
        {
            pNode = Abc_NtkPo( pNtkOld, i );
            //if( strstr( Abc_ObjName( pNode ), "assume_fair" ) != NULL )
            if(    nodeName_starts_with( pNode, "assume_fair" ) )
            {
                if( strMatch == oldIndex )
                {
                    sprintf( dummyStr, "%s__%s", Abc_ObjName( pNode ), "FAIRNESS");
                    //return dummyStr;
                    break;
                }
                else
                    strMatch++;
            }
        }
        assert( dummyStr[0] != '\0' );
        return dummyStr;
    }
    else
        return "UNKNOWN";
}

Vec_Ptr_t *vecPis, *vecPiNames;
Vec_Ptr_t *vecLos, *vecLoNames;


int Aig_ManPiCleanupBiere( Aig_Man_t * p )
{
    int k = 0, nPisOld = Aig_ManPiNum(p);
    
    p->nObjs[AIG_OBJ_PI] = Vec_PtrSize( p->vPis );
    if ( Aig_ManRegNum(p) )
        p->nTruePis = Aig_ManPiNum(p) - Aig_ManRegNum(p);
    
    return nPisOld - Aig_ManPiNum(p);
}


int Aig_ManPoCleanupBiere( Aig_Man_t * p )
{
    int k = 0, nPosOld = Aig_ManPoNum(p);

    p->nObjs[AIG_OBJ_PO] = Vec_PtrSize( p->vPos );
    if ( Aig_ManRegNum(p) )
        p->nTruePos = Aig_ManPoNum(p) - Aig_ManRegNum(p);
    return nPosOld - Aig_ManPoNum(p);
}

Aig_Man_t * LivenessToSafetyTransformation( int mode, Abc_Ntk_t * pNtk, Aig_Man_t * p, 
                                           Vec_Ptr_t *vLive, Vec_Ptr_t *vFair, Vec_Ptr_t *vAssertSafety, Vec_Ptr_t *vAssumeSafety )
{
    Aig_Man_t * pNew;
    int i, nRegCount;
    Aig_Obj_t * pObjSavePi;
    Aig_Obj_t *pObjSavedLo, *pObjSavedLi;
    Aig_Obj_t *pObj, *pMatch;
    Aig_Obj_t *pObjSaveOrSaved, *pObjSaveAndNotSaved, *pObjSavedLoAndEquality;
    Aig_Obj_t *pObjShadowLo, *pObjShadowLi, *pObjShadowLiDriver;
    Aig_Obj_t *pObjXor, *pObjXnor, *pObjAndAcc;
    Aig_Obj_t *pObjLive, *pObjFair, *pObjSafetyGate;
    Aig_Obj_t *pObjSafetyPropertyOutput;
    Aig_Obj_t *pObjOriginalSafetyPropertyOutput;
    Aig_Obj_t *pDriverImage, *pArgument, *collectiveAssertSafety, *collectiveAssumeSafety;
    char *nodeName;
    int piCopied = 0, liCopied = 0, loCopied = 0, liCreated = 0, loCreated = 0, piVecIndex = 0, liveLatch = 0, fairLatch = 0;
    
    vecPis = Vec_PtrAlloc( Saig_ManPiNum( p ) + 1);
    vecPiNames = Vec_PtrAlloc( Saig_ManPiNum( p ) + 1);

    vecLos = Vec_PtrAlloc( Saig_ManRegNum( p )*2 + 1 + Vec_PtrSize( vLive ) + Vec_PtrSize( vFair ) );
    vecLoNames = Vec_PtrAlloc( Saig_ManRegNum( p )*2 + 1 + Vec_PtrSize( vLive ) + Vec_PtrSize( vFair ) );

    //****************************************************************
    // Step1: create the new manager
    // Note: The new manager is created with "2 * Aig_ManObjNumMax(p)"
    // nodes, but this selection is arbitrary - need to be justified
    //****************************************************************
    pNew = Aig_ManStart( 2 * Aig_ManObjNumMax(p) );
    pNew->pName = (char *)malloc( strlen( pNtk->pName ) + strlen("_l2s") + 1 );
    sprintf(pNew->pName, "%s_%s", pNtk->pName, "l2s");
    pNew->pSpec = NULL;
    
    //****************************************************************
    // Step 2: map constant nodes
    //****************************************************************
    pObj = Aig_ManConst1( p );
    pObj->pData = Aig_ManConst1( pNew );

    //****************************************************************
    // Step 3: create true PIs
    //****************************************************************
    Saig_ManForEachPi( p, pObj, i )
    {
        piCopied++;
        pObj->pData = Aig_ObjCreatePi(pNew);
        Vec_PtrPush( vecPis, pObj->pData );
        nodeName = Aig_UtilStrsav(Abc_ObjName( Abc_NtkPi( pNtk, i ) ));
        Vec_PtrPush( vecPiNames, nodeName );
    }

    //****************************************************************
    // Step 4: create the special Pi corresponding to SAVE
    //****************************************************************
    if( mode == FULL_BIERE_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_MODE )
    {
        pObjSavePi = Aig_ObjCreatePi( pNew );
        nodeName = "SAVE_BIERE",
        Vec_PtrPush( vecPiNames, nodeName );
    }
        
    //****************************************************************
    // Step 5: create register outputs
    //****************************************************************
    Saig_ManForEachLo( p, pObj, i )
    {
        loCopied++;
        pObj->pData = Aig_ObjCreatePi(pNew);
        Vec_PtrPush( vecLos, pObj->pData );
        nodeName = Aig_UtilStrsav(Abc_ObjName( Abc_NtkCi( pNtk, Abc_NtkPiNum(pNtk) + i ) ));
        Vec_PtrPush( vecLoNames, nodeName );
    }

    //****************************************************************
    // Step 6: create "saved" register output
    //****************************************************************
    if( mode == FULL_BIERE_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_MODE )
    {
        loCreated++;
        pObjSavedLo = Aig_ObjCreatePi( pNew );
        Vec_PtrPush( vecLos, pObjSavedLo );
        nodeName = "SAVED_LO";
        Vec_PtrPush( vecLoNames, nodeName );
    }

    //****************************************************************
    // Step 7: create the OR gate and the AND gate directly fed by "SAVE" Pi
    //****************************************************************
    if( mode == FULL_BIERE_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_MODE )
    {
        pObjSaveOrSaved = Aig_Or( pNew, pObjSavePi, pObjSavedLo );
        pObjSaveAndNotSaved = Aig_And( pNew, pObjSavePi, Aig_Not(pObjSavedLo) );
    }

    //********************************************************************
    // Step 8: create internal nodes
    //********************************************************************
    Aig_ManForEachNode( p, pObj, i )
    {
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    }

    
    //********************************************************************
    // Step 8.x : create PO for each safety assertions
    // NOTE : Here the output is purposely inverted as it will be thrown to 
    // dprove
    //********************************************************************
    if( mode == FULL_BIERE_MODE || mode == IGNORE_LIVENESS_KEEP_SAFETY_MODE )
    {
        if( Vec_PtrSize( vAssertSafety ) != 0 && Vec_PtrSize( vAssumeSafety ) == 0 )
        {
            pObjAndAcc = Aig_ManConst1( pNew );
            Vec_PtrForEachEntry( Aig_Obj_t *, vAssertSafety, pObj, i )
            {
                pArgument = Aig_NotCond( (Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0( pObj ) );
                pObjAndAcc = Aig_And( pNew, pArgument, pObjAndAcc );
            }
            pObjOriginalSafetyPropertyOutput = Aig_ObjCreatePo( pNew, Aig_Not(pObjAndAcc) );
        }
        else if( Vec_PtrSize( vAssertSafety ) != 0 && Vec_PtrSize( vAssumeSafety ) != 0 )
        {
            pObjAndAcc = Aig_ManConst1( pNew );
            Vec_PtrForEachEntry( Aig_Obj_t *, vAssertSafety, pObj, i )
            {
                pArgument = Aig_NotCond( (Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0( pObj ) );
                pObjAndAcc = Aig_And( pNew, pArgument, pObjAndAcc );
            }
            collectiveAssertSafety = pObjAndAcc;

            pObjAndAcc = Aig_ManConst1( pNew );
            Vec_PtrForEachEntry( Aig_Obj_t *, vAssumeSafety, pObj, i )
            {
                pArgument = Aig_NotCond( (Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0( pObj ) );
                pObjAndAcc = Aig_And( pNew, pArgument, pObjAndAcc );
            }
            collectiveAssumeSafety = pObjAndAcc;
            pObjOriginalSafetyPropertyOutput = Aig_ObjCreatePo( pNew, Aig_And( pNew, Aig_Not(collectiveAssertSafety), collectiveAssumeSafety ) );
        }
        else
        {
            printf("WARNING!! No safety property is found, a new (negated) constant 1 output is created\n");
            pObjOriginalSafetyPropertyOutput = Aig_ObjCreatePo( pNew, Aig_Not( Aig_ManConst1(pNew) ) );
        }
    }

    //********************************************************************
    // Step 9: create the safety property output gate for the liveness properties
    // discuss with Sat/Alan for an alternative implementation
    //********************************************************************
    if( mode == FULL_BIERE_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_MODE )
    {
        pObjSafetyPropertyOutput = Aig_ObjCreatePo( pNew, (Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData );
    }

    // create register inputs for the original registers
    nRegCount = 0;
    
    Saig_ManForEachLo( p, pObj, i )
    {
        pMatch = Saig_ObjLoToLi( p, pObj );
        Aig_ObjCreatePo( pNew, Aig_NotCond((Aig_Obj_t *)Aig_ObjFanin0(pMatch)->pData, Aig_ObjFaninC0( pMatch ) ) );
        nRegCount++;
        liCopied++;
    }

    // create register input corresponding to the register "saved"
    if( mode == FULL_BIERE_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_MODE )
    {
        #ifndef DUPLICATE_CKT_DEBUG
            pObjSavedLi = Aig_ObjCreatePo( pNew, pObjSaveOrSaved );
            nRegCount++;
            liCreated++;

            //Changed on October 13, 2009
            //pObjAndAcc = NULL;
            pObjAndAcc = Aig_ManConst1( pNew );

    // create the family of shadow registers, then create the cascade of Xnor and And gates for the comparator 
            Saig_ManForEachLo( p, pObj, i )
            {
                pObjShadowLo = Aig_ObjCreatePi( pNew );

                #ifdef PROPAGATE_NAMES
                    Vec_PtrPush( vecLos, pObjShadowLo );
                    nodeName = (char *)malloc( strlen( Abc_ObjName( Abc_NtkCi( pNtk, Abc_NtkPiNum(pNtk) + i ) ) ) + 10 );
                    sprintf( nodeName, "%s__%s", Abc_ObjName( Abc_NtkCi( pNtk, Abc_NtkPiNum(pNtk) + i ) ), "SHADOW" );
                    
                    Vec_PtrPush( vecLoNames, nodeName );
                #endif

                pObjShadowLiDriver = Aig_Mux( pNew, pObjSaveAndNotSaved, (Aig_Obj_t *)pObj->pData, pObjShadowLo );
                pObjShadowLi = Aig_ObjCreatePo( pNew, pObjShadowLiDriver );
                nRegCount++;
                loCreated++; liCreated++;
        
                pObjXor = Aig_Exor( pNew, (Aig_Obj_t *)pObj->pData, pObjShadowLo );
                pObjXnor = Aig_Not( pObjXor );
                
                pObjAndAcc = Aig_And( pNew, pObjXnor, pObjAndAcc );
            }

            // create the AND gate whose output will be the signal "looped"
            pObjSavedLoAndEquality = Aig_And( pNew, pObjSavedLo, pObjAndAcc );

            // create the master AND gate and corresponding AND and OR logic for the liveness properties
            pObjAndAcc = Aig_ManConst1( pNew );
            if( vLive == NULL || Vec_PtrSize( vLive ) == 0 )
            {
                printf("Circuit without any liveness property\n");
            }
            else
            {
                Vec_PtrForEachEntry( Aig_Obj_t *, vLive, pObj, i )
                {
                    liveLatch++;
                    pDriverImage = Aig_NotCond((Aig_Obj_t *)Aig_Regular(Aig_ObjChild0( pObj ))->pData, Aig_ObjFaninC0(pObj));
                    pObjShadowLo = Aig_ObjCreatePi( pNew );

                    #ifdef PROPAGATE_NAMES
                        Vec_PtrPush( vecLos, pObjShadowLo );
                        nodeName = (char *)malloc( strlen( Abc_ObjName( Abc_NtkPo( pNtk, getPoIndex( p, pObj ) ) ) ) + 12 );
                        sprintf( nodeName, "%s__%s", Abc_ObjName( Abc_NtkPo( pNtk, getPoIndex( p, pObj ) ) ), "LIVENESS" );
                        Vec_PtrPush( vecLoNames, nodeName );
                    #endif

                    pObjShadowLiDriver = Aig_Or( pNew, pObjShadowLo, Aig_And( pNew, pDriverImage, pObjSaveOrSaved ) );
                    pObjShadowLi = Aig_ObjCreatePo( pNew, pObjShadowLiDriver );
                    nRegCount++;
                    loCreated++; liCreated++;
            
                    pObjAndAcc = Aig_And( pNew, pObjShadowLo, pObjAndAcc );
                }
            }

            pObjLive = pObjAndAcc;
                
            pObjAndAcc = Aig_ManConst1( pNew );
            if( vFair == NULL || Vec_PtrSize( vFair ) == 0 )
                printf("Circuit without any fairness property\n");
            else
            {
                Vec_PtrForEachEntry( Aig_Obj_t *, vFair, pObj, i )
                {
                    fairLatch++;
                    pDriverImage = Aig_NotCond((Aig_Obj_t *)Aig_Regular(Aig_ObjChild0( pObj ))->pData, Aig_ObjFaninC0(pObj));
                    pObjShadowLo = Aig_ObjCreatePi( pNew );

                    #ifdef PROPAGATE_NAMES
                        Vec_PtrPush( vecLos, pObjShadowLo );
                        nodeName = (char *)malloc( strlen( Abc_ObjName( Abc_NtkPo( pNtk, getPoIndex( p, pObj ) ) ) ) + 12 );
                        sprintf( nodeName, "%s__%s", Abc_ObjName( Abc_NtkPo( pNtk, getPoIndex( p, pObj ) ) ), "FAIRNESS" );
                        Vec_PtrPush( vecLoNames, nodeName );
                    #endif

                    pObjShadowLiDriver = Aig_Or( pNew, pObjShadowLo, Aig_And( pNew, pDriverImage, pObjSaveOrSaved ) );
                    pObjShadowLi = Aig_ObjCreatePo( pNew, pObjShadowLiDriver );
                    nRegCount++;
                    loCreated++; liCreated++;
            
                    pObjAndAcc = Aig_And( pNew, pObjShadowLo, pObjAndAcc );
                }
            }

            pObjFair = pObjAndAcc;
                
            //pObjSafetyGate = Aig_Exor( pNew, Aig_Not(Aig_ManConst1( pNew )), Aig_And( pNew, pObjSavedLoAndEquality, Aig_And( pNew, pObjFair, Aig_Not( pObjLive ) ) ) );
            //Following is the actual Biere translation
            pObjSafetyGate = Aig_And( pNew, pObjSavedLoAndEquality, Aig_And( pNew, pObjFair, Aig_Not( pObjLive ) ) );

            Aig_ObjPatchFanin0( pNew, pObjSafetyPropertyOutput, pObjSafetyGate );
        #endif
    }

    Aig_ManSetRegNum( pNew, nRegCount );

    Aig_ManPiCleanupBiere( pNew );
    Aig_ManPoCleanupBiere( pNew );
    
    Aig_ManCleanup( pNew );
    
    assert( Aig_ManCheck( pNew ) );
    
    if( mode == FULL_BIERE_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_MODE )
    {
            assert((Aig_Obj_t *)Vec_PtrEntry(pNew->vPos, Saig_ManPoNum(pNew)+Aig_ObjPioNum(pObjSavedLo)-Saig_ManPiNum(p)-1) == pObjSavedLi);
            assert( Saig_ManPiNum( p ) + 1 == Saig_ManPiNum( pNew ) );
            assert( Saig_ManRegNum( pNew ) == Saig_ManRegNum( p ) * 2 + 1 + liveLatch + fairLatch );
    }

    return pNew;
}





Aig_Man_t * LivenessToSafetyTransformationAbs( int mode, Abc_Ntk_t * pNtk, Aig_Man_t * p, Vec_Int_t *vFlops, 
                                           Vec_Ptr_t *vLive, Vec_Ptr_t *vFair, Vec_Ptr_t *vAssertSafety, Vec_Ptr_t *vAssumeSafety )
{
    Aig_Man_t * pNew;
    int i, nRegCount, iEntry;
    Aig_Obj_t * pObjSavePi;
    Aig_Obj_t *pObjSavedLo, *pObjSavedLi;
    Aig_Obj_t *pObj, *pMatch;
    Aig_Obj_t *pObjSaveOrSaved, *pObjSaveAndNotSaved, *pObjSavedLoAndEquality;
    Aig_Obj_t *pObjShadowLo, *pObjShadowLi, *pObjShadowLiDriver;
    Aig_Obj_t *pObjXor, *pObjXnor, *pObjAndAcc;
    Aig_Obj_t *pObjLive, *pObjFair, *pObjSafetyGate;
    Aig_Obj_t *pObjSafetyPropertyOutput;
    Aig_Obj_t *pDriverImage, *pArgument, *collectiveAssertSafety, *collectiveAssumeSafety;
    char *nodeName;
    int piCopied = 0, liCopied = 0, loCopied = 0, liCreated = 0, loCreated = 0, piVecIndex = 0, liveLatch = 0, fairLatch = 0;
    
    vecPis = Vec_PtrAlloc( Saig_ManPiNum( p ) + 1);
    vecPiNames = Vec_PtrAlloc( Saig_ManPiNum( p ) + 1);

    vecLos = Vec_PtrAlloc( Saig_ManRegNum( p ) + Vec_IntSize( vFlops ) + 1 + Vec_PtrSize( vLive ) + Vec_PtrSize( vFair ) );
    vecLoNames = Vec_PtrAlloc( Saig_ManRegNum( p ) + Vec_IntSize( vFlops ) + 1 + Vec_PtrSize( vLive ) + Vec_PtrSize( vFair ) );

    //****************************************************************
    // Step1: create the new manager
    // Note: The new manager is created with "2 * Aig_ManObjNumMax(p)"
    // nodes, but this selection is arbitrary - need to be justified
    //****************************************************************
    pNew = Aig_ManStart( 2 * Aig_ManObjNumMax(p) );
    pNew->pName = (char *)malloc( strlen( pNtk->pName ) + strlen("_l2s") + 1 );
    sprintf(pNew->pName, "%s_%s", pNtk->pName, "l2s");
    pNew->pSpec = NULL;
    
    //****************************************************************
    // Step 2: map constant nodes
    //****************************************************************
    pObj = Aig_ManConst1( p );
    pObj->pData = Aig_ManConst1( pNew );

    //****************************************************************
    // Step 3: create true PIs
    //****************************************************************
    Saig_ManForEachPi( p, pObj, i )
    {
        piCopied++;
        pObj->pData = Aig_ObjCreatePi(pNew);
        Vec_PtrPush( vecPis, pObj->pData );
        nodeName = Aig_UtilStrsav(Abc_ObjName( Abc_NtkPi( pNtk, i ) ));
        Vec_PtrPush( vecPiNames, nodeName );
    }

    //****************************************************************
    // Step 4: create the special Pi corresponding to SAVE
    //****************************************************************
    if( mode == FULL_BIERE_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_MODE )
    {
        pObjSavePi = Aig_ObjCreatePi( pNew );
        nodeName = "SAVE_BIERE",
        Vec_PtrPush( vecPiNames, nodeName );
    }
        
    //****************************************************************
    // Step 5: create register outputs
    //****************************************************************
    Saig_ManForEachLo( p, pObj, i )
    {
        loCopied++;
        pObj->pData = Aig_ObjCreatePi(pNew);
        Vec_PtrPush( vecLos, pObj->pData );
        nodeName = Aig_UtilStrsav(Abc_ObjName( Abc_NtkCi( pNtk, Abc_NtkPiNum(pNtk) + i ) ));
        Vec_PtrPush( vecLoNames, nodeName );
    }

    //****************************************************************
    // Step 6: create "saved" register output
    //****************************************************************
    if( mode == FULL_BIERE_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_MODE )
    {
        loCreated++;
        pObjSavedLo = Aig_ObjCreatePi( pNew );
        Vec_PtrPush( vecLos, pObjSavedLo );
        nodeName = "SAVED_LO";
        Vec_PtrPush( vecLoNames, nodeName );
    }

    //****************************************************************
    // Step 7: create the OR gate and the AND gate directly fed by "SAVE" Pi
    //****************************************************************
    if( mode == FULL_BIERE_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_MODE )
    {
        pObjSaveOrSaved = Aig_Or( pNew, pObjSavePi, pObjSavedLo );
        pObjSaveAndNotSaved = Aig_And( pNew, pObjSavePi, Aig_Not(pObjSavedLo) );
    }

    //********************************************************************
    // Step 8: create internal nodes
    //********************************************************************
    Aig_ManForEachNode( p, pObj, i )
    {
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    }

    
    //********************************************************************
    // Step 8.x : create PO for each safety assertions
    // NOTE : Here the output is purposely inverted as it will be thrown to 
    // dprove
    //********************************************************************
    if( mode == FULL_BIERE_MODE || mode == IGNORE_LIVENESS_KEEP_SAFETY_MODE )
    {
        if( Vec_PtrSize( vAssertSafety ) != 0 && Vec_PtrSize( vAssumeSafety ) == 0 )
        {
            pObjAndAcc = Aig_ManConst1( pNew );
            Vec_PtrForEachEntry( Aig_Obj_t *, vAssertSafety, pObj, i )
            {
                pArgument = Aig_NotCond( (Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0( pObj ) );
                pObjAndAcc = Aig_And( pNew, pArgument, pObjAndAcc );
            }
            Aig_ObjCreatePo( pNew, Aig_Not(pObjAndAcc) );
        }
        else if( Vec_PtrSize( vAssertSafety ) != 0 && Vec_PtrSize( vAssumeSafety ) != 0 )
        {
            pObjAndAcc = Aig_ManConst1( pNew );
            Vec_PtrForEachEntry( Aig_Obj_t *, vAssertSafety, pObj, i )
            {
                pArgument = Aig_NotCond( (Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0( pObj ) );
                pObjAndAcc = Aig_And( pNew, pArgument, pObjAndAcc );
            }
            collectiveAssertSafety = pObjAndAcc;

            pObjAndAcc = Aig_ManConst1( pNew );
            Vec_PtrForEachEntry( Aig_Obj_t *, vAssumeSafety, pObj, i )
            {
                pArgument = Aig_NotCond( (Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0( pObj ) );
                pObjAndAcc = Aig_And( pNew, pArgument, pObjAndAcc );
            }
            collectiveAssumeSafety = pObjAndAcc;
            Aig_ObjCreatePo( pNew, Aig_And( pNew, Aig_Not(collectiveAssertSafety), collectiveAssumeSafety ) );
        }
        else
        {
            printf("WARNING!! No safety property is found, a new (negated) constant 1 output is created\n");
            Aig_ObjCreatePo( pNew, Aig_Not( Aig_ManConst1(pNew) ) );
        }
    }

    //********************************************************************
    // Step 9: create the safety property output gate for the liveness properties
    // discuss with Sat/Alan for an alternative implementation
    //********************************************************************
    if( mode == FULL_BIERE_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_MODE )
    {
        pObjSafetyPropertyOutput = Aig_ObjCreatePo( pNew, (Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData );
    }

    // create register inputs for the original registers
    nRegCount = 0;
    
    Saig_ManForEachLo( p, pObj, i )
    {
        pMatch = Saig_ObjLoToLi( p, pObj );
        Aig_ObjCreatePo( pNew, Aig_NotCond((Aig_Obj_t *)Aig_ObjFanin0(pMatch)->pData, Aig_ObjFaninC0( pMatch ) ) );
        nRegCount++;
        liCopied++;
    }

    // create register input corresponding to the register "saved"
    if( mode == FULL_BIERE_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_MODE )
    {
        #ifndef DUPLICATE_CKT_DEBUG
            pObjSavedLi = Aig_ObjCreatePo( pNew, pObjSaveOrSaved );
            nRegCount++;
            liCreated++;

            //Changed on October 13, 2009
            //pObjAndAcc = NULL;
            pObjAndAcc = Aig_ManConst1( pNew );

    // create the family of shadow registers, then create the cascade of Xnor and And gates for the comparator 
            //Saig_ManForEachLo( p, pObj, i )
            Saig_ManForEachLo( p, pObj, i )
            {
                printf("Flop[%d] = %s\n", i, Abc_ObjName( Abc_NtkCi( pNtk, Abc_NtkPiNum(pNtk) + i ) ) );
            }
            Vec_IntForEachEntry( vFlops, iEntry, i )
            {
                pObjShadowLo = Aig_ObjCreatePi( pNew );
                pObj = Aig_ManLo( p, iEntry );

                #ifdef PROPAGATE_NAMES
                    Vec_PtrPush( vecLos, pObjShadowLo );
                    nodeName = (char *)malloc( strlen( Abc_ObjName( Abc_NtkCi( pNtk, Abc_NtkPiNum(pNtk) + iEntry ) ) ) + 10 );
                    sprintf( nodeName, "%s__%s", Abc_ObjName( Abc_NtkCi( pNtk, Abc_NtkPiNum(pNtk) + iEntry ) ), "SHADOW" );
                    printf("Flop copied [%d] = %s\n", iEntry, nodeName );
                    Vec_PtrPush( vecLoNames, nodeName );
                #endif

                pObjShadowLiDriver = Aig_Mux( pNew, pObjSaveAndNotSaved, (Aig_Obj_t *)pObj->pData, pObjShadowLo );
                pObjShadowLi = Aig_ObjCreatePo( pNew, pObjShadowLiDriver );
                nRegCount++;
                loCreated++; liCreated++;
        
                pObjXor = Aig_Exor( pNew, (Aig_Obj_t *)pObj->pData, pObjShadowLo );
                pObjXnor = Aig_Not( pObjXor );
                
                pObjAndAcc = Aig_And( pNew, pObjXnor, pObjAndAcc );
            }

            // create the AND gate whose output will be the signal "looped"
            pObjSavedLoAndEquality = Aig_And( pNew, pObjSavedLo, pObjAndAcc );

            // create the master AND gate and corresponding AND and OR logic for the liveness properties
            pObjAndAcc = Aig_ManConst1( pNew );
            if( vLive == NULL || Vec_PtrSize( vLive ) == 0 )
            {
                printf("Circuit without any liveness property\n");
            }
            else
            {
                Vec_PtrForEachEntry( Aig_Obj_t *, vLive, pObj, i )
                {
                    liveLatch++;
                    pDriverImage = Aig_NotCond((Aig_Obj_t *)Aig_Regular(Aig_ObjChild0( pObj ))->pData, Aig_ObjFaninC0(pObj));
                    pObjShadowLo = Aig_ObjCreatePi( pNew );

                    #ifdef PROPAGATE_NAMES
                        Vec_PtrPush( vecLos, pObjShadowLo );
                        nodeName = (char *)malloc( strlen( Abc_ObjName( Abc_NtkPo( pNtk, getPoIndex( p, pObj ) ) ) ) + 12 );
                        sprintf( nodeName, "%s__%s", Abc_ObjName( Abc_NtkPo( pNtk, getPoIndex( p, pObj ) ) ), "LIVENESS" );
                        Vec_PtrPush( vecLoNames, nodeName );
                    #endif

                    pObjShadowLiDriver = Aig_Or( pNew, pObjShadowLo, Aig_And( pNew, pDriverImage, pObjSaveOrSaved ) );
                    pObjShadowLi = Aig_ObjCreatePo( pNew, pObjShadowLiDriver );
                    nRegCount++;
                    loCreated++; liCreated++;
            
                    pObjAndAcc = Aig_And( pNew, pObjShadowLo, pObjAndAcc );
                }
            }

            pObjLive = pObjAndAcc;
                
            pObjAndAcc = Aig_ManConst1( pNew );
            if( vFair == NULL || Vec_PtrSize( vFair ) == 0 )
                printf("Circuit without any fairness property\n");
            else
            {
                Vec_PtrForEachEntry( Aig_Obj_t *, vFair, pObj, i )
                {
                    fairLatch++;
                    pDriverImage = Aig_NotCond((Aig_Obj_t *)Aig_Regular(Aig_ObjChild0( pObj ))->pData, Aig_ObjFaninC0(pObj));
                    pObjShadowLo = Aig_ObjCreatePi( pNew );

                    #ifdef PROPAGATE_NAMES
                        Vec_PtrPush( vecLos, pObjShadowLo );
                        nodeName = (char *)malloc( strlen( Abc_ObjName( Abc_NtkPo( pNtk, getPoIndex( p, pObj ) ) ) ) + 12 );
                        sprintf( nodeName, "%s__%s", Abc_ObjName( Abc_NtkPo( pNtk, getPoIndex( p, pObj ) ) ), "FAIRNESS" );
                        Vec_PtrPush( vecLoNames, nodeName );
                    #endif

                    pObjShadowLiDriver = Aig_Or( pNew, pObjShadowLo, Aig_And( pNew, pDriverImage, pObjSaveOrSaved ) );
                    pObjShadowLi = Aig_ObjCreatePo( pNew, pObjShadowLiDriver );
                    nRegCount++;
                    loCreated++; liCreated++;
            
                    pObjAndAcc = Aig_And( pNew, pObjShadowLo, pObjAndAcc );
                }
            }

            pObjFair = pObjAndAcc;
                
            //pObjSafetyGate = Aig_Exor( pNew, Aig_Not(Aig_ManConst1( pNew )), Aig_And( pNew, pObjSavedLoAndEquality, Aig_And( pNew, pObjFair, Aig_Not( pObjLive ) ) ) );
            //Following is the actual Biere translation
            pObjSafetyGate = Aig_And( pNew, pObjSavedLoAndEquality, Aig_And( pNew, pObjFair, Aig_Not( pObjLive ) ) );

            Aig_ObjPatchFanin0( pNew, pObjSafetyPropertyOutput, pObjSafetyGate );
        #endif
    }

    Aig_ManSetRegNum( pNew, nRegCount );

    Aig_ManPiCleanupBiere( pNew );
    Aig_ManPoCleanupBiere( pNew );
    
    Aig_ManCleanup( pNew );
    
    assert( Aig_ManCheck( pNew ) );
    
    if( mode == FULL_BIERE_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_MODE )
    {
            assert((Aig_Obj_t *)Vec_PtrEntry(pNew->vPos, Saig_ManPoNum(pNew)+Aig_ObjPioNum(pObjSavedLo)-Saig_ManPiNum(p)-1) == pObjSavedLi);
            assert( Saig_ManPiNum( p ) + 1 == Saig_ManPiNum( pNew ) );
            assert( Saig_ManRegNum( pNew ) == Saig_ManRegNum( p ) + Vec_IntSize( vFlops ) + 1 + liveLatch + fairLatch );
    }

    return pNew;
}



Aig_Man_t * LivenessToSafetyTransformationOneStepLoop( int mode, Abc_Ntk_t * pNtk, Aig_Man_t * p, 
                                                      Vec_Ptr_t *vLive, Vec_Ptr_t *vFair, Vec_Ptr_t *vAssertSafety, Vec_Ptr_t *vAssumeSafety )
{
    Aig_Man_t * pNew;
    int i, nRegCount;
    Aig_Obj_t * pObjSavePi;
    Aig_Obj_t *pObj, *pMatch;
    Aig_Obj_t *pObjSavedLoAndEquality;
    Aig_Obj_t *pObjXor, *pObjXnor, *pObjAndAcc, *pObjAndAccDummy;
    Aig_Obj_t *pObjLive, *pObjFair, *pObjSafetyGate;
    Aig_Obj_t *pObjSafetyPropertyOutput;
    Aig_Obj_t *pDriverImage;
    Aig_Obj_t *pObjCorrespondingLi;
    Aig_Obj_t *pArgument;
    Aig_Obj_t *collectiveAssertSafety, *collectiveAssumeSafety;

    char *nodeName;
    int piCopied = 0, liCopied = 0, loCopied = 0, liCreated = 0, loCreated = 0, piVecIndex = 0;

    if( Aig_ManRegNum( p ) == 0 )
    {
        printf("The input AIG contains no register, returning the original AIG as it is\n");
        return p;
    }

    vecPis = Vec_PtrAlloc( Saig_ManPiNum( p ) + 1);
    vecPiNames = Vec_PtrAlloc( Saig_ManPiNum( p ) + 1);

    vecLos = Vec_PtrAlloc( Saig_ManRegNum( p )*2 + 1 + Vec_PtrSize( vLive ) + Vec_PtrSize( vFair ) );
    vecLoNames = Vec_PtrAlloc( Saig_ManRegNum( p )*2 + 1 + Vec_PtrSize( vLive ) + Vec_PtrSize( vFair ) );

    //****************************************************************
    // Step1: create the new manager
    // Note: The new manager is created with "2 * Aig_ManObjNumMax(p)"
    // nodes, but this selection is arbitrary - need to be justified
    //****************************************************************
    pNew = Aig_ManStart( 2 * Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( "live2safe" );
    pNew->pSpec = NULL;
    
    //****************************************************************
    // Step 2: map constant nodes
    //****************************************************************
    pObj = Aig_ManConst1( p );
    pObj->pData = Aig_ManConst1( pNew );

    //****************************************************************
    // Step 3: create true PIs
    //****************************************************************
    Saig_ManForEachPi( p, pObj, i )
    {
        piCopied++;
        pObj->pData = Aig_ObjCreatePi(pNew);
        Vec_PtrPush( vecPis, pObj->pData );
        nodeName = Aig_UtilStrsav(Abc_ObjName( Abc_NtkPi( pNtk, i ) ));
        Vec_PtrPush( vecPiNames, nodeName );
    }

    //****************************************************************
    // Step 4: create the special Pi corresponding to SAVE
    //****************************************************************
    if( mode == FULL_BIERE_ONE_LOOP_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_ONE_LOOP_MODE )
    {
        pObjSavePi = Aig_ObjCreatePi( pNew );
        nodeName = "SAVE_BIERE",
        Vec_PtrPush( vecPiNames, nodeName );
    }
            
    //****************************************************************
    // Step 5: create register outputs
    //****************************************************************
    Saig_ManForEachLo( p, pObj, i )
    {
        loCopied++;
        pObj->pData = Aig_ObjCreatePi(pNew);
        Vec_PtrPush( vecLos, pObj->pData );
        nodeName = Aig_UtilStrsav(Abc_ObjName( Abc_NtkCi( pNtk, Abc_NtkPiNum(pNtk) + i ) ));
        Vec_PtrPush( vecLoNames, nodeName );
    }

    //****************************************************************
    // Step 6: create "saved" register output
    //****************************************************************

#if 0
    loCreated++;
    pObjSavedLo = Aig_ObjCreatePi( pNew );
    Vec_PtrPush( vecLos, pObjSavedLo );
    nodeName = "SAVED_LO";
    Vec_PtrPush( vecLoNames, nodeName );
#endif

    //****************************************************************
    // Step 7: create the OR gate and the AND gate directly fed by "SAVE" Pi
    //****************************************************************
#if 0
    pObjSaveOrSaved = Aig_Or( pNew, pObjSavePi, pObjSavedLo );
    pObjSaveAndNotSaved = Aig_And( pNew, pObjSavePi, Aig_Not(pObjSavedLo) );
#endif

    //********************************************************************
    // Step 8: create internal nodes
    //********************************************************************
    Aig_ManForEachNode( p, pObj, i )
    {
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    }

#if 0
    //********************************************************************
    // Step 8.x : create PO for each safety assertions
    //********************************************************************
    Vec_PtrForEachEntry( Aig_Obj_t *, vAssertSafety, pObj, i )
    {
        pObj->pData = Aig_ObjCreatePo( pNew, Aig_NotCond(Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0( pObj ) ) );
    }
#endif

    if( mode == FULL_BIERE_ONE_LOOP_MODE || mode == IGNORE_LIVENESS_KEEP_SAFETY_MODE )
    {
        if( Vec_PtrSize( vAssertSafety ) != 0 && Vec_PtrSize( vAssumeSafety ) == 0 )
        {
            pObjAndAcc = NULL;
            Vec_PtrForEachEntry( Aig_Obj_t *, vAssertSafety, pObj, i )
            {
                //pObj->pData = Aig_ObjCreatePo( pNew, Aig_NotCond(Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0( pObj ) ) );
                pArgument = Aig_NotCond( (Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0( pObj ) );
                if( pObjAndAcc == NULL )
                    pObjAndAcc = pArgument;
                else
                {
                    pObjAndAccDummy = pObjAndAcc;
                    pObjAndAcc = Aig_And( pNew, pArgument, pObjAndAccDummy );
                }
            }
            Aig_ObjCreatePo( pNew, Aig_Not(pObjAndAcc) );
        }
        else if( Vec_PtrSize( vAssertSafety ) != 0 && Vec_PtrSize( vAssumeSafety ) != 0 )
        {
            pObjAndAcc = NULL;
            Vec_PtrForEachEntry( Aig_Obj_t *, vAssertSafety, pObj, i )
            {
                //pObj->pData = Aig_ObjCreatePo( pNew, Aig_NotCond(Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0( pObj ) ) );
                pArgument = Aig_NotCond( (Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0( pObj ) );
                if( pObjAndAcc == NULL )
                    pObjAndAcc = pArgument;
                else
                {
                    pObjAndAccDummy = pObjAndAcc;
                    pObjAndAcc = Aig_And( pNew, pArgument, pObjAndAccDummy );
                }
            }
            collectiveAssertSafety = pObjAndAcc;
            pObjAndAcc = NULL;
            Vec_PtrForEachEntry( Aig_Obj_t *, vAssumeSafety, pObj, i )
            {
                //pObj->pData = Aig_ObjCreatePo( pNew, Aig_NotCond(Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0( pObj ) ) );
                pArgument = Aig_NotCond( (Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0( pObj ) );
                if( pObjAndAcc == NULL )
                    pObjAndAcc = pArgument;
                else
                {
                    pObjAndAccDummy = pObjAndAcc;
                    pObjAndAcc = Aig_And( pNew, pArgument, pObjAndAccDummy );
                }
            }
            collectiveAssumeSafety = pObjAndAcc;
            Aig_ObjCreatePo( pNew, Aig_And( pNew, Aig_Not(collectiveAssertSafety), collectiveAssumeSafety ) );
        }
        else
            printf("No safety property is specified, hence no safety gate is created\n");
    }

    //********************************************************************
    // Step 9: create the safety property output gate
    // create the safety property output gate, this will be the sole true PO 
    // of the whole circuit, discuss with Sat/Alan for an alternative implementation
    //********************************************************************

    if( mode == FULL_BIERE_ONE_LOOP_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_ONE_LOOP_MODE )
    {
        pObjSafetyPropertyOutput = Aig_ObjCreatePo( pNew, (Aig_Obj_t *)Aig_ObjFanin0(pObj)->pData );
    }

    // create register inputs for the original registers
    nRegCount = 0;
    
    Saig_ManForEachLo( p, pObj, i )
    {
        pMatch = Saig_ObjLoToLi( p, pObj );
        //Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pMatch) );
        Aig_ObjCreatePo( pNew, Aig_NotCond((Aig_Obj_t *)Aig_ObjFanin0(pMatch)->pData, Aig_ObjFaninC0( pMatch ) ) );
        nRegCount++;
        liCopied++;
    }

#if 0
    // create register input corresponding to the register "saved"
    pObjSavedLi = Aig_ObjCreatePo( pNew, pObjSaveOrSaved );
    nRegCount++;
    liCreated++;7
#endif

    pObjAndAcc = NULL;

    //****************************************************************************************************
    //For detection of loop of length 1 we do not need any shadow register, we only need equality detector
    //between Lo_j and Li_j and then a cascade of AND gates
    //****************************************************************************************************

    if( mode == FULL_BIERE_ONE_LOOP_MODE || mode == IGNORE_SAFETY_KEEP_LIVENESS_ONE_LOOP_MODE )
    {
        Saig_ManForEachLo( p, pObj, i )
        {
            pObjCorrespondingLi = Saig_ObjLoToLi( p, pObj );
        
            pObjXor = Aig_Exor( pNew, (Aig_Obj_t *)pObj->pData,  Aig_NotCond( (Aig_Obj_t *)Aig_ObjFanin0( pObjCorrespondingLi )->pData, Aig_ObjFaninC0( pObjCorrespondingLi ) ) );
            pObjXnor = Aig_Not( pObjXor );
        
            if( pObjAndAcc == NULL )
                pObjAndAcc = pObjXnor;
            else
            {
                pObjAndAccDummy = pObjAndAcc;
                pObjAndAcc = Aig_And( pNew, pObjXnor, pObjAndAccDummy );
            }
        }

        // create the AND gate whose output will be the signal "looped"
        pObjSavedLoAndEquality = Aig_And( pNew, pObjSavePi, pObjAndAcc );
    
        // create the master AND gate and corresponding AND and OR logic for the liveness properties
        pObjAndAcc = NULL;
        if( vLive == NULL || Vec_PtrSize( vLive ) == 0 )
            printf("Circuit without any liveness property\n");
        else
        {
            Vec_PtrForEachEntry( Aig_Obj_t *, vLive, pObj, i )
            {
                pDriverImage = Aig_NotCond((Aig_Obj_t *)Aig_Regular(Aig_ObjChild0( pObj ))->pData, Aig_ObjFaninC0(pObj));
                if( pObjAndAcc == NULL )
                    pObjAndAcc = pDriverImage;
                else
                {
                    pObjAndAccDummy = pObjAndAcc;
                    pObjAndAcc = Aig_And( pNew, pDriverImage, pObjAndAccDummy );
                }
            }
        }

        if( pObjAndAcc != NULL )
            pObjLive = pObjAndAcc;
        else
            pObjLive = Aig_ManConst1( pNew );
    
        // create the master AND gate and corresponding AND and OR logic for the fairness properties
        pObjAndAcc = NULL;
        if( vFair == NULL || Vec_PtrSize( vFair ) == 0 )
            printf("Circuit without any fairness property\n");
        else
        {
            Vec_PtrForEachEntry( Aig_Obj_t *, vFair, pObj, i )
            {
                pDriverImage = Aig_NotCond((Aig_Obj_t *)Aig_Regular(Aig_ObjChild0( pObj ))->pData, Aig_ObjFaninC0(pObj));
                if( pObjAndAcc == NULL )
                    pObjAndAcc = pDriverImage;
                else
                {
                    pObjAndAccDummy = pObjAndAcc;
                    pObjAndAcc = Aig_And( pNew, pDriverImage, pObjAndAccDummy );
                }
            }
        }

        if( pObjAndAcc != NULL )
            pObjFair = pObjAndAcc;
        else
            pObjFair = Aig_ManConst1( pNew );
    
        pObjSafetyGate = Aig_And( pNew, pObjSavedLoAndEquality, Aig_And( pNew, pObjFair, Aig_Not( pObjLive ) ) );
    
        Aig_ObjPatchFanin0( pNew, pObjSafetyPropertyOutput, pObjSafetyGate );
    }

    Aig_ManSetRegNum( pNew, nRegCount );

    //printf("\nSaig_ManPiNum = %d, Reg Num = %d, before everything, before Pi cleanup\n", Vec_PtrSize( pNew->vPis ), pNew->nRegs );

    Aig_ManPiCleanupBiere( pNew );
    Aig_ManPoCleanupBiere( pNew );

    Aig_ManCleanup( pNew );
    
    assert( Aig_ManCheck( pNew ) );
    
    return pNew;
}



Vec_Ptr_t * populateLivenessVector( Abc_Ntk_t *pNtk, Aig_Man_t *pAig )
{
    Abc_Obj_t * pNode;
    int i, liveCounter = 0;
    Vec_Ptr_t * vLive;

    vLive = Vec_PtrAlloc( 100 );
    Abc_NtkForEachPo( pNtk, pNode, i )
        //if( strstr( Abc_ObjName( pNode ), "assert_fair") != NULL )
        if( nodeName_starts_with( pNode, "assert_fair" ) )
        {
            Vec_PtrPush( vLive, Aig_ManPo( pAig, i ) );
            liveCounter++;
        }
    printf("Number of liveness property found = %d\n", liveCounter);
    return vLive;
}

Vec_Ptr_t * populateFairnessVector( Abc_Ntk_t *pNtk, Aig_Man_t *pAig )
{
    Abc_Obj_t * pNode;
    int i, fairCounter = 0;
    Vec_Ptr_t * vFair;

    vFair = Vec_PtrAlloc( 100 );
    Abc_NtkForEachPo( pNtk, pNode, i )
        //if( strstr( Abc_ObjName( pNode ), "assume_fair") != NULL )
        if( nodeName_starts_with( pNode, "assume_fair" ) )
        {
            Vec_PtrPush( vFair, Aig_ManPo( pAig, i ) );
            fairCounter++;
        }
    printf("Number of fairness property found = %d\n", fairCounter);
    return vFair;
}

Vec_Ptr_t * populateSafetyAssertionVector( Abc_Ntk_t *pNtk, Aig_Man_t *pAig )
{
    Abc_Obj_t * pNode;
    int i, assertSafetyCounter = 0;
    Vec_Ptr_t * vAssertSafety;

    vAssertSafety = Vec_PtrAlloc( 100 );
    Abc_NtkForEachPo( pNtk, pNode, i )
        //if( strstr( Abc_ObjName( pNode ), "Assert") != NULL )
        if( nodeName_starts_with( pNode, "assert_safety" ) || nodeName_starts_with( pNode, "Assert" ))
        {
            Vec_PtrPush( vAssertSafety, Aig_ManPo( pAig, i ) );
            assertSafetyCounter++;
        }
    printf("Number of safety property found = %d\n", assertSafetyCounter);
    return vAssertSafety;
}

Vec_Ptr_t * populateSafetyAssumptionVector( Abc_Ntk_t *pNtk, Aig_Man_t *pAig )
{
    Abc_Obj_t * pNode;
    int i, assumeSafetyCounter = 0;
    Vec_Ptr_t * vAssumeSafety;

    vAssumeSafety = Vec_PtrAlloc( 100 );
    Abc_NtkForEachPo( pNtk, pNode, i )
        //if( strstr( Abc_ObjName( pNode ), "Assert") != NULL )
        if( nodeName_starts_with( pNode, "assume_safety" ) || nodeName_starts_with( pNode, "Assume" ))
        {
            Vec_PtrPush( vAssumeSafety, Aig_ManPo( pAig, i ) );
            assumeSafetyCounter++;
        }
    printf("Number of assume_safety property found = %d\n", assumeSafetyCounter);
    return vAssumeSafety;
}

void updateNewNetworkNameManager( Abc_Ntk_t *pNtk, Aig_Man_t *pAig, Vec_Ptr_t *vPiNames, Vec_Ptr_t *vLoNames )
{
    Aig_Obj_t *pObj;
    Abc_Obj_t *pNode;
    int i, ntkObjId;

    pNtk->pManName = Nm_ManCreate( Abc_NtkCiNum( pNtk ) );

    if( vPiNames )
    {
        Saig_ManForEachPi( pAig, pObj, i )
        {
            ntkObjId = Abc_NtkCi( pNtk, i )->Id;
            //printf("Pi %d, Saved Name = %s, id = %d\n", i, Nm_ManStoreIdName( pNtk->pManName, ntkObjId, Aig_ObjType(pObj), Vec_PtrEntry(vPiNames, i), NULL ), ntkObjId);  
            Nm_ManStoreIdName( pNtk->pManName, ntkObjId, Aig_ObjType(pObj), (char *)Vec_PtrEntry(vPiNames, i), NULL );
        }
    }
    if( vLoNames )
    {
        Saig_ManForEachLo( pAig, pObj, i )
        {
            ntkObjId = Abc_NtkCi( pNtk, Saig_ManPiNum( pAig ) + i )->Id;
            //printf("Lo %d, Saved name = %s, id = %d\n", i, Nm_ManStoreIdName( pNtk->pManName, ntkObjId, Aig_ObjType(pObj), Vec_PtrEntry(vLoNames, i), NULL ), ntkObjId);  
            Nm_ManStoreIdName( pNtk->pManName, ntkObjId, Aig_ObjType(pObj), (char *)Vec_PtrEntry(vLoNames, i), NULL );
        }
    }

    Abc_NtkForEachPo(pNtk, pNode, i)
    {
        Abc_ObjAssignName(pNode, "assert_safety_", Abc_ObjName(pNode) );
    }

    // assign latch input names
    Abc_NtkForEachLatch(pNtk, pNode, i)
        if ( Nm_ManFindNameById(pNtk->pManName, Abc_ObjFanin0(pNode)->Id) == NULL )
            Abc_ObjAssignName( Abc_ObjFanin0(pNode), Abc_ObjName(Abc_ObjFanin0(pNode)), NULL );
}


int Abc_CommandAbcLivenessToSafety( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkTemp, *pNtkNew, *pNtkOld;
    Aig_Man_t * pAig, *pAigNew;
    int c;
    Vec_Ptr_t * vLive, * vFair, *vAssertSafety, *vAssumeSafety;
    int directive = -1;
                
    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    if( argc == 1 )
    {
        assert( directive == -1 );
        directive = FULL_BIERE_MODE;
    }
    else
    {
        Extra_UtilGetoptReset();
        while ( ( c = Extra_UtilGetopt( argc, argv, "1slh" ) ) != EOF )
        {
            switch( c )
            {
            case '1': 
                if( directive == -1 )
                    directive = FULL_BIERE_ONE_LOOP_MODE;
                else
                {
                    assert( directive == IGNORE_LIVENESS_KEEP_SAFETY_MODE || directive == IGNORE_SAFETY_KEEP_LIVENESS_MODE );
                    if( directive == IGNORE_LIVENESS_KEEP_SAFETY_MODE )
                        directive = IGNORE_LIVENESS_KEEP_SAFETY_MODE;
                    else
                        directive = IGNORE_SAFETY_KEEP_LIVENESS_ONE_LOOP_MODE;
                }
                break;
            case 's':
                if( directive == -1 )
                    directive = IGNORE_SAFETY_KEEP_LIVENESS_MODE;
                else
                {
                    if( directive != FULL_BIERE_ONE_LOOP_MODE )
                        goto usage;
                    assert(directive == FULL_BIERE_ONE_LOOP_MODE);
                    directive = IGNORE_SAFETY_KEEP_LIVENESS_ONE_LOOP_MODE;
                }
                break;
            case 'l':
                if( directive == -1 )
                    directive = IGNORE_LIVENESS_KEEP_SAFETY_MODE;
                else
                {
                    if( directive != FULL_BIERE_ONE_LOOP_MODE )
                        goto usage;
                    assert(directive == FULL_BIERE_ONE_LOOP_MODE);
                    directive = IGNORE_LIVENESS_KEEP_SAFETY_MODE;
                }
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
            }
        }
    }

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if( !Abc_NtkIsStrash( pNtk ) )
    {
        printf("The input network was not strashed, strashing....\n");
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );
        pNtkOld = pNtkTemp;
        pAig = Abc_NtkToDar( pNtkTemp, 0, 1 );
        vLive = populateLivenessVector( pNtk, pAig );
        vFair = populateFairnessVector( pNtk, pAig );
        vAssertSafety = populateSafetyAssertionVector( pNtk, pAig );
        vAssumeSafety = populateSafetyAssumptionVector( pNtk, pAig );
    }
    else
    {
        pAig = Abc_NtkToDar( pNtk, 0, 1 );
        pNtkOld = pNtk;
        vLive = populateLivenessVector( pNtk, pAig );
        vFair = populateFairnessVector( pNtk, pAig );
        vAssertSafety = populateSafetyAssertionVector( pNtk, pAig );
        vAssumeSafety = populateSafetyAssumptionVector( pNtk, pAig );
    }

    switch( directive )
    {
    case FULL_BIERE_MODE:
        //if( Vec_PtrSize(vLive) == 0 && Vec_PtrSize(vAssertSafety) == 0 )
        //{
        //    printf("Input circuit has NO safety and NO liveness property, original network is not disturbed\n");
        //    return 1;
        //}
        //else
        //{
            pAigNew = LivenessToSafetyTransformation( FULL_BIERE_MODE, pNtk, pAig, vLive, vFair, vAssertSafety, vAssumeSafety );
            if( Aig_ManRegNum(pAigNew) != 0 )
                printf("A new circuit is produced with\n\t2 POs - one for safety and one for liveness.\n\tone additional input is added (due to Biere's nondeterminism)\n\tshadow flops are not created if the original circuit is combinational\n\tnon-property POs are suppressed\n");
            break;
        //}
    case FULL_BIERE_ONE_LOOP_MODE:
        //if( Vec_PtrSize(vLive) == 0 && Vec_PtrSize(vAssertSafety) == 0 )
        //{
        //    printf("Input circuit has NO safety and NO liveness property, original network is not disturbed\n");
        //    return 1;
        //}
        //else
        //{
            pAigNew = LivenessToSafetyTransformationOneStepLoop( FULL_BIERE_ONE_LOOP_MODE, pNtk, pAig, vLive, vFair, vAssertSafety, vAssumeSafety );
            if( Aig_ManRegNum(pAigNew) != 0 )
                printf("A new circuit is produced with\n\t2 POs - one for safety and one for liveness.\n\tone additional input is added (due to Biere's nondeterminism)\n\tshadow flops are not created\n\tnon-property POs are suppressed\n");
            break;
        //}
    case IGNORE_LIVENESS_KEEP_SAFETY_MODE:
        //if( Vec_PtrSize(vAssertSafety) == 0 )
        //{    
        //    printf("Input circuit has NO safety property, original network is not disturbed\n");
        //    return 1;
        //}
        //else
        //{
            pAigNew = LivenessToSafetyTransformation( IGNORE_LIVENESS_KEEP_SAFETY_MODE, pNtk, pAig, vLive, vFair, vAssertSafety, vAssumeSafety );
            if( Aig_ManRegNum(pAigNew) != 0 )
                printf("A new circuit is produced with\n\t1 PO - only for safety property; liveness properties are ignored, if any.\n\tno additional input is added (due to Biere's nondeterminism)\n\tshadow flops are not created\n\tnon-property POs are suppressed\n");
            break;
        //}
    case IGNORE_SAFETY_KEEP_LIVENESS_MODE:
        //if( Vec_PtrSize(vLive) == 0 )
        //{    
        //    printf("Input circuit has NO liveness property, original network is not disturbed\n");
        //    return 1;
        //}
        //else
        //{
            pAigNew = LivenessToSafetyTransformation( IGNORE_SAFETY_KEEP_LIVENESS_MODE, pNtk, pAig, vLive, vFair, vAssertSafety, vAssumeSafety );
            if( Aig_ManRegNum(pAigNew) != 0 )
                printf("A new circuit is produced with\n\t1 PO - only for liveness property; safety properties are ignored, if any.\n\tone additional input is added (due to Biere's nondeterminism)\n\tshadow flops are not created if the original circuit is combinational\n\tnon-property POs are suppressed\n");
            break;
        //}
    case IGNORE_SAFETY_KEEP_LIVENESS_ONE_LOOP_MODE:
        //if( Vec_PtrSize(vLive) == 0 )
        //{
        //    printf("Input circuit has NO liveness property, original network is not disturbed\n");
        //    return 1;
        //}
        //else
        //{
            pAigNew = LivenessToSafetyTransformationOneStepLoop( IGNORE_SAFETY_KEEP_LIVENESS_ONE_LOOP_MODE, pNtk, pAig, vLive, vFair, vAssertSafety, vAssumeSafety );
            if( Aig_ManRegNum(pAigNew) != 0 )
                printf("New circuit is produced ignoring safety outputs!\nOnly liveness and fairness outputs are considered.\nShadow registers are not created\n");
            break;
        //}
    }

#if 0
    if( argc == 1 )
    {
        pAigNew = LivenessToSafetyTransformation( FULL_BIERE_MODE, pNtk, pAig, vLive, vFair, vAssertSafety, vAssumeSafety );
        if( Aig_ManRegNum(pAigNew) != 0 )
            printf("New circuit is produced considering all safety, liveness and fairness outputs.\nBiere's logic is created\n");
    }
    else 
    {
        Extra_UtilGetoptReset();
        c = Extra_UtilGetopt( argc, argv, "1lsh" );
        if( c == '1' )
        {
            if ( pNtk == NULL )
            {
                fprintf( pErr, "Empty network.\n" );
                return 1;
            }
            if( !Abc_NtkIsStrash( pNtk ) )
            {
                printf("The input network was not strashed, strashing....\n");
                pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );
                pNtkOld = pNtkTemp;
                pAig = Abc_NtkToDar( pNtkTemp, 0, 1 );
                vLive = populateLivenessVector( pNtk, pAig );
                vFair = populateFairnessVector( pNtk, pAig );
                vAssertSafety = populateSafetyAssertionVector( pNtk, pAig );
                vAssumeSafety = populateSafetyAssumptionVector( pNtk, pAig );
            }
            else
            {
                pAig = Abc_NtkToDar( pNtk, 0, 1 );
                pNtkOld = pNtk;
                vLive = populateLivenessVector( pNtk, pAig );
                vFair = populateFairnessVector( pNtk, pAig );
                vAssertSafety = populateSafetyAssertionVector( pNtk, pAig );
                vAssumeSafety = populateSafetyAssumptionVector( pNtk, pAig );
            }
            pAigNew = LivenessToSafetyTransformationOneStepLoop( pNtk, pAig, vLive, vFair, vAssertSafety, vAssumeSafety );
        }
        else if( c == 'l' )
        {
            if ( pNtk == NULL )
            {
                fprintf( pErr, "Empty network.\n" );
                return 1;
            }
            if( !Abc_NtkIsStrash( pNtk ) )
            {
                printf("The input network was not strashed, strashing....\n");
                pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );
                pNtkOld = pNtkTemp;
                pAig = Abc_NtkToDar( pNtkTemp, 0, 1 );
                vLive = populateLivenessVector( pNtk, pAig );
                vFair = populateFairnessVector( pNtk, pAig );
                vAssertSafety = populateSafetyAssertionVector( pNtk, pAig );
                vAssumeSafety = populateSafetyAssumptionVector( pNtk, pAig );
            }
            else
            {
                pAig = Abc_NtkToDar( pNtk, 0, 1 );
                pNtkOld = pNtk;
                vLive = populateLivenessVector( pNtk, pAig );
                vFair = populateFairnessVector( pNtk, pAig );
                vAssertSafety = populateSafetyAssertionVector( pNtk, pAig );
                vAssumeSafety = populateSafetyAssumptionVector( pNtk, pAig );
            }
            pAigNew = LivenessToSafetyTransformation( IGNORE_LIVENESS_KEEP_SAFETY_MODE, pNtk, pAig, vLive, vFair, vAssertSafety, vAssumeSafety );
            if( Aig_ManRegNum(pAigNew) != 0 )
                printf("New circuit is produced ignoring liveness outputs!\nOnly safety outputs are kept.\nBiere's logic is not created\n");
        }
        else if( c == 's' )
        {
            if ( pNtk == NULL )
            {
                fprintf( pErr, "Empty network.\n" );
                return 1;
            }
            
            if( !Abc_NtkIsStrash( pNtk ) )
            {
                printf("The input network was not strashed, strashing....\n");
                pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );
                pNtkOld = pNtkTemp;
                pAig = Abc_NtkToDar( pNtkTemp, 0, 1 );
                vLive = populateLivenessVector( pNtk, pAig );
                vFair = populateFairnessVector( pNtk, pAig );
                vAssertSafety = populateSafetyAssertionVector( pNtk, pAig );
                vAssumeSafety = populateSafetyAssumptionVector( pNtk, pAig );
            }
            else
            {
                pAig = Abc_NtkToDar( pNtk, 0, 1 );
                pNtkOld = pNtk;
                vLive = populateLivenessVector( pNtk, pAig );
                vFair = populateFairnessVector( pNtk, pAig );
                vAssertSafety = populateSafetyAssertionVector( pNtk, pAig );
                vAssumeSafety = populateSafetyAssumptionVector( pNtk, pAig );
            }
            pAigNew = LivenessToSafetyTransformation( IGNORE_SAFETY_KEEP_LIVENESS_MODE, pNtk, pAig, vLive, vFair, vAssertSafety, vAssumeSafety );
            if( Aig_ManRegNum(pAigNew) != 0 )
                printf("New circuit is produced ignoring safety outputs!\nOnly liveness and fairness outputs are considered.\nBiere's logic is created\n");
        }
        else if( c == 'h' )
            goto usage;
        else
            goto usage;
    }
#endif
    
#if 0
    Aig_ManPrintStats( pAigNew );
    printf("\nDetail statistics*************************************\n");
    printf("Number of true primary inputs = %d\n", Saig_ManPiNum( pAigNew ));
    printf("Number of true primary outputs = %d\n", Saig_ManPoNum( pAigNew ));
    printf("Number of true latch outputs = %d\n", Saig_ManCiNum( pAigNew ) - Saig_ManPiNum( pAigNew ));
    printf("Number of true latch inputs = %d\n", Saig_ManCoNum( pAigNew ) - Saig_ManPoNum( pAigNew ));
    printf("Numer of registers = %d\n", Saig_ManRegNum( pAigNew ) );
    printf("\n*******************************************************\n");
#endif

    pNtkNew = Abc_NtkFromAigPhase( pAigNew );
    pNtkNew->pName = Aig_UtilStrsav( pAigNew->pName );
    
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkCreateCone(): Network check has failed.\n" );
    
    updateNewNetworkNameManager( pNtkNew, pAigNew, vecPiNames, vecLoNames );
    Abc_FrameSetCurrentNetwork( pAbc, pNtkNew );

#if 0
#ifndef DUPLICATE_CKT_DEBUG
    Saig_ManForEachPi( pAigNew, pObj, i )
        assert( strcmp( (char *)Vec_PtrEntry(vecPiNames, i), retrieveTruePiName( pNtk, pAig, pAigNew, pObj ) ) == 0 );
        //printf("Name of %d-th Pi = %s, %s\n", i, retrieveTruePiName( pNtk, pAig, pAigNew, pObj ), (char *)Vec_PtrEntry(vecPiNames, i) );

    Saig_ManForEachLo( pAigNew, pObj, i )
        assert( strcmp( (char *)Vec_PtrEntry(vecLoNames, i), retrieveLOName( pNtk, pAig, pAigNew, pObj, vLive, vFair ) ) == 0 );
#endif    
#endif
        
    return 0;

usage:
    fprintf( stdout, "usage: l2s [-1lsh]\n" );
    fprintf( stdout, "\t         performs Armin Biere's live-to-safe transformation\n" );
    fprintf( stdout, "\t-1 : no shadow logic, presume all loops are self loops\n");
    fprintf( stdout, "\t-l : ignore liveness and fairness outputs\n");
    fprintf( stdout, "\t-s : ignore safety assertions and assumptions\n");
    fprintf( stdout, "\t-h : print command usage\n");
    return 1;
}

Vec_Int_t * prepareFlopVector( Aig_Man_t * pAig, int vectorLength )
{
    Vec_Int_t *vFlops;
    int i;

    vFlops = Vec_IntAlloc( vectorLength );

    for( i=0; i<vectorLength; i++ )
        Vec_IntPush( vFlops, i );

#if 0
    Vec_IntPush( vFlops, 19 );
    Vec_IntPush( vFlops, 20 );
    Vec_IntPush( vFlops, 23 );
    Vec_IntPush( vFlops, 24 );
    //Vec_IntPush( vFlops, 2 );
    //Vec_IntPush( vFlops, 3 );
    //Vec_IntPush( vFlops, 4 );
    //Vec_IntPush( vFlops, 5 );
    //Vec_IntPush( vFlops, 8 );
    //Vec_IntPush( vFlops, 9 );
    //Vec_IntPush( vFlops, 10 );
    //Vec_IntPush( vFlops, 11 );
    //Vec_IntPush( vFlops, 0 );
    //Vec_IntPush( vFlops, 0 );
#endif

    return vFlops;
}

int Abc_CommandAbcLivenessToSafetyAbstraction( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pOut, * pErr;
    Abc_Ntk_t * pNtk, * pNtkTemp, *pNtkNew, *pNtkOld;
    Aig_Man_t * pAig, *pAigNew;
    int c;
    Vec_Ptr_t * vLive, * vFair, *vAssertSafety, *vAssumeSafety;
    int directive = -1;
    Vec_Int_t * vFlops;
                
    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);

    if( argc == 1 )
    {
        assert( directive == -1 );
        directive = FULL_BIERE_MODE;
    }
    else
    {
        Extra_UtilGetoptReset();
        while ( ( c = Extra_UtilGetopt( argc, argv, "1slh" ) ) != EOF )
        {
            switch( c )
            {
            case '1': 
                if( directive == -1 )
                    directive = FULL_BIERE_ONE_LOOP_MODE;
                else
                {
                    assert( directive == IGNORE_LIVENESS_KEEP_SAFETY_MODE || directive == IGNORE_SAFETY_KEEP_LIVENESS_MODE );
                    if( directive == IGNORE_LIVENESS_KEEP_SAFETY_MODE )
                        directive = IGNORE_LIVENESS_KEEP_SAFETY_MODE;
                    else
                        directive = IGNORE_SAFETY_KEEP_LIVENESS_ONE_LOOP_MODE;
                }
                break;
            case 's':
                if( directive == -1 )
                    directive = IGNORE_SAFETY_KEEP_LIVENESS_MODE;
                else
                {
                    if( directive != FULL_BIERE_ONE_LOOP_MODE )
                        goto usage;
                    assert(directive == FULL_BIERE_ONE_LOOP_MODE);
                    directive = IGNORE_SAFETY_KEEP_LIVENESS_ONE_LOOP_MODE;
                }
                break;
            case 'l':
                if( directive == -1 )
                    directive = IGNORE_LIVENESS_KEEP_SAFETY_MODE;
                else
                {
                    if( directive != FULL_BIERE_ONE_LOOP_MODE )
                        goto usage;
                    assert(directive == FULL_BIERE_ONE_LOOP_MODE);
                    directive = IGNORE_LIVENESS_KEEP_SAFETY_MODE;
                }
                break;
            case 'h':
                goto usage;
            default:
                goto usage;
            }
        }
    }

    if ( pNtk == NULL )
    {
        fprintf( pErr, "Empty network.\n" );
        return 1;
    }
    if( !Abc_NtkIsStrash( pNtk ) )
    {
        printf("The input network was not strashed, strashing....\n");
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );
        pNtkOld = pNtkTemp;
        pAig = Abc_NtkToDar( pNtkTemp, 0, 1 );
        vLive = populateLivenessVector( pNtk, pAig );
        vFair = populateFairnessVector( pNtk, pAig );
        vAssertSafety = populateSafetyAssertionVector( pNtk, pAig );
        vAssumeSafety = populateSafetyAssumptionVector( pNtk, pAig );
    }
    else
    {
        pAig = Abc_NtkToDar( pNtk, 0, 1 );
        pNtkOld = pNtk;
        vLive = populateLivenessVector( pNtk, pAig );
        vFair = populateFairnessVector( pNtk, pAig );
        vAssertSafety = populateSafetyAssertionVector( pNtk, pAig );
        vAssumeSafety = populateSafetyAssumptionVector( pNtk, pAig );
    }

    vFlops = prepareFlopVector( pAig, Aig_ManRegNum(pAig)%2 == 0? Aig_ManRegNum(pAig)/2 : (Aig_ManRegNum(pAig)-1)/2);

    //vFlops = prepareFlopVector( pAig, 100 );

    switch( directive )
    {
    case FULL_BIERE_MODE:
        //if( Vec_PtrSize(vLive) == 0 && Vec_PtrSize(vAssertSafety) == 0 )
        //{
        //    printf("Input circuit has NO safety and NO liveness property, original network is not disturbed\n");
        //    return 1;
        //}
        //else
        //{
            pAigNew = LivenessToSafetyTransformationAbs( FULL_BIERE_MODE, pNtk, pAig, vFlops, vLive, vFair, vAssertSafety, vAssumeSafety );
            if( Aig_ManRegNum(pAigNew) != 0 )
                printf("A new circuit is produced with\n\t2 POs - one for safety and one for liveness.\n\tone additional input is added (due to Biere's nondeterminism)\n\tshadow flops are not created if the original circuit is combinational\n\tnon-property POs are suppressed\n");
            break;
        //}
    case FULL_BIERE_ONE_LOOP_MODE:
        //if( Vec_PtrSize(vLive) == 0 && Vec_PtrSize(vAssertSafety) == 0 )
        //{
        //    printf("Input circuit has NO safety and NO liveness property, original network is not disturbed\n");
        //    return 1;
        //}
        //else
        //{
            pAigNew = LivenessToSafetyTransformationOneStepLoop( FULL_BIERE_ONE_LOOP_MODE, pNtk, pAig, vLive, vFair, vAssertSafety, vAssumeSafety );
            if( Aig_ManRegNum(pAigNew) != 0 )
                printf("A new circuit is produced with\n\t2 POs - one for safety and one for liveness.\n\tone additional input is added (due to Biere's nondeterminism)\n\tshadow flops are not created\n\tnon-property POs are suppressed\n");
            break;
        //}
    case IGNORE_LIVENESS_KEEP_SAFETY_MODE:
        //if( Vec_PtrSize(vAssertSafety) == 0 )
        //{    
        //    printf("Input circuit has NO safety property, original network is not disturbed\n");
        //    return 1;
        //}
        //else
        //{
            pAigNew = LivenessToSafetyTransformationAbs( IGNORE_LIVENESS_KEEP_SAFETY_MODE, pNtk, pAig, vFlops, vLive, vFair, vAssertSafety, vAssumeSafety );
            if( Aig_ManRegNum(pAigNew) != 0 )
                printf("A new circuit is produced with\n\t1 PO - only for safety property; liveness properties are ignored, if any.\n\tno additional input is added (due to Biere's nondeterminism)\n\tshadow flops are not created\n\tnon-property POs are suppressed\n");
            break;
        //}
    case IGNORE_SAFETY_KEEP_LIVENESS_MODE:
        //if( Vec_PtrSize(vLive) == 0 )
        //{    
        //    printf("Input circuit has NO liveness property, original network is not disturbed\n");
        //    return 1;
        //}
        //else
        //{
            pAigNew = LivenessToSafetyTransformationAbs( IGNORE_SAFETY_KEEP_LIVENESS_MODE, pNtk, pAig, vFlops, vLive, vFair, vAssertSafety, vAssumeSafety );
            if( Aig_ManRegNum(pAigNew) != 0 )
                printf("A new circuit is produced with\n\t1 PO - only for liveness property; safety properties are ignored, if any.\n\tone additional input is added (due to Biere's nondeterminism)\n\tshadow flops are not created if the original circuit is combinational\n\tnon-property POs are suppressed\n");
            break;
        //}
    case IGNORE_SAFETY_KEEP_LIVENESS_ONE_LOOP_MODE:
        //if( Vec_PtrSize(vLive) == 0 )
        //{
        //    printf("Input circuit has NO liveness property, original network is not disturbed\n");
        //    return 1;
        //}
        //else
        //{
            pAigNew = LivenessToSafetyTransformationOneStepLoop( IGNORE_SAFETY_KEEP_LIVENESS_ONE_LOOP_MODE, pNtk, pAig, vLive, vFair, vAssertSafety, vAssumeSafety );
            if( Aig_ManRegNum(pAigNew) != 0 )
                printf("New circuit is produced ignoring safety outputs!\nOnly liveness and fairness outputs are considered.\nShadow registers are not created\n");
            break;
        //}
    }

    pNtkNew = Abc_NtkFromAigPhase( pAigNew );
    pNtkNew->pName = Aig_UtilStrsav( pAigNew->pName );
    
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkCreateCone(): Network check has failed.\n" );
    
    updateNewNetworkNameManager( pNtkNew, pAigNew, vecPiNames,vecLoNames );
    Abc_FrameSetCurrentNetwork( pAbc, pNtkNew );

#if 0
#ifndef DUPLICATE_CKT_DEBUG
    Saig_ManForEachPi( pAigNew, pObj, i )
        assert( strcmp( (char *)Vec_PtrEntry(vecPiNames, i), retrieveTruePiName( pNtk, pAig, pAigNew, pObj ) ) == 0 );
        //printf("Name of %d-th Pi = %s, %s\n", i, retrieveTruePiName( pNtk, pAig, pAigNew, pObj ), (char *)Vec_PtrEntry(vecPiNames, i) );

    Saig_ManForEachLo( pAigNew, pObj, i )
        assert( strcmp( (char *)Vec_PtrEntry(vecLoNames, i), retrieveLOName( pNtk, pAig, pAigNew, pObj, vLive, vFair ) ) == 0 );
#endif    
#endif
        
    return 0;

usage:
    fprintf( stdout, "usage: l2s [-1lsh]\n" );
    fprintf( stdout, "\t         performs Armin Biere's live-to-safe transformation\n" );
    fprintf( stdout, "\t-1 : no shadow logic, presume all loops are self loops\n");
    fprintf( stdout, "\t-l : ignore liveness and fairness outputs\n");
    fprintf( stdout, "\t-s : ignore safety assertions and assumptions\n");
    fprintf( stdout, "\t-h : print command usage\n");
    return 1;
}
ABC_NAMESPACE_IMPL_END

