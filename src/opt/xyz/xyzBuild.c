/**CFile****************************************************************

  FileName    [xyzBuild.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cover manipulation package.]

  Synopsis    [Network construction procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: xyzBuild.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "xyz.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Derives the decomposed network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkXyzDeriveCube( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj, Min_Cube_t * pCube, Vec_Int_t * vSupp )
{
    Vec_Int_t * vLits;
    Abc_Obj_t * pNodeNew, * pFanin;
    int i, iFanin, Lit;
    // create empty cube
    if ( pCube->nLits == 0 )
        return Abc_NodeCreateConst1(pNtkNew);
    // get the literals of this cube
    vLits = Vec_IntAlloc( 10 );
    Min_CubeGetLits( pCube, vLits );
    assert( pCube->nLits == (unsigned)vLits->nSize );
    // create special case when there is only one literal
    if ( pCube->nLits == 1 )
    {
        iFanin = Vec_IntEntry(vLits,0);
        pFanin = Abc_NtkObj( pObj->pNtk, Vec_IntEntry(vSupp, iFanin) );
        Lit = Min_CubeGetVar(pCube, iFanin);
        assert( Lit == 1 || Lit == 2 );
        Vec_IntFree( vLits );
        if ( Lit == 1 )// negative
            return Abc_NodeCreateInv( pNtkNew, pFanin->pCopy );
        return pFanin->pCopy;
    }
    assert( pCube->nLits > 1 );
    // create the AND cube
    pNodeNew = Abc_NtkCreateNode( pNtkNew );
    for ( i = 0; i < vLits->nSize; i++ )
    {
        iFanin = Vec_IntEntry(vLits,i);
        pFanin = Abc_NtkObj( pObj->pNtk, Vec_IntEntry(vSupp, iFanin) );
        Lit = Min_CubeGetVar(pCube, iFanin);
        assert( Lit == 1 || Lit == 2 );
        Vec_IntWriteEntry( vLits, i, Lit==1 );
        Abc_ObjAddFanin( pNodeNew, pFanin->pCopy );
    }
    pNodeNew->pData = Abc_SopCreateAnd( pNtkNew->pManFunc, vLits->nSize, vLits->pArray );
    Vec_IntFree( vLits );
    return pNodeNew;
}

/**Function*************************************************************

  Synopsis    [Derives the decomposed network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkXyzDeriveNode_rec( Xyz_Man_t * p, Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj, int Level )
{
    Min_Cube_t * pCover, * pCube;
    Abc_Obj_t * pFaninNew, * pNodeNew, * pFanin;
    Vec_Int_t * vSupp;
    int Entry, nCubes, i;

    if ( Abc_ObjIsCi(pObj) )
        return pObj->pCopy;
    assert( Abc_ObjIsNode(pObj) );
    // skip if already computed
    if ( pObj->pCopy )
        return pObj->pCopy;

    // get the support and the cover
    vSupp  = Abc_ObjGetSupp( pObj ); 
    pCover = Abc_ObjGetCover2( pObj );
    assert( vSupp );
/*
    if ( pCover &&  pCover->nVars - Min_CoverSuppVarNum(p->pManMin, pCover) > 0 )
    {
        printf( "%d\n ", pCover->nVars - Min_CoverSuppVarNum(p->pManMin, pCover) );
        Min_CoverWrite( stdout, pCover );
    }
*/
/*
    // print the support of this node
    printf( "{ " );
    Vec_IntForEachEntry( vSupp, Entry, i )
        printf( "%d ", Entry );
    printf( "}  cubes = %d\n", Min_CoverCountCubes( pCover ) );
*/
    // process the fanins
    Vec_IntForEachEntry( vSupp, Entry, i )
    {
        pFanin = Abc_NtkObj(pObj->pNtk, Entry);
        Abc_NtkXyzDeriveNode_rec( p, pNtkNew, pFanin, Level+1 );
    }

    // for each cube, construct the node
    nCubes = Min_CoverCountCubes( pCover );
    if ( nCubes == 0 )
        pNodeNew = Abc_NodeCreateConst0(pNtkNew);
    else if ( nCubes == 1 )
        pNodeNew = Abc_NtkXyzDeriveCube( pNtkNew, pObj, pCover, vSupp );
    else
    {
        pNodeNew = Abc_NtkCreateNode( pNtkNew );
        Min_CoverForEachCube( pCover, pCube )
        {
            pFaninNew = Abc_NtkXyzDeriveCube( pNtkNew, pObj, pCube, vSupp );
            Abc_ObjAddFanin( pNodeNew, pFaninNew );
        }
        pNodeNew->pData = Abc_SopCreateXorSpecial( pNtkNew->pManFunc, nCubes );
    }
/*
    printf( "Created node %d(%d) at level %d: ", pNodeNew->Id, pObj->Id, Level );
    Vec_IntForEachEntry( vSupp, Entry, i )
    {
        pFanin = Abc_NtkObj(pObj->pNtk, Entry);
        printf( "%d(%d) ", pFanin->pCopy->Id, pFanin->Id );
    }
    printf( "\n" );
    Min_CoverWrite( stdout, pCover );
*/
    pObj->pCopy = pNodeNew;
    return pNodeNew;
}

/**Function*************************************************************

  Synopsis    [Derives the decomposed network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkXyzDerive( Xyz_Man_t * p, Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkIsStrash(pNtk) );
    // perform strashing
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    // reconstruct the network
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        Abc_NtkXyzDeriveNode_rec( p, pNtkNew, Abc_ObjFanin0(pObj), 0 );
//        printf( "*** CO %s : %d -> %d \n", Abc_ObjName(pObj), pObj->pCopy->Id, Abc_ObjFanin0(pObj)->pCopy->Id );
    }
    // add the COs
    Abc_NtkFinalize( pNtk, pNtkNew );
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 1 );
    // make sure everything is okay
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkXyzDerive: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}




/**Function*************************************************************

  Synopsis    [Derives the decomposed network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkXyzDeriveInv( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj, int fCompl )
{
    assert( pObj->pCopy );
    if ( !fCompl )
        return pObj->pCopy;
    if ( pObj->pCopy->pCopy == NULL )
        pObj->pCopy->pCopy = Abc_NodeCreateInv( pNtkNew, pObj->pCopy );
    return pObj->pCopy->pCopy;
 }

/**Function*************************************************************

  Synopsis    [Derives the decomposed network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkXyzDeriveCubeInv( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj, Min_Cube_t * pCube, Vec_Int_t * vSupp )
{
    Vec_Int_t * vLits;
    Abc_Obj_t * pNodeNew, * pFanin;
    int i, iFanin, Lit;
    // create empty cube
    if ( pCube->nLits == 0 )
        return Abc_NodeCreateConst1(pNtkNew);
    // get the literals of this cube
    vLits = Vec_IntAlloc( 10 );
    Min_CubeGetLits( pCube, vLits );
    assert( pCube->nLits == (unsigned)vLits->nSize );
    // create special case when there is only one literal
    if ( pCube->nLits == 1 )
    {
        iFanin = Vec_IntEntry(vLits,0);
        pFanin = Abc_NtkObj( pObj->pNtk, Vec_IntEntry(vSupp, iFanin) );
        Lit = Min_CubeGetVar(pCube, iFanin);
        assert( Lit == 1 || Lit == 2 );
        Vec_IntFree( vLits );
//        if ( Lit == 1 )// negative
//            return Abc_NodeCreateInv( pNtkNew, pFanin->pCopy );
//        return pFanin->pCopy;
        return Abc_NtkXyzDeriveInv( pNtkNew, pFanin, Lit==1 );
    }
    assert( pCube->nLits > 1 );
    // create the AND cube
    pNodeNew = Abc_NtkCreateNode( pNtkNew );
    for ( i = 0; i < vLits->nSize; i++ )
    {
        iFanin = Vec_IntEntry(vLits,i);
        pFanin = Abc_NtkObj( pObj->pNtk, Vec_IntEntry(vSupp, iFanin) );
        Lit = Min_CubeGetVar(pCube, iFanin);
        assert( Lit == 1 || Lit == 2 );
        Vec_IntWriteEntry( vLits, i, Lit==1 );
//        Abc_ObjAddFanin( pNodeNew, pFanin->pCopy );
        Abc_ObjAddFanin( pNodeNew, Abc_NtkXyzDeriveInv( pNtkNew, pFanin, Lit==1 ) );
    }
//    pNodeNew->pData = Abc_SopCreateAnd( pNtkNew->pManFunc, vLits->nSize, vLits->pArray );
    pNodeNew->pData = Abc_SopCreateAnd( pNtkNew->pManFunc, vLits->nSize, NULL );
    Vec_IntFree( vLits );
    return pNodeNew;
}

/**Function*************************************************************

  Synopsis    [Derives the decomposed network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkXyzDeriveNodeInv_rec( Xyz_Man_t * p, Abc_Ntk_t * pNtkNew, Abc_Obj_t * pObj, int fCompl )
{
    Min_Cube_t * pCover, * pCube;
    Abc_Obj_t * pFaninNew, * pNodeNew, * pFanin;
    Vec_Int_t * vSupp;
    int Entry, nCubes, i;

    // skip if already computed
    if ( pObj->pCopy )
        return Abc_NtkXyzDeriveInv( pNtkNew, pObj, fCompl );
    assert( Abc_ObjIsNode(pObj) );

    // get the support and the cover
    vSupp  = Abc_ObjGetSupp( pObj ); 
    pCover = Abc_ObjGetCover2( pObj );
    assert( vSupp );

    // process the fanins
    Vec_IntForEachEntry( vSupp, Entry, i )
    {
        pFanin = Abc_NtkObj(pObj->pNtk, Entry);
        Abc_NtkXyzDeriveNodeInv_rec( p, pNtkNew, pFanin, 0 );
    }

    // for each cube, construct the node
    nCubes = Min_CoverCountCubes( pCover );
    if ( nCubes == 0 )
        pNodeNew = Abc_NodeCreateConst0(pNtkNew);
    else if ( nCubes == 1 )
        pNodeNew = Abc_NtkXyzDeriveCubeInv( pNtkNew, pObj, pCover, vSupp );
    else
    {
        pNodeNew = Abc_NtkCreateNode( pNtkNew );
        Min_CoverForEachCube( pCover, pCube )
        {
            pFaninNew = Abc_NtkXyzDeriveCubeInv( pNtkNew, pObj, pCube, vSupp );
            Abc_ObjAddFanin( pNodeNew, pFaninNew );
        }
        pNodeNew->pData = Abc_SopCreateXorSpecial( pNtkNew->pManFunc, nCubes );
    }

    pObj->pCopy = pNodeNew;
    return Abc_NtkXyzDeriveInv( pNtkNew, pObj, fCompl );
}

/**Function*************************************************************

  Synopsis    [Derives the decomposed network.]

  Description [The resulting network contains only pure AND/OR/EXOR gates
  and inverters. This procedure is usedful to generate Verilog.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkXyzDeriveClean( Xyz_Man_t * p, Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObj, * pNodeNew;
    int i;
    assert( Abc_NtkIsStrash(pNtk) );
    // perform strashing
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_SOP );
    // reconstruct the network
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        pNodeNew = Abc_NtkXyzDeriveNodeInv_rec( p, pNtkNew, Abc_ObjFanin0(pObj), Abc_ObjFaninC0(pObj) );
        Abc_ObjAddFanin( pObj->pCopy, pNodeNew );
    }
    // add the COs
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 0 );
    // make sure everything is okay
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkXyzDeriveInv: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


