/**CFile****************************************************************

  FileName    [abcDetect.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Detect conditions.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 7, 2016.]

  Revision    [$Id: abcDetect.c,v 1.00 2016/06/07 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "misc/vec/vecHsh.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Detect equivalence classes of nodes in terms of their TFO.]

  Description [Given is the logic network (pNtk) and the set of objects
  (primary inputs or internal nodes) to be considered (vObjs), this function
  returns a set of equivalence classes of these objects in terms of their 
  transitive fanout (TFO). Two objects belong to the same class if the set 
  of COs they feed into are the same.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkDetectClasses_rec( Abc_Obj_t * pObj, Vec_Int_t * vMap, Hsh_VecMan_t * pHash, Vec_Int_t * vTemp )
{
    Vec_Int_t * vArray, * vSet;
    Abc_Obj_t * pNext; int i;
    // get the CO set for this object
    int Entry = Vec_IntEntry(vMap, Abc_ObjId(pObj));
    if ( Entry != -1 ) // the set is already computed
        return Entry;
    // compute a new CO set
    assert( Abc_ObjIsCi(pObj) || Abc_ObjIsNode(pObj) );
    // if there is no fanouts, the set of COs is empty
    if ( Abc_ObjFanoutNum(pObj) == 0 )
    {
        Vec_IntWriteEntry( vMap, Abc_ObjId(pObj), 0 );
        return 0;
    }
    // compute the set for the first fanout
    Entry = Abc_NtkDetectClasses_rec( Abc_ObjFanout0(pObj), vMap, pHash, vTemp );
    if ( Abc_ObjFanoutNum(pObj) == 1 )
        return Entry;
    vSet = Vec_IntAlloc( 16 );
    // initialize the set with that of first fanout
    vArray = Hsh_VecReadEntry( pHash, Entry );
    Vec_IntClear( vSet );
    Vec_IntAppend( vSet, vArray );
    // iteratively add sets of other fanouts
    Abc_ObjForEachFanout( pObj, pNext, i )
    {
        if ( i == 0 ) 
            continue;
        Entry = Abc_NtkDetectClasses_rec( pNext, vMap, pHash, vTemp );
        vArray = Hsh_VecReadEntry( pHash, Entry );
        Vec_IntTwoMerge2( vSet, vArray, vTemp );
        ABC_SWAP( Vec_Int_t, *vSet, *vTemp );
    }
    // create or find new set and map the object into it
    Entry = Hsh_VecManAdd( pHash, vSet );
    Vec_IntWriteEntry( vMap, Abc_ObjId(pObj), Entry );
    Vec_IntFree( vSet );
    return Entry;
}
Vec_Wec_t * Abc_NtkDetectClasses( Abc_Ntk_t * pNtk, Vec_Int_t * vObjs )
{
    Vec_Wec_t * vClasses;   // classes of equivalence objects from vObjs
    Vec_Int_t * vClassMap;  // mapping of each CO set into its class in vClasses
    Vec_Int_t * vClass;     // one equivalence class     
    Abc_Obj_t * pObj; 
    int i, iObj, SetId, ClassId;
    // create hash table to hash sets of CO indexes
    Hsh_VecMan_t * pHash = Hsh_VecManStart( 1000 );
    // create elementary sets (each composed of one CO) and map COs into them
    Vec_Int_t * vMap = Vec_IntStartFull( Abc_NtkObjNumMax(pNtk) );
    Vec_Int_t * vSet = Vec_IntAlloc( 16 );
    assert( Abc_NtkIsLogic(pNtk) );
    // compute empty set
    SetId = Hsh_VecManAdd( pHash, vSet );
    assert( SetId == 0 );
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        Vec_IntFill( vSet, 1, i );
        SetId = Hsh_VecManAdd( pHash, vSet );
        Vec_IntWriteEntry( vMap, Abc_ObjId(pObj), SetId );
    }
    // make sure the array of objects is sorted
    Vec_IntSort( vObjs, 0 );
    // begin from the objects and map their IDs into sets of COs
    Abc_NtkForEachObjVec( vObjs, pNtk, pObj, i )
        Abc_NtkDetectClasses_rec( pObj, vMap, pHash, vSet );
    Vec_IntFree( vSet );
    // create map for mapping CO set its their classes
    vClassMap = Vec_IntStartFull( Hsh_VecSize(pHash) + 1 );
    // collect classes of objects
    vClasses = Vec_WecAlloc( 1000 );
    Vec_IntForEachEntry( vObjs, iObj, i )
    {
        // for a given object (iObj), find the ID of its COs set
        SetId = Vec_IntEntry( vMap, iObj );
        assert( SetId >= 0 );
        // for the given CO set, finds its equivalence class
        ClassId = Vec_IntEntry( vClassMap, SetId );
        if ( ClassId == -1 )  // there is no equivalence class
        {
            // map this CO set into a new equivalence class
            Vec_IntWriteEntry( vClassMap, SetId, Vec_WecSize(vClasses) );
            vClass = Vec_WecPushLevel( vClasses );
        }
        else // get hold of the equivalence class
            vClass = Vec_WecEntry( vClasses, ClassId );
        // add objects to the class
        Vec_IntPush( vClass, iObj );
        // print the set for this object
        //printf( "Object %5d : ", iObj );
        //Vec_IntPrint( Hsh_VecReadEntry(pHash, SetId) );
    }
    Hsh_VecManStop( pHash );
    Vec_IntFree( vClassMap );
    Vec_IntFree( vMap );
    return vClasses;
}
void Abc_NtkDetectClassesTest( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vObjs;
    Vec_Wec_t * vRes;
    // for testing, create the set of object IDs for all combinational inputs (CIs)
    Abc_Obj_t * pObj; int i;
    vObjs = Vec_IntAlloc( Abc_NtkCiNum(pNtk) );
    Abc_NtkForEachCi( pNtk, pObj, i )
        Vec_IntPush( vObjs, Abc_ObjId(pObj) );
    // compute equivalence classes of CIs and print them
    vRes = Abc_NtkDetectClasses( pNtk, vObjs );
    Vec_WecPrint( vRes, 0 );
    // clean up
    Vec_IntFree( vObjs );
    Vec_WecFree( vRes );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

