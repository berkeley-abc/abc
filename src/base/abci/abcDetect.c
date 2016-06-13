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
#include "misc/util/utilNam.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef enum { 
    ABC_FIN_NONE = 0,      //  0:  unknown
    ABC_FIN_SA0,           //  1:
    ABC_FIN_SA1,           //  2:
    ABC_FIN_NEG,           //  3:
    ABC_FIN_RDOB_AND,      //  4:
    ABC_FIN_RDOB_NAND,     //  5:
    ABC_FIN_RDOB_OR,       //  6:
    ABC_FIN_RDOB_NOR,      //  7:
    ABC_FIN_RDOB_XOR,      //  8:
    ABC_FIN_RDOB_NXOR,     //  9:
    ABC_FIN_RDOB_NOT,      // 10:
    ABC_FIN_RDOB_BUFF,     // 11:
    ABC_FIN_RDOB_LAST      // 12:
} Abc_FinType_t;

typedef struct Fin_Info_t_
{
    Vec_Int_t * vPairs;    // original info as a set of pairs (ObjId, TypeId)
    Vec_Int_t * vObjs;     // all those objects that have some info 
    Vec_Wec_t * vMap;      // for each object, the set of types
    Vec_Wec_t * vClasses;  // classes of objects

} Abc_FinInfo_t;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Recognize type.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Io_ReadFinType( char * pThis )
{
    if ( !strcmp(pThis, "SA0") )        return ABC_FIN_SA0;
    if ( !strcmp(pThis, "SA1") )        return ABC_FIN_SA1;
    if ( !strcmp(pThis, "NEG") )        return ABC_FIN_NEG;
    if ( !strcmp(pThis, "RDOB_AND") )   return ABC_FIN_RDOB_AND;
    if ( !strcmp(pThis, "RDOB_NAND") )  return ABC_FIN_RDOB_NAND;
    if ( !strcmp(pThis, "RDOB_OR") )    return ABC_FIN_RDOB_OR;
    if ( !strcmp(pThis, "RDOB_NOR") )   return ABC_FIN_RDOB_NOR;
    if ( !strcmp(pThis, "RDOB_XOR") )   return ABC_FIN_RDOB_XOR;
    if ( !strcmp(pThis, "RDOB_NXOR") )  return ABC_FIN_RDOB_NXOR;
    if ( !strcmp(pThis, "RDOB_NOT") )   return ABC_FIN_RDOB_NOT;
    if ( !strcmp(pThis, "RDOB_BUFF") )  return ABC_FIN_RDOB_BUFF;
    return ABC_FIN_NONE;
}
char * Io_WriteFinType( int Type )
{
    if ( Type == ABC_FIN_SA0 )          return "SA0";
    if ( Type == ABC_FIN_SA1 )          return "SA1";
    if ( Type == ABC_FIN_NEG )          return "NEG";
    if ( Type == ABC_FIN_RDOB_AND  )    return "RDOB_AND" ;
    if ( Type == ABC_FIN_RDOB_NAND )    return "RDOB_NAND";
    if ( Type == ABC_FIN_RDOB_OR   )    return "RDOB_OR"  ;
    if ( Type == ABC_FIN_RDOB_NOR  )    return "RDOB_NOR" ;
    if ( Type == ABC_FIN_RDOB_XOR  )    return "RDOB_XOR" ;
    if ( Type == ABC_FIN_RDOB_NXOR )    return "RDOB_NXOR";
    if ( Type == ABC_FIN_RDOB_NOT  )    return "RDOB_NOT" ;
    if ( Type == ABC_FIN_RDOB_BUFF )    return "RDOB_BUFF";
    return "Unknown";
}

/**Function*************************************************************

  Synopsis    [Read information from file.]

  Description [Returns information as a set of pairs: (ObjId, TypeId).
  Uses the current network to map ObjName given in the file into ObjId.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Io_ReadFins( Abc_Ntk_t * pNtk, char * pFileName, int fVerbose )
{
    char Buffer[1000];
    Abc_Obj_t * pObj;
    Abc_Nam_t * pNam;
    Vec_Int_t * vMap; 
    Vec_Int_t * vPairs = NULL;
    int i, Type, iObj, fFound, nLines = 1;
    FILE * pFile = fopen( pFileName, "r" );
    if ( pFile == NULL )
    {
        printf( "Cannot open input file \"%s\" for reading.\n", pFileName );
        return NULL;
    }
    // map CI/node names into their IDs
    pNam = Abc_NamStart( 1000, 10 );
    vMap = Vec_IntAlloc( 1000 );
    Vec_IntPush( vMap, -1 );
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        if ( !Abc_ObjIsCi(pObj) && !Abc_ObjIsNode(pObj) )
            continue;
        Abc_NamStrFindOrAdd( pNam, Abc_ObjName(pObj), &fFound );
        if ( fFound )
        {
            printf( "The same name \"%s\" appears twice among CIs and internal nodes.\n", Abc_ObjName(pObj) );
            goto finish;
        }
        Vec_IntPush( vMap, Abc_ObjId(pObj) );
    }
    assert( Vec_IntSize(vMap) == Abc_NamObjNumMax(pNam) );
    // read file lines
    vPairs = Vec_IntAlloc( 1000 );
    while ( fgets(Buffer, 1000, pFile) != NULL )
    {
        // read line number
        char * pToken = strtok( Buffer, " \n\r\t" );
        if ( nLines++ != atoi(pToken) )
        {
            printf( "Line numbers are not consecutive. Quitting.\n" );
            Vec_IntFreeP( &vPairs );
            goto finish;
        }
        // read object name and find its ID
        pToken = strtok( NULL, " \n\r\t" );
        iObj = Abc_NamStrFind( pNam, pToken );
        if ( !iObj )
        {
            printf( "Cannot find object with name \"%s\".\n", pToken );
            continue;
        }
        // read type
        pToken = strtok( NULL, " \n\r\t" );
        Type = Io_ReadFinType( pToken );
        if ( Type == ABC_FIN_NONE )
        {
            printf( "Cannot read type \"%s\" of object \"%s\".\n", pToken, Abc_ObjName(pObj) );
            continue;
        }
        Vec_IntPushTwo( vPairs, Vec_IntEntry(vMap, iObj), Type );
    }
    printf( "Finished reading %d lines.\n", nLines - 1 );

    // verify the reader by printing the results
    if ( fVerbose )
        Vec_IntForEachEntryDouble( vPairs, iObj, Type, i )
            printf( "%-10d%-10s%-10s\n", i/2+1, Abc_ObjName(Abc_NtkObj(pNtk, iObj)), Io_WriteFinType(Type) );

finish:
    Vec_IntFree( vMap );
    Abc_NamDeref( pNam );
    fclose( pFile );
    return vPairs;
}


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

/**Function*************************************************************

  Synopsis    [Miter construction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkComputeObjects( Vec_Int_t * vPairs )
{
    int iObj, Type, i;
    Vec_Int_t * vObjs = Vec_IntAlloc( 100 );
    Vec_IntForEachEntryDouble( vPairs, iObj, Type, i )
        Vec_IntPush( vObjs, iObj );
    Vec_IntUniqify( vObjs );
    return vObjs;
}
Vec_Wec_t * Abc_NtkComputeObjInfo( Vec_Int_t * vPairs, int nObjs )
{
    int iObj, Type, i;
    Vec_Wec_t * vInfo = Vec_WecStart( nObjs );
    Vec_IntForEachEntryDouble( vPairs, iObj, Type, i )
        Vec_WecPush( vInfo, iObj, Type );
    return vInfo;
}
void Abc_NtkSolveClassesTest( Abc_Ntk_t * pNtk )
{
    Abc_FinInfo_t * p;
    if ( pNtk->vFins == NULL )
    {
        printf( "Current network does not have the required info.\n" );
        return;
    }
    // collect data
    p = ABC_CALLOC( Abc_FinInfo_t, 1 );
    p->vPairs   = pNtk->vFins;
    p->vObjs    = Abc_NtkComputeObjects( p->vPairs );
    p->vMap     = Abc_NtkComputeObjInfo( p->vPairs, Abc_NtkObjNumMax(pNtk) );
    p->vClasses = Abc_NtkDetectClasses( pNtk, p->vObjs );


    // cleanup
    Vec_WecFree( p->vClasses );
    Vec_WecFree( p->vMap );
    Vec_IntFree( p->vObjs );
    ABC_FREE( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

