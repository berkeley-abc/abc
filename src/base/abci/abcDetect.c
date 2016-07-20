/**CFile****************************************************************

  FileName    [abcDetect.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Detect conditions.]

  Author      [Alan Mishchenko, Dao Ai Quoc]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 7, 2016.]

  Revision    [$Id: abcDetect.c,v 1.00 2016/06/07 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "misc/vec/vecHsh.h"
#include "misc/util/utilNam.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"

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
    Vec_IntPushTwo( vPairs, -1, -1 );
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
            printf( "Cannot read type \"%s\" of object \"%s\".\n", pToken, Abc_ObjName(Abc_NtkObj(pNtk, iObj)) );
            continue;
        }
        Vec_IntPushTwo( vPairs, Vec_IntEntry(vMap, iObj), Type );
    }
    assert( Vec_IntSize(vPairs) == 2 * nLines );
    printf( "Finished reading %d lines.\n", nLines - 1 );

    // verify the reader by printing the results
    if ( fVerbose )
        Vec_IntForEachEntryDoubleStart( vPairs, iObj, Type, i, 2 )
            printf( "%-10d%-10s%-10s\n", i/2, Abc_ObjName(Abc_NtkObj(pNtk, iObj)), Io_WriteFinType(Type) );

finish:
    Vec_IntFree( vMap );
    Abc_NamDeref( pNam );
    fclose( pFile );
    return vPairs;
}


/**Function*************************************************************

  Synopsis    [Top-level procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkDetectClassesTest( Abc_Ntk_t * pNtk, int fSeq, int fVerbose )
{
    printf( "This procedure is currently not used.\n" );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

