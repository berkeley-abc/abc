/**CFile****************************************************************

  FileName    [wlnRtl.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Word-level network.]

  Synopsis    [Constructing WLN network from Rtl data structure.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 23, 2018.]

  Revision    [$Id: wlnRtl.c,v 1.00 2018/09/23 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wln.h"
#include "base/main/main.h"

#ifdef WIN32
#include <process.h> 
#define unlink _unlink
#else
#include <unistd.h>
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Wln_Ntk_t * Wln_ReadRtl( char * pFileName )
{
    return NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Wln_GetYosysName()
{
    char * pYosysName = NULL;
    char * pYosysNameWin = "yosys.exe";
    char * pYosysNameUnix = "yosys";
    if ( Abc_FrameReadFlag("yosyswin") )
        pYosysNameWin = Abc_FrameReadFlag("yosyswin");
    if ( Abc_FrameReadFlag("yosysunix") )
        pYosysNameUnix = Abc_FrameReadFlag("yosysunix");
#ifdef WIN32
    pYosysName = pYosysNameWin;
#else
    pYosysName = pYosysNameUnix;
#endif
    return pYosysName;
}
int Wln_ConvertToRtl( char * pCommand, char * pFileTemp )
{
    FILE * pFile;
    if ( system( pCommand ) == -1 )
    {
        fprintf( stdout, "Cannot execute \"%s\".\n", pCommand );
        return 0;
    }
    if ( (pFile = fopen(pFileTemp, "r")) == NULL )
    {
        fprintf( stdout, "Cannot open intermediate file \"%s\".\n", pFileTemp );
        return 0;
    }
    fclose( pFile );
    return 1;
}
Wln_Ntk_t * Wln_ReadSystemVerilog( char * pFileName, char * pTopModule, int fVerbose )
{
    Wln_Ntk_t * pNtk = NULL;
    char Command[1000];
    char * pFileTemp = "_temp_.rtlil";
    int fSVlog = strstr(pFileName, ".sv") != NULL;
    sprintf( Command, "%s -qp \"read_verilog %s%s; hierarchy %s%s; flatten; proc; write_rtlil %s\"", 
        Wln_GetYosysName(), fSVlog ? "-sv ":"", pFileName, 
        pTopModule ? "-top " : "-auto-top", pTopModule ? pTopModule : "", pFileTemp );
    if ( fVerbose )
    printf( "%s\n", Command );
    if ( !Wln_ConvertToRtl(Command, pFileTemp) )
    {
        return NULL;
    }
    pNtk = Wln_ReadRtl( pFileTemp );
    if ( pNtk == NULL )
    {
        printf( "Dumped the design into file \"%s\".\n", pFileTemp );
        return NULL;
    }
    unlink( pFileTemp );
    return pNtk;
}
Gia_Man_t * Wln_BlastSystemVerilog( char * pFileName, char * pTopModule, int fSkipStrash, int fInvert, int fTechMap, int fVerbose )
{
    Gia_Man_t * pGia = NULL;
    char Command[1000];
    char * pFileTemp = "_temp_.aig";
    int fSVlog = strstr(pFileName, ".sv") != NULL;
    sprintf( Command, "%s -qp \"read_verilog %s%s; hierarchy %s%s; flatten; proc; %saigmap; write_aiger %s\"", 
        Wln_GetYosysName(), fSVlog ? "-sv ":"", pFileName, 
        pTopModule ? "-top " : "-auto-top", pTopModule ? pTopModule : "", fTechMap ? "techmap; setundef -zero; " : "", pFileTemp );
    if ( fVerbose )
    printf( "%s\n", Command );
    if ( !Wln_ConvertToRtl(Command, pFileTemp) )
        return NULL;
    pGia = Gia_AigerRead( pFileTemp, 0, fSkipStrash, 0 );
    if ( pGia == NULL )
    {
        printf( "Converting to AIG has failed.\n" );
        return NULL;
    }
    ABC_FREE( pGia->pName );
    pGia->pName = pTopModule ? Abc_UtilStrsav(pTopModule) :
        Extra_FileNameGeneric( Extra_FileNameWithoutPath(pFileName) );
    unlink( pFileTemp );
    // complement the outputs
    if ( fInvert )
    {
        Gia_Obj_t * pObj; int i;
        Gia_ManForEachPo( pGia, pObj, i )
            Gia_ObjFlipFaninC0( pObj );
    }
    return pGia;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

