/**CFile****************************************************************

  FileName    [mainInit.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The main package.]

  Synopsis    [Initialization procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mainInit.c,v 1.3 2005/09/14 22:53:37 casem Exp $]

***********************************************************************/

#include "src/base/abc/abc.h"
#include "mainInt.h"

ABC_NAMESPACE_IMPL_START

 
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern void Abc_Init( Abc_Frame_t * pAbc );
extern void Abc_End ( Abc_Frame_t * pAbc );
extern void Io_Init( Abc_Frame_t * pAbc );
extern void Io_End ( Abc_Frame_t * pAbc );
extern void Cmd_Init( Abc_Frame_t * pAbc );
extern void Cmd_End ( Abc_Frame_t * pAbc );
extern void Fpga_Init( Abc_Frame_t * pAbc );
extern void Fpga_End ( Abc_Frame_t * pAbc );
extern void Map_Init( Abc_Frame_t * pAbc );
extern void Map_End ( Abc_Frame_t * pAbc );
extern void Mio_Init( Abc_Frame_t * pAbc );
extern void Mio_End ( Abc_Frame_t * pAbc );
extern void Super_Init( Abc_Frame_t * pAbc );
extern void Super_End ( Abc_Frame_t * pAbc );
extern void Libs_Init( Abc_Frame_t * pAbc );
extern void Libs_End( Abc_Frame_t * pAbc );
extern void Load_Init( Abc_Frame_t * pAbc );
extern void Load_End( Abc_Frame_t * pAbc );
extern void Test_Init( Abc_Frame_t * pAbc );
extern void Test_End( Abc_Frame_t * pAbc );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts all the packages.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameInit( Abc_Frame_t * pAbc )
{
    Cmd_Init( pAbc );
    Cmd_CommandExecute( pAbc, "set checkread" ); 
    Io_Init( pAbc );
    Abc_Init( pAbc );
    Fpga_Init( pAbc );
    Map_Init( pAbc );
    Mio_Init( pAbc );
    Super_Init( pAbc );
    Libs_Init( pAbc );
    Load_Init( pAbc );
    Test_Init( pAbc );
    EXT_ABC_INIT(pAbc) // plugin for external functionality
}


/**Function*************************************************************

  Synopsis    [Stops all the packages.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameEnd( Abc_Frame_t * pAbc )
{
    Abc_End( pAbc );
    Io_End( pAbc );
    Cmd_End( pAbc );
    Fpga_End( pAbc );
    Map_End( pAbc );
    Mio_End( pAbc );
    Super_End( pAbc );
    Libs_End( pAbc );
    Load_End( pAbc );
    Test_End( pAbc );
    EXT_ABC_END(pAbc) // plugin for external functionality
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

