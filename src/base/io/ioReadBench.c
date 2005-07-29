/**CFile****************************************************************

  FileName    [ioReadBench.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to read BENCH files.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioReadBench.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Ntk_t * Io_ReadBenchNetwork( Extra_FileReader_t * p );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Read the network from BENCH file.]

  Description [Currently works only for the miter cone.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Io_ReadBench( char * pFileName, int fCheck )
{
    Extra_FileReader_t * p;
    Abc_Ntk_t * pNtk;

    // start the file
    p = Extra_FileReaderAlloc( pFileName, "#", "\n", " \t\r,()=" );
    if ( p == NULL )
        return NULL;

    // read the network
    pNtk = Io_ReadBenchNetwork( p );
    Extra_FileReaderFree( p );
    if ( pNtk == NULL )
        return NULL;

    // make sure that everything is okay with the network structure
    if ( fCheck && !Abc_NtkCheck( pNtk ) )
    {
        printf( "Io_ReadBench: The network check has failed.\n" );
        Abc_NtkDelete( pNtk );
        return NULL;
    }
    return pNtk;
}
/**Function*************************************************************

  Synopsis    [Read the network from BENCH file.]

  Description [Currently works only for the miter cone.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Io_ReadBenchNetwork( Extra_FileReader_t * p )
{
    ProgressBar * pProgress;
    Vec_Ptr_t * vTokens;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pNet, * pLatch, * pNode;
    Vec_Str_t * vString;
    char * pType;
    int SymbolIn, SymbolOut, i, iLine;
    
    // allocate the empty network
    pNtk = Abc_NtkAlloc( ABC_NTK_NETLIST );

    // set the specs
    pNtk->pName = util_strsav( Extra_FileReaderGetFileName(p) );
    pNtk->pSpec = util_strsav( Extra_FileReaderGetFileName(p) );

    // go through the lines of the file
    vString = Vec_StrAlloc( 100 );
    pProgress = Extra_ProgressBarStart( stdout, Extra_FileReaderGetFileSize(p) );
    for ( iLine = 0; vTokens = Extra_FileReaderGetTokens(p); iLine++ )
    {
        Extra_ProgressBarUpdate( pProgress, Extra_FileReaderGetCurPosition(p), NULL );

        if ( vTokens->nSize == 1 )
        {
            printf( "%s: Wrong input file format.\n", Extra_FileReaderGetFileName(p) );
            Abc_NtkDelete( pNtk );
            return NULL;
        }

        // get the type of the line
        if ( strncmp( vTokens->pArray[0], "INPUT", 5 ) == 0 )
        {
            pNet = Abc_NtkFindOrCreateNet( pNtk, vTokens->pArray[1] );
            if ( Abc_ObjIsPi(pNet) )
                printf( "Warning: PI net \"%s\" appears twice in the list.\n", vTokens->pArray[1] );
            else
                Abc_NtkMarkNetPi( pNet );
        }
        else if ( strncmp( vTokens->pArray[0], "OUTPUT", 5 ) == 0 )
        {
            pNet = Abc_NtkFindOrCreateNet( pNtk, vTokens->pArray[1] );
            if ( Abc_ObjIsPo(pNet) )
                printf( "Warning: PO net \"%s\" appears twice in the list.\n", vTokens->pArray[1] );
            else
                Abc_NtkMarkNetPo( pNet );
        }
        else 
        {
            // get the node name and the node type
            pType = vTokens->pArray[1];
            if ( strcmp(pType, "DFF") == 0 )
            {
                // create a new node and add it to the network
                pLatch = Abc_NtkCreateLatch( pNtk );
                // create the LO (PI)
                pNet = Abc_NtkFindOrCreateNet( pNtk, vTokens->pArray[0] );
                Abc_ObjAddFanin( pNet, pLatch );
                Abc_ObjSetSubtype( pNet, ABC_OBJ_SUBTYPE_LO );
                // save the LI (PO)
                pNet = Abc_NtkFindOrCreateNet( pNtk, vTokens->pArray[2] );
                Abc_ObjAddFanin( pLatch, pNet );
                Abc_ObjSetSubtype( pNet, ABC_OBJ_SUBTYPE_LI );
            }
            else
            {
                // create a new node and add it to the network
                pNode = Abc_NtkCreateNode( pNtk );
                // get the input symbol to be inserted
                if ( !strncmp(pType, "BUF", 3) || !strcmp(pType, "AND") || !strcmp(pType, "NAND") )
                    SymbolIn = '1';
                else if ( !strncmp(pType, "NOT", 3) || !strcmp(pType, "OR") || !strcmp(pType, "NOR") )
                    SymbolIn = '0';
                else if ( !strcmp(pType, "XOR") || !strcmp(pType, "NXOR") )
                    SymbolIn = '*';
                else
                {
                    printf( "Cannot determine gate type \"%s\" in line %d.\n", pType, Extra_FileReaderGetLineNumber(p, 0) );
                    Abc_NtkDelete( pNtk );
                    return NULL;
                }
                // get the output symbol
                if ( !strcmp(pType, "NAND") || !strcmp(pType, "OR") || !strcmp(pType, "NXOR") )
                    SymbolOut = '0';
                else
                    SymbolOut = '1';

                // add the fanout net
                pNet = Abc_NtkFindOrCreateNet( pNtk, vTokens->pArray[0] );
                Abc_ObjAddFanin( pNet, pNode );
                // add the fanin nets
                for ( i = 2; i < vTokens->nSize; i++ )
                {
                    pNet = Abc_NtkFindOrCreateNet( pNtk, vTokens->pArray[i] );
                    Abc_ObjAddFanin( pNode, pNet );
                }
                if ( SymbolIn != '*' )
                {
                    // fill in the function
                    Vec_StrFill( vString, vTokens->nSize - 2, (char)SymbolIn );
                    Vec_StrPush( vString, ' ' );
                    Vec_StrPush( vString, (char)SymbolOut );
                    Vec_StrPush( vString, '\n' );
                    Vec_StrPush( vString, '\0' );
                    Abc_ObjSetData( pNode, Abc_SopRegister(pNtk->pManFunc, vString->pArray) );
                }
                else
                { // write XOR/NXOR gates
                    assert( i == 4 );
                    if ( SymbolOut == '1' )
                        Abc_ObjSetData( pNode, Abc_SopRegister(pNtk->pManFunc, "01 1\n10 1\n") );
                    else
                        Abc_ObjSetData( pNode, Abc_SopRegister(pNtk->pManFunc, "00 1\n11 1\n") );
                }
            }
        }
    }
    Extra_ProgressBarStop( pProgress );
    // check if constant have been added
    if ( pNet = Abc_NtkFindNet( pNtk, "vdd" ) )
    {
        // create the constant 1 node
        pNode = Abc_NtkCreateNode( pNtk );
        Abc_ObjAddFanin( pNet, pNode );
        Abc_ObjSetData( pNode, Abc_SopRegister(pNtk->pManFunc, " 1\n") );
    }
    if ( pNet = Abc_NtkFindNet( pNtk, "gnd" ) )
    {
        // create the constant 1 node
        pNode = Abc_NtkCreateNode( pNtk );
        Abc_ObjAddFanin( pNet, pNode );
        Abc_ObjSetData( pNode, Abc_SopRegister(pNtk->pManFunc, " 0\n") );
    }

    Io_ReadSetNonDrivenNets( pNtk );
    Vec_StrFree( vString );
    return pNtk;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////



