/**CFile****************************************************************

  FileName    [ioaReadAiger.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to read binary AIGER format developed by
  Armin Biere, Johannes Kepler University (http://fmv.jku.at/)]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - December 16, 2006.]

  Revision    [$Id: ioaReadAiger.c,v 1.00 2006/12/16 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ioa.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

unsigned Ioa_ReadAigerDecode( char ** ppPos );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reads the AIG in the binary AIGER format.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ioa_ReadAiger( char * pFileName, int fCheck )
{
    Bar_Progress_t * pProgress;
    FILE * pFile;
    Vec_Ptr_t * vNodes, * vDrivers;//, * vTerms;
    Aig_Obj_t * pObj, * pNode0, * pNode1;
    Aig_Man_t * pManNew;
    int nTotal, nInputs, nOutputs, nLatches, nAnds, nFileSize, i;//, iTerm, nDigits;
    char * pContents, * pDrivers, * pSymbols, * pCur, * pName;//, * pType;
    unsigned uLit0, uLit1, uLit;

    // read the file into the buffer
    nFileSize = Ioa_FileSize( pFileName );
    pFile = fopen( pFileName, "rb" );
    pContents = ALLOC( char, nFileSize );
    fread( pContents, nFileSize, 1, pFile );
    fclose( pFile );

    // check if the input file format is correct
    if ( strncmp(pContents, "aig", 3) != 0 )
    {
        fprintf( stdout, "Wrong input file format.\n" );
        return NULL;
    }

    // read the file type
    pCur = pContents;         while ( *pCur++ != ' ' );
    // read the number of objects
    nTotal = atoi( pCur );    while ( *pCur++ != ' ' );
    // read the number of inputs
    nInputs = atoi( pCur );   while ( *pCur++ != ' ' );
    // read the number of latches
    nLatches = atoi( pCur );  while ( *pCur++ != ' ' );
    // read the number of outputs
    nOutputs = atoi( pCur );  while ( *pCur++ != ' ' );
    // read the number of nodes
    nAnds = atoi( pCur );     while ( *pCur++ != '\n' );  
    // check the parameters
    if ( nTotal != nInputs + nLatches + nAnds )
    {
        fprintf( stdout, "The paramters are wrong.\n" );
        return NULL;
    }

    // allocate the empty AIG
    pManNew = Aig_ManStart( nAnds );
    pName = Ioa_FileNameGeneric( pFileName );
    pManNew->pName = Aig_UtilStrsav( pName );
//    pManNew->pSpec = Ioa_UtilStrsav( pFileName );
    free( pName );

    // prepare the array of nodes
    vNodes = Vec_PtrAlloc( 1 + nInputs + nLatches + nAnds );
    Vec_PtrPush( vNodes, Aig_ManConst0(pManNew) );

    // create the PIs
    for ( i = 0; i < nInputs + nLatches; i++ )
    {
        pObj = Aig_ObjCreatePi(pManNew);    
        Vec_PtrPush( vNodes, pObj );
    }
/*
    // create the POs
    for ( i = 0; i < nOutputs + nLatches; i++ )
    {
        pObj = Aig_ObjCreatePo(pManNew);   
    }
*/
    // create the latches
    pManNew->nRegs = nLatches;
/*
    nDigits = Ioa_Base10Log( nLatches );
    for ( i = 0; i < nLatches; i++ )
    {
        pObj = Aig_ObjCreateLatch(pManNew);
        Aig_LatchSetInit0( pObj );
        pNode0 = Aig_ObjCreateBi(pManNew);
        pNode1 = Aig_ObjCreateBo(pManNew);
        Aig_ObjAddFanin( pObj, pNode0 );
        Aig_ObjAddFanin( pNode1, pObj );
        Vec_PtrPush( vNodes, pNode1 );
        // assign names to latch and its input
//        Aig_ObjAssignName( pObj, Aig_ObjNameDummy("_L", i, nDigits), NULL );
//        printf( "Creating latch %s with input %d and output %d.\n", Aig_ObjName(pObj), pNode0->Id, pNode1->Id );
    } 
*/
    
    // remember the beginning of latch/PO literals
    pDrivers = pCur;

    // scroll to the beginning of the binary data
    for ( i = 0; i < nLatches + nOutputs; )
        if ( *pCur++ == '\n' )
            i++;

    // create the AND gates
    pProgress = Bar_ProgressStart( stdout, nAnds );
    for ( i = 0; i < nAnds; i++ )
    {
        Bar_ProgressUpdate( pProgress, i, NULL );
        uLit = ((i + 1 + nInputs + nLatches) << 1);
        uLit1 = uLit  - Ioa_ReadAigerDecode( &pCur );
        uLit0 = uLit1 - Ioa_ReadAigerDecode( &pCur );
//        assert( uLit1 > uLit0 );
        pNode0 = Aig_NotCond( Vec_PtrEntry(vNodes, uLit0 >> 1), uLit0 & 1 );
        pNode1 = Aig_NotCond( Vec_PtrEntry(vNodes, uLit1 >> 1), uLit1 & 1 );
        assert( Vec_PtrSize(vNodes) == i + 1 + nInputs + nLatches );
        Vec_PtrPush( vNodes, Aig_And(pManNew, pNode0, pNode1) );
    }
    Bar_ProgressStop( pProgress );

    // remember the place where symbols begin
    pSymbols = pCur;

    // read the latch driver literals
    vDrivers = Vec_PtrAlloc( nLatches + nOutputs );
    pCur = pDrivers;
//    Aig_ManForEachLatchInput( pManNew, pObj, i )
    for ( i = 0; i < nLatches; i++ )
    {
        uLit0 = atoi( pCur );  while ( *pCur++ != '\n' );
        pNode0 = Aig_NotCond( Vec_PtrEntry(vNodes, uLit0 >> 1), (uLit0 & 1) );//^ (uLit0 < 2) );
//        Aig_ObjAddFanin( pObj, pNode0 );
        Vec_PtrPush( vDrivers, pNode0 );
    }
    // read the PO driver literals
//    Aig_ManForEachPo( pManNew, pObj, i )
    for ( i = 0; i < nOutputs; i++ )
    {
        uLit0 = atoi( pCur );  while ( *pCur++ != '\n' );
        pNode0 = Aig_NotCond( Vec_PtrEntry(vNodes, uLit0 >> 1), (uLit0 & 1) );//^ (uLit0 < 2) );
//        Aig_ObjAddFanin( pObj, pNode0 );
        Vec_PtrPush( vDrivers, pNode0 );
    }


    // create the POs
    for ( i = 0; i < nOutputs; i++ )
        Aig_ObjCreatePo( pManNew, Vec_PtrEntry(vDrivers, nLatches + i) );
    for ( i = 0; i < nLatches; i++ )
        Aig_ObjCreatePo( pManNew, Vec_PtrEntry(vDrivers, i) );
    Vec_PtrFree( vDrivers );

/*
    // read the names if present
    pCur = pSymbols;
    if ( *pCur != 'c' )
    {
        int Counter = 0;
        while ( pCur < pContents + nFileSize && *pCur != 'c' )
        {
            // get the terminal type
            pType = pCur;
            if ( *pCur == 'i' )
                vTerms = pManNew->vPis;
            else if ( *pCur == 'l' )
                vTerms = pManNew->vBoxes;
            else if ( *pCur == 'o' )
                vTerms = pManNew->vPos;
            else
            {
                fprintf( stdout, "Wrong terminal type.\n" );
                return NULL;
            }
            // get the terminal number
            iTerm = atoi( ++pCur );  while ( *pCur++ != ' ' );
            // get the node
            if ( iTerm >= Vec_PtrSize(vTerms) )
            {
                fprintf( stdout, "The number of terminal is out of bound.\n" );
                return NULL;
            }
            pObj = Vec_PtrEntry( vTerms, iTerm );
            if ( *pType == 'l' )
                pObj = Aig_ObjFanout0(pObj);
            // assign the name
            pName = pCur;          while ( *pCur++ != '\n' );
            // assign this name 
            *(pCur-1) = 0;
            Aig_ObjAssignName( pObj, pName, NULL );
            if ( *pType == 'l' )
            {
                Aig_ObjAssignName( Aig_ObjFanin0(pObj), Aig_ObjName(pObj), "L" );
                Aig_ObjAssignName( Aig_ObjFanin0(Aig_ObjFanin0(pObj)), Aig_ObjName(pObj), "_in" );
            }
            // mark the node as named
            pObj->pCopy = (Aig_Obj_t *)Aig_ObjName(pObj);
        } 

        // assign the remaining names
        Aig_ManForEachPi( pManNew, pObj, i )
        {
            if ( pObj->pCopy ) continue;
            Aig_ObjAssignName( pObj, Aig_ObjName(pObj), NULL );
            Counter++;
        }
        Aig_ManForEachLatchOutput( pManNew, pObj, i )
        {
            if ( pObj->pCopy ) continue;
            Aig_ObjAssignName( pObj, Aig_ObjName(pObj), NULL );
            Aig_ObjAssignName( Aig_ObjFanin0(pObj), Aig_ObjName(pObj), "L" );
            Aig_ObjAssignName( Aig_ObjFanin0(Aig_ObjFanin0(pObj)), Aig_ObjName(pObj), "_in" );
            Counter++;
        }
        Aig_ManForEachPo( pManNew, pObj, i )
        {
            if ( pObj->pCopy ) continue;
            Aig_ObjAssignName( pObj, Aig_ObjName(pObj), NULL );
            Counter++;
        }
        if ( Counter )
            printf( "Ioa_ReadAiger(): Added %d default names for nameless I/O/register objects.\n", Counter );
    }
    else
    {
//        printf( "Ioa_ReadAiger(): I/O/register names are not given. Generating short names.\n" );
        Aig_ManShortNames( pManNew );
    }
*/

    // skipping the comments
    free( pContents );
    Vec_PtrFree( vNodes );

    // remove the extra nodes
    Aig_ManCleanup( pManNew );

    // check the result
    if ( fCheck && !Aig_ManCheck( pManNew ) )
    {
        printf( "Ioa_ReadAiger: The network check has failed.\n" );
        Aig_ManStop( pManNew );
        return NULL;
    }
    return pManNew;
}


/**Function*************************************************************

  Synopsis    [Extracts one unsigned AIG edge from the input buffer.]

  Description [This procedure is a slightly modified version of Armin Biere's
  procedure "unsigned decode (FILE * file)". ]
  
  SideEffects [Updates the current reading position.]

  SeeAlso     []

***********************************************************************/
unsigned Ioa_ReadAigerDecode( char ** ppPos )
{
    unsigned x = 0, i = 0;
    unsigned char ch;

//    while ((ch = getnoneofch (file)) & 0x80)
    while ((ch = *(*ppPos)++) & 0x80)
        x |= (ch & 0x7f) << (7 * i++);

    return x | (ch << (7 * i));
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


