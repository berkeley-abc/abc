/**CFile****************************************************************

  FileName    [mainFrame.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [The main package.]

  Synopsis    [The global framework resides in this file.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: mainFrame.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "mainInt.h"
#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Frame_t * Abc_FrameGlobalFrame = 0;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Frame_t * Abc_FrameAllocate()
{
    Abc_Frame_t * p;

    // allocate and clean
    p = ALLOC( Abc_Frame_t, 1 );
    memset( p, 0, sizeof(Abc_Frame_t) );
    // get version
    p->sVersion = Abc_UtilsGetVersion( p );
    // set streams
    p->Err = stderr;
    p->Out = stdout;
    p->Hst = NULL;
    // set the starting step
    p->nSteps = 1;
    p->fBatchMode = 0;
    return p;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameDeallocate( Abc_Frame_t * p )
{
    Abc_FrameDeleteAllNetworks( p );
    free( p );
    p = NULL;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameRestart( Abc_Frame_t * p )
{
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_FrameReadNet( Abc_Frame_t * p )
{
    return p->pNtkCur;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
FILE * Abc_FrameReadOut( Abc_Frame_t * p )
{
    return p->Out;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
FILE * Abc_FrameReadErr( Abc_Frame_t * p )
{
    return p->Err;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_FrameReadMode( Abc_Frame_t * p )
{
    int fShortNames;
    char * pValue;
    pValue = Cmd_FlagReadByName( p, "namemode" );
    if ( pValue == NULL )
        fShortNames = 0;
    else 
        fShortNames = atoi(pValue);
    return fShortNames;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_FrameSetMode( Abc_Frame_t * p, bool fNameMode )
{
    char Buffer[2];
    bool fNameModeOld;
    fNameModeOld = Abc_FrameReadMode( p );
    Buffer[0] = '0' + fNameMode;
    Buffer[1] = 0;
    Cmd_FlagUpdateValue( p, "namemode", (char *)Buffer );
    return fNameModeOld;
}


/**Function*************************************************************

  Synopsis    [Sets the given network to be the current one.]

  Description [Takes the network and makes it the current network.
  The previous current network is attached to the given network as 
  a backup copy. In the stack of backup networks contains too many
  networks (defined by the paramater "savesteps"), the bottom
  most network is deleted.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameSetCurrentNetwork( Abc_Frame_t * p, Abc_Ntk_t * pNtkNew )
{
    Abc_Ntk_t * pNtk, * pNtk2, * pNtk3;
    int nNetsPresent;
    int nNetsToSave;
    char * pValue;

    // link it to the previous network
    Abc_NtkSetBackup( pNtkNew, p->pNtkCur );
    // set the step of this network
    Abc_NtkSetStep( pNtkNew, ++p->nSteps );
    // set this network to be the current network
    p->pNtkCur = pNtkNew;

    // remove any extra network that may happen to be in the stack
    pValue = Cmd_FlagReadByName( p, "savesteps" );
    // if the value of steps to save is not set, assume 1-level undo
    if ( pValue == NULL )
        nNetsToSave = 1;
    else 
        nNetsToSave = atoi(pValue);
    
    // count the network, remember the last one, and the one before the last one
    nNetsPresent = 0;
    pNtk2 = pNtk3 = NULL;
    for ( pNtk = p->pNtkCur; pNtk; pNtk = Abc_NtkBackup(pNtk2) )
    {
        nNetsPresent++;
        pNtk3 = pNtk2;
        pNtk2 = pNtk;
    }

    // remove the earliest backup network if it is more steps away than we store
    if ( nNetsPresent - 1 > nNetsToSave )
    { // delete the last network
        Abc_NtkDelete( pNtk2 );
        // clean the pointer of the network before the last one
        Abc_NtkSetBackup( pNtk3, NULL );
    }
}

/**Function*************************************************************

  Synopsis    [This procedure swaps the current and the backup network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameSwapCurrentAndBackup( Abc_Frame_t * p )
{
    Abc_Ntk_t * pNtkCur, * pNtkBack, * pNtkBack2;
    int iStepCur, iStepBack;

    pNtkCur  = p->pNtkCur;
    pNtkBack = Abc_NtkBackup( pNtkCur );
    iStepCur = Abc_NtkStep  ( pNtkCur );

    // if there is no backup nothing to reset
    if ( pNtkBack == NULL )
        return;

    // remember the backup of the backup
    pNtkBack2 = Abc_NtkBackup( pNtkBack );
    iStepBack = Abc_NtkStep  ( pNtkBack );

    // set pNtkCur to be the next after the backup's backup
    Abc_NtkSetBackup( pNtkCur, pNtkBack2 );
    Abc_NtkSetStep  ( pNtkCur, iStepBack );

    // set pNtkCur to be the next after the backup
    Abc_NtkSetBackup( pNtkBack, pNtkCur );
    Abc_NtkSetStep  ( pNtkBack, iStepCur );

    // set the current network
    p->pNtkCur = pNtkBack;
}


/**Function*************************************************************

  Synopsis    [Replaces the current network by the given one.]

  Description [This procedure does not modify the stack of saved
  networks.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameReplaceCurrentNetwork( Abc_Frame_t * p, Abc_Ntk_t * pNtk )
{
    if ( pNtk == NULL )
        return;

    // transfer the parameters to the new network
    if ( p->pNtkCur )
    {
        Abc_NtkSetBackup( pNtk, Abc_NtkBackup(p->pNtkCur) );
        Abc_NtkSetStep( pNtk, Abc_NtkStep(p->pNtkCur) );
        // delete the current network
        Abc_NtkDelete( p->pNtkCur );
    }
    else
    {
        Abc_NtkSetBackup( pNtk, NULL );
        Abc_NtkSetStep( pNtk, ++p->nSteps );
    }
    // set the new current network
    p->pNtkCur = pNtk;
}

/**Function*************************************************************

  Synopsis    [Removes library binding of all currently stored networks.]

  Description [This procedure is called when the library is freed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameUnmapAllNetworks( Abc_Frame_t * p )
{
    Abc_Ntk_t * pNtk;
    for ( pNtk = p->pNtkCur; pNtk; pNtk = Abc_NtkBackup(pNtk) )
        if ( Abc_NtkIsLogicMap(pNtk) )
            Abc_NtkUnmap( pNtk );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameDeleteAllNetworks( Abc_Frame_t * p )
{
    Abc_Ntk_t * pNtk, * pNtk2;
    // delete all the currently saved networks
    for ( pNtk  = p->pNtkCur, 
          pNtk2 = pNtk? Abc_NtkBackup(pNtk): NULL; 
          pNtk; 
          pNtk  = pNtk2, 
          pNtk2 = pNtk? Abc_NtkBackup(pNtk): NULL )
        Abc_NtkDelete( pNtk );
    // set the current network empty
    p->pNtkCur = NULL;
    fprintf( p->Out, "All networks have been deleted.\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameSetGlobalFrame( Abc_Frame_t * p )
{
    Abc_FrameGlobalFrame = p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Frame_t * Abc_FrameGetGlobalFrame()
{
    if ( Abc_FrameGlobalFrame == 0 )
    {
        // start the framework
        Abc_FrameGlobalFrame = Abc_FrameAllocate();
        // perform initializations
        Abc_FrameInit( Abc_FrameGlobalFrame );
    }
    return Abc_FrameGlobalFrame;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_FrameReadNtkStore       ( Abc_Frame_t * pFrame )                     { return pFrame->pStored;  } 
int         Abc_FrameReadNtkStoreSize   ( Abc_Frame_t * pFrame )                     { return pFrame->nStored;  }
void        Abc_FrameSetNtkStore        ( Abc_Frame_t * pFrame, Abc_Ntk_t * pNtk )   { pFrame->pStored  = pNtk;     } 
void        Abc_FrameSetNtkStoreSize    ( Abc_Frame_t * pFrame, int nStored )        { pFrame->nStored  = nStored;  }

void *      Abc_FrameReadLibLut         ( Abc_Frame_t * pFrame )                     { return pFrame->pLibLut;    } 
void *      Abc_FrameReadLibGen         ( Abc_Frame_t * pFrame )                     { return pFrame->pLibGen;    } 
void *      Abc_FrameReadLibSuper       ( Abc_Frame_t * pFrame )                     { return pFrame->pLibSuper;  } 
void        Abc_FrameSetLibLut          ( Abc_Frame_t * pFrame, void * pLib )        { pFrame->pLibLut   = pLib;   } 
void        Abc_FrameSetLibGen          ( Abc_Frame_t * pFrame, void * pLib )        { pFrame->pLibGen   = pLib;   } 
void        Abc_FrameSetLibSuper        ( Abc_Frame_t * pFrame, void * pLib )        { pFrame->pLibSuper = pLib;   } 

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


