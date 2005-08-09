/**CFile****************************************************************

  FileName    [sim.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Simulation package.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sim.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef __SIM_H__
#define __SIM_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Sim_Man_t_ Sim_Man_t;
struct Sim_Man_t_
{
    // user specified parameters
    Abc_Ntk_t *       pNtk;
    // internal simulation information
    int               nSimBits;      // the number of bits in simulation info
    int               nSimWords;     // the number of words in simulation info
    Vec_Ptr_t *       vSim0;         // simulation info 1
    Vec_Ptr_t *       vSim1;         // simulation info 2
    // support information
    int               nSuppBits;     // the number of bits in support info
    int               nSuppWords;    // the number of words in support info
    Vec_Ptr_t *       vSuppStr;      // structural supports
    Vec_Ptr_t *       vSuppFun;      // functional supports
    // unateness info
    Vec_Ptr_t *       vUnateVarsP;   // unate variables
    Vec_Ptr_t *       vUnateVarsN;   // unate variables
    // symmtry info
    Extra_BitMat_t *  pMatSym;       // symmetric pairs
    Extra_BitMat_t *  pMatNonSym;    // non-symmetric pairs
    // simulation targets
    Vec_Ptr_t *       vSuppTargs;    // support targets
    Vec_Ptr_t *       vUnateTargs;   // unateness targets
    Vec_Ptr_t *       vSymmTargs;    // symmetry targets
    // internal data structures
    Extra_MmFixed_t * pMmPat;   
    Vec_Ptr_t *       vFifo;
    Vec_Int_t *       vDiffs;
    // runtime statistics
    int               time1;
    int               time2;
    int               time3;
    int               time4;
};

typedef struct Sim_Pat_t_ Sim_Pat_t;
struct Sim_Pat_t_
{
    int              Input;         // the input which it has detected
    int              Output;        // the output for which it was collected
    unsigned *       pData;         // the simulation data
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFITIONS                             ///
////////////////////////////////////////////////////////////////////////

#define SIM_NUM_WORDS(n)      ((n)/32 + (((n)%32) > 0))
#define SIM_LAST_BITS(n)      ((((n)%32) > 0)? (n)%32 : 32)

// generating random unsigned (#define RAND_MAX 0x7fff)
#define SIM_RANDOM_UNSIGNED   ((((unsigned)rand()) << 24) ^ (((unsigned)rand()) << 12) ^ ((unsigned)rand()))

// macros to get hold of bits in a bit string
#define Sim_SetBit(p,i)       ((p)[(i)>>5] |= (1<<((i) & 31)))
#define Sim_XorBit(p,i)       ((p)[(i)>>5] ^= (1<<((i) & 31)))
#define Sim_HasBit(p,i)      (((p)[(i)>>5]  & (1<<((i) & 31))) > 0)

// macros to get hold of the support info
#define Sim_SuppStrSetVar(pMan,pNode,v)     Sim_SetBit((unsigned*)pMan->vSuppStr->pArray[(pNode)->Id],(v))
#define Sim_SuppStrHasVar(pMan,pNode,v)     Sim_HasBit((unsigned*)pMan->vSuppStr->pArray[(pNode)->Id],(v))
#define Sim_SuppFunSetVar(pMan,Output,v)    Sim_SetBit((unsigned*)pMan->vSuppFun->pArray[Output],(v))
#define Sim_SuppFunHasVar(pMan,Output,v)    Sim_HasBit((unsigned*)pMan->vSuppFun->pArray[Output],(v))
#define Sim_SimInfoSetVar(pMan,pNode,v)     Sim_SetBit((unsigned*)pMan->vSim0->pArray[(pNode)->Id],(v))
#define Sim_SimInfoHasVar(pMan,pNode,v)     Sim_HasBit((unsigned*)pMan->vSim0->pArray[(pNode)->Id],(v))

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== simMan.c ==========================================================*/
extern Sim_Man_t *     Sim_ManStart( Abc_Ntk_t * pNtk );
extern void            Sim_ManStop( Sim_Man_t * p );
extern Sim_Pat_t *     Sim_ManPatAlloc( Sim_Man_t * p );
extern void            Sim_ManPatFree( Sim_Man_t * p, Sim_Pat_t * pPat );
extern void            Sim_ManPrintStats( Sim_Man_t * p );

/*=== simSupp.c ==========================================================*/
extern Sim_Man_t *     Sim_ComputeSupp( Abc_Ntk_t * pNtk );

/*=== simUtil.c ==========================================================*/
extern Vec_Ptr_t *     Sim_UtilInfoAlloc( int nSize, int nWords, bool fClean );
extern void            Sim_UtilInfoFree( Vec_Ptr_t * p );
extern void            Sim_UtilInfoAdd( unsigned * pInfo1, unsigned * pInfo2, int nWords );
extern void            Sim_UtilInfoDetectDiffs( unsigned * pInfo1, unsigned * pInfo2, int nWords, Vec_Int_t * vDiffs );
extern void            Sim_UtilInfoDetectNews( unsigned * pInfo1, unsigned * pInfo2, int nWords, Vec_Int_t * vDiffs );
extern void            Sim_UtilComputeStrSupp( Sim_Man_t * p );
extern void            Sim_UtilAssignRandom( Sim_Man_t * p );
extern void            Sim_UtilFlipSimInfo( Sim_Man_t * p, Abc_Obj_t * pNode );
extern bool            Sim_UtilCompareSimInfo( Sim_Man_t * p, Abc_Obj_t * pNode );
extern void            Sim_UtilSimulate( Sim_Man_t * p, bool fFirst );
extern void            Sim_UtilSimulateNode( Sim_Man_t * p, Abc_Obj_t * pNode, bool fType, bool fType1, bool fType2 );
extern int             Sim_UtilCountSuppSizes( Sim_Man_t * p, int fStruct );

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#endif

