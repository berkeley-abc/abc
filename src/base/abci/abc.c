/**CFile****************************************************************
 
  FileName    [abc.c] 

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]
  
  Synopsis    [Command file.]

  Author      [Alan Mishchenko]
   
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abc.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "src/base/abc/abc.h"
#include "src/base/main/main.h"
#include "src/base/main/mainInt.h"
#include "src/proof/fraig/fraig.h"
#include "src/opt/fxu/fxu.h"
#include "src/opt/cut/cut.h"
#include "src/map/fpga/fpga.h"
#include "src/map/if/if.h"
#include "src/opt/sim/sim.h"
#include "src/opt/res/res.h"
#include "src/opt/lpk/lpk.h"
#include "src/aig/gia/giaAig.h"
#include "src/opt/dar/dar.h"
#include "src/opt/mfs/mfs.h"
#include "src/proof/fra/fra.h"
#include "src/aig/saig/saig.h"
#include "src/proof/int/int.h"
#include "src/proof/dch/dch.h"
#include "src/proof/ssw/ssw.h"
#include "src/opt/cgt/cgt.h"
#include "src/bool/kit/kit.h"
#include "src/map/amap/amap.h"
#include "src/opt/ret/retInt.h"
#include "src/sat/cnf/cnf.h"
#include "src/proof/cec/cec.h"
#include "src/proof/pdr/pdr.h"
#include "src/misc/tim/tim.h"
#include "src/proof/llb/llb.h"
#include "src/proof/bbr/bbr.h"
#include "src/map/cov/cov.h"
#include "src/base/cmd/cmd.h"

#ifdef _WIN32
//#include <io.h>
#else
#include <unistd.h>
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Abc_CommandPrintStats             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintExdc              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintIo                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintLatch             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintFanio             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintMffc              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintFactor            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintLevel             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintSupport           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintSymms             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintUnate             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintAuto              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintKMap              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintGates             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintSharing           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintXCut              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintDsd               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintCone              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintMiter             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPrintStatus            ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandShow                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShowBdd                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShowCut                ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandCollapse               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandStrash                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBalance                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMuxStruct              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMulti                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRenode                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCleanup                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSweep                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFastExtract            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandEliminate              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDisjoint               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandLutpack                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandLutmin                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandImfs                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMfs                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTrace                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSpeedup                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPowerdown              ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandMerge                  ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandRewrite                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRefactor               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRestructure            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandResubstitute           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRr                     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCascade                ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandLogic                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandComb                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMiter                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDemiter                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOrPos                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAndPos                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandZeroPo                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSwapPos                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRemovePo               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAddPi                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAppend                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFrames                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDFrames                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSop                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBdd                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAig                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandReorder                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBidec                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOrder                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMuxes                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExtSeqDcs              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandReach                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCone                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandNode                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTopmost                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTopAnd                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTrim                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandShortNames             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExdcFree               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExdcGet                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExdcSet                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCareSet                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCut                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandEspresso               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandGen                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCover                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDouble                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandInter                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBb2Wb                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOutdec                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTest                   ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandQuaVar                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandQuaRel                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandQuaReach               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSenseInput             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandNpnLoad                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandNpnSave                ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandIStrash                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandICut                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIRewrite               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDRewrite               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDRefactor              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDc2                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDChoice                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDch                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDrwsat                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIRewriteSeq            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIResyn                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandISat                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIFraig                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDFraig                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCSweep                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDProve                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandDProve2                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbSec                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSimSec                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandMatch                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandHaig                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandMini                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandQbf                    ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandFraig                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigTrust             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigStore             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigRestore           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigClean             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigSweep             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFraigDress             ( Abc_Frame_t * pAbc, int argc, char ** argv );

//static int Abc_CommandHaigStart              ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandHaigStop               ( Abc_Frame_t * pAbc, int argc, char ** argv );
//static int Abc_CommandHaigUse                ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandRecStart               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecStop                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecAdd                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecPs                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecUse                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecFilter              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRecMerge               ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandMap                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAmap                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUnmap                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAttach                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSuperChoice            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSuperChoiceLut         ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandFpga                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFpgaFast               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIf                     ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandScut                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandInit                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandZero                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUndc                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandOneHot                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPipe                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeq                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUnseq                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandRetime                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDRetime                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFlowRetime             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCRetime                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqFpga                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqMap                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqSweep               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqSweep2              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTestSeqSweep           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTestScorr              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandLcorr                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSeqCleanup             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCycle                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandXsim                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSim                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSim3                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDarPhase               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSynch                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandClockGate              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandExtWin                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandInsWin                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPermute                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUnpermute              ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandCec                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDCec                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSec                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDSec                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandSat                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDSat                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPSat                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandProve                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIProve                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDebug                  ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBmc                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBmc2                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBmc3                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBmcInter               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandIndcut                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandEnlarge                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTempor                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandInduction              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandConstr                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandUnfold                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandFold                   ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBm                     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTestCex                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandPdr                    ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandReconcile              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandCexMin                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandDualRail               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandBlockPo                ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandTraceStart             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandTraceCheck             ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandAbc9Get                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Put                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Read               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ReadBlif           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ReadCBlif          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Write              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Ps                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9PFan               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9PSig               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Status             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Show               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Hash               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Topand             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Cof                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Trim               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Dfs                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Sim                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Sim3               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Resim              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9SpecI              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Equiv              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Equiv2             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Equiv3             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Semi               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Times              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Frames             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Retime             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Enable             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Dc2                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Bidec              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Shrink             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Miter              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Scl                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Lcorr              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Scorr              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Choice             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Sat                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Fraig              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Srm                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Srm2               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Filter             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Reduce             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9EquivMark          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Cec                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Force              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Embed              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9If                 ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Trace              ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Speedup            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Era                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Dch                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9AbsStart           ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9AbsDerive          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9AbsRefine          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9AbsCba             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9AbsPba             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GlaDerive          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GlaCba             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9GlaPba             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Vta                ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Vta2Gla            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Reparam            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9BackReach          ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Posplit            ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ReachM             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ReachP             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ReachN             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9ReachY             ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Undo               ( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Abc_CommandAbc9Test               ( Abc_Frame_t * pAbc, int argc, char ** argv );

static int Abc_CommandAbcTestNew             ( Abc_Frame_t * pAbc, int argc, char ** argv );

extern int Abc_CommandAbcLivenessToSafety    ( Abc_Frame_t * pAbc, int argc, char ** argv );
extern int Abc_CommandAbcLivenessToSafetySim ( Abc_Frame_t * pAbc, int argc, char ** argv );
extern int Abc_CommandAbcLivenessToSafetyWithLTL( Abc_Frame_t * pAbc, int argc, char ** argv );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameReplaceCex( Abc_Frame_t * pAbc, Abc_Cex_t ** ppCex )
{
    // update CEX
    ABC_FREE( pAbc->pCex );
    pAbc->pCex = *ppCex;
    *ppCex = NULL;
    // remove CEX vector
    if ( pAbc->vCexVec )
    {
        Vec_PtrFreeFree( pAbc->vCexVec );
        pAbc->vCexVec = NULL;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameReplaceCexVec( Abc_Frame_t * pAbc, Vec_Ptr_t ** pvCexVec )
{
    // update CEX vector
    if ( pAbc->vCexVec )
        Vec_PtrFreeFree( pAbc->vCexVec );
    pAbc->vCexVec = *pvCexVec;
    *pvCexVec = NULL;
    // remove CEX
    ABC_FREE( pAbc->pCex );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_FrameClearDesign()
{
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_CommandUpdate9( Abc_Frame_t * pAbc, Gia_Man_t * pNew )
{
    if ( pNew == NULL )
    {
        Abc_Print( -1, "Abc_CommandUpdate9(): Tranformation has failed.\n" );
        return;
    }
    // transfer names
    if (!pNew->vNamesIn && pAbc->pGia && pAbc->pGia->vNamesIn && Gia_ManCiNum(pNew) == Vec_PtrSize(pAbc->pGia->vNamesIn))
    {
        pNew->vNamesIn = pAbc->pGia->vNamesIn;
        pAbc->pGia->vNamesIn = NULL;
    }
    if (!pNew->vNamesOut && pAbc->pGia && pAbc->pGia->vNamesOut && Gia_ManCoNum(pNew) == Vec_PtrSize(pAbc->pGia->vNamesOut))
    {
        pNew->vNamesOut = pAbc->pGia->vNamesOut;
        pAbc->pGia->vNamesOut = NULL;
    }
    // update
    if ( pAbc->pGia2 )
        Gia_ManStop( pAbc->pGia2 );
    pAbc->pGia2 = pAbc->pGia;
    pAbc->pGia  = pNew;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "Printing",     "print_stats",   Abc_CommandPrintStats,       0 ); 
    Cmd_CommandAdd( pAbc, "Printing",     "print_exdc",    Abc_CommandPrintExdc,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_io",      Abc_CommandPrintIo,          0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_latch",   Abc_CommandPrintLatch,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_fanio",   Abc_CommandPrintFanio,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_mffc",    Abc_CommandPrintMffc,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_factor",  Abc_CommandPrintFactor,      0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_level",   Abc_CommandPrintLevel,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_supp",    Abc_CommandPrintSupport,     0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_symm",    Abc_CommandPrintSymms,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_unate",   Abc_CommandPrintUnate,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_auto",    Abc_CommandPrintAuto,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_kmap",    Abc_CommandPrintKMap,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_gates",   Abc_CommandPrintGates,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_sharing", Abc_CommandPrintSharing,     0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_xcut",    Abc_CommandPrintXCut,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_dsd",     Abc_CommandPrintDsd,         0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_cone",    Abc_CommandPrintCone,        0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_miter",   Abc_CommandPrintMiter,       0 );
    Cmd_CommandAdd( pAbc, "Printing",     "print_status",  Abc_CommandPrintStatus,      0 );

    Cmd_CommandAdd( pAbc, "Printing",     "show",          Abc_CommandShow,             0 );
    Cmd_CommandAdd( pAbc, "Printing",     "show_bdd",      Abc_CommandShowBdd,          0 );
    Cmd_CommandAdd( pAbc, "Printing",     "show_cut",      Abc_CommandShowCut,          0 );

    Cmd_CommandAdd( pAbc, "Synthesis",    "collapse",      Abc_CommandCollapse,         1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "strash",        Abc_CommandStrash,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "balance",       Abc_CommandBalance,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "mux_struct",    Abc_CommandMuxStruct,        1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "multi",         Abc_CommandMulti,            1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "renode",        Abc_CommandRenode,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "cleanup",       Abc_CommandCleanup,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "sweep",         Abc_CommandSweep,            1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "fx",            Abc_CommandFastExtract,      1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "eliminate",     Abc_CommandEliminate,        1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "dsd",           Abc_CommandDisjoint,         1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "lutpack",       Abc_CommandLutpack,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "lutmin",        Abc_CommandLutmin,           1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "imfs",          Abc_CommandImfs,             1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "mfs",           Abc_CommandMfs,              1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "trace",         Abc_CommandTrace,            0 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "speedup",       Abc_CommandSpeedup,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "powerdown",     Abc_CommandPowerdown,        1 );
//    Cmd_CommandAdd( pAbc, "Synthesis",    "merge",         Abc_CommandMerge,            1 );

    Cmd_CommandAdd( pAbc, "Synthesis",    "rewrite",       Abc_CommandRewrite,          1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "refactor",      Abc_CommandRefactor,         1 );
//    Cmd_CommandAdd( pAbc, "Synthesis",    "restructure",   Abc_CommandRestructure,      1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "resub",         Abc_CommandResubstitute,     1 );
//    Cmd_CommandAdd( pAbc, "Synthesis",    "rr",            Abc_CommandRr,               1 );
    Cmd_CommandAdd( pAbc, "Synthesis",    "cascade",       Abc_CommandCascade,          1 );

    Cmd_CommandAdd( pAbc, "Various",      "logic",         Abc_CommandLogic,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "comb",          Abc_CommandComb,             1 );
    Cmd_CommandAdd( pAbc, "Various",      "miter",         Abc_CommandMiter,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "demiter",       Abc_CommandDemiter,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "orpos",         Abc_CommandOrPos,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "andpos",        Abc_CommandAndPos,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "zeropo",        Abc_CommandZeroPo,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "swappos",       Abc_CommandSwapPos,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "removepo",      Abc_CommandRemovePo,         1 );
    Cmd_CommandAdd( pAbc, "Various",      "addpi",         Abc_CommandAddPi,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "append",        Abc_CommandAppend,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "frames",        Abc_CommandFrames,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "dframes",       Abc_CommandDFrames,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "sop",           Abc_CommandSop,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "bdd",           Abc_CommandBdd,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "aig",           Abc_CommandAig,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "reorder",       Abc_CommandReorder,          0 );
    Cmd_CommandAdd( pAbc, "Various",      "bidec",         Abc_CommandBidec,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "order",         Abc_CommandOrder,            0 );
    Cmd_CommandAdd( pAbc, "Various",      "muxes",         Abc_CommandMuxes,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "ext_seq_dcs",   Abc_CommandExtSeqDcs,        0 );
    Cmd_CommandAdd( pAbc, "Various",      "reach",         Abc_CommandReach,            0 );
    Cmd_CommandAdd( pAbc, "Various",      "cone",          Abc_CommandCone,             1 );
    Cmd_CommandAdd( pAbc, "Various",      "node",          Abc_CommandNode,             1 );
    Cmd_CommandAdd( pAbc, "Various",      "topmost",       Abc_CommandTopmost,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "topand",        Abc_CommandTopAnd,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "trim",          Abc_CommandTrim,             1 );
    Cmd_CommandAdd( pAbc, "Various",      "short_names",   Abc_CommandShortNames,       0 );
    Cmd_CommandAdd( pAbc, "Various",      "exdc_free",     Abc_CommandExdcFree,         1 );
    Cmd_CommandAdd( pAbc, "Various",      "exdc_get",      Abc_CommandExdcGet,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "exdc_set",      Abc_CommandExdcSet,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "care_set",      Abc_CommandCareSet,          1 );
    Cmd_CommandAdd( pAbc, "Various",      "cut",           Abc_CommandCut,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "espresso",      Abc_CommandEspresso,         1 );
    Cmd_CommandAdd( pAbc, "Various",      "gen",           Abc_CommandGen,              0 );
    Cmd_CommandAdd( pAbc, "Various",      "cover",         Abc_CommandCover,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "double",        Abc_CommandDouble,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "inter",         Abc_CommandInter,            1 );
    Cmd_CommandAdd( pAbc, "Various",      "bb2wb",         Abc_CommandBb2Wb,            0 );
    Cmd_CommandAdd( pAbc, "Various",      "outdec",        Abc_CommandOutdec,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "test",          Abc_CommandTest,             0 );
//    Cmd_CommandAdd( pAbc, "Various",      "qbf_solve",     Abc_CommandTest,               0 );

    Cmd_CommandAdd( pAbc, "Various",      "qvar",          Abc_CommandQuaVar,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "qrel",          Abc_CommandQuaRel,           1 );
    Cmd_CommandAdd( pAbc, "Various",      "qreach",        Abc_CommandQuaReach,         1 );
    Cmd_CommandAdd( pAbc, "Various",      "senseinput",    Abc_CommandSenseInput,       1 );
    Cmd_CommandAdd( pAbc, "Various",      "npnload",       Abc_CommandNpnLoad,          0 );
    Cmd_CommandAdd( pAbc, "Various",      "npnsave",       Abc_CommandNpnSave,          0 );

    Cmd_CommandAdd( pAbc, "New AIG",      "istrash",       Abc_CommandIStrash,          1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "icut",          Abc_CommandICut,             0 );
    Cmd_CommandAdd( pAbc, "New AIG",      "irw",           Abc_CommandIRewrite,         1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "drw",           Abc_CommandDRewrite,         1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "drf",           Abc_CommandDRefactor,        1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "dc2",           Abc_CommandDc2,              1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "dchoice",       Abc_CommandDChoice,          1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "dch",           Abc_CommandDch,              1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "drwsat",        Abc_CommandDrwsat,           1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "irws",          Abc_CommandIRewriteSeq,      1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "iresyn",        Abc_CommandIResyn,           1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "isat",          Abc_CommandISat,             1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "ifraig",        Abc_CommandIFraig,           1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "dfraig",        Abc_CommandDFraig,           1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "csweep",        Abc_CommandCSweep,           1 );
//    Cmd_CommandAdd( pAbc, "New AIG",      "haig",          Abc_CommandHaig,             1 );
//    Cmd_CommandAdd( pAbc, "New AIG",      "mini",          Abc_CommandMini,             1 );
    Cmd_CommandAdd( pAbc, "New AIG",      "qbf",           Abc_CommandQbf,              0 );

    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig",         Abc_CommandFraig,            1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_trust",   Abc_CommandFraigTrust,       1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_store",   Abc_CommandFraigStore,       0 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_restore", Abc_CommandFraigRestore,     1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_clean",   Abc_CommandFraigClean,       0 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "fraig_sweep",   Abc_CommandFraigSweep,       1 );
    Cmd_CommandAdd( pAbc, "Fraiging",     "dress",         Abc_CommandFraigDress,       1 );

//    Cmd_CommandAdd( pAbc, "Choicing",     "haig_start",    Abc_CommandHaigStart,        0 );
//    Cmd_CommandAdd( pAbc, "Choicing",     "haig_stop",     Abc_CommandHaigStop,         0 );
//    Cmd_CommandAdd( pAbc, "Choicing",     "haig_use",      Abc_CommandHaigUse,          1 );

    Cmd_CommandAdd( pAbc, "Choicing",     "rec_start",     Abc_CommandRecStart,         0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_stop",      Abc_CommandRecStop,          0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_add",       Abc_CommandRecAdd,           0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_ps",        Abc_CommandRecPs,            0 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_use",       Abc_CommandRecUse,           1 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_filter",    Abc_CommandRecFilter,        1 );
    Cmd_CommandAdd( pAbc, "Choicing",     "rec_merge",     Abc_CommandRecMerge,         1 );

    Cmd_CommandAdd( pAbc, "SC mapping",   "map",           Abc_CommandMap,              1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "amap",          Abc_CommandAmap,             1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "unmap",         Abc_CommandUnmap,            1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "attach",        Abc_CommandAttach,           1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "sc",            Abc_CommandSuperChoice,      1 );
    Cmd_CommandAdd( pAbc, "SC mapping",   "scl",           Abc_CommandSuperChoiceLut,   1 );

    Cmd_CommandAdd( pAbc, "FPGA mapping", "fpga",          Abc_CommandFpga,             1 );
    Cmd_CommandAdd( pAbc, "FPGA mapping", "ffpga",         Abc_CommandFpgaFast,         1 );
    Cmd_CommandAdd( pAbc, "FPGA mapping", "if",            Abc_CommandIf,               1 );

//    Cmd_CommandAdd( pAbc, "Sequential",   "scut",          Abc_CommandScut,             0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "init",          Abc_CommandInit,             1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "zero",          Abc_CommandZero,             1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "undc",          Abc_CommandUndc,             1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "onehot",        Abc_CommandOneHot,           1 );
//    Cmd_CommandAdd( pAbc, "Sequential",   "pipe",          Abc_CommandPipe,             1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "retime",        Abc_CommandRetime,           1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "dretime",       Abc_CommandDRetime,          1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "fretime",       Abc_CommandFlowRetime,       1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "cretime",       Abc_CommandCRetime,          1 );
//    Cmd_CommandAdd( pAbc, "Sequential",   "sfpga",         Abc_CommandSeqFpga,          1 );
//    Cmd_CommandAdd( pAbc, "Sequential",   "smap",          Abc_CommandSeqMap,           1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "ssweep",        Abc_CommandSeqSweep,         1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "scorr",         Abc_CommandSeqSweep2,        1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "testssw",       Abc_CommandTestSeqSweep,     0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "testscorr",     Abc_CommandTestScorr,        0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "lcorr",         Abc_CommandLcorr,            1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "scleanup",      Abc_CommandSeqCleanup,       1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "cycle",         Abc_CommandCycle,            1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "xsim",          Abc_CommandXsim,             0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "sim",           Abc_CommandSim,              0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "sim3",          Abc_CommandSim3,             0 );
    Cmd_CommandAdd( pAbc, "Sequential",   "phase",         Abc_CommandDarPhase,         1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "synch",         Abc_CommandSynch,            1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "clockgate",     Abc_CommandClockGate,        1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "extwin",        Abc_CommandExtWin,           1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "inswin",        Abc_CommandInsWin,           1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "permute",       Abc_CommandPermute,          1 );
    Cmd_CommandAdd( pAbc, "Sequential",   "unpermute",     Abc_CommandUnpermute,        1 );

    Cmd_CommandAdd( pAbc, "Verification", "cec",           Abc_CommandCec,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "dcec",          Abc_CommandDCec,             0 );
//    Cmd_CommandAdd( pAbc, "Verification", "sec",           Abc_CommandSec,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "dsec",          Abc_CommandDSec,             0 );
    Cmd_CommandAdd( pAbc, "Verification", "dprove",        Abc_CommandDProve,           0 );
//    Cmd_CommandAdd( pAbc, "Verification", "dprove2",       Abc_CommandDProve2,          0 );
    Cmd_CommandAdd( pAbc, "Verification", "absec",         Abc_CommandAbSec,            0 );
    Cmd_CommandAdd( pAbc, "Verification", "simsec",        Abc_CommandSimSec,           0 );
    Cmd_CommandAdd( pAbc, "Verification", "match",         Abc_CommandMatch,            0 );
    Cmd_CommandAdd( pAbc, "Verification", "sat",           Abc_CommandSat,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "dsat",          Abc_CommandDSat,             0 );
    Cmd_CommandAdd( pAbc, "Verification", "psat",          Abc_CommandPSat,             0 );
    Cmd_CommandAdd( pAbc, "Verification", "prove",         Abc_CommandProve,            1 );
    Cmd_CommandAdd( pAbc, "Verification", "iprove",        Abc_CommandIProve,           1 );
    Cmd_CommandAdd( pAbc, "Verification", "debug",         Abc_CommandDebug,            0 );
    Cmd_CommandAdd( pAbc, "Verification", "bmc",           Abc_CommandBmc,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "bmc2",          Abc_CommandBmc2,             0 );
    Cmd_CommandAdd( pAbc, "Verification", "bmc3",          Abc_CommandBmc3,             1 );
    Cmd_CommandAdd( pAbc, "Verification", "int",           Abc_CommandBmcInter,         1 );
    Cmd_CommandAdd( pAbc, "Verification", "indcut",        Abc_CommandIndcut,           0 );
    Cmd_CommandAdd( pAbc, "Verification", "enlarge",       Abc_CommandEnlarge,          1 );
    Cmd_CommandAdd( pAbc, "Verification", "tempor",        Abc_CommandTempor,           1 );
    Cmd_CommandAdd( pAbc, "Verification", "ind",           Abc_CommandInduction,        0 );
    Cmd_CommandAdd( pAbc, "Verification", "constr",        Abc_CommandConstr,           0 );
    Cmd_CommandAdd( pAbc, "Verification", "unfold",        Abc_CommandUnfold,           1 );
    Cmd_CommandAdd( pAbc, "Verification", "fold",          Abc_CommandFold,             1 );
    Cmd_CommandAdd( pAbc, "Verification", "bm",            Abc_CommandBm,               1 );
    Cmd_CommandAdd( pAbc, "Verification", "testcex",       Abc_CommandTestCex,          0 );
    Cmd_CommandAdd( pAbc, "Verification", "pdr",           Abc_CommandPdr,              0 );
    Cmd_CommandAdd( pAbc, "Verification", "reconcile",     Abc_CommandReconcile,        1 );
    Cmd_CommandAdd( pAbc, "Verification", "cexmin",        Abc_CommandCexMin,           0 );
    Cmd_CommandAdd( pAbc, "Verification", "dualrail",      Abc_CommandDualRail,         1 );
    Cmd_CommandAdd( pAbc, "Verification", "blockpo",       Abc_CommandBlockPo,          1 );

    Cmd_CommandAdd( pAbc, "ABC9",         "&get",          Abc_CommandAbc9Get,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&put",          Abc_CommandAbc9Put,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&r",            Abc_CommandAbc9Read,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&read_blif",    Abc_CommandAbc9ReadBlif,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&read_cblif",   Abc_CommandAbc9ReadCBlif,    0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&w",            Abc_CommandAbc9Write,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&ps",           Abc_CommandAbc9Ps,           0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&pfan",         Abc_CommandAbc9PFan,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&psig",         Abc_CommandAbc9PSig,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&status",       Abc_CommandAbc9Status,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&show",         Abc_CommandAbc9Show,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&st",           Abc_CommandAbc9Hash,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&topand",       Abc_CommandAbc9Topand,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&cof",          Abc_CommandAbc9Cof,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&trim",         Abc_CommandAbc9Trim,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&dfs",          Abc_CommandAbc9Dfs,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sim",          Abc_CommandAbc9Sim,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sim3",         Abc_CommandAbc9Sim3,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&resim",        Abc_CommandAbc9Resim,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&speci",        Abc_CommandAbc9SpecI,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&equiv",        Abc_CommandAbc9Equiv,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&equiv2",       Abc_CommandAbc9Equiv2,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&equiv3",       Abc_CommandAbc9Equiv3,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&semi",         Abc_CommandAbc9Semi,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&times",        Abc_CommandAbc9Times,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&frames",       Abc_CommandAbc9Frames,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&retime",       Abc_CommandAbc9Retime,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&enable",       Abc_CommandAbc9Enable,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&dc2",          Abc_CommandAbc9Dc2,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&bidec",        Abc_CommandAbc9Bidec,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&shrink",       Abc_CommandAbc9Shrink,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&miter",        Abc_CommandAbc9Miter,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&scl",          Abc_CommandAbc9Scl,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&lcorr",        Abc_CommandAbc9Lcorr,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&scorr",        Abc_CommandAbc9Scorr,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&choice",       Abc_CommandAbc9Choice,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&sat",          Abc_CommandAbc9Sat,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&fraig",        Abc_CommandAbc9Fraig,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&srm",          Abc_CommandAbc9Srm,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&srm2",         Abc_CommandAbc9Srm2,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&filter",       Abc_CommandAbc9Filter,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&reduce",       Abc_CommandAbc9Reduce,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&equiv_mark",   Abc_CommandAbc9EquivMark,    0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&cec",          Abc_CommandAbc9Cec,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&force",        Abc_CommandAbc9Force,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&embed",        Abc_CommandAbc9Embed,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&if",           Abc_CommandAbc9If,           0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&trace",        Abc_CommandAbc9Trace,        0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&speedup",      Abc_CommandAbc9Speedup,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&era",          Abc_CommandAbc9Era,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&dch",          Abc_CommandAbc9Dch,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&abs_start",    Abc_CommandAbc9AbsStart,     0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&abs_derive",   Abc_CommandAbc9AbsDerive,    0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&abs_refine",   Abc_CommandAbc9AbsRefine,    0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&abs_cba",      Abc_CommandAbc9AbsCba,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&abs_pba",      Abc_CommandAbc9AbsPba,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&gla_derive",   Abc_CommandAbc9GlaDerive,    0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&gla_cba",      Abc_CommandAbc9GlaCba,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&gla_pba",      Abc_CommandAbc9GlaPba,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&vta",          Abc_CommandAbc9Vta,          0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&vta_gla",      Abc_CommandAbc9Vta2Gla,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&reparam",      Abc_CommandAbc9Reparam,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&back_reach",   Abc_CommandAbc9BackReach,    0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&posplit",      Abc_CommandAbc9Posplit,      0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&reachm",       Abc_CommandAbc9ReachM,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&reachp",       Abc_CommandAbc9ReachP,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&reachn",       Abc_CommandAbc9ReachN,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&reachy",       Abc_CommandAbc9ReachY,       0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&undo",         Abc_CommandAbc9Undo,         0 );
    Cmd_CommandAdd( pAbc, "ABC9",         "&test",         Abc_CommandAbc9Test,         0 );

    Cmd_CommandAdd( pAbc, "Liveness",     "l2s",           Abc_CommandAbcLivenessToSafety,    0 );
    Cmd_CommandAdd( pAbc, "Liveness",     "l2ssim",        Abc_CommandAbcLivenessToSafetySim, 0 );
    Cmd_CommandAdd( pAbc, "Liveness",     "l3s",           Abc_CommandAbcLivenessToSafetyWithLTL,    0 );

    Cmd_CommandAdd( pAbc, "Various",      "testnew",       Abc_CommandAbcTestNew,       0 );

//    Cmd_CommandAdd( pAbc, "Verification", "trace_start",   Abc_CommandTraceStart,       0 );
//    Cmd_CommandAdd( pAbc, "Verification", "trace_check",   Abc_CommandTraceCheck,       0 );

//    Rwt_Man4ExploreStart();
//    Map_Var3Print();
//    Map_Var4Test();

//    Abc_NtkPrint256();
//    Kit_TruthCountMintermsPrecomp();
//    Kit_DsdPrecompute4Vars();

    {
        extern void Dar_LibStart();
        Dar_LibStart();
    }
    {
//        extern void Bdc_ManDecomposeTest( unsigned uTruth, int nVars );
//        Bdc_ManDecomposeTest( 0x0f0f0f0f, 3 );
    }

    {
//        extern void Aig_ManRandomTest1();
//        Aig_ManRandomTest1();
    }
    {
        extern void Extra_MemTest();
//       Extra_MemTest();
    }

    {
        extern void Gia_SortTest();
//        Gia_SortTest();
    }
    {
        void For_ManFileExperiment();
//        For_ManFileExperiment();
    }
/*
    {
        int i1, i2, i3, i4, i5, i6, N, Counter = 0;
        for ( N = 20; N < 40; N++ )
        {
            Counter = 0;
            for ( i1 = 0;    i1 < N; i1++ )
            for ( i2 = i1+1; i2 < N; i2++ )
            for ( i3 = i2; i3 < N; i3++ )
            for ( i4 = i3; i4 < N; i4++ )
//            for ( i5 = i4+1; i5 < N; i5++ )
//            for ( i6 = i5+1; i6 < N; i6++ )
                Counter++;
            printf( "%d=%d  ", N, Counter );
        }
        printf( "\n" );
    }
*/
    {
        extern void If_CluTest();
        If_CluTest();
    }
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_End( Abc_Frame_t * pAbc )
{
    extern Abc_Frame_t * Abc_FrameGetGlobalFrame();
    Abc_FrameClearDesign(); 

    {
//        extern void Au_TabManPrint();
//        Au_TabManPrint();
    }

//    Dar_LibDumpPriorities();
    {
        extern int Abc_NtkCompareAndSaveBest( Abc_Ntk_t * pNtk );
        Abc_NtkCompareAndSaveBest( NULL );
    }

    {
//        extern void Cnf_ClearMemory();
        Cnf_ClearMemory();
    }
    {
        extern void Dar_LibStop();
        Dar_LibStop();
    }
    {
        extern void Aig_RManQuit();
        Aig_RManQuit();
    }
    {
        extern void Npn_ManClean();
        Npn_ManClean();
    }
    Abc_NtkFraigStoreClean();
    if ( Abc_FrameGetGlobalFrame()->pGia )
        Gia_ManStop( Abc_FrameGetGlobalFrame()->pGia );
    if ( Abc_FrameGetGlobalFrame()->pGia2 )
        Gia_ManStop( Abc_FrameGetGlobalFrame()->pGia2 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintStats( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int fFactor;
    int fSaveBest;
    int fDumpResult;
    int fUseLutLib;
    int fPrintTime;
    int fPrintMuxes;
    int fPower;
    int fGlitch;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);

    // set the defaults
    fFactor   = 0;
    fSaveBest = 0;
    fDumpResult = 0;
    fUseLutLib = 0;
    fPrintTime = 0;
    fPrintMuxes = 0;
    fPower = 0;
    fGlitch = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "fbdltmpgh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            fFactor ^= 1;
            break;
        case 'b':
            fSaveBest ^= 1;
            break;
        case 'd':
            fDumpResult ^= 1;
            break;
        case 'l':
            fUseLutLib ^= 1;
            break;
        case 't':
            fPrintTime ^= 1;
            break;
        case 'm':
            fPrintMuxes ^= 1;
            break;
        case 'p':
            fPower ^= 1;
            break;
        case 'g':
            fGlitch ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) && fUseLutLib )
    {
        Abc_Print( -1, "Cannot print LUT delay for a non-logic network.\n" );
        return 1;
    }
    Abc_NtkPrintStats( pNtk, fFactor, fSaveBest, fDumpResult, fUseLutLib, fPrintMuxes, fPower, fGlitch );
    if ( fPrintTime )
    {
        pAbc->TimeTotal += pAbc->TimeCommand;
        Abc_Print( 1, "elapse: %3.2f seconds, total: %3.2f seconds\n", pAbc->TimeCommand, pAbc->TimeTotal );
        pAbc->TimeCommand = 0.0;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: print_stats [-fbdltmpgh]\n" );
    Abc_Print( -2, "\t        prints the network statistics\n" );
    Abc_Print( -2, "\t-f    : toggles printing the literal count in the factored forms [default = %s]\n", fFactor? "yes": "no" );
    Abc_Print( -2, "\t-b    : toggles saving the best logic network in \"best.blif\" [default = %s]\n", fSaveBest? "yes": "no" );
    Abc_Print( -2, "\t-d    : toggles dumping network into file \"<input_file_name>_dump.blif\" [default = %s]\n", fDumpResult? "yes": "no" );
    Abc_Print( -2, "\t-l    : toggles printing delay of LUT mapping using LUT library [default = %s]\n", fSaveBest? "yes": "no" );
    Abc_Print( -2, "\t-t    : toggles printing runtime statistics [default = %s]\n", fPrintTime? "yes": "no" );
    Abc_Print( -2, "\t-m    : toggles printing MUX statistics [default = %s]\n", fPrintMuxes? "yes": "no" );
    Abc_Print( -2, "\t-p    : toggles printing power dissipation due to switching [default = %s]\n", fPower? "yes": "no" );
    Abc_Print( -2, "\t-q    : toggles printing percentage of increased power due to glitching [default = %s]\n", fGlitch? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintExdc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkTemp;
    double Percentage;
    int fShort;
    int c;
    int fPrintDc;
    extern double Abc_NtkSpacePercentage( Abc_Obj_t * pNode );
    pNtk = Abc_FrameReadNtk(pAbc);

    // set the defaults
    fShort  = 1;
    fPrintDc = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "sdh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fShort ^= 1;
            break;
        case 'd':
            fPrintDc ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( pNtk->pExdc == NULL )
    {
        Abc_Print( -1, "Network has no EXDC.\n" );
        return 1;
    }

    if ( fPrintDc )
    {
        if ( !Abc_NtkIsStrash(pNtk->pExdc) )
        {
            pNtkTemp = Abc_NtkStrash(pNtk->pExdc, 0, 0, 0);
            Percentage = Abc_NtkSpacePercentage( Abc_ObjChild0( Abc_NtkPo(pNtkTemp, 0) ) );
            Abc_NtkDelete( pNtkTemp );
        }
        else
            Percentage = Abc_NtkSpacePercentage( Abc_ObjChild0( Abc_NtkPo(pNtk->pExdc, 0) ) );

        Abc_Print( 1, "EXDC network statistics: " );
        Abc_Print( 1, "(" );
        if ( Percentage > 0.05 && Percentage < 99.95 )
            Abc_Print( 1, "%.2f", Percentage );
        else if ( Percentage > 0.000005 && Percentage < 99.999995 )
            Abc_Print( 1, "%.6f", Percentage );
        else
            Abc_Print( 1, "%f", Percentage );
        Abc_Print( 1, " %% don't-cares)\n" );
    }
    else
        Abc_Print( 1, "EXDC network statistics: \n" );
    Abc_NtkPrintStats( pNtk->pExdc, 0, 0, 0, 0, 0, 0, 0 );
    return 0;

usage:
    Abc_Print( -2, "usage: print_exdc [-dh]\n" );
    Abc_Print( -2, "\t        prints the EXDC network statistics\n" );
    Abc_Print( -2, "\t-d    : toggles printing don't-care percentage [default = %s]\n", fPrintDc? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintIo( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pNode;
    int c;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( argc == globalUtilOptind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
        Abc_NodePrintFanio( stdout, pNode );
        return 0;
    }
    // print the nodes
    Abc_NtkPrintIo( stdout, pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: print_io [-h] <node>\n" );
    Abc_Print( -2, "\t        prints the PIs/POs or fanins/fanouts of a node\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    Abc_Print( -2, "\tnode  : the node to print fanins/fanouts\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintLatch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fPrintSccs;
    extern void Abc_NtkPrintSccs( Abc_Ntk_t * pNtk, int fVerbose );

    // set defaults
    fPrintSccs = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "sh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fPrintSccs ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    // print the nodes
    Abc_NtkPrintLatch( stdout, pNtk );
    if ( fPrintSccs )
        Abc_NtkPrintSccs( pNtk, 0 );
    return 0;

usage:
    Abc_Print( -2, "usage: print_latch [-sh]\n" );
    Abc_Print( -2, "\t        prints information about latches\n" );
    Abc_Print( -2, "\t-s    : toggles printing SCCs of registers [default = %s]\n", fPrintSccs? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintFanio( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fMffc;
    int fVerbose;

    // set defaults
    fMffc    = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "mvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'm':
            fMffc ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // print the nodes
    if ( fVerbose )
        Abc_NtkPrintFanio( stdout, pNtk );
    else
        Abc_NtkPrintFanioNew( stdout, pNtk, fMffc );
    return 0;

usage:
    Abc_Print( -2, "usage: print_fanio [-mvh]\n" );
    Abc_Print( -2, "\t        prints the statistics about fanins/fanouts of all nodes\n" );
    Abc_Print( -2, "\t-m    : toggles printing MFFC sizes instead of fanouts [default = %s]\n", fMffc? "yes": "no" );
    Abc_Print( -2, "\t-v    : toggles verbose way of printing the stats [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintMffc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    extern void Abc_NtkPrintMffc( FILE * pFile, Abc_Ntk_t * pNtk );

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // print the nodes
    Abc_NtkPrintMffc( stdout, pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: print_mffc [-h]\n" );
    Abc_Print( -2, "\t        prints the MFFC of each node in the network\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintFactor( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pNode;
    int c;
    int fUseRealNames;

    // set defaults
    fUseRealNames = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "nh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'n':
            fUseRealNames ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        Abc_Print( -1, "Printing factored forms can be done for SOP networks.\n" );
        return 1;
    }

    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( argc == globalUtilOptind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
        Abc_NodePrintFactor( stdout, pNode, fUseRealNames );
        return 0;
    }
    // print the nodes
    Abc_NtkPrintFactor( stdout, pNtk, fUseRealNames );
    return 0;

usage:
    Abc_Print( -2, "usage: print_factor [-nh] <node>\n" );
    Abc_Print( -2, "\t        prints the factored forms of nodes\n" );
    Abc_Print( -2, "\t-n    : toggles real/dummy fanin names [default = %s]\n", fUseRealNames? "real": "dummy" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    Abc_Print( -2, "\tnode  : (optional) one node to consider\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintLevel( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pNode;
    int c;
    int fListNodes;
    int fProfile;

    // set defaults
    fListNodes = 0;
    fProfile   = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "nph" ) ) != EOF )
    {
        switch ( c )
        {
        case 'n':
            fListNodes ^= 1;
            break;
        case 'p':
            fProfile ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !fProfile && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }

    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }

    if ( argc == globalUtilOptind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
        Abc_NodePrintLevel( stdout, pNode );
        return 0;
    }
    // process all COs
    Abc_NtkPrintLevel( stdout, pNtk, fProfile, fListNodes );
    return 0;

usage:
    Abc_Print( -2, "usage: print_level [-nph] <node>\n" );
    Abc_Print( -2, "\t        prints information about node level and cone size\n" );
    Abc_Print( -2, "\t-n    : toggles printing nodes by levels [default = %s]\n", fListNodes? "yes": "no" );
    Abc_Print( -2, "\t-p    : toggles printing level profile [default = %s]\n", fProfile? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    Abc_Print( -2, "\tnode  : (optional) one node to consider\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintSupport( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Vec_Ptr_t * vSuppFun;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fStruct;
    int fVerbose;
    extern Vec_Ptr_t * Sim_ComputeFunSupp( Abc_Ntk_t * pNtk, int fVerbose );
    extern void Abc_NtkPrintStrSupports( Abc_Ntk_t * pNtk );

    // set defaults
    fStruct = 1;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "svh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fStruct ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // print support information
    if ( fStruct )
    {
        Abc_NtkPrintStrSupports( pNtk );
        return 0;
    }

    if ( !Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "This command works only for combinational networks (run \"comb\").\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }
    vSuppFun = Sim_ComputeFunSupp( pNtk, fVerbose );
    ABC_FREE( vSuppFun->pArray[0] );
    Vec_PtrFree( vSuppFun );
    return 0;

usage:
    Abc_Print( -2, "usage: print_supp [-svh]\n" );
    Abc_Print( -2, "\t        prints the supports of the CO nodes\n" );
    Abc_Print( -2, "\t-s    : toggle printing structural support only [default = %s].\n", fStruct? "yes": "no" );  
    Abc_Print( -2, "\t-v    : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintSymms( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseBdds;
    int fNaive;
    int fReorder;
    int fVerbose;
    extern void Abc_NtkSymmetries( Abc_Ntk_t * pNtk, int fUseBdds, int fNaive, int fReorder, int fVerbose );

    // set defaults
    fUseBdds = 0;
    fNaive   = 0;
    fReorder = 1;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "bnrvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fUseBdds ^= 1;
            break;
        case 'n':
            fNaive ^= 1;
            break;
        case 'r':
            fReorder ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "This command works only for combinational networks (run \"comb\").\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
        Abc_NtkSymmetries( pNtk, fUseBdds, fNaive, fReorder, fVerbose );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        Abc_NtkSymmetries( pNtk, fUseBdds, fNaive, fReorder, fVerbose );
        Abc_NtkDelete( pNtk );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: print_symm [-bnrvh]\n" );
    Abc_Print( -2, "\t         computes symmetries of the PO functions\n" );
    Abc_Print( -2, "\t-b     : toggle BDD-based or SAT-based computations [default = %s].\n", fUseBdds? "BDD": "SAT" );  
    Abc_Print( -2, "\t-n     : enable naive BDD-based computation [default = %s].\n", fNaive? "yes": "no" );  
    Abc_Print( -2, "\t-r     : enable dynamic BDD variable reordering [default = %s].\n", fReorder? "yes": "no" );  
    Abc_Print( -2, "\t-v     : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintUnate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseBdds;
    int fUseNaive;
    int fVerbose;
    extern void Abc_NtkPrintUnate( Abc_Ntk_t * pNtk, int fUseBdds, int fUseNaive, int fVerbose );

    // set defaults
    fUseBdds  = 1;
    fUseNaive = 0;
    fVerbose  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "bnvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fUseBdds ^= 1;
            break;
        case 'n':
            fUseNaive ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }
    Abc_NtkPrintUnate( pNtk, fUseBdds, fUseNaive, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: print_unate [-bnvh]\n" );
    Abc_Print( -2, "\t         computes unate variables of the PO functions\n" );
    Abc_Print( -2, "\t-b     : toggle BDD-based or SAT-based computations [default = %s].\n", fUseBdds? "BDD": "SAT" );  
    Abc_Print( -2, "\t-n     : toggle naive BDD-based computation [default = %s].\n", fUseNaive? "yes": "no" );  
    Abc_Print( -2, "\t-v     : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintAuto( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int Output;
    int fNaive;
    int fVerbose;
    extern void Abc_NtkAutoPrint( Abc_Ntk_t * pNtk, int Output, int fNaive, int fVerbose );

    // set defaults
    Output   = -1;
    fNaive   = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Onvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            Output = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Output < 0 ) 
                goto usage;
            break;
        case 'n':
            fNaive ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs (run \"strash\").\n" );
        return 1;
    }


    Abc_NtkAutoPrint( pNtk, Output, fNaive, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: print_auto [-O <num>] [-nvh]\n" );
    Abc_Print( -2, "\t           computes autosymmetries of the PO functions\n" );
    Abc_Print( -2, "\t-O <num> : (optional) the 0-based number of the output [default = all]\n");
    Abc_Print( -2, "\t-n       : enable naive BDD-based computation [default = %s].\n", fNaive? "yes": "no" );  
    Abc_Print( -2, "\t-v       : enable verbose output [default = %s].\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintKMap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pNode;
    int c;
    int fUseRealNames;

    extern void Abc_NodePrintKMap( Abc_Obj_t * pNode, int fUseRealNames );

    // set defaults
    fUseRealNames = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "nh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'n':
            fUseRealNames ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( argc == globalUtilOptind + 2 )
    {
        Abc_NtkShow6VarFunc( argv[globalUtilOptind], argv[globalUtilOptind+1] );
        return 0;
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Visualization of Karnaugh maps works for logic networks.\n" );
        return 1;
    }
    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }
    if ( argc == globalUtilOptind )
    {
        pNode = Abc_ObjFanin0( Abc_NtkPo(pNtk, 0) );
        if ( !Abc_ObjIsNode(pNode) )
        {
            Abc_Print( -1, "The driver \"%s\" of the first PO is not an internal node.\n", Abc_ObjName(pNode) );
            return 1;
        }
    }
    else
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
    }
    Abc_NtkToBdd(pNtk);
    Abc_NodePrintKMap( pNode, fUseRealNames );
    return 0;

usage:
    Abc_Print( -2, "usage: print_kmap [-nh] <node>\n" );
    Abc_Print( -2, "\t        shows the truth table of the node\n" );
    Abc_Print( -2, "\t-n    : toggles real/dummy fanin names [default = %s]\n", fUseRealNames? "real": "dummy" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    Abc_Print( -2, "\t<node>: the node to consider (default = the driver of the first PO)\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintGates( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseLibrary;

    extern void Abc_NtkPrintGates( Abc_Ntk_t * pNtk, int fUseLibrary );

    // set defaults
    fUseLibrary = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUseLibrary ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkHasAig(pNtk) )
    {
        Abc_Print( -1, "Printing gates does not work for AIGs and sequential AIGs.\n" );
        return 1;
    }

    Abc_NtkPrintGates( pNtk, fUseLibrary );
    return 0;

usage:
    Abc_Print( -2, "usage: print_gates [-lh]\n" );
    Abc_Print( -2, "\t        prints statistics about gates used in the network\n" );
    Abc_Print( -2, "\t-l    : used library gate names (if mapped) [default = %s]\n", fUseLibrary? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintSharing( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseLibrary;

    extern void Abc_NtkPrintSharing( Abc_Ntk_t * pNtk );

    // set defaults
    fUseLibrary = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUseLibrary ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    Abc_NtkPrintSharing( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: print_sharing [-h]\n" );
    Abc_Print( -2, "\t        prints the number of shared nodes in the TFI cones of the COs\n" );
//    Abc_Print( -2, "\t-l    : used library gate names (if mapped) [default = %s]\n", fUseLibrary? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintXCut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseLibrary;

    extern int Abc_NtkCrossCut( Abc_Ntk_t * pNtk );

    // set defaults
    fUseLibrary = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUseLibrary ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    Abc_NtkCrossCut( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: print_xcut [-h]\n" );
    Abc_Print( -2, "\t        prints the size of the cross cut of the current network\n" );
//    Abc_Print( -2, "\t-l    : used library gate names (if mapped) [default = %s]\n", fUseLibrary? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintDsd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fCofactor;
    int nCofLevel;
    int fProfile;

    extern void Kit_DsdTest( unsigned * pTruth, int nVars );
    extern void Kit_DsdPrintCofactors( unsigned * pTruth, int nVars, int nCofLevel, int fVerbose );

    // set defaults
    nCofLevel = 1;
    fCofactor = 0;
    fProfile  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Npch" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nCofLevel = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCofLevel < 0 ) 
                goto usage;
            break;
        case 'c':
            fCofactor ^= 1;
            break;
        case 'p':
            fProfile ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    // get the truth table of the first output
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Currently works only for logic networks.\n" );
        return 1;
    }
    Abc_NtkToAig( pNtk );
    // convert it to truth table
    {
        Abc_Obj_t * pObj = Abc_ObjFanin0( Abc_NtkPo(pNtk, 0) );
        Vec_Int_t * vMemory;
        unsigned * pTruth;
        if ( !Abc_ObjIsNode(pObj) )
        {
            Abc_Print( -1, "The fanin of the first PO node does not have a logic function.\n" );
            return 1;
        }
        if ( Abc_ObjFaninNum(pObj) > 16 )
        {
            Abc_Print( -1, "Currently works only for up to 16 inputs.\n" );
            return 1;
        }
        vMemory = Vec_IntAlloc(0);
        pTruth = Hop_ManConvertAigToTruth( (Hop_Man_t *)pNtk->pManFunc, Hop_Regular((Hop_Obj_t *)pObj->pData), Abc_ObjFaninNum(pObj), vMemory, 0 );
        if ( Hop_IsComplement((Hop_Obj_t *)pObj->pData) )
            Extra_TruthNot( pTruth, pTruth, Abc_ObjFaninNum(pObj) );
//        Extra_PrintBinary( stdout, pTruth, 1 << Abc_ObjFaninNum(pObj) );
//        Abc_Print( -1, "\n" );
        if ( fProfile )
            Kit_TruthPrintProfile( pTruth, Abc_ObjFaninNum(pObj) );
        else if ( fCofactor )
            Kit_DsdPrintCofactors( pTruth, Abc_ObjFaninNum(pObj), nCofLevel, 1 );
        else
            Kit_DsdTest( pTruth, Abc_ObjFaninNum(pObj) );
        Vec_IntFree( vMemory );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: print_dsd [-pch] [-N <num>]\n" );
    Abc_Print( -2, "\t           print DSD formula for a single-output function with less than 16 variables\n" );
    Abc_Print( -2, "\t-p       : toggle printing profile [default = %s]\n", fProfile? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggle recursive cofactoring [default = %s]\n", fCofactor? "yes": "no" );
    Abc_Print( -2, "\t-N <num> : the number of levels to cofactor [default = %d]\n", nCofLevel );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintCone( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseLibrary;

    // set defaults
    fUseLibrary = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUseLibrary ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 1;
    }
    Abc_NtkDarPrintCone( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: print_cone [-h]\n" );
    Abc_Print( -2, "\t        prints cones of influence info for each primary output\n" );
//    Abc_Print( -2, "\t-l    : used library gate names (if mapped) [default = %s]\n", fUseLibrary? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintMiter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseLibrary;

    extern void Abc_NtkPrintMiter( Abc_Ntk_t * pNtk );

    // set defaults
    fUseLibrary = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUseLibrary ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "The network is should be structurally hashed.\n" );
        return 1;
    }
    Abc_NtkPrintMiter( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: print_miter [-h]\n" );
    Abc_Print( -2, "\t        prints the status of the miter\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPrintStatus( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    printf( "Status = %d  Frames = %d   ", pAbc->Status, pAbc->nFrames );
    if ( pAbc->pCex == NULL )
        printf( "Cex is not defined.\n" );
    else
        printf( "Cex: PIs = %d  Regs = %d  PO = %d  Frame = %d  Bits = %d\n", 
            pAbc->pCex->nPis, pAbc->pCex->nRegs, 
            pAbc->pCex->iPo, pAbc->pCex->iFrame, 
            pAbc->pCex->nBits ); 
    return 0;

usage:
    Abc_Print( -2, "usage: print_status [-h]\n" );
    Abc_Print( -2, "\t        prints verification status\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandShow( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fSeq;
    int fGateNames;
    int fUseReverse;
    int fFlopDep;
    extern void Abc_NtkShow( Abc_Ntk_t * pNtk, int fGateNames, int fSeq, int fUseReverse );
    extern void Abc_NtkShowFlopDependency( Abc_Ntk_t * pNtk );

    // set defaults
    fSeq        = 0;
    fGateNames  = 0;
    fUseReverse = 1;
    fFlopDep    = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rsgfh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'r':
            fUseReverse ^= 1;
            break;
        case 's':
            fSeq ^= 1;
            break;
        case 'g':
            fGateNames ^= 1;
            break;
        case 'f':
            fFlopDep ^= 1;
            break;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( fFlopDep )
        Abc_NtkShowFlopDependency( pNtk );
    else
        Abc_NtkShow( pNtk, fGateNames, fSeq, fUseReverse );
    return 0;

usage:
    Abc_Print( -2, "usage: show [-srgfh]\n" );
    Abc_Print( -2, "       visualizes the network structure using DOT and GSVIEW\n" );
#ifdef WIN32
    Abc_Print( -2, "       \"dot.exe\" and \"gsview32.exe\" should be set in the paths\n" );
    Abc_Print( -2, "       (\"gsview32.exe\" may be in \"C:\\Program Files\\Ghostgum\\gsview\\\")\n" );
#endif
    Abc_Print( -2, "\t-s    : toggles visualization of sequential networks [default = %s].\n", fSeq? "yes": "no" );  
    Abc_Print( -2, "\t-r    : toggles ordering nodes in reverse order [default = %s].\n", fUseReverse? "yes": "no" );  
    Abc_Print( -2, "\t-g    : toggles printing gate names for mapped network [default = %s].\n", fGateNames? "yes": "no" );  
    Abc_Print( -2, "\t-f    : toggles visualizing flop dependency graph [default = %s].\n", fFlopDep? "yes": "no" );  
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandShowBdd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pNode;
    int c;
    extern void Abc_NodeShowBdd( Abc_Obj_t * pNode );

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsBddLogic(pNtk) )
    {
        Abc_Print( -1, "Visualizing BDDs can only be done for logic BDD networks (run \"bdd\").\n" );
        return 1;
    }

    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }
    if ( argc == globalUtilOptind )
    {
        pNode = Abc_ObjFanin0( Abc_NtkPo(pNtk, 0) );
        if ( !Abc_ObjIsNode(pNode) )
        {
            Abc_Print( -1, "The driver \"%s\" of the first PO is not an internal node.\n", Abc_ObjName(pNode) );
            return 1;
        }
    }
    else
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
    }
    Abc_NodeShowBdd( pNode );
    return 0;

usage:
    Abc_Print( -2, "usage: show_bdd [-h] <node>\n" );
    Abc_Print( -2, "       visualizes the BDD of a node using DOT and GSVIEW\n" );
#ifdef WIN32
    Abc_Print( -2, "       \"dot.exe\" and \"gsview32.exe\" should be set in the paths\n" );
    Abc_Print( -2, "       (\"gsview32.exe\" may be in \"C:\\Program Files\\Ghostgum\\gsview\\\")\n" );
#endif
    Abc_Print( -2, "\t<node>: the node to consider [default = the driver of the first PO]\n");
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandShowCut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pNode;
    int c;
    int nNodeSizeMax;
    int nConeSizeMax;
    extern void Abc_NodeShowCut( Abc_Obj_t * pNode, int nNodeSizeMax, int nConeSizeMax );

    // set defaults
    nNodeSizeMax = 10;
    nConeSizeMax = ABC_INFINITY;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NCh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodeSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodeSizeMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConeSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConeSizeMax < 0 ) 
                goto usage;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Visualizing cuts only works for AIGs (run \"strash\").\n" );
        return 1;
    }
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }

    pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
    if ( pNode == NULL )
    {
        Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
        return 1;
    }
    Abc_NodeShowCut( pNode, nNodeSizeMax, nConeSizeMax );
    return 0;

usage:
    Abc_Print( -2, "usage: show_cut [-N <num>] [-C <num>] [-h] <node>\n" );
    Abc_Print( -2, "             visualizes the cut of a node using DOT and GSVIEW\n" );
#ifdef WIN32
    Abc_Print( -2, "             \"dot.exe\" and \"gsview32.exe\" should be set in the paths\n" );
    Abc_Print( -2, "             (\"gsview32.exe\" may be in \"C:\\Program Files\\Ghostgum\\gsview\\\")\n" );
#endif
    Abc_Print( -2, "\t-N <num> : the max size of the cut to be computed [default = %d]\n", nNodeSizeMax );  
    Abc_Print( -2, "\t-C <num> : the max support of the containing cone [default = %d]\n", nConeSizeMax );  
    Abc_Print( -2, "\t<node>   : the node to consider\n");
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCollapse( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fVerbose;
    int fBddSizeMax;
    int fDualRail;
    int fReorder;
    int c;
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fVerbose = 1;
    fReorder = 1;
    fDualRail = 0;
    fBddSizeMax = 50000000;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Brdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            fBddSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( fBddSizeMax < 0 ) 
                goto usage;
            break;
        case 'd':
            fDualRail ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'r':
            fReorder ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Can only collapse a logic network or an AIG.\n" );
        return 1;
    }

    // get the new network
    if ( Abc_NtkIsStrash(pNtk) )
        pNtkRes = Abc_NtkCollapse( pNtk, fBddSizeMax, fDualRail, fReorder, fVerbose );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        pNtkRes = Abc_NtkCollapse( pNtk, fBddSizeMax, fDualRail, fReorder, fVerbose );
        Abc_NtkDelete( pNtk );
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Collapsing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: collapse [-B <num>] [-rdvh]\n" );
    Abc_Print( -2, "\t          collapses the network by constructing global BDDs\n" );
    Abc_Print( -2, "\t-B <num>: limit on live BDD nodes during collapsing [default = %d]\n", fBddSizeMax );
    Abc_Print( -2, "\t-r      : toggles dynamic variable reordering [default = %s]\n", fReorder? "yes": "no" );
    Abc_Print( -2, "\t-d      : toggles dual-rail collapsing mode [default = %s]\n", fDualRail? "yes": "no" );
    Abc_Print( -2, "\t-v      : print verbose information [default = %s]\n", fVerbose? "yes": "no" ); 
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandStrash( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Abc_Obj_t * pObj;
    int c;
    int fAllNodes;
    int fRecord;
    int fCleanup;
    int fComplOuts;
    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fAllNodes = 0;
    fCleanup  = 1;
    fRecord   = 0;
    fComplOuts= 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "acrih" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fAllNodes ^= 1;
            break;
        case 'c':
            fCleanup ^= 1;
            break;
        case 'r':
            fRecord ^= 1;
            break;
        case 'i':
            fComplOuts ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkStrash( pNtk, fAllNodes, fCleanup, fRecord );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Strashing has failed.\n" );
        return 1;
    }
    if ( fComplOuts )
    Abc_NtkForEachPo( pNtkRes, pObj, c )
        Abc_ObjXorFaninC( pObj, 0 );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: strash [-acrih]\n" );
    Abc_Print( -2, "\t        transforms combinational logic into an AIG\n" );
    Abc_Print( -2, "\t-a    : toggles between using all nodes and DFS nodes [default = %s]\n", fAllNodes? "all": "DFS" );
    Abc_Print( -2, "\t-c    : toggles cleanup to remove the dagling AIG nodes [default = %s]\n", fCleanup? "all": "DFS" );
    Abc_Print( -2, "\t-r    : toggles using the record of AIG subgraphs [default = %s]\n", fRecord? "yes": "no" );
    Abc_Print( -2, "\t-i    : toggles complementing the COs of the AIG [default = %s]\n", fComplOuts? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBalance( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes, * pNtkTemp;
    int c;
    int fDuplicate;
    int fSelective;
    int fUpdateLevel;
    int fExor;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkBalanceExor( Abc_Ntk_t * pNtk, int fUpdateLevel, int fVerbose );
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fDuplicate   = 0;
    fSelective   = 0;
    fUpdateLevel = 1;
    fExor        = 0;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ldsxvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'd':
            fDuplicate ^= 1;
            break;
        case 's':
            fSelective ^= 1;
            break;
        case 'x':
            fExor ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    // get the new network
    if ( Abc_NtkIsStrash(pNtk) )
    {
        if ( fExor ) 
            pNtkRes = Abc_NtkBalanceExor( pNtk, fUpdateLevel, fVerbose );
        else
            pNtkRes = Abc_NtkBalance( pNtk, fDuplicate, fSelective, fUpdateLevel );
    }
    else
    {
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtkTemp == NULL )
        {
            Abc_Print( -1, "Strashing before balancing has failed.\n" );
            return 1;
        }
        if ( fExor ) 
            pNtkRes = Abc_NtkBalanceExor( pNtkTemp, fUpdateLevel, fVerbose );
        else
            pNtkRes = Abc_NtkBalance( pNtkTemp, fDuplicate, fSelective, fUpdateLevel );
        Abc_NtkDelete( pNtkTemp );
    }

    // check if balancing worked
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Balancing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: balance [-ldsxvh]\n" );
    Abc_Print( -2, "\t        transforms the current network into a well-balanced AIG\n" );
    Abc_Print( -2, "\t-l    : toggle minimizing the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    Abc_Print( -2, "\t-s    : toggle duplication on the critical paths [default = %s]\n", fSelective? "yes": "no" );
    Abc_Print( -2, "\t-x    : toggle balancing multi-input EXORs [default = %s]\n", fExor? "yes": "no" );
    Abc_Print( -2, "\t-v    : print verbose information [default = %s]\n", fVerbose? "yes": "no" ); 
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMuxStruct( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fVerbose;

    extern Abc_Ntk_t * Abc_NtkMuxRestructure( Abc_Ntk_t * pNtk, int fVerbose );
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    // get the new network
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Does not work for a logic network.\n" );
        return 1;
    }
    // check if balancing worked
//    pNtkRes = Abc_NtkMuxRestructure( pNtk, fVerbose );
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "MUX restructuring has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: mux_struct [-vh]\n" );
    Abc_Print( -2, "\t        performs MUX restructuring of the current network\n" );
    Abc_Print( -2, "\t-v    : print verbose information [default = %s]\n", fVerbose? "yes": "no" ); 
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMulti( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int nThresh, nFaninMax, c;
    int fCnf;
    int fMulti;
    int fSimple;
    int fFactor;
    extern Abc_Ntk_t * Abc_NtkMulti( Abc_Ntk_t * pNtk, int nThresh, int nFaninMax, int fCnf, int fMulti, int fSimple, int fFactor );

    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    nThresh   =  1;
    nFaninMax = 20;
    fCnf      =  0;
    fMulti    =  1;
    fSimple   =  0;
    fFactor   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TFmcsfh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nThresh = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nThresh < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFaninMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFaninMax < 0 ) 
                goto usage;
            break;
        case 'c':
            fCnf ^= 1;
            break;
        case 'm':
            fMulti ^= 1;
            break;
        case 's':
            fSimple ^= 1;
            break;
        case 'f':
            fFactor ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Cannot renode a network that is not an AIG (run \"strash\").\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkMulti( pNtk, nThresh, nFaninMax, fCnf, fMulti, fSimple, fFactor );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Renoding has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: multi [-TF <num>] [-msfch]\n" );
    Abc_Print( -2, "\t          transforms an AIG into a logic network by creating larger nodes\n" );
    Abc_Print( -2, "\t-F <num>: the maximum fanin size after renoding [default = %d]\n", nFaninMax );
    Abc_Print( -2, "\t-T <num>: the threshold for AIG node duplication [default = %d]\n", nThresh );
    Abc_Print( -2, "\t          (an AIG node is the root of a new node after renoding\n" );
    Abc_Print( -2, "\t          if this leads to duplication of no more than %d AIG nodes,\n", nThresh );
    Abc_Print( -2, "\t          that is, if [(numFanouts(Node)-1) * size(MFFC(Node))] <= %d)\n", nThresh );
    Abc_Print( -2, "\t-m      : creates multi-input AND graph [default = %s]\n", fMulti? "yes": "no" );
    Abc_Print( -2, "\t-s      : creates a simple AIG (no renoding) [default = %s]\n", fSimple? "yes": "no" );
    Abc_Print( -2, "\t-f      : creates a factor-cut network [default = %s]\n", fFactor? "yes": "no" );
    Abc_Print( -2, "\t-c      : performs renoding to derive the CNF [default = %s]\n", fCnf? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRenode( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int nLutSize, nCutsMax, c;
    int nFlowIters, nAreaIters;
    int fArea;
    int fUseBdds;
    int fUseSops;
    int fUseCnfs;
    int fUseMv;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkRenode( Abc_Ntk_t * pNtk, int nLutSize, int nCutsMax, int nFlowIters, int nAreaIters, int fArea, int fUseBdds, int fUseSops, int fUseCnfs, int fUseMv, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    nLutSize   =  8;
    nCutsMax   =  4;
    nFlowIters =  1;
    nAreaIters =  1;
    fArea      =  0;
    fUseBdds   =  0;
    fUseSops   =  0;
    fUseCnfs   =  0;
    fUseMv     =  0;
    fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCFAabscivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutSize < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutsMax < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nFlowIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFlowIters < 0 ) 
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nAreaIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nAreaIters < 0 ) 
                goto usage;
            break;
        case 'a':
            fArea ^= 1;
            break;
        case 'b':
            fUseBdds ^= 1;
            break;
        case 's':
            fUseSops ^= 1;
            break;
        case 'c':
            fUseCnfs ^= 1;
            break;
        case 'i':
            fUseMv ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( fUseBdds + fUseSops + fUseCnfs + fUseMv > 1 )
    {
        Abc_Print( -1, "Cannot optimize two parameters at the same time.\n" );
        return 1;
    }

    if ( nLutSize < 3 || nLutSize > IF_MAX_FUNC_LUTSIZE )
    {
        Abc_Print( -1, "Incorrect LUT size (%d).\n", nLutSize );
        return 1;
    }

    if ( nCutsMax < 1 || nCutsMax >= (1<<12) )
    {
        Abc_Print( -1, "Incorrect number of cuts.\n" );
        return 1;
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Cannot renode a network that is not an AIG (run \"strash\").\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkRenode( pNtk, nLutSize, nCutsMax, nFlowIters, nAreaIters, fArea, fUseBdds, fUseSops, fUseCnfs, fUseMv, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Renoding has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: renode [-KCFA <num>] [-sbciav]\n" );
    Abc_Print( -2, "\t          transforms the AIG into a logic network with larger nodes\n" );
    Abc_Print( -2, "\t          while minimizing the number of FF literals of the node SOPs\n" );
    Abc_Print( -2, "\t-K <num>: the max cut size for renoding (2 < num < %d) [default = %d]\n", IF_MAX_FUNC_LUTSIZE+1, nLutSize );
    Abc_Print( -2, "\t-C <num>: the max number of cuts used at a node (0 < num < 2^12) [default = %d]\n", nCutsMax );
    Abc_Print( -2, "\t-F <num>: the number of area flow recovery iterations (num >= 0) [default = %d]\n", nFlowIters );
    Abc_Print( -2, "\t-A <num>: the number of exact area recovery iterations (num >= 0) [default = %d]\n", nAreaIters );
    Abc_Print( -2, "\t-s      : toggles minimizing SOP cubes instead of FF lits [default = %s]\n", fUseSops? "yes": "no" );
    Abc_Print( -2, "\t-b      : toggles minimizing BDD nodes instead of FF lits [default = %s]\n", fUseBdds? "yes": "no" );
    Abc_Print( -2, "\t-c      : toggles minimizing CNF clauses instead of FF lits [default = %s]\n", fUseCnfs? "yes": "no" );
    Abc_Print( -2, "\t-i      : toggles minimizing MV-SOP instead of FF lits [default = %s]\n", fUseMv? "yes": "no" );
    Abc_Print( -2, "\t-a      : toggles area-oriented mapping [default = %s]\n", fArea? "yes": "no" );
    Abc_Print( -2, "\t-v      : print verbose information [default = %s]\n", fVerbose? "yes": "no" ); 
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCleanup( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fCleanupPis;
    int fCleanupPos;
    int fVerbose;

    extern Abc_Ntk_t * Abc_NtkDarCleanupAig( Abc_Ntk_t * pNtk, int fCleanupPis, int fCleanupPos, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fCleanupPis = 1;
    fCleanupPos = 1;
    fVerbose    = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "iovh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'i':
            fCleanupPis ^= 1;
            break;
        case 'o':
            fCleanupPos ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
    {
        if ( !fCleanupPos && !fCleanupPos )
        {
            Abc_Print( -1, "Cleanup for PIs and POs is not enabled.\n" );
            pNtkRes = Abc_NtkDup( pNtk );
        }
        else
            pNtkRes = Abc_NtkDarCleanupAig( pNtk, fCleanupPis, fCleanupPos, fVerbose );
    }
    else
    {
        Abc_NtkCleanup( pNtk, fVerbose );
        pNtkRes = Abc_NtkDup( pNtk );
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Cleanup has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: cleanup [-iovh]\n" );
    Abc_Print( -2, "\t        for logic networks, removes dangling combinatinal logic\n" );
    Abc_Print( -2, "\t        for AIGs, removes PIs w/o fanout and POs driven by const-0\n" );
    Abc_Print( -2, "\t-i    : toggles removing PIs without fanout [default = %s]\n", fCleanupPis? "yes": "no" );
    Abc_Print( -2, "\t-o    : toggles removing POs with const-0 drivers [default = %s]\n", fCleanupPos? "yes": "no" );
    Abc_Print( -2, "\t-v    : print verbose information [default = %s]\n", fVerbose? "yes": "no" ); 
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSweep( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fSingle = 0;
    int fVerbose = 0;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "svh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fSingle ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "The classical (SIS-like) sweep can only be performed on a logic network.\n" );
        return 1;
    }
    // modify the current network
    if ( fSingle )
        Abc_NtkSweepBufsInvs( pNtk, fVerbose );
    else
        Abc_NtkSweep( pNtk, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: sweep [-svh]\n" );
    Abc_Print( -2, "\t        removes dangling nodes; propagates constant, buffers, inverters\n" );
    Abc_Print( -2, "\t-s    : toggle sweeping buffers/inverters only [default = %s]\n", fSingle? "yes": "no" );  
    Abc_Print( -2, "\t-v    : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" ); 
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFastExtract( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Fxu_Data_t * p = NULL;
    int c;
    extern int Abc_NtkFastExtract( Abc_Ntk_t * pNtk, Fxu_Data_t * p );
    extern void Abc_NtkFxuFreeInfo( Fxu_Data_t * p );

    // allocate the structure
    p = ABC_CALLOC( Fxu_Data_t, 1 );
    // set the defaults
    p->nSingleMax = 20000;
    p->nPairsMax  = 30000;
    p->nNodesExt  = 10000;
    p->WeightMax  = 0;
    p->fOnlyS     = 0;
    p->fOnlyD     = 0;
    p->fUse0      = 0;
    p->fUseCompl  = 1;
    p->fVerbose   = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "SDNWsdzcvh")) != EOF ) 
    {
        switch (c) 
        {
            case 'S':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                    goto usage;
                }
                p->nSingleMax = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( p->nSingleMax < 0 ) 
                    goto usage;
                break;
            case 'D':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                    goto usage;
                }
                p->nPairsMax = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( p->nPairsMax < 0 ) 
                    goto usage;
                break;
            case 'N':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                    goto usage;
                }
                p->nNodesExt = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( p->nNodesExt < 0 ) 
                    goto usage;
                break;
            case 'W':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                    goto usage;
                }
                p->WeightMax = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( p->WeightMax < 0 ) 
                    goto usage;
                break;
            case 's':
                p->fOnlyS ^= 1;
                break;
            case 'd':
                p->fOnlyD ^= 1;
                break;
            case 'z':
                p->fUse0 ^= 1;
                break;
            case 'c':
                p->fUseCompl ^= 1;
                break;
            case 'v':
                p->fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    } 

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        Abc_NtkFxuFreeInfo( p );
        return 1;
    }

    if ( Abc_NtkNodeNum(pNtk) == 0 )
    {
        Abc_Print( -1, "The network does not have internal nodes.\n" );
        Abc_NtkFxuFreeInfo( p );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Fast extract can only be applied to a logic network (run \"renode\").\n" );
        Abc_NtkFxuFreeInfo( p );
        return 1;
    }


    // the nodes to be merged are linked into the special linked list
    Abc_NtkFastExtract( pNtk, p );
    Abc_NtkFxuFreeInfo( p );
    return 0;

usage:
    Abc_Print( -2, "usage: fx [-SDNW <num>] [-sdzcvh]\n");
    Abc_Print( -2, "\t           performs unate fast extract on the current network\n");
    Abc_Print( -2, "\t-S <num> : max number of single-cube divisors to consider [default = %d]\n", p->nSingleMax );  
    Abc_Print( -2, "\t-D <num> : max number of double-cube divisors to consider [default = %d]\n", p->nPairsMax );  
    Abc_Print( -2, "\t-N <num> : the maximum number of divisors to extract [default = %d]\n", p->nNodesExt );  
    Abc_Print( -2, "\t-W <num> : only extract divisors with weight more than this [default = %d]\n", p->nSingleMax );  
    Abc_Print( -2, "\t-s       : use only single-cube divisors [default = %s]\n", p->fOnlyS? "yes": "no" );  
    Abc_Print( -2, "\t-d       : use only double-cube divisors [default = %s]\n", p->fOnlyD? "yes": "no" );  
    Abc_Print( -2, "\t-z       : use zero-weight divisors [default = %s]\n", p->fUse0? "yes": "no" );  
    Abc_Print( -2, "\t-c       : use complement in the binary case [default = %s]\n", p->fUseCompl? "yes": "no" );  
    Abc_Print( -2, "\t-v       : print verbose information [default = %s]\n", p->fVerbose? "yes": "no" ); 
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_NtkFxuFreeInfo( p );
    return 1;       
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandEliminate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int nMaxSize;
    int fReverse;
    int fVerbose;
    int c;
    extern int Abc_NtkEliminate( Abc_Ntk_t * pNtk, int nMaxSize, int fReverse, int fVerbose );

    // set the defaults
    nMaxSize  = 8;
    fReverse  = 0;
    fVerbose  = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "Nrvh")) != EOF ) 
    {
        switch (c) 
        {
            case 'N':
                if ( globalUtilOptind >= argc )
                {
                    Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                    goto usage;
                }
                nMaxSize = atoi(argv[globalUtilOptind]);
                globalUtilOptind++;
                if ( nMaxSize <= 0 ) 
                    goto usage;
                break;
            case 'r':
                fReverse ^= 1;
                break;
            case 'v':
                fVerbose ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    } 

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkNodeNum(pNtk) == 0 )
    {
        Abc_Print( -1, "The network does not have internal nodes.\n" );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network (run \"renode\" or \"if\").\n" );
        return 1;
    }

    // the nodes to be merged are linked into the special linked list
    Abc_NtkEliminate( pNtk, nMaxSize, fReverse, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: eliminate [-N <num>] [-rvh]\n");
    Abc_Print( -2, "\t           greedily eliminates nodes by collapsing them into fanouts\n");
    Abc_Print( -2, "\t-N <num> : the maximum support size after collapsing [default = %d]\n", nMaxSize );  
    Abc_Print( -2, "\t-r       : use the reverse topological order [default = %s]\n", fReverse? "yes": "no" );  
    Abc_Print( -2, "\t-v       : print verbose information [default = %s]\n", fVerbose? "yes": "no" ); 
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;       
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDisjoint( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes, * pNtkNew;
    int fGlobal, fRecursive, fVerbose, fPrint, fShort, c;

    extern Abc_Ntk_t * Abc_NtkDsdGlobal( Abc_Ntk_t * pNtk, int fVerbose, int fPrint, int fShort );
    extern int         Abc_NtkDsdLocal( Abc_Ntk_t * pNtk, int fVerbose, int fRecursive );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fGlobal    = 1;
    fRecursive = 0;
    fVerbose   = 0;
    fPrint     = 0;
    fShort     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "grvpsh" ) ) != EOF )
    {
        switch ( c )
        {
            case 'g':
                fGlobal ^= 1;
                break;
            case 'r':
                fRecursive ^= 1;
                break;
            case 'v':
                fVerbose ^= 1;
                break;
            case 'p':
                fPrint ^= 1;
                break;
            case 's':
                fShort ^= 1;
                break;
            case 'h':
                goto usage;
                break;
            default:
                goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( fGlobal )
    {
//        Abc_Print( -1, "Performing DSD of global functions of the network.\n" );
        // get the new network
        if ( !Abc_NtkIsStrash(pNtk) )
        {
            pNtkNew = Abc_NtkStrash( pNtk, 0, 0, 0 );
            pNtkRes = Abc_NtkDsdGlobal( pNtkNew, fVerbose, fPrint, fShort );
            Abc_NtkDelete( pNtkNew );
        }
        else
        {
            pNtkRes = Abc_NtkDsdGlobal( pNtk, fVerbose, fPrint, fShort );
        }
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "Global DSD has failed.\n" );
            return 1;
        }
        // replace the current network
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    }
    else if ( fRecursive )
    {
        if ( !Abc_NtkIsBddLogic( pNtk ) )
        {
            Abc_Print( -1, "This command is only applicable to logic BDD networks.\n" );
            return 1;
        }
        Abc_Print( -1, "Performing recursive DSD and MUX decomposition of local functions.\n" );
        if ( !Abc_NtkDsdLocal( pNtk, fVerbose, fRecursive ) )
            Abc_Print( -1, "Recursive DSD has failed.\n" );
    }
    else 
    {
        if ( !Abc_NtkIsBddLogic( pNtk ) )
        {
            Abc_Print( -1, "This command is only applicable to logic BDD networks (run \"bdd\").\n" );
            return 1;
        }
        Abc_Print( -1, "Performing simple non-recursive DSD of local functions.\n" );
        if ( !Abc_NtkDsdLocal( pNtk, fVerbose, fRecursive ) )
            Abc_Print( -1, "Simple DSD of local functions has failed.\n" );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: dsd [-grvpsh]\n" );
    Abc_Print( -2, "\t     decomposes the network using disjoint-support decomposition\n" );
    Abc_Print( -2, "\t-g     : toggle DSD of global and local functions [default = %s]\n", fGlobal? "global": "local" );  
    Abc_Print( -2, "\t-r     : toggle recursive DSD/MUX and simple DSD [default = %s]\n", fRecursive? "recursive DSD/MUX": "simple DSD" );  
    Abc_Print( -2, "\t-v     : prints DSD statistics and runtime [default = %s]\n", fVerbose? "yes": "no" ); 
    Abc_Print( -2, "\t-p     : prints DSD structure to the standard output [default = %s]\n", fPrint? "yes": "no" ); 
    Abc_Print( -2, "\t-s     : use short PI names when printing DSD structure [default = %s]\n", fShort? "yes": "no" ); 
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLutpack( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Lpk_Par_t Pars, * pPars = &Pars;
    int c;
 
    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    memset( pPars, 0, sizeof(Lpk_Par_t) );
    pPars->nLutsMax     =  4; // (N) the maximum number of LUTs in the structure
    pPars->nLutsOver    =  3; // (Q) the maximum number of LUTs not in the MFFC
    pPars->nVarsShared  =  0; // (S) the maximum number of shared variables (crossbars)
    pPars->nGrowthLevel =  0; // (L) the maximum number of increased levels
    pPars->fSatur       =  1;
    pPars->fZeroCost    =  0; 
    pPars->fFirst       =  0;
    pPars->fOldAlgo     =  0;
    pPars->fVerbose     =  0;
    pPars->fVeryVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NQSLszfovwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLutsMax < 2 || pPars->nLutsMax > 8 ) 
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLutsOver = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLutsOver < 0 || pPars->nLutsOver > 8 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nVarsShared = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nVarsShared < 0 || pPars->nVarsShared > 4 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nGrowthLevel = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nGrowthLevel < 0 || pPars->nGrowthLevel > ABC_INFINITY ) 
                goto usage;
            break;
        case 's':
            pPars->fSatur ^= 1;
            break;
        case 'z':
            pPars->fZeroCost ^= 1;
            break;
        case 'f':
            pPars->fFirst ^= 1;
            break;
        case 'o':
            pPars->fOldAlgo ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network.\n" );
        return 1;
    }
    if ( pPars->nVarsShared < 0 || pPars->nVarsShared > 3 )
    {
        Abc_Print( -1, "The number of shared variables (%d) is not in the range 0 <= S <= 3.\n", pPars->nVarsShared );
        return 1;
    }

    // modify the current network
    if ( !Lpk_Resynthesize( pNtk, pPars ) )
    {
        Abc_Print( -1, "Resynthesis has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: lutpack [-NQSL <num>] [-szfovwh]\n" );
    Abc_Print( -2, "\t           performs \"rewriting\" for LUT network;\n" );
    Abc_Print( -2, "\t           determines LUT size as the max fanin count of a node;\n" );
    Abc_Print( -2, "\t           if the network is not LUT-mapped, packs it into 6-LUTs\n" );
    Abc_Print( -2, "\t           (there is another command for resynthesis after LUT mapping, \"imfs\")\n" );
    Abc_Print( -2, "\t-N <num> : the max number of LUTs in the structure (2 <= num) [default = %d]\n", pPars->nLutsMax );
    Abc_Print( -2, "\t-Q <num> : the max number of LUTs not in MFFC (0 <= num) [default = %d]\n", pPars->nLutsOver );
    Abc_Print( -2, "\t-S <num> : the max number of LUT inputs shared (0 <= num <= 3) [default = %d]\n", pPars->nVarsShared );
    Abc_Print( -2, "\t-L <num> : max level increase after resynthesis (0 <= num) [default = %d]\n", pPars->nGrowthLevel );
    Abc_Print( -2, "\t-s       : toggle iteration till saturation [default = %s]\n", pPars->fSatur? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggle zero-cost replacements [default = %s]\n", pPars->fZeroCost? "yes": "no" );
    Abc_Print( -2, "\t-f       : toggle using only first node and first cut [default = %s]\n", pPars->fFirst? "yes": "no" );
    Abc_Print( -2, "\t-o       : toggle using old implementation [default = %s]\n", pPars->fOldAlgo? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle detailed printout of decomposed functions [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLutmin( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nLutSize;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkLutmin( Abc_Ntk_t * pNtk, int nLutSize, int fVerbose );
 
    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nLutSize = 4;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Kvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    // modify the current network
    pNtkRes = Abc_NtkLutmin( pNtk, nLutSize, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: lutmin [-K <num>] [-vh]\n" );
    Abc_Print( -2, "\t           perform FPGA mapping while minimizing the LUT count\n" );
    Abc_Print( -2, "\t           as described in the paper T. Sasao and A. Mishchenko:\n" );
    Abc_Print( -2, "\t           \"On the number of LUTs to implement logic functions\".\n" );
    Abc_Print( -2, "\t-K <num> : the LUT size to use for the mapping (2 <= num) [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandImfs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Res_Par_t Pars, * pPars = &Pars;
    int c;

    // set defaults
    pPars->nWindow      = 62;
    pPars->nCands       =  5;
    pPars->nSimWords    =  4;
    pPars->nGrowthLevel =  0;
    pPars->fArea        =  0;
    pPars->fVerbose     =  0;
    pPars->fVeryVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WSCLavwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWindow = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWindow < 1 || pPars->nWindow > 99 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSimWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSimWords < 1 || pPars->nSimWords > 256 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCands = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCands < 0 || pPars->nCands > ABC_INFINITY ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nGrowthLevel = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nGrowthLevel < 0 || pPars->nGrowthLevel > ABC_INFINITY ) 
                goto usage;
            break;
        case 'a':
            pPars->fArea ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkResynthesize( pNtk, pPars ) )
    {
        Abc_Print( -1, "Resynthesis has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: imfs [-W <NM>] [-LCS <num>] [-avwh]\n" );
    Abc_Print( -2, "\t           performs resubstitution-based resynthesis with interpolation\n" );
    Abc_Print( -2, "\t           (there is another command for resynthesis after LUT mapping, \"lutpack\")\n" );
    Abc_Print( -2, "\t-W <NM>  : fanin/fanout levels (NxM) of the window (00 <= NM <= 99) [default = %d%d]\n", pPars->nWindow/10, pPars->nWindow%10 );
    Abc_Print( -2, "\t-C <num> : the max number of resub candidates (1 <= n) [default = %d]\n", pPars->nCands );
    Abc_Print( -2, "\t-S <num> : the number of simulation words (1 <= n <= 256) [default = %d]\n", pPars->nSimWords );
    Abc_Print( -2, "\t-L <num> : the max increase in node level after resynthesis (0 <= num) [default = %d]\n", pPars->nGrowthLevel );
    Abc_Print( -2, "\t-a       : toggle optimization for area only [default = %s]\n", pPars->fArea? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printout subgraph statistics [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMfs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Mfs_Par_t Pars, * pPars = &Pars;
    int c;
    // set defaults
    Abc_NtkMfsParsDefault( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WFDMLCraestpgvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWinTfoLevs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWinTfoLevs < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFanoutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFanoutsMax < 1 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nDepthMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDepthMax < 0 ) 
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWinSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWinSizeMax < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nGrowthLevel = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nGrowthLevel < 0 || pPars->nGrowthLevel > ABC_INFINITY ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBTLimit < 0 ) 
                goto usage;
            break;
        case 'r':
            pPars->fResub ^= 1;
            break;
        case 'a':
            pPars->fArea ^= 1;
            break;
        case 'e':
            pPars->fMoreEffort ^= 1;
            break;
        case 's':
            pPars->fSwapEdge ^= 1;
            break;
        case 't':
            pPars->fOneHotness ^= 1;
            break;
        case 'p':
            pPars->fPower ^= 1;
            break;
        case 'g':
            pPars->fGiaSat ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkMfs( pNtk, pPars ) )
    {
        Abc_Print( -1, "Resynthesis has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: mfs [-WFDMLC <num>] [-raestpgvh]\n" );
    Abc_Print( -2, "\t           performs don't-care-based optimization of logic networks\n" );
    Abc_Print( -2, "\t-W <num> : the number of levels in the TFO cone (0 <= num) [default = %d]\n", pPars->nWinTfoLevs );
    Abc_Print( -2, "\t-F <num> : the max number of fanouts to skip (1 <= num) [default = %d]\n", pPars->nFanoutsMax );
    Abc_Print( -2, "\t-D <num> : the max depth nodes to try (0 = no limit) [default = %d]\n", pPars->nDepthMax );
    Abc_Print( -2, "\t-M <num> : the max node count of windows to consider (0 = no limit) [default = %d]\n", pPars->nWinSizeMax );
    Abc_Print( -2, "\t-L <num> : the max increase in node level after resynthesis (0 <= num) [default = %d]\n", pPars->nGrowthLevel );
    Abc_Print( -2, "\t-C <num> : the max number of conflicts in one SAT run (0 = no limit) [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-r       : toggle resubstitution and dc-minimization [default = %s]\n", pPars->fResub? "resub": "dc-min" );
    Abc_Print( -2, "\t-a       : toggle minimizing area or area+edges [default = %s]\n", pPars->fArea? "area": "area+edges" );
    Abc_Print( -2, "\t-e       : toggle high-effort resubstitution [default = %s]\n", pPars->fMoreEffort? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggle evaluation of edge swapping [default = %s]\n", pPars->fSwapEdge? "yes": "no" );
    Abc_Print( -2, "\t-t       : toggle using artificial one-hotness conditions [default = %s]\n", pPars->fOneHotness? "yes": "no" );
    Abc_Print( -2, "\t-p       : toggle power-aware optimization [default = %s]\n", pPars->fPower? "yes": "no" );
    Abc_Print( -2, "\t-g       : toggle using new SAT solver [default = %s]\n", pPars->fGiaSat? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
} 


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTrace( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseLutLib;
    int fVerbose;
    extern void Abc_NtkDelayTracePrint( Abc_Ntk_t * pNtk, int fUseLutLib, int fVerbose );

    // set defaults
    fUseLutLib = 0;
    fVerbose   = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUseLutLib ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network.\n" );
        return 1;
    }

    // modify the current network
    Abc_NtkDelayTracePrint( pNtk, fUseLutLib, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: trace [-lvh]\n" );
    Abc_Print( -2, "\t           performs delay trace of LUT-mapped network\n" );
    Abc_Print( -2, "\t-l       : toggle using unit- or LUT-library-delay model [default = %s]\n", fUseLutLib? "lib": "unit" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSpeedup( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fUseLutLib;
    int Percentage;
    int Degree;
    int fVerbose;
    int fVeryVerbose;
    extern Abc_Ntk_t * Abc_NtkSpeedup( Abc_Ntk_t * pNtk, int fUseLutLib, int Percentage, int Degree, int fVerbose, int fVeryVerbose );
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fUseLutLib = 0;
    Percentage = 5;
    Degree     = 2;
    fVerbose   = 0;
    fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PNlvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            Percentage = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Percentage < 1 || Percentage > 100 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            Degree = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Degree < 1 || Degree > 5 ) 
                goto usage;
            break;
        case 'l':
            fUseLutLib ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network.\n" );
        return 1;
    }

    // modify the current network
    pNtkRes = Abc_NtkSpeedup( pNtk, fUseLutLib, Percentage, Degree, fVerbose, fVeryVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: speedup [-PN <num>] [-lvwh]\n" );
    Abc_Print( -2, "\t           transforms LUT-mapped network into an AIG with choices;\n" );
    Abc_Print( -2, "\t           the choices are added to speedup the next round of mapping\n" );
    Abc_Print( -2, "\t-P <num> : delay delta defining critical path for library model [default = %d%%]\n", Percentage );
    Abc_Print( -2, "\t-N <num> : the max critical path degree for resynthesis (0 < num < 6) [default = %d]\n", Degree );
    Abc_Print( -2, "\t-l       : toggle using unit- or LUT-library-delay model [default = %s]\n", fUseLutLib? "lib" : "unit" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPowerdown( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fUseLutLib;
    int Percentage;
    int Degree;
    int fVerbose;
    int fVeryVerbose;
    extern Abc_Ntk_t * Abc_NtkPowerdown( Abc_Ntk_t * pNtk, int fUseLutLib, int Percentage, int Degree, int fVerbose, int fVeryVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fUseLutLib = 0;
    Percentage =10;
    Degree     = 2;
    fVerbose   = 0;
    fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PNlvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            Percentage = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Percentage < 1 || Percentage > 100 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            Degree = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Degree < 1 || Degree > 5 ) 
                goto usage;
            break;
        case 'l':
            fUseLutLib ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to a logic network.\n" );
        return 1;
    }

    // modify the current network
    pNtkRes = Abc_NtkPowerdown( pNtk, fUseLutLib, Percentage, Degree, fVerbose, fVeryVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: powerdown [-PN <num>] [-vwh]\n" );
    Abc_Print( -2, "\t           transforms LUT-mapped network into an AIG with choices;\n" );
    Abc_Print( -2, "\t           the choices are added to power down the next round of mapping\n" );
    Abc_Print( -2, "\t-P <num> : switching propability delta defining power critical edges [default = %d%%]\n", Percentage );
    Abc_Print( -2, "\t           (e.g. 5% means hot wires switch with probability: 0.45 <= p <= 0.50 (max)\n" );
    Abc_Print( -2, "\t-N <num> : the max critical path degree for resynthesis (0 < num < 6) [default = %d]\n", Degree );
//    Abc_Print( -2, "\t-l       : toggle using unit- or LUT-library-delay model [default = %s]\n", fUseLutLib? "lib" : "unit" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
} 

#if 0
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMerge( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Nwk_LMPars_t Pars, * pPars = &Pars;
    Vec_Int_t * vResult;
    int c;
    extern Vec_Int_t * Abc_NtkLutMerge( Abc_Ntk_t * pNtk, Nwk_LMPars_t * pPars );
    // set defaults
    memset( pPars, 0, sizeof(Nwk_LMPars_t) );
    pPars->nMaxLutSize    = 5;   // the max LUT size for merging (N=5)
    pPars->nMaxSuppSize   = 5;   // the max total support size after merging (S=5)
    pPars->nMaxDistance   = 3;   // the max number of nodes separating LUTs
    pPars->nMaxLevelDiff  = 2;   // the max difference in levels
    pPars->nMaxFanout     = 100; // the max number of fanouts to traverse
    pPars->fUseDiffSupp   = 0;   // enables the use of nodes with different support
    pPars->fUseTfiTfo     = 0;   // enables the use of TFO/TFO nodes as candidates
    pPars->fVeryVerbose   = 0;   // enables additional verbose output
    pPars->fVerbose       = 1;   // enables verbose output
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NSDLFscvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxLutSize < 2 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxSuppSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxSuppSize < 2 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxDistance = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxDistance < 2 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxLevelDiff = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxLevelDiff < 2 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxFanout = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxFanout < 2 ) 
                goto usage;
            break;
        case 's':
            pPars->fUseDiffSupp ^= 1;
            break;
        case 'c':
            pPars->fUseTfiTfo ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL || !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Abc_CommandMerge(): There is no mapped network to merge LUTs.\n" );
        return 1;
    }
       
    vResult = Abc_NtkLutMerge( pNtk, pPars );
    Vec_IntFree( vResult );
    return 0;

usage:
    Abc_Print( -2, "usage: merge [-NSDLF <num>] [-scwvh]\n" );
    Abc_Print( -2, "\t           creates pairs of topologically-related LUTs\n" );
    Abc_Print( -2, "\t-N <num> : the max LUT size for merging (1 < num) [default = %d]\n", pPars->nMaxLutSize );
    Abc_Print( -2, "\t-S <num> : the max total support size after merging (1 < num) [default = %d]\n", pPars->nMaxSuppSize );
    Abc_Print( -2, "\t-D <num> : the max distance in terms of LUTs (0 < num) [default = %d]\n", pPars->nMaxDistance );
    Abc_Print( -2, "\t-L <num> : the max difference in levels (0 <= num) [default = %d]\n", pPars->nMaxLevelDiff );
    Abc_Print( -2, "\t-F <num> : the max number of fanouts to stop traversal (0 < num) [default = %d]\n", pPars->nMaxFanout );
    Abc_Print( -2, "\t-s       : toggle the use of nodes without support overlap [default = %s]\n", pPars->fUseDiffSupp? "yes" : "no" );
    Abc_Print( -2, "\t-c       : toggle the use of TFI/TFO nodes as candidates [default = %s]\n", pPars->fUseTfiTfo? "yes" : "no" );
    Abc_Print( -2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}
#endif
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRewrite( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUpdateLevel;
    int fPrecompute;
    int fUseZeros;
    int fVerbose;
    int fVeryVerbose;
    int fPlaceEnable;
    // external functions
    extern void Rwr_Precompute();

    // set defaults
    fUpdateLevel = 1;
    fPrecompute  = 0;
    fUseZeros    = 0;
    fVerbose     = 0;
    fVeryVerbose = 0;
    fPlaceEnable = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lxzvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'x':
            fPrecompute ^= 1;
            break;
        case 'z':
            fUseZeros ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'p':
            fPlaceEnable ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( fPrecompute )
    {
        Rwr_Precompute();
        return 0;
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkRewrite( pNtk, fUpdateLevel, fUseZeros, fVerbose, fVeryVerbose, fPlaceEnable ) )
    {
        Abc_Print( -1, "Rewriting has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: rewrite [-lzvwh]\n" );
    Abc_Print( -2, "\t         performs technology-independent rewriting of the AIG\n" );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printout subgraph statistics [default = %s]\n", fVeryVerbose? "yes": "no" );
//    Abc_Print( -2, "\t-p     : toggle placement-aware rewriting [default = %s]\n", fPlaceEnable? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRefactor( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nNodeSizeMax;
    int nConeSizeMax;
    int fUpdateLevel;
    int fUseZeros;
    int fUseDcs;
    int fVerbose;
    extern int Abc_NtkRefactor( Abc_Ntk_t * pNtk, int nNodeSizeMax, int nConeSizeMax, int fUpdateLevel, int fUseZeros, int fUseDcs, int fVerbose );

    // set defaults
    nNodeSizeMax = 10;
    nConeSizeMax = 16;
    fUpdateLevel =  1;
    fUseZeros    =  0;
    fUseDcs      =  0;
    fVerbose     =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NClzdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodeSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodeSizeMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConeSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConeSizeMax < 0 ) 
                goto usage;
            break;
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'z':
            fUseZeros ^= 1;
            break;
        case 'd':
            fUseDcs ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }

    if ( fUseDcs && nNodeSizeMax >= nConeSizeMax )
    {
        Abc_Print( -1, "For don't-care to work, containing cone should be larger than collapsed node.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkRefactor( pNtk, nNodeSizeMax, nConeSizeMax, fUpdateLevel, fUseZeros, fUseDcs, fVerbose ) )
    {
        Abc_Print( -1, "Refactoring has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: refactor [-NC <num>] [-lzdvh]\n" );
    Abc_Print( -2, "\t           performs technology-independent refactoring of the AIG\n" );
    Abc_Print( -2, "\t-N <num> : the max support of the collapsed node [default = %d]\n", nNodeSizeMax );  
    Abc_Print( -2, "\t-C <num> : the max support of the containing cone [default = %d]\n", nConeSizeMax );  
    Abc_Print( -2, "\t-l       : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
    Abc_Print( -2, "\t-d       : toggle using don't-cares [default = %s]\n", fUseDcs? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRestructure( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nCutsMax;
    int fUpdateLevel;
    int fUseZeros;
    int fVerbose;
    extern int Abc_NtkRestructure( Abc_Ntk_t * pNtk, int nCutsMax, int fUpdateLevel, int fUseZeros, int fVerbose );

    // set defaults
    nCutsMax      =  5;
    fUpdateLevel =  0;
    fUseZeros    =  0;
    fVerbose     =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Klzvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutsMax < 0 ) 
                goto usage;
            break;
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'z':
            fUseZeros ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( nCutsMax < 4 || nCutsMax > CUT_SIZE_MAX )
    {
        Abc_Print( -1, "Can only compute the cuts for %d <= K <= %d.\n", 4, CUT_SIZE_MAX );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkRestructure( pNtk, nCutsMax, fUpdateLevel, fUseZeros, fVerbose ) )
    {
        Abc_Print( -1, "Refactoring has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: restructure [-K <num>] [-lzvh]\n" );
    Abc_Print( -2, "\t           performs technology-independent restructuring of the AIG\n" );
    Abc_Print( -2, "\t-K <num> : the max cut size (%d <= num <= %d) [default = %d]\n",   CUT_SIZE_MIN, CUT_SIZE_MAX, nCutsMax );  
    Abc_Print( -2, "\t-l       : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandResubstitute( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int RS_CUT_MIN =  4;
    int RS_CUT_MAX = 16;
    int c;
    int nCutsMax;
    int nNodesMax;
    int nLevelsOdc;
    int fUpdateLevel;
    int fUseZeros;
    int fVerbose;
    int fVeryVerbose;
    extern int Abc_NtkResubstitute( Abc_Ntk_t * pNtk, int nCutsMax, int nNodesMax, int nLevelsOdc, int fUpdateLevel, int fVerbose, int fVeryVerbose );

    // set defaults
    nCutsMax     =  8;
    nNodesMax    =  1;
    nLevelsOdc   =  0;
    fUpdateLevel =  1;
    fUseZeros    =  0;
    fVerbose     =  0;
    fVeryVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KNFlzvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutsMax < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodesMax < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nLevelsOdc = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevelsOdc < 0 ) 
                goto usage;
            break;
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'z':
            fUseZeros ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( nCutsMax < RS_CUT_MIN || nCutsMax > RS_CUT_MAX )
    {
        Abc_Print( -1, "Can only compute cuts for %d <= K <= %d.\n", RS_CUT_MIN, RS_CUT_MAX );
        return 1;
    }
    if ( nNodesMax < 0 || nNodesMax > 3 )
    {
        Abc_Print( -1, "Can only resubstitute at most 3 nodes.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkResubstitute( pNtk, nCutsMax, nNodesMax, nLevelsOdc, fUpdateLevel, fVerbose, fVeryVerbose ) )
    {
        Abc_Print( -1, "Refactoring has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: resub [-KN <num>] [-lzvwh]\n" );
    Abc_Print( -2, "\t           performs technology-independent restructuring of the AIG\n" );
    Abc_Print( -2, "\t-K <num> : the max cut size (%d <= num <= %d) [default = %d]\n", RS_CUT_MIN, RS_CUT_MAX, nCutsMax );  
    Abc_Print( -2, "\t-N <num> : the max number of nodes to add (0 <= num <= 3) [default = %d]\n", nNodesMax );  
    Abc_Print( -2, "\t-F <num> : the number of fanout levels for ODC computation [default = %d]\n", nLevelsOdc );  
    Abc_Print( -2, "\t-l       : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z       : toggle using zero-cost replacements [default = %s]\n", fUseZeros? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle verbose printout of ODC computation [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c, Window;
    int nFaninLevels;
    int nFanoutLevels;
    int fUseFanouts;
    int fVerbose;
    extern int Abc_NtkRR( Abc_Ntk_t * pNtk, int nFaninLevels, int nFanoutLevels, int fUseFanouts, int fVerbose );

    // set defaults
    nFaninLevels  = 3;
    nFanoutLevels = 3;
    fUseFanouts   = 0;
    fVerbose      = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Wfvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            Window = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Window < 0 ) 
                goto usage;
            nFaninLevels  = Window / 10;
            nFanoutLevels = Window % 10;
            break;
        case 'f':
            fUseFanouts ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command can only be applied to an AIG (run \"strash\").\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum(pNtk) )
    {
        Abc_Print( -1, "AIG resynthesis cannot be applied to AIGs with choice nodes.\n" );
        return 1;
    }

    // modify the current network
    if ( !Abc_NtkRR( pNtk, nFaninLevels, nFanoutLevels, fUseFanouts, fVerbose ) )
    {
        Abc_Print( -1, "Redundancy removal has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: rr [-W NM] [-fvh]\n" );
    Abc_Print( -2, "\t         removes combinational redundancies in the current network\n" );
    Abc_Print( -2, "\t-W NM  : window size: TFI (N) and TFO (M) logic levels [default = %d%d]\n", nFaninLevels, nFanoutLevels );
    Abc_Print( -2, "\t-f     : toggle RR w.r.t. fanouts [default = %s]\n", fUseFanouts? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCascade( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nLutSize;
    int fCheck;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkCascade( Abc_Ntk_t * pNtk, int nLutSize, int fCheck, int fVerbose );
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    nLutSize = 12;
    fCheck   = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Kcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutSize < 0 ) 
                goto usage;
            break;
        case 'c':
            fCheck ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Can only collapse a logic network or an AIG.\n" );
        return 1;
    }

    // get the new network
    if ( Abc_NtkIsStrash(pNtk) )
        pNtkRes = Abc_NtkCascade( pNtk, nLutSize, fCheck, fVerbose );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        pNtkRes = Abc_NtkCascade( pNtk, nLutSize, fCheck, fVerbose );
        Abc_NtkDelete( pNtk );
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Cascade synthesis has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: cascade [-K <num>] [-cvh]\n" );
    Abc_Print( -2, "\t           performs LUT cascade synthesis for the current network\n" );
    Abc_Print( -2, "\t-K <num> : the number of LUT inputs [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-c       : check equivalence after synthesis [default = %s]\n", fCheck? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\t           \n");
    Abc_Print( -2, "  A lookup-table cascade is a programmable architecture developed by\n");
    Abc_Print( -2, "  Professor Tsutomu Sasao (sasao@cse.kyutech.ac.jp) at Kyushu Institute\n");
    Abc_Print( -2, "  of Technology. This work received Takeda Techno-Entrepreneurship Award:\n");
    Abc_Print( -2, "  http://www.lsi-cad.com/sasao/photo/takeda.html\n");
    Abc_Print( -2, "\t         \n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLogic( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash( pNtk ) )
    {
        Abc_Print( -1, "This command is only applicable to strashed networks.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkToLogic( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Converting to a logic network has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: logic [-h]\n" );
    Abc_Print( -2, "\t        transforms an AIG into a logic network with SOPs\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandComb( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fRemoveLatches;
    int nLatchesToAdd;
    extern void Abc_NtkMakeSeq( Abc_Ntk_t * pNtk, int nLatchesToAdd );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fRemoveLatches = 0;
    nLatchesToAdd = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Llh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            } 
            nLatchesToAdd = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLatchesToAdd < 0 ) 
                goto usage;
            break;
        case 'l':
            fRemoveLatches ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsComb(pNtk) && nLatchesToAdd == 0 )
    {
        Abc_Print( -1, "The network is already combinational.\n" );
        return 0;
    }
    if ( !Abc_NtkIsComb(pNtk) && nLatchesToAdd != 0 )
    {
        Abc_Print( -1, "The network is already combinational.\n" );
        return 0;
    }

    // get the new network
    pNtkRes = Abc_NtkDup( pNtk );
    if ( nLatchesToAdd ) 
        Abc_NtkMakeSeq( pNtkRes, nLatchesToAdd );
    else
        Abc_NtkMakeComb( pNtkRes, fRemoveLatches );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: comb [-L <num>] [-lh]\n" );
    Abc_Print( -2, "\t           converts comb network into seq, and vice versa\n" );
    Abc_Print( -2, "\t-L <num> : number of latches to add to comb network (0 = do not add) [default = %d]\n", nLatchesToAdd );
    Abc_Print( -2, "\t-l       : toggle converting latches to PIs/POs or removing them [default = %s]\n", fRemoveLatches? "remove": "convert" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMiter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[32];
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2, * pNtkRes;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fCheck;
    int fComb;
    int fImplic;
    int fMulti;
    int nPartSize;
    int fTrans;
    int fIgnoreNames;

    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fComb  = 1;
    fCheck = 1;
    fImplic = 0;
    fMulti = 0;
    nPartSize = 0;
    fTrans = 0;
    fIgnoreNames = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Pcmitnh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPartSize < 0 ) 
                goto usage;
            break;
        case 'c':
            fComb ^= 1;
            break;
        case 'm':
            fMulti ^= 1;
            break;
        case 'i':
            fImplic ^= 1;
            break;
        case 't':
            fTrans ^= 1;
            break;
        case 'n':
            fIgnoreNames ^= 1;
            break;
        default:
            goto usage;
        }
    }

    if ( fTrans )
    {
        if ( (Abc_NtkPoNum(pNtk) & 1) == 1 )
        {
            Abc_Print( -1, "Abc_CommandMiter(): The number of outputs should be even.\n" );
            return 0;
        }
        // replace the current network
        pNtkRes = Abc_NtkDupTransformMiter( pNtk );
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        Abc_Print( 1, "The miter (current network) is transformed by XORing POs pair-wise.\n" );
        return 0;
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
        return 1;
    
    if ( fIgnoreNames )
    {
        Abc_NtkShortNames( pNtk1 );
        Abc_NtkShortNames( pNtk2 );
    }
    // compute the miter
    pNtkRes = Abc_NtkMiter( pNtk1, pNtk2, fComb, nPartSize, fImplic, fMulti );
    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );

    // get the new network
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Miter computation has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    if ( nPartSize == 0 )
        strcpy( Buffer, "unused" );
    else
        sprintf( Buffer, "%d", nPartSize );
    Abc_Print( -2, "usage: miter [-P <num>] [-cimtnh] <file1> <file2>\n" );
    Abc_Print( -2, "\t           computes the miter of the two circuits\n" );
    Abc_Print( -2, "\t-P <num> : output partition size [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-c       : toggles deriving combinational miter (latches as POs) [default = %s]\n", fComb? "yes": "no" );
    Abc_Print( -2, "\t-i       : toggles deriving implication miter (file1 => file2) [default = %s]\n", fImplic? "yes": "no" );
    Abc_Print( -2, "\t-m       : toggles creating multi-output miter [default = %s]\n", fMulti? "yes": "no" );
    Abc_Print( -2, "\t-t       : toggle XORing pair-wise POs of the miter [default = %s]\n", fTrans? "yes": "no" );
    Abc_Print( -2, "\t-n       : toggle ignoring names when matching CIs/COs [default = %s]\n", fIgnoreNames? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    Abc_Print( -2, "\tfile1    : (optional) the file with the first network\n");
    Abc_Print( -2, "\tfile2    : (optional) the file with the second network\n");
    Abc_Print( -2, "\t           if no files are given, uses the current network and its spec\n");
    Abc_Print( -2, "\t           if one file is given, uses the current network and the file\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDemiter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);//, * pNtkRes;
    int fDual, fSeq, fVerbose;
    int c;
    extern int Abc_NtkDemiter( Abc_Ntk_t * pNtk );
    extern int Abc_NtkDarDemiter( Abc_Ntk_t * pNtk );
    extern int Abc_NtkDarDemiterDual( Abc_Ntk_t * pNtk, int fVerbose );

    extern int Abc_NtkDarDemiterNew( Abc_Ntk_t * pNtk );

    // set defaults
    fDual = 0;
    fSeq = 1;
    fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDual ^= 1;
            break;
        case 's':
            fSeq ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    } 

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "The network is not strashed.\n" );
        return 1;
    }

//    Abc_NtkDarDemiterNew( pNtk );
//    return 0;

    if ( fDual )
    {
        if ( (Abc_NtkPoNum(pNtk) & 1) )
        {
            Abc_Print( -1, "The number of POs should be even.\n" );
            return 0;
        }
        if ( !Abc_NtkDarDemiterDual( pNtk, fVerbose ) )
        {
            Abc_Print( -1, "Demitering has failed.\n" );
            return 1;
        }
        return 0;
    }

    // get the new network
    if ( fSeq )
    {
        if ( !Abc_NtkDarDemiter( pNtk ) )
        {
            Abc_Print( -1, "Demitering has failed.\n" );
            return 1;
        }
    }
    else
    {
        if ( Abc_NtkPoNum(pNtk) != 1 )
        {
            Abc_Print( -1, "The network is not a single-output miter.\n" );
            return 1;
        }
        if ( !Abc_NodeIsExorType(Abc_ObjFanin0(Abc_NtkPo(pNtk,0))) )
        {
            Abc_Print( -1, "The miter's PO is not an EXOR.\n" );
            return 1;
        }
        if ( !Abc_NtkDemiter( pNtk ) )
        {
            Abc_Print( -1, "Demitering has failed.\n" );
            return 1;
        }
    }
    // replace the current network
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: demiter [-dsvh]\n" );
    Abc_Print( -2, "\t        removes topmost XOR from the miter to create two POs\n" );
    Abc_Print( -2, "\t-d    : demiters a dual-output miter (without XORs) [default = %s]\n", fSeq? "yes": "no" );
    Abc_Print( -2, "\t-s    : applies a multi-output algorithm [default = %s]\n", fSeq? "yes": "no" );
    Abc_Print( -2, "\t-v    : toggles outputting verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandOrPos( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);//, * pNtkRes;
    int fComb = 0;
    int c;
    extern int Abc_NtkCombinePos( Abc_Ntk_t * pNtk, int fAnd );

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ch" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fComb ^= 1;
            break;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "The network is not strashed.\n" );
        return 1;
    }
/*
    if ( Abc_NtkPoNum(pNtk) == 1 )
    {
        Abc_Print( -1, "The network already has one PO.\n" );
        return 1;
    }
*/
/*
    if ( Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The miter has latches. ORing is not performed.\n" );
        return 1;
    }
*/
    // get the new network
    if ( !Abc_NtkCombinePos( pNtk, 0 ) )
    {
        Abc_Print( -1, "ORing the POs has failed.\n" );
        return 1;
    }
    // Bug fix: there is now only one PO.  make sure the counterexample points to the right one
    if ( pAbc->pCex )
        pAbc->pCex->iPo = 0;
    // replace the current network
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: orpos [-h]\n" );
    Abc_Print( -2, "\t        creates single-output miter by ORing the POs of the current network\n" );
//    Abc_Print( -2, "\t-c    : computes combinational miter (latches as POs) [default = %s]\n", fComb? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAndPos( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);//, * pNtkRes;
    int fComb = 0;
    int c;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ch" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fComb ^= 1;
            break;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "The network is not strashed.\n" );
        return 1;
    }

    if ( Abc_NtkPoNum(pNtk) == 1 )
    {
        Abc_Print( -1, "The network already has one PO.\n" );
        return 1;
    }

    if ( Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The miter has latches. ORing is not performed.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkCombinePos( pNtk, 1 ) )
    {
        Abc_Print( -1, "ANDing the POs has failed.\n" );
        return 1;
    }
    // replace the current network
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: andpos [-h]\n" );
    Abc_Print( -2, "\t        creates single-output miter by ANDing the POs of the current network\n" );
//    Abc_Print( -2, "\t-c    : computes combinational miter (latches as POs) [default = %s]\n", fComb? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandZeroPo( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkRes = NULL;
    int c, iOutput = -1;
    extern void Abc_NtkDropOneOutput( Abc_Ntk_t * pNtk, int iOutput );

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            iOutput = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iOutput < 0 ) 
                goto usage;
            break;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "The network is not strashed.\n" );
        return 1;
    }
    if ( iOutput < 0 )
    {
        Abc_Print( -1, "The output index is not specified.\n" );
        return 1;
    }
    if ( iOutput >= Abc_NtkPoNum(pNtk) )
    {
        Abc_Print( -1, "The output index is larger than the allowed POs.\n" );
        return 1;
    }

    // get the new network
//    pNtkRes = Abc_NtkDup( pNtk );
//    Abc_NtkDropOneOutput( pNtkRes, iOutput );
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    Abc_NtkDropOneOutput( pNtk, iOutput );
    return 0;

usage:
    Abc_Print( -2, "usage: zeropo [-N <num>] [-h]\n" );
    Abc_Print( -2, "\t           replaces the PO driver by constant 0\n" );
    Abc_Print( -2, "\t-N <num> : the zero-based index of the PO to replace [default = %d]\n", iOutput );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSwapPos( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkRes;
    int c, iOutput = -1;
    extern void Abc_NtkSwapOneOutput( Abc_Ntk_t * pNtk, int iOutput );

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            iOutput = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iOutput < 0 ) 
                goto usage;
            break;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "The network is not strashed.\n" );
        return 1;
    }
    if ( iOutput < 0 )
    {
        Abc_Print( -1, "The output index is not specified.\n" );
        return 1;
    }
    if ( iOutput >= Abc_NtkPoNum(pNtk) )
    {
        Abc_Print( -1, "The output index is larger than the allowed POs.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkDup( pNtk );
    Abc_NtkSwapOneOutput( pNtkRes, iOutput );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: swappos [-N <num>] [-h]\n" );
    Abc_Print( -2, "\t           swap the 0-th PO with the <num>-th PO\n" );
    Abc_Print( -2, "\t-N <num> : the zero-based index of the PO to swap [default = %d]\n", iOutput );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRemovePo( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkRes = NULL;
    int c, iOutput = -1;
    extern void Abc_NtkRemovePo( Abc_Ntk_t * pNtk, int iOutput );

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            iOutput = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iOutput < 0 ) 
                goto usage;
            break;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "The network is not strashed.\n" );
        return 1;
    }
    if ( iOutput < 0 )
    {
        Abc_Print( -1, "The output index is not specified.\n" );
        return 1;
    }
    if ( iOutput >= Abc_NtkPoNum(pNtk) )
    {
        Abc_Print( -1, "The output index is larger than the allowed POs.\n" );
        return 1;
    }

    // get the new network
//    pNtkRes = Abc_NtkDup( pNtk );
//    Abc_NtkRemovePo( pNtkRes, iOutput );
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    Abc_NtkRemovePo( pNtk, iOutput );
    return 0;

usage:
    Abc_Print( -2, "usage: removepo [-N <num>] [-h]\n" );
    Abc_Print( -2, "\t           remove PO with number <num> if it is const0\n" );
    Abc_Print( -2, "\t-N <num> : the zero-based index of the PO to remove [default = %d]\n", iOutput );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAddPi( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtkRes;
    int c;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h': 
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkDup( pNtk );
    if ( Abc_NtkPiNum(pNtkRes) == 0 )
    {
        Abc_Obj_t * pObj = Abc_NtkCreatePi( pNtkRes );
        Abc_ObjAssignName( pObj, "dummy_pi", NULL );
        Abc_NtkOrderCisCos( pNtkRes );
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: addpi [-h]\n" );
    Abc_Print( -2, "\t         if the network has no PIs, add one dummy PI\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAppend( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtk2;
    char * FileName;
    int fComb = 0;
    int c;
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ch" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fComb ^= 1;
            break;
        default:
            goto usage;
        }
    }

    // get the second network
    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "The network to append is not given.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "The base network should be strashed for the appending to work.\n" );
        return 1;
    }

    // read the second network
    FileName = argv[globalUtilOptind];
    pNtk2 = Io_Read( FileName, Io_ReadFileType(FileName), 1 );
    if ( pNtk2 == NULL )
        return 1;

    // check if the second network is combinational
    if ( Abc_NtkLatchNum(pNtk2) )
    {
        Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "The second network has latches. Appending does not work for such networks.\n" );
        return 0;
    }

    // get the new network
    if ( !Abc_NtkAppend( pNtk, pNtk2, 1 ) )
    {
        Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "Appending the networks failed.\n" );
        return 1;
    }
    Abc_NtkDelete( pNtk2 );
    // sweep dangling logic
    Abc_AigCleanup( (Abc_Aig_t *)pNtk->pManFunc );
    // replace the current network
//    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: append [-h] <file>\n" );
    Abc_Print( -2, "\t         appends a combinational network on top of the current network\n" );
//    Abc_Print( -2, "\t-c     : computes combinational miter (latches as POs) [default = %s]\n", fComb? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file name with the second network\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFrames( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkTemp, * pNtkRes;
    int nFrames;
    int fInitial;
    int fVerbose;
    int c;
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    nFrames  = 5;
    fInitial = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames <= 0 ) 
                goto usage;
            break;
        case 'i':
            fInitial ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );
        pNtkRes  = Abc_NtkFrames( pNtkTemp, nFrames, fInitial, fVerbose );
        Abc_NtkDelete( pNtkTemp );
    }
    else
        pNtkRes  = Abc_NtkFrames( pNtk, nFrames, fInitial, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Unrolling the network has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: frames [-F <num>] [-ivh]\n" );
    Abc_Print( -2, "\t           unrolls the network for a number of time frames\n" );
    Abc_Print( -2, "\t-F <num> : the number of frames to unroll [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-i       : toggles initializing the first frame [default = %s]\n", fInitial? "yes": "no" );  
    Abc_Print( -2, "\t-v       : toggles outputting verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDFrames( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkTemp, * pNtkRes;
    int nPrefix;
    int nFrames;
    int fInitial;
    int fVerbose;
    int c;

    extern Abc_Ntk_t * Abc_NtkDarFrames( Abc_Ntk_t * pNtk, int nPrefix, int nFrames, int fInitial, int fVerbose );
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    nPrefix  = 5;
    nFrames  = 5;
    fInitial = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NFivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nPrefix = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPrefix <= 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames <= 0 ) 
                goto usage;
            break;
        case 'i':
            fInitial ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( nPrefix > nFrames )
    {
        Abc_Print( -1, "Prefix (%d) cannot be more than the number of frames (%d).\n", nPrefix, nFrames );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );
        pNtkRes  = Abc_NtkDarFrames( pNtkTemp, nPrefix, nFrames, fInitial, fVerbose );
        Abc_NtkDelete( pNtkTemp );
    }
    else
        pNtkRes  = Abc_NtkDarFrames( pNtk, nPrefix, nFrames, fInitial, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Unrolling the network has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: dframes [-NF <num>] [-ivh]\n" );
    Abc_Print( -2, "\t         unrolls the network with simplification\n" );
    Abc_Print( -2, "\t-N num : the number of frames to use as prefix [default = %d]\n", nPrefix );
    Abc_Print( -2, "\t-F num : the number of frames to unroll [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-i     : toggles initializing the first frame [default = %s]\n", fInitial? "yes": "no" );  
    Abc_Print( -2, "\t-v     : toggles outputting verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSop( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int fDirect;
    int c;

    // set defaults
    fDirect = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDirect ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Converting to SOP is possible only for logic networks.\n" );
        return 1;
    }
    if ( !Abc_NtkToSop(pNtk, fDirect) )
    {
        Abc_Print( -1, "Converting to SOP has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: sop [-dh]\n" );
    Abc_Print( -2, "\t         converts node functions to SOP\n" );
    Abc_Print( -2, "\t-d     : toggles using both phases or only positive [default = %s]\n", fDirect? "direct": "both" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBdd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Converting to BDD is possible only for logic networks.\n" );
        return 1;
    }
    if ( Abc_NtkIsBddLogic(pNtk) )
    {
        Abc_Print( -1, "The logic network is already in the BDD form.\n" );
        return 0;
    }
    if ( !Abc_NtkToBdd(pNtk) )
    {
        Abc_Print( -1, "Converting to BDD has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: bdd [-h]\n" );
    Abc_Print( -2, "\t         converts node functions to BDD\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Converting to AIG is possible only for logic networks.\n" );
        return 1;
    }
    if ( Abc_NtkIsAigLogic(pNtk) )
    {
        Abc_Print( -1, "The logic network is already in the AIG form.\n" );
        return 0;
    }
    if ( !Abc_NtkToAig(pNtk) )
    {
        Abc_Print( -1, "Converting to AIG has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: aig [-h]\n" );
    Abc_Print( -2, "\t         converts node functions to AIG\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandReorder( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fVerbose;
    extern void Abc_NtkBddReorder( Abc_Ntk_t * pNtk, int fVerbose );

    // set defaults
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkIsBddLogic(pNtk) )
    {
        Abc_Print( -1, "Variable reordering is possible when node functions are BDDs (run \"bdd\").\n" );
        return 1;
    }
    Abc_NtkBddReorder( pNtk, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: reorder [-vh]\n" );
    Abc_Print( -2, "\t         reorders local functions of the nodes using sifting\n" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBidec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fVerbose;
    extern void Abc_NtkBidecResyn( Abc_Ntk_t * pNtk, int fVerbose );

    // set defaults
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkIsAigLogic(pNtk) )
    {
        Abc_Print( -1, "Bi-decomposition only works when node functions are AIGs (run \"aig\").\n" );
        return 1;
    }
    Abc_NtkBidecResyn( pNtk, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: bidec [-vh]\n" );
    Abc_Print( -2, "\t         applies bi-decomposition to local functions of the nodes\n" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandOrder( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pFile;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    char * pFileName;
    int c;
    int fReverse;
    int fVerbose;
    extern void Abc_NtkImplementCiOrder( Abc_Ntk_t * pNtk, char * pFileName, int fReverse, int fVerbose );
    extern void Abc_NtkFindCiOrder( Abc_Ntk_t * pNtk, int fReverse, int fVerbose );

    // set defaults
    fReverse = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'r':
            fReverse ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
//    if ( Abc_NtkLatchNum(pNtk) > 0 )
//    {
//        Abc_Print( -1, "Currently this procedure does not work for sequential networks.\n" );
//        return 1;
//    }

    // if the var order file is given, implement this order
    pFileName = NULL;
    if ( argc == globalUtilOptind + 1 )
    {
        pFileName = argv[globalUtilOptind];
        pFile = fopen( pFileName, "r" );
        if ( pFile == NULL )
        {
            Abc_Print( -1, "Cannot open file \"%s\" with the BDD variable order.\n", pFileName );
            return 1;
        }
        fclose( pFile );
    }
    if ( pFileName )
        Abc_NtkImplementCiOrder( pNtk, pFileName, fReverse, fVerbose );
    else
        Abc_NtkFindCiOrder( pNtk, fReverse, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: order [-rvh] <file>\n" );
    Abc_Print( -2, "\t         computes a good static CI variable order\n" );
    Abc_Print( -2, "\t-r     : toggle reverse ordering [default = %s]\n", fReverse? "yes": "no" );  
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : (optional) file with the given variable order\n" );  
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMuxes( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsBddLogic(pNtk) )
    {
        Abc_Print( -1, "Only a BDD logic network can be converted to MUXes.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkBddToMuxes( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Converting to MUXes has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: muxes [-h]\n" );
    Abc_Print( -2, "\t        converts the current network into a network derived by\n" );
    Abc_Print( -2, "\t        replacing all nodes by DAGs isomorphic to the local BDDs\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandExtSeqDcs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fVerbose;
    extern int Abc_NtkExtractSequentialDcs( Abc_Ntk_t * pNet, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "The current network has no latches.\n" );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Extracting sequential don't-cares works only for AIGs (run \"strash\").\n" );
        return 0;
    }
    if ( !Abc_NtkExtractSequentialDcs( pNtk, fVerbose ) )
    {
        Abc_Print( -1, "Extracting sequential don't-cares has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: ext_seq_dcs [-vh]\n" );
    Abc_Print( -2, "\t         create EXDC network using unreachable states\n" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandReach( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Saig_ParBbr_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    char * pLogFileName = NULL;

    extern int Abc_NtkDarReach( Abc_Ntk_t * pNtk, Saig_ParBbr_t * pPars );

    // set defaults
    Bbr_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TBFLproyvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeLimit < 0 ) 
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBddMax < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterMax < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'p':
            pPars->fPartition ^= 1;
            break;
        case 'r':
            pPars->fReorder ^= 1;
            break;
        case 'o':
            pPars->fReorderImage ^= 1;
            break;
        case 'y':
            pPars->fSkipOutCheck ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "The current network has no latches.\n" );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Reachability analysis works only for AIGs (run \"strash\").\n" );
        return 1;
    }
    pAbc->Status  = Abc_NtkDarReach( pNtk, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "reach" );
    return 0;

usage:
    Abc_Print( -2, "usage: reach [-TBF num] [-L file] [-proyvh]\n" );
    Abc_Print( -2, "\t         verifies sequential miter using BDD-based reachability\n" );
    Abc_Print( -2, "\t-T num : approximate time limit in seconds (0=infinite) [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-B num : max number of nodes in the intermediate BDDs [default = %d]\n", pPars->nBddMax );
    Abc_Print( -2, "\t-F num : max number of reachability iterations [default = %d]\n", pPars->nIterMax );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-p     : enable partitioned image computation [default = %s]\n", pPars->fPartition? "yes": "no" );  
    Abc_Print( -2, "\t-r     : enable dynamic BDD variable reordering [default = %s]\n", pPars->fReorder? "yes": "no" );  
    Abc_Print( -2, "\t-o     : toggles BDD variable reordering during image computation [default = %s]\n", pPars->fReorderImage? "yes": "no" );
    Abc_Print( -2, "\t-y     : skip checking property outputs [default = %s]\n", pPars->fSkipOutCheck? "yes": "no" );  
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCone( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Abc_Obj_t * pNode, * pNodeCo;
    int c;
    int fUseAllCis;
    int fUseMffc;
    int fSeq;
    int Output;
    int nRange;

    extern Abc_Ntk_t * Abc_NtkMakeOnePo( Abc_Ntk_t * pNtk, int Output, int nRange );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fUseAllCis = 0;
    fUseMffc = 0;
    fSeq = 0;
    Output = -1;
    nRange = -1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ORmash" ) ) != EOF )
    {
        switch ( c )
        {
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            Output = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Output < 0 ) 
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRange = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRange < 0 ) 
                goto usage;
            break;
        case 'm':
            fUseMffc ^= 1;
            break;
        case 'a':
            fUseAllCis ^= 1;
            break;
        case 's':
            fSeq ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently can only be applied to the logic network or an AIG.\n" );
        return 1;
    }

    if ( argc > globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }

    pNodeCo = NULL;
    if ( argc == globalUtilOptind + 1 )
    {
        pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
        if ( pNode == NULL )
        {
            Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
            return 1;
        }
        if ( fUseMffc )
            pNtkRes = Abc_NtkCreateMffc( pNtk, pNode, argv[globalUtilOptind] );
        else
            pNtkRes = Abc_NtkCreateCone( pNtk, pNode, argv[globalUtilOptind], fUseAllCis );
    }
    else
    {
        if ( Output == -1 )
        {
            Abc_Print( -1, "The node is not specified.\n" );
            return 1;
        }
        if ( Output >= Abc_NtkCoNum(pNtk) )
        {
            Abc_Print( -1, "The 0-based output number (%d) is larger than the number of outputs (%d).\n", Output, Abc_NtkCoNum(pNtk) );
            return 1;
        }
        pNodeCo = Abc_NtkCo( pNtk, Output );
        if ( fSeq )
            pNtkRes = Abc_NtkMakeOnePo( pNtk, Output, nRange );
        else if ( fUseMffc )
            pNtkRes = Abc_NtkCreateMffc( pNtk, Abc_ObjFanin0(pNodeCo), Abc_ObjName(pNodeCo) );
        else 
            pNtkRes = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pNodeCo), Abc_ObjName(pNodeCo), fUseAllCis );
    }
    if ( pNodeCo && Abc_ObjFaninC0(pNodeCo) && !fSeq )
    {
        Abc_NtkPo(pNtkRes, 0)->fCompl0  ^= 1;
//        Abc_Print( -1, "The extracted cone represents the complement function of the CO.\n" );
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Writing the logic cone of one node has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: cone [-OR num] [-amsh] <name>\n" );
    Abc_Print( -2, "\t         replaces the current network by one logic cone\n" );
    Abc_Print( -2, "\t-a     : toggle keeping all CIs or structral support only [default = %s]\n", fUseAllCis? "all": "structural" );
    Abc_Print( -2, "\t-m     : toggle keeping only MFFC or complete TFI cone [default = %s]\n", fUseMffc? "MFFC": "TFI cone" );
    Abc_Print( -2, "\t-s     : toggle comb or sequential cone (works with \"-O num\") [default = %s]\n", fSeq? "seq": "comb" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t-O num : (optional) the 0-based number of the CO to extract\n");
    Abc_Print( -2, "\t-R num : (optional) the number of outputs to extract\n");
    Abc_Print( -2, "\tname   : (optional) the name of the node to extract\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandNode( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Abc_Obj_t * pNode;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
       case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Currently can only be applied to a logic network.\n" );
        return 1;
    }

    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Wrong number of auguments.\n" );
        goto usage;
    }

    pNode = Abc_NtkFindNode( pNtk, argv[globalUtilOptind] );
    if ( pNode == NULL )
    {
        Abc_Print( -1, "Cannot find node \"%s\".\n", argv[globalUtilOptind] );
        return 1;
    }

    pNtkRes = Abc_NtkCreateFromNode( pNtk, pNode );
//    pNtkRes = Abc_NtkDeriveFromBdd( pNtk->pManFunc, pNode->pData, NULL, NULL );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Splitting one node has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: node [-h] <name>\n" );
    Abc_Print( -2, "\t         replaces the current network by the network composed of one node\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tname   : the node name\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTopmost( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nLevels;
    extern Abc_Ntk_t * Abc_NtkTopmost( Abc_Ntk_t * pNtk, int nLevels );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nLevels = 10;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nLevels = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevels < 0 ) 
                goto usage;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }

    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Currently can only works for combinational circuits.\n" );
        return 0;
    } 
    if ( Abc_NtkPoNum(pNtk) != 1 )
    {
        Abc_Print( -1, "Currently expects a single-output miter.\n" );
        return 0;
    } 

    pNtkRes = Abc_NtkTopmost( pNtk, nLevels );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: topmost [-N num] [-h]\n" );
    Abc_Print( -2, "\t         replaces the current network by several of its topmost levels\n" );
    Abc_Print( -2, "\t-N num : max number of levels [default = %d]\n", nLevels );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tname   : the node name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTopAnd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    extern Abc_Ntk_t * Abc_NtkTopAnd( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }

    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Currently can only works for combinational circuits.\n" );
        return 0;
    } 
    if ( Abc_NtkPoNum(pNtk) != 1 )
    {
        Abc_Print( -1, "Currently expects a single-output miter.\n" );
        return 0;
    } 
    if ( Abc_ObjFaninC0(Abc_NtkPo(pNtk, 0)) )
    {
        Abc_Print( -1, "The PO driver is complemented. AND-decomposition is impossible.\n" );
        return 0;
    } 
    if ( !Abc_ObjIsNode(Abc_ObjChild0(Abc_NtkPo(pNtk, 0))) )
    {
        Abc_Print( -1, "The PO driver is not a node. AND-decomposition is impossible.\n" );
        return 0;
    } 
    pNtkRes = Abc_NtkTopAnd( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: topand [-h]\n" );
    Abc_Print( -2, "\t         performs AND-decomposition of single-output combinational miter\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tname   : the node name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []
 
  SeeAlso     []

***********************************************************************/
int Abc_CommandTrim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nLevels;
    extern Abc_Ntk_t * Abc_NtkTrim( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nLevels = 10;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nh" ) ) != EOF )
    {
        switch ( c )
        {
/* 
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nLevels = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevels < 0 ) 
                goto usage;
            break;
*/
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for logic circuits.\n" );
        return 0;
    }

    pNtkRes = Abc_NtkTrim( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "The command has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: trim [-h]\n" );
    Abc_Print( -2, "\t         removes POs fed by PIs and constants, and PIs w/o fanout\n" );
//    Abc_Print( -2, "\t-N num : max number of levels [default = %d]\n", nLevels );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandShortNames( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    Abc_NtkShortNames( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: short_names [-h]\n" );
    Abc_Print( -2, "\t         replaces PI/PO/latch names by short char strings\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandExdcFree( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( pNtk->pExdc == NULL )
    {
        Abc_Print( -1, "The network has no EXDC.\n" );
        return 1;
    }

    Abc_NtkDelete( pNtk->pExdc );
    pNtk->pExdc = NULL;

    // replace the current network
    pNtkRes = Abc_NtkDup( pNtk );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: exdc_free [-h]\n" );
    Abc_Print( -2, "\t         frees the EXDC network of the current network\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandExdcGet( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( pNtk->pExdc == NULL )
    {
        Abc_Print( -1, "The network has no EXDC.\n" );
        return 1;
    }

    // replace the current network
    pNtkRes = Abc_NtkDup( pNtk->pExdc );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: exdc_get [-h]\n" );
    Abc_Print( -2, "\t         replaces the current network by the EXDC of the current network\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandExdcSet( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pFile;
    Abc_Ntk_t * pNtk, * pNtkNew, * pNtkRes;
    char * FileName;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( argc != globalUtilOptind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[globalUtilOptind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".mv", ".blif", ".pla", ".eqn", ".bench" )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );

    // set the new network
    pNtkNew = Io_Read( FileName, Io_ReadFileType(FileName), 1 );
    if ( pNtkNew == NULL )
    {
        Abc_Print( -1, "Reading network from file has failed.\n" );
        return 1;
    }

    // replace the EXDC
    if ( pNtk->pExdc )
    {
        Abc_NtkDelete( pNtk->pExdc );
        pNtk->pExdc = NULL;
    }
    pNtkRes = Abc_NtkDup( pNtk );
    pNtkRes->pExdc = pNtkNew;

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: exdc_set [-h] <file>\n" );
    Abc_Print( -2, "\t         sets the network from file as EXDC for the current network\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file with the new EXDC network\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCareSet( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pFile;
    Abc_Ntk_t * pNtk, * pNtkNew, * pNtkRes;
    char * FileName;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( argc != globalUtilOptind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[globalUtilOptind];
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".mv", ".blif", ".pla", ".eqn", ".bench" )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );

    // set the new network
    pNtkNew = Io_Read( FileName, Io_ReadFileType(FileName), 1 );
    if ( pNtkNew == NULL )
    {
        Abc_Print( -1, "Reading network from file has failed.\n" );
        return 1;
    }

    // replace the EXDC
    if ( pNtk->pExcare )
    {
        Abc_NtkDelete( (Abc_Ntk_t *)pNtk->pExcare );
        pNtk->pExcare = NULL;
    }
    pNtkRes = Abc_NtkDup( pNtk );
    pNtkRes->pExcare = pNtkNew;

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: care_set [-h] <file>\n" );
    Abc_Print( -2, "\t         sets the network from file as a care for the current network\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : file with the new care network\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cut_Params_t Params, * pParams = &Params;
    Cut_Man_t * pCutMan;
    Cut_Oracle_t * pCutOracle = NULL;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fOracle;
    extern Cut_Man_t * Abc_NtkCuts( Abc_Ntk_t * pNtk, Cut_Params_t * pParams );
    extern void Abc_NtkCutsOracle( Abc_Ntk_t * pNtk, Cut_Oracle_t * pCutOracle );

    // set defaults
    fOracle = 0;
    memset( pParams, 0, sizeof(Cut_Params_t) );
    pParams->nVarsMax    = 5;     // the max cut size ("k" of the k-feasible cuts)
    pParams->nKeepMax    = 1000;  // the max number of cuts kept at a node
    pParams->fTruth      = 1;     // compute truth tables
    pParams->fFilter     = 1;     // filter dominated cuts
    pParams->fDrop       = 0;     // drop cuts on the fly
    pParams->fDag        = 1;     // compute DAG cuts
    pParams->fTree       = 0;     // compute tree cuts
    pParams->fGlobal     = 0;     // compute global cuts
    pParams->fLocal      = 0;     // compute local cuts
    pParams->fFancy      = 0;     // compute something fancy
    pParams->fRecordAig  = 1;     // compute something fancy
    pParams->fMap        = 0;     // compute mapping delay
    pParams->fAdjust     = 0;     // removes useless fanouts
    pParams->fNpnSave    = 0;     // enables dumping truth tables  
    pParams->fVerbose    = 0;     // the verbosiness flag
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KMtfdxyglzamjvosh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nVarsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nVarsMax < 0 ) 
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nKeepMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nKeepMax < 0 ) 
                goto usage;
            break;
        case 't':
            pParams->fTruth ^= 1;
            break;
        case 'f':
            pParams->fFilter ^= 1;
            break;
        case 'd':
            pParams->fDrop ^= 1;
            break;
        case 'x':
            pParams->fDag ^= 1;
            break;
        case 'y':
            pParams->fTree ^= 1;
            break;
        case 'g':
            pParams->fGlobal ^= 1;
            break;
        case 'l':
            pParams->fLocal ^= 1;
            break;
        case 'z':
            pParams->fFancy ^= 1;
            break;
        case 'a':
            pParams->fRecordAig ^= 1;
            break;
        case 'm':
            pParams->fMap ^= 1;
            break;
        case 'j':
            pParams->fAdjust ^= 1;
            break;
        case 'v':
            pParams->fVerbose ^= 1;
            break;
        case 'o':
            fOracle ^= 1;
            break;
        case 's':
            pParams->fNpnSave ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Cut computation is available only for AIGs (run \"strash\").\n" );
        return 1;
    }
    if ( pParams->nVarsMax < CUT_SIZE_MIN || pParams->nVarsMax > CUT_SIZE_MAX )
    {
        Abc_Print( -1, "Can only compute the cuts for %d <= K <= %d.\n", CUT_SIZE_MIN, CUT_SIZE_MAX );
        return 1;
    }
    if ( pParams->fDag && pParams->fTree )
    {
        Abc_Print( -1, "Cannot compute both DAG cuts and tree cuts at the same time.\n" );
        return 1;
    }

    if ( pParams->fNpnSave )
    {
        pParams->nVarsMax = 6;
        pParams->fTruth = 1;
    }

    if ( fOracle )
        pParams->fRecord = 1;
    pCutMan = Abc_NtkCuts( pNtk, pParams );
    if ( fOracle )
        pCutOracle = Cut_OracleStart( pCutMan );
    Cut_ManStop( pCutMan );
    if ( fOracle )
    {
        assert(pCutOracle);
        Abc_NtkCutsOracle( pNtk, pCutOracle );
        Cut_OracleStop( pCutOracle );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: cut [-K num] [-M num] [-tfdcovamjsvh]\n" );
    Abc_Print( -2, "\t         computes k-feasible cuts for the AIG\n" );
    Abc_Print( -2, "\t-K num : max number of leaves (%d <= num <= %d) [default = %d]\n",     CUT_SIZE_MIN, CUT_SIZE_MAX, pParams->nVarsMax );
    Abc_Print( -2, "\t-M num : max number of cuts stored at a node [default = %d]\n",        pParams->nKeepMax );
    Abc_Print( -2, "\t-t     : toggle truth table computation [default = %s]\n",             pParams->fTruth?   "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle filtering of duplicated/dominated [default = %s]\n",   pParams->fFilter?  "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle dropping when fanouts are done [default = %s]\n",      pParams->fDrop?    "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle computing only DAG cuts [default = %s]\n",             pParams->fDag?     "yes": "no" );
    Abc_Print( -2, "\t-y     : toggle computing only tree cuts [default = %s]\n",            pParams->fTree?    "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle computing only global cuts [default = %s]\n",          pParams->fGlobal?  "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle computing only local cuts [default = %s]\n",           pParams->fLocal?   "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle fancy computations [default = %s]\n",                  pParams->fFancy?   "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle recording cut functions [default = %s]\n",             pParams->fRecordAig?"yes": "no" );
    Abc_Print( -2, "\t-m     : toggle delay-oriented FPGA mapping [default = %s]\n",         pParams->fMap?     "yes": "no" );
    Abc_Print( -2, "\t-j     : toggle removing fanouts due to XOR/MUX [default = %s]\n",     pParams->fAdjust?  "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle creating library of 6-var functions [default = %s]\n", pParams->fNpnSave?  "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",        pParams->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandScut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cut_Params_t Params, * pParams = &Params;
    Cut_Man_t * pCutMan;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    extern Cut_Man_t * Abc_NtkSeqCuts( Abc_Ntk_t * pNtk, Cut_Params_t * pParams );

    // set defaults
    memset( pParams, 0, sizeof(Cut_Params_t) );
    pParams->nVarsMax  = 5;     // the max cut size ("k" of the k-feasible cuts)
    pParams->nKeepMax  = 1000;  // the max number of cuts kept at a node
    pParams->fTruth    = 0;     // compute truth tables
    pParams->fFilter   = 1;     // filter dominated cuts
    pParams->fSeq      = 1;     // compute sequential cuts
    pParams->fVerbose  = 0;     // the verbosiness flag
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KMtvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nVarsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nVarsMax < 0 ) 
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nKeepMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nKeepMax < 0 ) 
                goto usage;
            break;
        case 't':
            pParams->fTruth ^= 1;
            break;
        case 'v':
            pParams->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
/*
    if ( !Abc_NtkIsSeq(pNtk) )
    {
        Abc_Print( -1, "Sequential cuts can be computed for sequential AIGs (run \"seq\").\n" );
        return 1;
    }
*/
    if ( pParams->nVarsMax < CUT_SIZE_MIN || pParams->nVarsMax > CUT_SIZE_MAX )
    {
        Abc_Print( -1, "Can only compute the cuts for %d <= K <= %d.\n", CUT_SIZE_MIN, CUT_SIZE_MAX );
        return 1;
    }

    pCutMan = Abc_NtkSeqCuts( pNtk, pParams );
    Cut_ManStop( pCutMan );
    return 0;

usage:
    Abc_Print( -2, "usage: scut [-K num] [-M num] [-tvh]\n" );
    Abc_Print( -2, "\t         computes k-feasible cuts for the sequential AIG\n" );
    Abc_Print( -2, "\t-K num : max number of leaves (%d <= num <= %d) [default = %d]\n",   CUT_SIZE_MIN, CUT_SIZE_MAX, pParams->nVarsMax );
    Abc_Print( -2, "\t-M num : max number of cuts stored at a node [default = %d]\n",      pParams->nKeepMax );
    Abc_Print( -2, "\t-t     : toggle truth table computation [default = %s]\n",           pParams->fTruth?   "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n",      pParams->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandEspresso( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fVerbose;
    extern void Abc_NtkEspresso( Abc_Ntk_t * pNtk, int fVerbose );

    Abc_Print( -1, "This command is currently disabled.\n" );
    return 0;

    // set defaults
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "SOP minimization is possible for logic networks (run \"renode\").\n" );
        return 1;
    }
//    Abc_NtkEspresso( pNtk, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: espresso [-vh]\n" );
    Abc_Print( -2, "\t         minimizes SOPs of the local functions using Espresso\n" );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandGen( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nVars;    // the number of variables
    int nLutSize; // the size of LUTs
    int nLuts;    // the number of LUTs
    int fAdder;
    int fSorter;
    int fMesh;
    int fFpga;
    int fOneHot;
    int fRandom;
    int fVerbose;
    char * FileName;
    extern void Abc_GenAdder( char * pFileName, int nVars );
    extern void Abc_GenSorter( char * pFileName, int nVars );
    extern void Abc_GenMesh( char * pFileName, int nVars );
    extern void Abc_GenFpga( char * pFileName, int nLutSize, int nLuts, int nVars );
    extern void Abc_GenOneHot( char * pFileName, int nVars );
    extern void Abc_GenRandom( char * pFileName, int nPis );

    // set defaults
    nVars = 8;
    fAdder = 0;
    fSorter = 0;
    fMesh = 0;
    fFpga = 0;
    fOneHot = 0;
    fRandom = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NKLasmftrvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 0 ) 
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutSize < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLuts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLuts < 0 ) 
                goto usage;
            break;
        case 'a':
            fAdder ^= 1;
            break;
        case 's':
            fSorter ^= 1;
            break;
        case 'm':
            fMesh ^= 1;
            break;
        case 'f':
            fFpga ^= 1;
            break;
        case 't':
            fOneHot ^= 1;
            break;
        case 'r':
            fRandom ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( argc != globalUtilOptind + 1 )
    {
        goto usage;
    }

    // get the input file name
    FileName = argv[globalUtilOptind];
    if ( fAdder )
        Abc_GenAdder( FileName, nVars );
    else if ( fSorter )
        Abc_GenSorter( FileName, nVars );
    else if ( fMesh )
        Abc_GenMesh( FileName, nVars );
    else if ( fFpga )
        Abc_GenFpga( FileName, nLutSize, nLuts, nVars );
//        Abc_GenFpga( FileName, 2, 2, 3 );
//        Abc_GenFpga( FileName, 3, 2, 5 );
    else if ( fOneHot )
        Abc_GenOneHot( FileName, nVars );
    else if ( fRandom )
        Abc_GenRandom( FileName, nVars );
    else
        Abc_Print( -1, "Type of circuit is not specified.\n" );
    return 0;

usage:
    Abc_Print( -2, "usage: gen [-NKL num] [-asmftrvh] <file>\n" );
    Abc_Print( -2, "\t         generates simple circuits\n" );
    Abc_Print( -2, "\t-N num : the number of variables [default = %d]\n", nVars );  
    Abc_Print( -2, "\t-K num : the LUT size (to be used with switch -f) [default = %d]\n", nLutSize );  
    Abc_Print( -2, "\t-L num : the LUT count (to be used with switch -f) [default = %d]\n", nLuts );  
    Abc_Print( -2, "\t-a     : generate ripple-carry adder [default = %s]\n", fAdder? "yes": "no" );  
    Abc_Print( -2, "\t-s     : generate a sorter [default = %s]\n", fSorter? "yes": "no" );  
    Abc_Print( -2, "\t-m     : generate a mesh [default = %s]\n", fMesh? "yes": "no" );  
    Abc_Print( -2, "\t-f     : generate a LUT FPGA structure [default = %s]\n", fFpga? "yes": "no" );  
    Abc_Print( -2, "\t-t     : generate one-hotness conditions [default = %s]\n", fOneHot? "yes": "no" );  
    Abc_Print( -2, "\t-r     : generate random single-output function [default = %s]\n", fRandom? "yes": "no" );  
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : output file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCover( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fVerbose;
    int fUseSop;
    int fUseEsop;
    int fUseInvs;
    int nFaninMax;
    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    fUseSop   =  1;
    fUseEsop  =  0;
    fVerbose  =  0;
    fUseInvs  =  1;
    nFaninMax =  8;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nsxivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nFaninMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFaninMax < 0 ) 
                goto usage;
            break;
        case 's':
            fUseSop ^= 1;
            break;
        case 'x':
            fUseEsop ^= 1;
            break;
        case 'i':
            fUseInvs ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for strashed networks.\n" );
        return 1;
    }

    // run the command
    pNtkRes = Abc_NtkSopEsopCover( pNtk, nFaninMax, fUseEsop, fUseSop, fUseInvs, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: cover [-N num] [-sxvh]\n" );
    Abc_Print( -2, "\t         decomposition into a network of SOP/ESOP PLAs\n" );
    Abc_Print( -2, "\t-N num : maximum number of inputs [default = %d]\n", nFaninMax );
    Abc_Print( -2, "\t-s     : toggle the use of SOPs [default = %s]\n", fUseSop? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle the use of ESOPs [default = %s]\n", fUseEsop? "yes": "no" );
//    Abc_Print( -2, "\t-i     : toggle the use of interters [default = %s]\n", fUseInvs? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandInter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2, * pNtkRes = NULL;
    char ** pArgvNew;
    int nArgcNew;
    int c, fDelete1, fDelete2;
    int fRelation;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkInter( Abc_Ntk_t * pNtkOn, Abc_Ntk_t * pNtkOff, int fRelation, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fRelation = 0;
    fVerbose  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'r':
            fRelation ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
        return 1;
    if ( nArgcNew == 0 )
    {
        Abc_Obj_t * pObj;
        int i;
        Abc_Print( -1, "Deriving new circuit structure for the current network.\n" );
        Abc_NtkForEachPo( pNtk2, pObj, i )
            Abc_ObjXorFaninC( pObj, 0 );
    }
    if ( fRelation && Abc_NtkCoNum(pNtk1) != 1 )
    {
        Abc_Print( -1, "Computation of interplants as a relation only works for single-output functions.\n" );
        Abc_Print( -1, "Use command \"cone\" to extract one output cone from the multi-output network.\n" );
    }
    else
        pNtkRes = Abc_NtkInter( pNtk1, pNtk2, fRelation, fVerbose );
    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );

    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: inter [-rvh] <onset.blif> <offset.blif>\n" );
    Abc_Print( -2, "\t         derives interpolant of two networks representing onset and offset;\n" );
    Abc_Print( -2, "\t-r     : toggle computing interpolant as a relation [default = %s]\n", fRelation? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t         \n" );
    Abc_Print( -2, "\t         Comments:\n" );
    Abc_Print( -2, "\t         \n" );
    Abc_Print( -2, "\t         The networks given on the command line should have the same CIs/COs.\n" );
    Abc_Print( -2, "\t         If only one network is given on the command line, this network\n" );
    Abc_Print( -2, "\t         is assumed to be the offset, while the current network is the onset.\n" );
    Abc_Print( -2, "\t         If no network is given on the command line, the current network is\n" );
    Abc_Print( -2, "\t         assumed to be the onset and its complement is taken to be the offset.\n" );
    Abc_Print( -2, "\t         The resulting interpolant is stored as the current network.\n" );
    Abc_Print( -2, "\t         To verify that the interpolant agrees with the onset and the offset,\n" );
    Abc_Print( -2, "\t         save it in file \"inter.blif\" and run the following:\n" );
    Abc_Print( -2, "\t         (a) \"miter -i <onset.blif> <inter.blif>; iprove\"\n" );
    Abc_Print( -2, "\t         (b) \"miter -i <inter.blif> <offset_inv.blif>; iprove\"\n" );
    Abc_Print( -2, "\t         where <offset_inv.blif> is the network derived by complementing the\n" );
    Abc_Print( -2, "\t         outputs of <offset.blif>: \"r <onset.blif>; st -i; w <offset_inv.blif>\"\n" ); 
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDouble( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nFrames;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkDouble( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nFrames    = 50;
    fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        Abc_Print( -1, "Only works for logic SOP networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkDouble( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: double [-vh]\n" );
    Abc_Print( -2, "\t         puts together two parallel copies of the current network\n" );
//    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBb2Wb( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkConvertBb2Wb( char * pFileNameIn, char * pFileNameOut, int fSeq, int fVerbose );
    int c;
    int fSeq;
    int fVerbose;
    // set defaults
    fSeq = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "svh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fSeq ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( argc != globalUtilOptind + 2 )
    {
        Abc_Print( -1, "Expecting two files names on the command line.\n" );
        goto usage;
    }
    Abc_NtkConvertBb2Wb( argv[globalUtilOptind], argv[globalUtilOptind+1], fSeq, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: bb2wb [-svh] <file_in> <file_out>\n" );
    Abc_Print( -2, "\t             replaces black boxes by white boxes with AND functions\n" );
    Abc_Print( -2, "\t             (file names should have standard extensions, e.g. \"blif\")\n" );
    Abc_Print( -2, "\t-s         : toggle using sequential white boxes [default = %s]\n", fSeq? "yes": "no" );
    Abc_Print( -2, "\t-v         : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h         : print the command usage\n");
    Abc_Print( -2, "\t<file_in>  : input file with design containing black boxes\n");
    Abc_Print( -2, "\t<file_out> : output file with design containing white boxes\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandOutdec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkDarOutdec( Abc_Ntk_t * pNtk, int nLits, int fVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Ntk_t * pNtkRes;
    int c, nLits = 1;
    int fVerbose = 0;

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Lvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLits = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLits < 1 || nLits > 2 ) 
            {
                printf( "Currently, command \"outdec\" works for 1-lit and 2-lit primes only.\n" );
                goto usage;
            }
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for strashed networks.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDarOutdec( pNtk, nLits, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: outdec [-Lvh]\n" );
    Abc_Print( -2, "\t         performs prime decomposition of the first output\n" );
    Abc_Print( -2, "\t-L num : the number of literals in the primes [default = %d]\n", nLits );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTest( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int nCutMax      =  1;
    int nLeafMax     = 10;
    int nDivMax      = 50;
    int nDecMax      =  3;
    int fNewAlgo     =  0;
    int fNewOrder    =  0;
    int fVerbose     =  0;
    int fVeryVerbose =  0;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CKDNaovwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutMax < 0 ) 
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nLeafMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLeafMax < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nDivMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDivMax < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nDecMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDecMax < 0 ) 
                goto usage;
            break;
        case 'a':
            fNewAlgo ^= 1;
            break;
        case 'o':
            fNewOrder ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
/*
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
*/
/*
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "Only works for sequential networks.\n" );
        return 1;
    }
*/
/*
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Network should be strashed. Command has failed.\n" );
        return 1;
    }
*/
/*
    if ( pNtk )
    {
        extern Abc_Ntk_t * Au_ManPerformTest( Abc_Ntk_t * p, int nCutMax, int nLeafMax, int nDivMax, int nDecMax, int fVerbose, int fVeryVerbose );
        Abc_Ntk_t * pNtkRes = Au_ManPerformTest( pNtk, nCutMax, nLeafMax, nDivMax, nDecMax, fVerbose, fVeryVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "Command has failed.\n" );
            return 1;
        }
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    }
*/

/*
    {
//        extern void Llb_Nonlin4Cluster( Aig_Man_t * pAig );
//        extern void Aig_ManTerSimulate( Aig_Man_t * pAig );
//        extern Llb4_Nonlin4SweepExperiment( Aig_Man_t * pAig );
        extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
        Aig_Man_t * pAig = Abc_NtkToDar( pNtk, 0, 0 );
//        Aig_ManTerSimulate( pAig );
//        Llb_Nonlin4Cluster( pAig );
//        Llb4_Nonlin4SweepExperiment( pAig );
        Aig_ManStop( pAig );
    }
*/

/*
{
    extern void Ssm_ManExperiment( char * pFileIn, char * pFileOut );
//    Ssm_ManExperiment( "m\\big2.ssim", "m\\big2_.ssim" );
//    Ssm_ManExperiment( "m\\big3.ssim", "m\\big3_.ssim" );
//    Ssm_ManExperiment( "m\\tb.ssim", "m\\tb_.ssim" );
    Ssm_ManExperiment( "m\\simp.ssim", "m\\simp_.ssim" );
}
*/
/*
{
    Gia_Man_t * pGia = Abc_ManReadAig( "bug\\61\\tmp.out", "aig:" );
    Gia_ManStop( pGia );
}
*/
/*
{
    extern void Abc_BddTest( Aig_Man_t * pAig, int fNew );
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    Aig_Man_t * pAig = Abc_NtkToDar( pNtk, 0, 0 );
    Abc_BddTest( pAig, fVeryVerbose );
    Aig_ManStop( pAig );
}
*/
/*
{
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    if ( pAbc->pCex && pNtk )
    {
        Abc_Cex_t * pNew;
        Aig_Man_t * pAig = Abc_NtkToDar( pNtk, 0, 1 );
        pNew = Saig_ManCbaFindCexCareBits( pAig, pAbc->pCex, 0, fVerbose );
        Aig_ManStop( pAig );
        Abc_FrameReplaceCex( pAbc, &pNew );
    }
}
*/

{
//    extern void Abs_VfaManTest( Aig_Man_t * pAig, int nFrames, int nConfLimit, int fVerbose );
    extern void Aig_ManInterRepar( Aig_Man_t * pMan, int fVerbose );
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    extern void Aig_ManSupportsTest( Aig_Man_t * pMan );
    extern int Aig_SupportSizeTest( Aig_Man_t * pMan );
    extern int Abc_NtkSuppSizeTest( Abc_Ntk_t * p );
    extern Aig_Man_t * Iso_ManTest( Aig_Man_t * pAig, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
    if ( pNtk )
    {
        Aig_Man_t * pAig = Abc_NtkToDar( pNtk, 0, 1 );
        Aig_Man_t * pRes;
        Abc_Ntk_t * pNtkRes;
//        Aig_ManInterRepar( pAig, 1 );
//        Aig_ManInterTest( pAig, 1 );
//        Aig_ManSupportsTest( pAig );
//        Aig_SupportSizeTest( pAig );
        pRes = Iso_ManTest( pAig, fVerbose );
        Aig_ManStop( pAig );

        pNtkRes = Abc_NtkFromAigPhase( pRes );
        Aig_ManStop( pRes );

        ABC_FREE( pNtkRes->pName );
        pNtkRes->pName = Extra_UtilStrsav(pNtk->pName);
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    }
}



    {
//        void Bdc_SpfdDecomposeTest();
//        Bdc_SpfdDecomposeTest();
    }
    return 0;
usage:
    Abc_Print( -2, "usage: test [-CKDN] [-aovwh] <file_name>\n" );
    Abc_Print( -2, "\t         testbench for new procedures\n" );
    Abc_Print( -2, "\t-C num : the max number of cuts [default = %d]\n", nCutMax );
    Abc_Print( -2, "\t-K num : the max number of leaves [default = %d]\n", nLeafMax );
    Abc_Print( -2, "\t-D num : the max number of divisors [default = %d]\n", nDivMax );
    Abc_Print( -2, "\t-N num : the max number of node inputs [default = %d]\n", nDecMax );
    Abc_Print( -2, "\t-a     : toggle using new algorithm [default = %s]\n", fNewAlgo? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle using new ordering [default = %s]\n", fNewOrder? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing very verbose information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandQuaVar( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, iVar, fUniv, fVerbose, RetValue;
    extern int Abc_NtkQuantify( Abc_Ntk_t * pNtk, int fUniv, int iVar, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    iVar = 0;
    fUniv = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Iuvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            iVar = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iVar < 0 ) 
                goto usage;
            break;
        case 'u':
            fUniv ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum( pNtk ) )
    {
        Abc_Print( -1, "This command cannot be applied to an AIG with choice nodes.\n" );
        return 1;
    }

    // get the strashed network
    pNtkRes = Abc_NtkStrash( pNtk, 0, 1, 0 );
    RetValue = Abc_NtkQuantify( pNtkRes, fUniv, iVar, fVerbose );
    // clean temporary storage for the cofactors
    Abc_NtkCleanData( pNtkRes );
    Abc_AigCleanup( (Abc_Aig_t *)pNtkRes->pManFunc );
    // check the result 
    if ( !RetValue )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: qvar [-I num] [-uvh]\n" );
    Abc_Print( -2, "\t         quantifies one variable using the AIG\n" );
    Abc_Print( -2, "\t-I num : the zero-based index of a variable to quantify [default = %d]\n", iVar );
    Abc_Print( -2, "\t-u     : toggle universal quantification [default = %s]\n", fUniv? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandQuaRel( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, iVar, fInputs, fVerbose;
    extern Abc_Ntk_t * Abc_NtkTransRel( Abc_Ntk_t * pNtk, int fInputs, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    iVar = 0;
    fInputs = 1;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Iqvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            iVar = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iVar < 0 ) 
                goto usage;
            break;
        case 'q':
            fInputs ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum( pNtk ) )
    {
        Abc_Print( -1, "This command cannot be applied to an AIG with choice nodes.\n" );
        return 1;
    }
    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "This command works only for sequential circuits.\n" );
        return 1;
    }

    // get the strashed network
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 1, 0 );
        pNtkRes = Abc_NtkTransRel( pNtk, fInputs, fVerbose );
        Abc_NtkDelete( pNtk );
    }
    else
        pNtkRes = Abc_NtkTransRel( pNtk, fInputs, fVerbose );
    // check if the result is available
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: qrel [-qvh]\n" );
    Abc_Print( -2, "\t         computes transition relation of the sequential network\n" );
//    Abc_Print( -2, "\t-I num : the zero-based index of a variable to quantify [default = %d]\n", iVar );
    Abc_Print( -2, "\t-q     : perform quantification of inputs [default = %s]\n", fInputs? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandQuaReach( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nIters, fVerbose;
    extern Abc_Ntk_t * Abc_NtkReachability( Abc_Ntk_t * pNtk, int nIters, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nIters   = 256;
    fVerbose =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nIters < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum( pNtk ) )
    {
        Abc_Print( -1, "This command cannot be applied to an AIG with choice nodes.\n" );
        return 1;
    }
    if ( !Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "This command works only for combinational transition relations.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }
    if ( Abc_NtkPoNum(pNtk) > 1 )
    {
        Abc_Print( -1, "The transition relation should have one output.\n" );
        return 1;
    }
    if ( Abc_NtkPiNum(pNtk) % 2 != 0 )
    {
        Abc_Print( -1, "The transition relation should have an even number of inputs.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkReachability( pNtk, nIters, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: qreach [-I num] [-vh]\n" );
    Abc_Print( -2, "\t         computes unreachable states using AIG-based quantification\n" );
    Abc_Print( -2, "\t         assumes that the current network is a transition relation\n" );
    Abc_Print( -2, "\t         assumes that the initial state is composed of all zeros\n" );
    Abc_Print( -2, "\t-I num : the number of image computations to perform [default = %d]\n", nIters );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSenseInput( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Vec_Int_t * vResult;
    int c, nConfLim, fVerbose;

    extern Vec_Int_t * Abc_NtkSensitivity( Abc_Ntk_t * pNtk, int nConfLim, int fVerbose );
    // set defaults
    nConfLim   = 1000;
    fVerbose   =    1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Cvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLim < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkGetChoiceNum( pNtk ) )
    {
        Abc_Print( -1, "This command cannot be applied to an AIG with choice nodes.\n" );
        return 1;
    }
    if ( !Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "This command works only for combinational transition relations.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }
    if ( Abc_NtkPoNum(pNtk) < 2 )
    {
        Abc_Print( -1, "The network should have at least two outputs.\n" );
        return 1;
    }

    vResult = Abc_NtkSensitivity( pNtk, nConfLim, fVerbose );
    Vec_IntFree( vResult );
    return 0;

usage:
    Abc_Print( -2, "usage: senseinput [-C num] [-vh]\n" );
    Abc_Print( -2, "\t         computes sensitivity of POs to PIs under constraint\n" );
    Abc_Print( -2, "\t         constraint should be represented as the last PO" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nConfLim );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIStrash( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes, * pNtkTemp;
    int c;
    extern Abc_Ntk_t * Abc_NtkIvyStrash( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 1, 0 );
        pNtkRes = Abc_NtkIvyStrash( pNtkTemp );
        Abc_NtkDelete( pNtkTemp );
    }
    else
        pNtkRes = Abc_NtkIvyStrash( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: istrash [-h]\n" );
    Abc_Print( -2, "\t         perform sequential structural hashing\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandICut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c, nInputs;
    extern void Abc_NtkIvyCuts( Abc_Ntk_t * pNtk, int nInputs );

    // set defaults
    nInputs = 5;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Kh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nInputs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInputs < 0 ) 
                goto usage;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    Abc_NtkIvyCuts( pNtk, nInputs );
    return 0;

usage:
    Abc_Print( -2, "usage: icut [-K num] [-h]\n" );
    Abc_Print( -2, "\t         computes sequential cuts of the given size\n" );
    Abc_Print( -2, "\t-K num : the number of cut inputs (2 <= num <= 6) [default = %d]\n", nInputs );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIRewrite( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fUpdateLevel, fUseZeroCost, fVerbose;
    extern Abc_Ntk_t * Abc_NtkIvyRewrite( Abc_Ntk_t * pNtk, int fUpdateLevel, int fUseZeroCost, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fUpdateLevel = 1;
    fUseZeroCost = 0;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lzvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'z':
            fUseZeroCost ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkIvyRewrite( pNtk, fUpdateLevel, fUseZeroCost, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: irw [-lzvh]\n" );
    Abc_Print( -2, "\t         perform combinational AIG rewriting\n" );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle using zero-cost replacements [default = %s]\n", fUseZeroCost? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDRewrite( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Dar_RwrPar_t Pars, * pPars = &Pars;
    int c;

    extern Abc_Ntk_t * Abc_NtkDRewrite( Abc_Ntk_t * pNtk, Dar_RwrPar_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Dar_ManDefaultRwrParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CNflzrvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCutsMax < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSubgMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSubgMax < 0 ) 
                goto usage;
            break;
        case 'f':
            pPars->fFanout ^= 1;
            break;
        case 'l':
            pPars->fUpdateLevel ^= 1;
            break;
        case 'z':
            pPars->fUseZeros ^= 1;
            break;
        case 'r':
            pPars->fRecycle ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDRewrite( pNtk, pPars );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: drw [-C num] [-N num] [-lfzrvwh]\n" );
    Abc_Print( -2, "\t         performs combinational AIG rewriting\n" );
    Abc_Print( -2, "\t-C num : the max number of cuts at a node [default = %d]\n", pPars->nCutsMax );
    Abc_Print( -2, "\t-N num : the max number of subgraphs tried [default = %d]\n", pPars->nSubgMax );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", pPars->fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle representing fanouts [default = %s]\n", pPars->fFanout? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle using zero-cost replacements [default = %s]\n", pPars->fUseZeros? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle using cut recycling [default = %s]\n", pPars->fRecycle? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle very verbose printout [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDRefactor( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Dar_RefPar_t Pars, * pPars = &Pars;
    int c;

    extern Abc_Ntk_t * Abc_NtkDRefactor( Abc_Ntk_t * pNtk, Dar_RefPar_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Dar_ManDefaultRefParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "MKCelzvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMffcMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMffcMin < 0 ) 
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLeafMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLeafMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCutsMax < 0 ) 
                goto usage;
            break;
        case 'e':
            pPars->fExtend ^= 1;
            break;
        case 'l':
            pPars->fUpdateLevel ^= 1;
            break;
        case 'z':
            pPars->fUseZeros ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }
    if ( pPars->nLeafMax < 4 || pPars->nLeafMax > 15 )
    {
        Abc_Print( -1, "This command only works for cut sizes 4 <= K <= 15.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDRefactor( pNtk, pPars );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: drf [-M num] [-K num] [-C num] [-elzvwh]\n" );
    Abc_Print( -2, "\t         performs combinational AIG refactoring\n" );
    Abc_Print( -2, "\t-M num : the min MFFC size to attempt refactoring [default = %d]\n", pPars->nMffcMin );
    Abc_Print( -2, "\t-K num : the max number of cuts leaves [default = %d]\n", pPars->nLeafMax );
    Abc_Print( -2, "\t-C num : the max number of cuts to try at a node [default = %d]\n", pPars->nCutsMax );
    Abc_Print( -2, "\t-e     : toggle extending tbe cut below MFFC [default = %s]\n", pPars->fExtend? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", pPars->fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle using zero-cost replacements [default = %s]\n", pPars->fUseZeros? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle very verbose printout [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDc2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fBalance, fVerbose, fUpdateLevel, fFanout, fPower, c;

    extern Abc_Ntk_t * Abc_NtkDC2( Abc_Ntk_t * pNtk, int fBalance, int fUpdateLevel, int fFanout, int fPower, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fBalance     = 0;
    fVerbose     = 0;
    fUpdateLevel = 0;
    fFanout      = 1;
    fPower       = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "blfpvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fBalance ^= 1;
            break;
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'f':
            fFanout ^= 1;
            break;
        case 'p':
            fPower ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDC2( pNtk, fBalance, fUpdateLevel, fFanout, fPower, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: dc2 [-blfpvh]\n" );
    Abc_Print( -2, "\t         performs combinational AIG optimization\n" );
    Abc_Print( -2, "\t-b     : toggle internal balancing [default = %s]\n", fBalance? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle updating level [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle representing fanouts [default = %s]\n", fFanout? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle power-aware rewriting [default = %s]\n", fPower? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDChoice( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fBalance, fVerbose, fUpdateLevel, fConstruct, c;
    int nConfMax, nLevelMax;

    extern Abc_Ntk_t * Abc_NtkDChoice( Abc_Ntk_t * pNtk, int fBalance, int fUpdateLevel, int fConstruct, int nConfMax, int nLevelMax, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fBalance     = 1;
    fUpdateLevel = 1;
    fConstruct   = 0;
    nConfMax     = 1000;
    nLevelMax    = 0;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CLblcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfMax < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLevelMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevelMax < 0 ) 
                goto usage;
            break;
        case 'b':
            fBalance ^= 1;
            break;
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'c':
            fConstruct ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDChoice( pNtk, fBalance, fUpdateLevel, fConstruct, nConfMax, nLevelMax, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: dchoice [-C num] [-L num] [-blcvh]\n" );
    Abc_Print( -2, "\t         performs partitioned choicing using new AIG package\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-L num : the max level of nodes to consider (0 = not used) [default = %d]\n", nLevelMax );
    Abc_Print( -2, "\t-b     : toggle internal balancing [default = %s]\n", fBalance? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle updating level [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle constructive computation of choices [default = %s]\n", fConstruct? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Dch_Pars_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    extern Abc_Ntk_t * Abc_NtkDch( Abc_Ntk_t * pNtk, Dch_Pars_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Dch_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WCSsptgcfvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWords < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBTLimit < 0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSatVarMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSatVarMax < 0 ) 
                goto usage;
            break;
        case 's':
            pPars->fSynthesis ^= 1;
            break;
        case 'p':
            pPars->fPower ^= 1;
            break;
        case 't':
            pPars->fSimulateTfo ^= 1;
            break;
        case 'g':
            pPars->fUseGia ^= 1;
            break;
        case 'c':
            pPars->fUseCSat ^= 1;
            break;
        case 'f':
            pPars->fLightSynth ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL ) 
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDch( pNtk, pPars );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: dch [-WCS num] [-sptgcfvh]\n" );
    Abc_Print( -2, "\t         computes structural choices using a new approach\n" );
    Abc_Print( -2, "\t-W num : the max number of simulation words [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-S num : the max number of SAT variables [default = %d]\n", pPars->nSatVarMax );
    Abc_Print( -2, "\t-s     : toggle synthesizing three snapshots [default = %s]\n", pPars->fSynthesis? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle power-aware rewriting [default = %s]\n", pPars->fPower? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle simulation of the TFO classes [default = %s]\n", pPars->fSimulateTfo? "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle using GIA to prove equivalences [default = %s]\n", pPars->fUseGia? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using circuit-based SAT vs. MiniSat [default = %s]\n", pPars->fUseCSat? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle using faster logic synthesis [default = %s]\n", pPars->fLightSynth? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDrwsat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fBalance, fVerbose, c;

    extern Abc_Ntk_t * Abc_NtkDrwsat( Abc_Ntk_t * pNtk, int fBalance, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fBalance = 0;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "bvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'b':
            fBalance ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDrwsat( pNtk, fBalance, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: drwsat [-bvh]\n" );
    Abc_Print( -2, "\t         performs combinational AIG optimization for SAT\n" );
    Abc_Print( -2, "\t-b     : toggle internal balancing [default = %s]\n", fBalance? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIRewriteSeq( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fUpdateLevel, fUseZeroCost, fVerbose;
    extern Abc_Ntk_t * Abc_NtkIvyRewriteSeq( Abc_Ntk_t * pNtk, int fUseZeroCost, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fUpdateLevel = 0;
    fUseZeroCost = 0;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lzvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'z':
            fUseZeroCost ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkIvyRewriteSeq( pNtk, fUseZeroCost, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: irws [-zvh]\n" );
    Abc_Print( -2, "\t         perform sequential AIG rewriting\n" );
//    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-z     : toggle using zero-cost replacements [default = %s]\n", fUseZeroCost? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIResyn( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fUpdateLevel, fVerbose;
    extern Abc_Ntk_t * Abc_NtkIvyResyn( Abc_Ntk_t * pNtk, int fUpdateLevel, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fUpdateLevel = 1;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lzvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkIvyResyn( pNtk, fUpdateLevel, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: iresyn [-lvh]\n" );
    Abc_Print( -2, "\t         performs combinational resynthesis\n" );
    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandISat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fUpdateLevel, fVerbose;
    int nConfLimit;

    extern Abc_Ntk_t * Abc_NtkIvySat( Abc_Ntk_t * pNtk, int nConfLimit, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nConfLimit   = 100000;   
    fUpdateLevel = 1;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Clzvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 ) 
                goto usage;
            break;
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkIvySat( pNtk, nConfLimit, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: isat [-C num] [-vh]\n" );
    Abc_Print( -2, "\t         tries to prove the miter constant 0\n" );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
//    Abc_Print( -2, "\t-l     : toggle preserving the number of levels [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIFraig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, fProve, fVerbose, fDoSparse;
    int nConfLimit;
    int nPartSize;
    int nLevelMax;

    extern Abc_Ntk_t * Abc_NtkIvyFraig( Abc_Ntk_t * pNtk, int nConfLimit, int fDoSparse, int fProve, int fTransfer, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkDarFraigPart( Abc_Ntk_t * pNtk, int nPartSize, int nConfLimit, int nLevelMax, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nPartSize    = 0;
    nLevelMax    = 0;
    nConfLimit   = 100;   
    fDoSparse    = 0;
    fProve       = 0;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PCLspvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPartSize < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 ) 
                goto usage;
            break;
         case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLevelMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevelMax < 0 ) 
                goto usage;
            break;
        case 's':
            fDoSparse ^= 1;
            break;
        case 'p':
            fProve ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    if ( nPartSize > 0 )
        pNtkRes = Abc_NtkDarFraigPart( pNtk, nPartSize, nConfLimit, nLevelMax, fVerbose );
    else
        pNtkRes = Abc_NtkIvyFraig( pNtk, nConfLimit, fDoSparse, fProve, 0, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: ifraig [-P num] [-C num] [-L num] [-spvh]\n" );
    Abc_Print( -2, "\t         performs fraiging using a new method\n" );
    Abc_Print( -2, "\t-P num : partition size (0 = partitioning is not used) [default = %d]\n", nPartSize );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n", nConfLimit );
    Abc_Print( -2, "\t-L num : limit on node level to fraig (0 = fraig all nodes) [default = %d]\n", nLevelMax );
    Abc_Print( -2, "\t-s     : toggle considering sparse functions [default = %s]\n", fDoSparse? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle proving the miter outputs [default = %s]\n", fProve? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDFraig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nConfLimit, fDoSparse, fProve, fSpeculate, fChoicing, fVerbose;

    extern Abc_Ntk_t * Abc_NtkDarFraig( Abc_Ntk_t * pNtk, int nConfLimit, int fDoSparse, int fProve, int fTransfer, int fSpeculate, int fChoicing, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nConfLimit   = 100;  
    fDoSparse    = 1;
    fProve       = 0;
    fSpeculate   = 0;
    fChoicing    = 0;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Csprcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 ) 
                goto usage;
            break;
        case 's':
            fDoSparse ^= 1;
            break;
        case 'p':
            fProve ^= 1;
            break;
        case 'r':
            fSpeculate ^= 1;
            break;
        case 'c':
            fChoicing ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkDarFraig( pNtk, nConfLimit, fDoSparse, fProve, 0, fSpeculate, fChoicing, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: dfraig [-C num] [-sprcvh]\n" );
    Abc_Print( -2, "\t         performs fraiging using a new method\n" );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n", nConfLimit );
    Abc_Print( -2, "\t-s     : toggle considering sparse functions [default = %s]\n", fDoSparse? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle proving the miter outputs [default = %s]\n", fProve? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle speculative reduction [default = %s]\n", fSpeculate? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle accumulation of choices [default = %s]\n", fChoicing? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCSweep( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nCutsMax, nLeafMax, fVerbose;

    extern Abc_Ntk_t * Abc_NtkCSweep( Abc_Ntk_t * pNtk, int nCutsMax, int nLeafMax, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nCutsMax  =  8;  
    nLeafMax  =  6;
    fVerbose  =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CKvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutsMax < 0 ) 
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nLeafMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLeafMax < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( nCutsMax < 2 )
    {
        Abc_Print( -1, "The number of cuts cannot be less than 2.\n" );
        return 1;
    }

    if ( nLeafMax < 3 || nLeafMax > 16 )
    {
        Abc_Print( -1, "The number of leaves is infeasible.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkCSweep( pNtk, nCutsMax, nLeafMax, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: csweep [-C num] [-K num] [-vh]\n" );
    Abc_Print( -2, "\t         performs cut sweeping using a new method\n" );
    Abc_Print( -2, "\t-C num : limit on the number of cuts (C >= 2) [default = %d]\n", nCutsMax );
    Abc_Print( -2, "\t-K num : limit on the cut size (3 <= K <= 16) [default = %d]\n", nLeafMax );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIProve( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Prove_Params_t Params, * pParams = &Params;
    Abc_Ntk_t * pNtk, * pNtkTemp;
    int c, clk, RetValue, iOut = -1;

    extern int Abc_NtkIvyProve( Abc_Ntk_t ** ppNtk, void * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Prove_ParamsSetDefault( pParams );
    pParams->fUseRewriting = 1;
    pParams->fVerbose      = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NCFGLIrfbvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nItersMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nItersMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nMiteringLimitStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nMiteringLimitStart < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nFraigingLimitStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nFraigingLimitStart < 0 ) 
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nFraigingLimitMulti = (float)atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nFraigingLimitMulti < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nMiteringLimitLast = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nMiteringLimitLast < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nTotalInspectLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nTotalInspectLimit < 0 ) 
                goto usage;
            break;
        case 'r':
            pParams->fUseRewriting ^= 1;
            break;
        case 'f':
            pParams->fUseFraiging ^= 1;
            break;
        case 'b':
            pParams->fUseBdds ^= 1;
            break;
        case 'v':
            pParams->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "The network has registers. Use \"dprove\".\n" );
        return 1;
    }

    clk = clock();

    if ( Abc_NtkIsStrash(pNtk) )
        pNtkTemp = Abc_NtkDup( pNtk );
    else
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );

    RetValue = Abc_NtkIvyProve( &pNtkTemp, pParams );

    // verify that the pattern is correct
    if ( RetValue == 0 )
    {
        Abc_Obj_t * pObj;
        int i;
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pNtkTemp->pModel );
        Abc_NtkForEachCo( pNtk, pObj, i )
            if ( pSimInfo[i] == 1 )
            {
                iOut = i;
                break;
            }
        if ( i == Abc_NtkCoNum(pNtk) )
            Abc_Print( 1, "ERROR in Abc_NtkMiterProve(): Generated counter-example is invalid.\n" );
        ABC_FREE( pSimInfo );
    }
    pAbc->Status = RetValue;
    if ( RetValue == -1 ) 
        Abc_Print( 1, "UNDECIDED      " );
    else if ( RetValue == 0 )
        Abc_Print( 1, "SATISFIABLE (output = %d) ", iOut );
    else
        Abc_Print( 1, "UNSATISFIABLE  " );
    //Abc_Print( -1, "\n" );

    Abc_PrintTime( 1, "Time", clock() - clk );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkTemp );
    // update counter example
    if ( RetValue == 0 && Abc_NtkLatchNum(pNtkTemp) == 0 )
    {
        Abc_Cex_t * pCex = Abc_CexDeriveFromCombModel( pNtkTemp->pModel, Abc_NtkPiNum(pNtkTemp), 0, iOut );
        Abc_FrameReplaceCex( pAbc, &pCex );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: iprove [-NCFGLI num] [-rfbvh]\n" );
    Abc_Print( -2, "\t         performs CEC using a new method\n" );
    Abc_Print( -2, "\t-N num : max number of iterations [default = %d]\n", pParams->nItersMax );
    Abc_Print( -2, "\t-C num : max starting number of conflicts in mitering [default = %d]\n", pParams->nMiteringLimitStart );
    Abc_Print( -2, "\t-F num : max starting number of conflicts in fraiging [default = %d]\n", pParams->nFraigingLimitStart );
    Abc_Print( -2, "\t-G num : multiplicative coefficient for fraiging [default = %d]\n", (int)pParams->nFraigingLimitMulti );
    Abc_Print( -2, "\t-L num : max last-gasp number of conflicts in mitering [default = %d]\n", pParams->nMiteringLimitLast );
    Abc_Print( -2, "\t-I num : max number of clause inspections in all SAT calls [default = %d]\n", (int)pParams->nTotalInspectLimit );
    Abc_Print( -2, "\t-r     : toggle the use of rewriting [default = %s]\n", pParams->fUseRewriting? "yes": "no" );  
    Abc_Print( -2, "\t-f     : toggle the use of FRAIGing [default = %s]\n", pParams->fUseFraiging? "yes": "no" );  
    Abc_Print( -2, "\t-b     : toggle the use of BDDs [default = %s]\n", pParams->fUseBdds? "yes": "no" );  
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pParams->fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*
int Abc_CommandHaig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * stdout, * pErr;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nIters;
    int nSteps;
    int fRetimingOnly;
    int fAddBugs;
    int fUseCnf;
    int fVerbose;

    extern Abc_Ntk_t * Abc_NtkDarHaigRecord( Abc_Ntk_t * pNtk, int nIters, int nSteps, int fRetimingOnly, int fAddBugs, int fUseCnf, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);



    // set defaults
    nIters        = 3;
    nSteps        = 3000;
    fRetimingOnly = 0;
    fAddBugs      = 0;
    fUseCnf       = 0;
    fVerbose      = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ISrbcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nIters < 0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nSteps = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSteps < 0 ) 
                goto usage;
            break;
        case 'r':
            fRetimingOnly ^= 1;
            break;
        case 'b':
            fAddBugs ^= 1;
            break;
        case 'c':
            fUseCnf ^= 1;
            break;
        case 'v':
            fUseCnf ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for strashed networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkDarHaigRecord( pNtk, nIters, nSteps, fRetimingOnly, fAddBugs, fUseCnf, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: haig [-IS num] [-rbcvh]\n" );
    Abc_Print( -2, "\t         run a few rounds of comb+seq synthesis to test HAIG recording\n" );
    Abc_Print( -2, "\t         the current network is set to be the result of synthesis performed\n" );
    Abc_Print( -2, "\t         (this network can be verified using command \"dsec\")\n" );
    Abc_Print( -2, "\t         HAIG is written out into the file \"haig.blif\"\n" );
    Abc_Print( -2, "\t         (this HAIG can be proved using \"r haig.blif; st; dprove -abc -F 16\")\n" );
    Abc_Print( -2, "\t-I num : the number of rounds of comb+seq synthesis [default = %d]\n", nIters );
    Abc_Print( -2, "\t-S num : the number of forward retiming moves performed [default = %d]\n", nSteps );
    Abc_Print( -2, "\t-r     : toggle the use of retiming only [default = %s]\n", fRetimingOnly? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle bug insertion [default = %s]\n", fAddBugs? "yes": "no" );
    Abc_Print( -2, "\t-c     : enable CNF-based proof (no speculative reduction) [default = %s]\n", fUseCnf? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}
*/

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMini( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    extern Abc_Ntk_t * Abc_NtkMiniBalance( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for combinatinally strashed AIG networks.\n" );
        return 1;
    }

    pNtkRes = Abc_NtkMiniBalance( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: mini [-h]\n" );
    Abc_Print( -2, "\t         perform balancing using new package\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandQbf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nPars;
    int nIters;
    int fVerbose;

    extern void Abc_NtkQbf( Abc_Ntk_t * pNtk, int nPars, int nIters, int fVerbose );
    // set defaults
    nPars    = -1;
    nIters   = -1;
    fVerbose =  1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PIvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPars < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nIters < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "Works only for combinational networks.\n" );
        return 1;
    }
    if ( Abc_NtkPoNum(pNtk) != 1 )
    {
        Abc_Print( -1, "The miter should have one primary output.\n" );
        return 1;
    }
    if ( !(nPars > 0 && nPars < Abc_NtkPiNum(pNtk)) )
    {
        Abc_Print( -1, "The number of paramter variables is invalid (should be > 0 and < PI num).\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
        Abc_NtkQbf( pNtk, nPars, nIters, fVerbose );
    else
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 1, 0 );
        Abc_NtkQbf( pNtk, nPars, nIters, fVerbose );
        Abc_NtkDelete( pNtk );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: qbf [-PI num] [-vh]\n" );
    Abc_Print( -2, "\t         solves QBF problem EpVxM(p,x)\n" );
    Abc_Print( -2, "\t-P num : number of parameters p (should be the first PIs) [default = %d]\n", nPars );
    Abc_Print( -2, "\t-I num : quit after the given iteration even if unsolved [default = %d]\n", nIters );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandNpnLoad( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Npn_ManLoad( char * pFileName );
    char * pFileName;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( argc != globalUtilOptind + 1 )
        goto usage;
    pFileName = argv[globalUtilOptind];
    Npn_ManLoad( pFileName );
    return 0;

usage:
    Abc_Print( -2, "usage: npnload <filename>\n" );
    Abc_Print( -2, "\t         loads previously saved 6-input function library from file\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandNpnSave( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Npn_ManSave( char * pFileName );
    char * pFileName;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( argc != globalUtilOptind + 1 )
        goto usage;
    pFileName = argv[globalUtilOptind];
    Npn_ManSave( pFileName );
    return 0;

usage:
    Abc_Print( -2, "usage: npnsave <filename>\n" );
    Abc_Print( -2, "\t         saves current 6-input function library into file\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFraig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[100];
    Fraig_Params_t Params, * pParams = &Params;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fAllNodes;
    int fExdc;
    int c;
    int fPartition = 0;
    extern void Abc_NtkFraigPartitionedTime( Abc_Ntk_t * pNtk, void * pParams );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fExdc     = 0;
    fAllNodes = 0;
    memset( pParams, 0, sizeof(Fraig_Params_t) );
    pParams->nPatsRand  = 2048; // the number of words of random simulation info
    pParams->nPatsDyna  = 2048; // the number of words of dynamic simulation info
    pParams->nBTLimit   =  100; // the max number of backtracks to perform
    pParams->fFuncRed   =    1; // performs only one level hashing
    pParams->fFeedBack  =    1; // enables solver feedback
    pParams->fDist1Pats =    1; // enables distance-1 patterns
    pParams->fDoSparse  =    1; // performs equiv tests for sparse functions 
    pParams->fChoicing  =    0; // enables recording structural choices
    pParams->fTryProve  =    0; // tries to solve the final miter
    pParams->fVerbose   =    0; // the verbosiness flag
    pParams->fVerboseP  =    0; // the verbosiness flag
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "RDCrscptvaeh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nPatsRand = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nPatsRand < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nPatsDyna = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nPatsDyna < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nBTLimit < 0 ) 
                goto usage;
            break;

        case 'r':
            pParams->fFuncRed ^= 1;
            break;
        case 's':
            pParams->fDoSparse ^= 1;
            break;
        case 'c':
            pParams->fChoicing ^= 1;
            break;
        case 'p':
            pParams->fTryProve ^= 1;
            break;
        case 'v':
            pParams->fVerbose ^= 1;
            break;
        case 't':
            fPartition ^= 1;
            break;
        case 'a':
            fAllNodes ^= 1;
            break;
        case 'e':
            fExdc ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    } 

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Can only fraig a logic network or an AIG.\n" );
        return 1;
    }

    // report the proof
    pParams->fVerboseP = pParams->fTryProve;

    // get the new network
    if ( fPartition )
    {
        pNtkRes = Abc_NtkDup( pNtk );
        if ( Abc_NtkIsStrash(pNtk) )
            Abc_NtkFraigPartitionedTime( pNtk, &Params );
        else
        {
            pNtk = Abc_NtkStrash( pNtk, fAllNodes, !fAllNodes, 0 );
            Abc_NtkFraigPartitionedTime( pNtk, &Params );
            Abc_NtkDelete( pNtk );
        }
    }
    else
    {
        if ( Abc_NtkIsStrash(pNtk) )
            pNtkRes = Abc_NtkFraig( pNtk, &Params, fAllNodes, fExdc );
        else
        {
            pNtk = Abc_NtkStrash( pNtk, fAllNodes, !fAllNodes, 0 );
            pNtkRes = Abc_NtkFraig( pNtk, &Params, fAllNodes, fExdc );
            Abc_NtkDelete( pNtk );
        }
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Fraiging has failed.\n" );
        return 1;
    }

    if ( pParams->fTryProve ) // report the result
        Abc_NtkMiterReport( pNtkRes );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    sprintf( Buffer, "%d", pParams->nBTLimit );
    Abc_Print( -2, "usage: fraig [-R num] [-D num] [-C num] [-rscpvtah]\n" );
    Abc_Print( -2, "\t         transforms a logic network into a functionally reduced AIG\n" );
    Abc_Print( -2, "\t         (known bugs: takes an UNSAT miter and returns a SAT one)\n");
    Abc_Print( -2, "\t         (there are newer fraiging commands, \"ifraig\" and \"dfraig\")\n" );
    Abc_Print( -2, "\t-R num : number of random patterns (127 < num < 32769) [default = %d]\n",     pParams->nPatsRand );
    Abc_Print( -2, "\t-D num : number of systematic patterns (127 < num < 32769) [default = %d]\n", pParams->nPatsDyna );
    Abc_Print( -2, "\t-C num : number of backtracks for one SAT problem [default = %s]\n",    pParams->nBTLimit==-1? "infinity" : Buffer );
    Abc_Print( -2, "\t-r     : toggle functional reduction [default = %s]\n",                 pParams->fFuncRed? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle considering sparse functions [default = %s]\n",         pParams->fDoSparse? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle accumulation of choices [default = %s]\n",              pParams->fChoicing? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle proving the miter outputs [default = %s]\n",              pParams->fTryProve? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n",                       pParams->fVerbose?  "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle functional sweeping using EXDC [default = %s]\n",       fExdc? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle between all nodes and DFS nodes [default = %s]\n",      fAllNodes? "all": "dfs" );
    Abc_Print( -2, "\t-t     : toggle using partitioned representation [default = %s]\n",     fPartition? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFraigTrust( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fDuplicate;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fDuplicate = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDuplicate ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkFraigTrust( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Fraiging in the trust mode has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: fraig_trust [-h]\n" );
    Abc_Print( -2, "\t        transforms the current network into an AIG assuming it is FRAIG with choices\n" );
//    Abc_Print( -2, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFraigStore( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fDuplicate;

    // set defaults
    fDuplicate = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDuplicate ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkFraigStore( pNtk ) )
    {
        Abc_Print( -1, "Fraig storing has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: fraig_store [-h]\n" );
    Abc_Print( -2, "\t        saves the current network in the AIG database\n" );
//    Abc_Print( -2, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFraigRestore( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fDuplicate;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fDuplicate = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDuplicate ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkFraigRestore();
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Fraig restoring has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: fraig_restore [-h]\n" );
    Abc_Print( -2, "\t        makes the current network by fraiging the AIG database\n" );
//    Abc_Print( -2, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFraigClean( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fDuplicate;
    // set defaults
    fDuplicate = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDuplicate ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    Abc_NtkFraigStoreClean();
    return 0;

usage:
    Abc_Print( -2, "usage: fraig_clean [-h]\n" );
    Abc_Print( -2, "\t        cleans the internal FRAIG storage\n" );
//    Abc_Print( -2, "\t-d    : toggle duplication of logic [default = %s]\n", fDuplicate? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFraigSweep( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseInv;
    int fExdc;
    int fVerbose;
    int fVeryVerbose;
    extern int Abc_NtkFraigSweep( Abc_Ntk_t * pNtk, int fUseInv, int fExdc, int fVerbose, int fVeryVerbose );
    // set defaults
    fUseInv   = 1;
    fExdc     = 0;
    fVerbose  = 0;
    fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ievwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'i':
            fUseInv ^= 1;
            break;
        case 'e':
            fExdc ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Cannot sweep AIGs (use \"fraig\").\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "Transform the current network into a logic network.\n" );
        return 1;
    }
    // modify the current network
    if ( !Abc_NtkFraigSweep( pNtk, fUseInv, fExdc, fVerbose, fVeryVerbose ) )
    {
        Abc_Print( -1, "Sweeping has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: fraig_sweep [-evwh]\n" );
    Abc_Print( -2, "\t        performs technology-dependent sweep\n" );
    Abc_Print( -2, "\t-e    : toggle functional sweeping using EXDC [default = %s]\n", fExdc? "yes": "no" );
    Abc_Print( -2, "\t-v    : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-w    : prints equivalence class information [default = %s]\n", fVeryVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFraigDress( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Abc_NtkDress( Abc_Ntk_t * pNtk, char * pFileName, int fVerbose );
    extern void Abc_NtkDress2( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConflictLimit, int fVerbose );
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc), * pNtk2;
    char * pFileName;
    int c;
    int nConfs;
    int fVerbose;
    // set defaults
    nConfs   = 1000;
    fVerbose =    0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Cvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfs < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for logic networks.\n" );
        return 1;
    }
    if ( argc != globalUtilOptind && argc != globalUtilOptind + 1 )
        goto usage;
    if ( argc == globalUtilOptind && Abc_NtkSpec(pNtk) == NULL )
    {
        Abc_Print( -1, "The current network has no spec.\n" );
        return 1;
    }
    // get the input file name
    pFileName = (argc == globalUtilOptind + 1) ? argv[globalUtilOptind] : Abc_NtkSpec(pNtk);
    // modify the current network
//    Abc_NtkDress( pNtk, pFileName, fVerbose );
    pNtk2 = Io_Read( pFileName, Io_ReadFileType(pFileName), 1 );
    Abc_NtkDress2( pNtk, pNtk2, nConfs, fVerbose );
    Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    Abc_Print( -2, "usage: dress [-C num] [-vh] <file>\n" );
    Abc_Print( -2, "\t         transfers internal node names from file to the current network\n" );
    Abc_Print( -2, "\t<file> : network with names (if not given, the current network spec is used)\n" );  
    Abc_Print( -2, "\t-C num : the maximum number of conflicts at each node [default = %d]\n", nConfs );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

#if 0

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandHaigStart( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs; run strashing (\"st\").\n" );
        return 0;
    }
    Abc_NtkHaigStart( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: haig_start [-h]\n" );
    Abc_Print( -2, "\t        starts constructive accumulation of combinational choices\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandHaigStop( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs; run strashing (\"st\").\n" );
        return 0;
    }
    Abc_NtkHaigStop( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: haig_stop [-h]\n" );
    Abc_Print( -2, "\t        cleans the internal storage for combinational choices\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandHaigUse( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs; run strashing (\"st\").\n" );
        return 0;
    }
    // get the new network
    pNtkRes = Abc_NtkHaigUse( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Transforming internal storage into AIG with choices has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: haig_use [-h]\n" );
    Abc_Print( -2, "\t        transforms internal storage into an AIG with choices\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

#endif


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRecStart( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nVars;
    int nCuts;
    int fTrim;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nVars = 6;
    nCuts = 32;
    fTrim = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCth" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 1 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nCuts = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCuts < 1 ) 
                goto usage;
            break;
        case 't':
            fTrim ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !(nVars >= 3 && nVars <= 16) )
    {
        Abc_Print( -1, "The range of allowed values is 3 <= K <= 16.\n" );
        return 0;
    }
    if ( Abc_NtkRecIsRunning() )
    {
        Abc_Print( -1, "The AIG subgraph recording is already started.\n" );
        return 0;
    }
    if ( pNtk && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs; run strashing (\"st\").\n" );
        return 0;
    }
    Abc_NtkRecStart( pNtk, nVars, nCuts, fTrim );
    return 0;

usage:
    Abc_Print( -2, "usage: rec_start [-K num] [-C num] [-th]\n" );
    Abc_Print( -2, "\t         starts recording AIG subgraphs (should be called for\n" );
    Abc_Print( -2, "\t         an empty network or after reading in a previous record)\n" );
    Abc_Print( -2, "\t-K num : the largest number of inputs [default = %d]\n", nVars );
    Abc_Print( -2, "\t-C num : the max number of cuts used at a node (0 < num < 2^12) [default = %d]\n", nCuts );
    Abc_Print( -2, "\t-t     : toggles the use of trimming [default = %s]\n", fTrim? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRecStop( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkRecIsRunning() )
    {
        Abc_Print( -1, "This command works only after calling \"rec_start\".\n" );
        return 0;
    }
    Abc_NtkRecStop();
    return 0;

usage:
    Abc_Print( -2, "usage: rec_stop [-h]\n" );
    Abc_Print( -2, "\t        cleans the internal storage for AIG subgraphs\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRecAdd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works for AIGs.\n" );
        return 0;
    }
    if ( !Abc_NtkRecIsRunning() )
    {
        Abc_Print( -1, "This command works for AIGs after calling \"rec_start\".\n" );
        return 0;
    }
    Abc_NtkRecAdd( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: rec_add [-h]\n" );
    Abc_Print( -2, "\t        adds subgraphs from the current network to the set\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRecPs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c, fPrintLib = 0;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ph" ) ) != EOF )
    {
        switch ( c )
        {
        case 'p':
            fPrintLib ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkRecIsRunning() )
    {
        Abc_Print( -1, "This command works for AIGs only after calling \"rec_start\".\n" );
        return 0;
    }
    Abc_NtkRecPs(fPrintLib);
    return 0;

usage:
    Abc_Print( -2, "usage: rec_ps [-h]\n" );
    Abc_Print( -2, "\t        prints statistics about the recorded AIG subgraphs\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRecUse( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkRecIsRunning() )
    {
        Abc_Print( -1, "This command works for AIGs only after calling \"rec_start\".\n" );
        return 0;
    }
    // get the new network
    pNtkRes = Abc_NtkRecUse();
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Transforming internal AIG subgraphs into an AIG with choices has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: rec_use [-h]\n" );
    Abc_Print( -2, "\t        transforms internal storage into an AIG with choices\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRecFilter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c, nLimit = 0;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLimit < 0 ) 
                goto usage;
        break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkRecIsRunning() )
    {
        Abc_Print( -1, "This command works for AIGs only after calling \"rec_start\".\n" );
        return 0;
    }
    if (!Abc_NtkRecIsInTrimMode())
        Abc_Print( 0, "This command works fine only in trim mode. Please call \"rec_start -t\" first.\n" );
    
    Abc_NtkRecFilter(nLimit);
    return 0;

usage:
    Abc_Print( -2, "usage: rec_filter [-h]\n" );
    Abc_Print( -2, "\t         filter the library of the recorder\n" );
    Abc_Print( -2, "\t-F num : the limit number of function class [default = %d]\n", nLimit );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRecMerge( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( !Abc_NtkRecIsRunning() )
    {
        Abc_Print( -1, "This command works for AIGs only after calling \"rec_start\".\n" );
        return 0;
    }
    Abc_NtkRecLibMerge(pNtk);
    return 0;

usage:
    Abc_Print( -2, "usage: rec_merge [-h]\n" );
    Abc_Print( -2, "\t        merge libraries\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    char Buffer[100];
    double DelayTarget;
    int fAreaOnly;
    int fRecovery;
    int fSweep;
    int fSwitching;
    int fVerbose;
    int c;
    extern Abc_Ntk_t * Abc_NtkMap( Abc_Ntk_t * pNtk, double DelayTarget, int fRecovery, int fSwitching, int fVerbose );
    extern int Abc_NtkFraigSweep( Abc_Ntk_t * pNtk, int fUseInv, int fExdc, int fVerbose, int fVeryVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    DelayTarget =-1;
    fAreaOnly   = 0;
    fRecovery   = 1;
    fSweep      = 1;
    fSwitching  = 0;
    fVerbose    = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Darspvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            DelayTarget = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( DelayTarget <= 0.0 ) 
                goto usage;
            break;
        case 'a':
            fAreaOnly ^= 1;
            break;
        case 'r':
            fRecovery ^= 1;
            break;
        case 's':
            fSweep ^= 1;
            break;
        case 'p':
            fSwitching ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( fAreaOnly )
        DelayTarget = ABC_INFINITY;

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Strashing before mapping has failed.\n" );
            return 1;
        }
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Balancing before mapping has failed.\n" );
            return 1;
        }
        Abc_Print( 0, "The network was strashed and balanced before mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkMap( pNtk, DelayTarget, fRecovery, fSwitching, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_NtkDelete( pNtk );
            Abc_Print( -1, "Mapping has failed.\n" );
            return 1;
        }
        Abc_NtkDelete( pNtk );
    }
    else
    {
        // get the new network
        pNtkRes = Abc_NtkMap( pNtk, DelayTarget, fRecovery, fSwitching, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "Mapping has failed.\n" );
            return 1;
        }
    }

    if ( fSweep )
        Abc_NtkFraigSweep( pNtkRes, 0, 0, 0, 0 );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    if ( DelayTarget == -1 ) 
        sprintf( Buffer, "not used" );
    else
        sprintf( Buffer, "%.3f", DelayTarget );
    Abc_Print( -2, "usage: map [-D float] [-arspvh]\n" );
    Abc_Print( -2, "\t           performs standard cell mapping of the current network\n" );
    Abc_Print( -2, "\t-D float : sets the global required times [default = %s]\n", Buffer );  
    Abc_Print( -2, "\t-a       : toggles area-only mapping [default = %s]\n", fAreaOnly? "yes": "no" );
    Abc_Print( -2, "\t-r       : toggles area recovery [default = %s]\n", fRecovery? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggles sweep after mapping [default = %s]\n", fSweep? "yes": "no" );
    Abc_Print( -2, "\t-p       : optimizes power by minimizing switching [default = %s]\n", fSwitching? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAmap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Amap_Par_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fSweep;
    int c;
    extern Abc_Ntk_t * Abc_NtkDarAmap( Abc_Ntk_t * pNtk, Amap_Par_t * pPars );
    extern int Abc_NtkFraigSweep( Abc_Ntk_t * pNtk, int fUseInv, int fExdc, int fVerbose, int fVeryVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fSweep = 0;
    Amap_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FAEmxisvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->nIterFlow = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterFlow < 0 ) 
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->nIterArea = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterArea < 0 ) 
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->fEpsilon = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->fEpsilon < 0.0 || pPars->fEpsilon > 1.0 ) 
                goto usage;
            break;
        case 'm':
            pPars->fUseMuxes ^= 1;
            break;
        case 'x':
            pPars->fUseXors ^= 1;
            break;
        case 'i':
            pPars->fFreeInvs ^= 1;
            break;
        case 's':
            fSweep ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Strashing before mapping has failed.\n" );
            return 1;
        }
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Balancing before mapping has failed.\n" );
            return 1;
        }
        Abc_Print( 0, "The network was strashed and balanced before mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkDarAmap( pNtk, pPars );
        if ( pNtkRes == NULL )
        {
            Abc_NtkDelete( pNtk );
            Abc_Print( -1, "Mapping has failed.\n" );
            return 1;
        }
        Abc_NtkDelete( pNtk );
    }
    else
    {
        // get the new network
        pNtkRes = Abc_NtkDarAmap( pNtk, pPars );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "Mapping has failed.\n" );
            return 1;
        }
    }

    if ( fSweep )
        Abc_NtkFraigSweep( pNtkRes, 0, 0, 0, 0 );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: amap [-FA <num>] [-E <float>] [-mxisvh]\n" );
    Abc_Print( -2, "\t           performs standard cell mapping of the current network\n" );
    Abc_Print( -2, "\t-F num   : the number of iterations of area flow [default = %d]\n", pPars->nIterFlow );
    Abc_Print( -2, "\t-A num   : the number of iterations of exact area [default = %d]\n", pPars->nIterArea );
    Abc_Print( -2, "\t-E float : sets epsilon used for tie-breaking [default = %f]\n", pPars->fEpsilon );  
    Abc_Print( -2, "\t-m       : toggles using MUX matching [default = %s]\n", pPars->fUseMuxes? "yes": "no" );
    Abc_Print( -2, "\t-x       : toggles using XOR matching [default = %s]\n", pPars->fUseXors? "yes": "no" );
    Abc_Print( -2, "\t-i       : toggles assuming inverters are free [default = %s]\n", pPars->fFreeInvs? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggles sweep after mapping [default = %s]\n", fSweep? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandUnmap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkHasMapping(pNtk) )
    {
        Abc_Print( -1, "Cannot unmap the network that is not mapped.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkMapToSop( pNtk ) )
    {
        Abc_Print( -1, "Unmapping has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: unmap [-h]\n" );
    Abc_Print( -2, "\t        replaces the library gates by the logic nodes represented using SOPs\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAttach( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsSopLogic(pNtk) )
    {
        Abc_Print( -1, "Can only attach gates if the nodes have SOP representations.\n" );
        return 1;
    }

    // get the new network
    if ( !Abc_NtkAttach( pNtk ) )
    {
        Abc_Print( -1, "Attaching gates has failed.\n" );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: attach [-h]\n" );
    Abc_Print( -2, "\t        replaces the SOP functions by the gates from the library\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSuperChoice( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    extern Abc_Ntk_t * Abc_NtkSuperChoice( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Superchoicing works only for the AIG representation (run \"strash\").\n" );
        return 1;
    }

    // get the new network
    pNtkRes = Abc_NtkSuperChoice( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Superchoicing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: sc [-h]\n" );
    Abc_Print( -2, "\t      performs superchoicing\n" );
    Abc_Print( -2, "\t      (accumulate: \"r file.blif; rsup; b; sc; f -ac; wb file_sc.blif\")\n" );
    Abc_Print( -2, "\t      (map without supergate library: \"r file_sc.blif; ft; map\")\n" );
    Abc_Print( -2, "\t-h  : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSuperChoiceLut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nLutSize;
    int nCutSizeMax;
    int fVerbose;
    extern int Abc_NtkSuperChoiceLut( Abc_Ntk_t * pNtk, int nLutSize, int nCutSizeMax, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fVerbose = 1;
    nLutSize = 4;
    nCutSizeMax = 10;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KNh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutSize < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nCutSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutSizeMax < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Superchoicing works only for the AIG representation (run \"strash\").\n" );
        return 1;
    }

    // convert the network into the SOP network
    pNtkRes = Abc_NtkToLogic( pNtk );

    // get the new network
    if ( !Abc_NtkSuperChoiceLut( pNtkRes, nLutSize, nCutSizeMax, fVerbose ) )
    {
        Abc_NtkDelete( pNtkRes );
        Abc_Print( -1, "Superchoicing has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: scl [-K num] [-N num] [-vh]\n" );
    Abc_Print( -2, "\t        performs superchoicing for K-LUTs\n" );
    Abc_Print( -2, "\t        (accumulate: \"r file.blif; b; scl; f -ac; wb file_sc.blif\")\n" );
    Abc_Print( -2, "\t        (FPGA map: \"r file_sc.blif; ft; read_lut lutlibK; fpga\")\n" );
    Abc_Print( -2, "\t-K num : the number of LUT inputs [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-N num : the max size of the cut [default = %d]\n", nCutSizeMax );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFpga( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[100];
    char LutSize[100];
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fRecovery;
    int fSwitching;
    int fLatchPaths;
    int fVerbose;
    int nLutSize;
    float DelayTarget;

    extern Abc_Ntk_t * Abc_NtkFpga( Abc_Ntk_t * pNtk, float DelayTarget, int fRecovery, int fSwitching, int fLatchPaths, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fRecovery   = 1;
    fSwitching  = 0;
    fLatchPaths = 0;
    fVerbose    = 0;
    DelayTarget =-1;
    nLutSize    =-1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "aplvhDK" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fRecovery ^= 1;
            break;
        case 'p':
            fSwitching ^= 1;
            break;
        case 'l':
            fLatchPaths ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            DelayTarget = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( DelayTarget <= 0.0 ) 
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutSize < 0 ) 
                goto usage;
            break;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // create the new LUT library
    if ( nLutSize >= 3 && nLutSize <= 10 )
        Fpga_SetSimpleLutLib( nLutSize );
/*
    else
    {
        Abc_Print( -1, "Cannot perform FPGA mapping with LUT size %d.\n", nLutSize );
        return 1;
    }
*/
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        // strash and balance the network
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Strashing before FPGA mapping has failed.\n" );
            return 1;
        }
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Balancing before FPGA mapping has failed.\n" );
            return 1;
        }
        Abc_Print( 1, "The network was strashed and balanced before FPGA mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkFpga( pNtk, DelayTarget, fRecovery, fSwitching, fLatchPaths, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_NtkDelete( pNtk );
            Abc_Print( -1, "FPGA mapping has failed.\n" );
            return 1;
        }
        Abc_NtkDelete( pNtk );
    }
    else
    {
        // get the new network
        pNtkRes = Abc_NtkFpga( pNtk, DelayTarget, fRecovery, fSwitching, fLatchPaths, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "FPGA mapping has failed.\n" );
            return 1;
        }
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    if ( DelayTarget == -1 ) 
        sprintf( Buffer, "best possible" );
    else
        sprintf( Buffer, "%.2f", DelayTarget );
    if ( nLutSize == -1 ) 
        sprintf( LutSize, "library" );
    else
        sprintf( LutSize, "%d", nLutSize );
    Abc_Print( -2, "usage: fpga [-D float] [-K num] [-aplvh]\n" );
    Abc_Print( -2, "\t           performs FPGA mapping of the current network\n" );
    Abc_Print( -2, "\t-a       : toggles area recovery [default = %s]\n", fRecovery? "yes": "no" );
    Abc_Print( -2, "\t-p       : optimizes power by minimizing switching activity [default = %s]\n", fSwitching? "yes": "no" );
    Abc_Print( -2, "\t-l       : optimizes latch paths for delay, other paths for area [default = %s]\n", fLatchPaths? "yes": "no" );
    Abc_Print( -2, "\t-D float : sets the required time for the mapping [default = %s]\n", Buffer );  
    Abc_Print( -2, "\t-K num   : the number of LUT inputs (2 < num < 11) [default = %s]%s\n", LutSize, (nLutSize == -1 ? " (type \"print_lut\")" : "") );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFpgaFast( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[100];
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fRecovery;
    int fVerbose;
    int nLutSize;
    float DelayTarget;

    extern Abc_Ntk_t * Abc_NtkFpgaFast( Abc_Ntk_t * pNtk, int nLutSize, int fRecovery, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fRecovery   = 1;
    fVerbose    = 0;
    DelayTarget =-1;
    nLutSize    = 5;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "avhDK" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fRecovery ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            DelayTarget = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( DelayTarget <= 0.0 ) 
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutSize < 0 ) 
                goto usage;
            break;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        // strash and balance the network
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Strashing before FPGA mapping has failed.\n" );
            return 1;
        }
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Balancing before FPGA mapping has failed.\n" );
            return 1;
        }
        Abc_Print( 1, "The network was strashed and balanced before FPGA mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkFpgaFast( pNtk, nLutSize, fRecovery, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_NtkDelete( pNtk );
            Abc_Print( -1, "FPGA mapping has failed.\n" );
            return 1;
        }
        Abc_NtkDelete( pNtk );
    }
    else
    {
        // get the new network
        pNtkRes = Abc_NtkFpgaFast( pNtk, nLutSize, fRecovery, fVerbose );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "FPGA mapping has failed.\n" );
            return 1;
        }
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    if ( DelayTarget == -1 ) 
        sprintf( Buffer, "not used" );
    else
        sprintf( Buffer, "%.2f", DelayTarget );
    Abc_Print( -2, "usage: ffpga [-K num] [-avh]\n" );
    Abc_Print( -2, "\t           performs fast FPGA mapping of the current network\n" );
    Abc_Print( -2, "\t-a       : toggles area recovery [default = %s]\n", fRecovery? "yes": "no" );
//    Abc_Print( -2, "\t-D float : sets the required time for the mapping [default = %s]\n", Buffer );  
    Abc_Print( -2, "\t-K num   : the number of LUT inputs (2 < num < 32) [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[100];
    char LutSize[100];
    Abc_Ntk_t * pNtk, * pNtkRes;
    If_Par_t Pars, * pPars = &Pars;
    int c, fLutMux;
    extern Abc_Ntk_t * Abc_NtkIf( Abc_Ntk_t * pNtk, If_Par_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    memset( pPars, 0, sizeof(If_Par_t) );
    // user-controlable paramters
    pPars->nLutSize    = -1;
    pPars->nCutsMax    =  8;
    pPars->nFlowIters  =  1;
    pPars->nAreaIters  =  2;
    pPars->DelayTarget = -1;
    pPars->Epsilon     =  (float)0.005;
    pPars->fPreprocess =  1; 
    pPars->fArea       =  0;
    pPars->fFancy      =  0;
    pPars->fExpRed     =  1;
    pPars->fLatchPaths =  0;
    pPars->fEdge       =  1;
    pPars->fPower      =  0;
    pPars->fCutMin     =  0;
    pPars->fSeqMap     =  0;
    pPars->fBidec      =  0;
    pPars->fVerbose    =  0;
    pPars->pLutStruct  =  NULL;
    // internal parameters
    pPars->fTruth      =  0;
    pPars->nLatches    =  pNtk? Abc_NtkLatchNum(pNtk) : 0;
    pPars->fLiftLeaves =  0;
    pPars->pLutLib     =  (If_Lib_t *)Abc_FrameReadLibLut();
    pPars->pTimesArr   =  NULL; 
    pPars->pTimesArr   =  NULL;   
    pPars->pFuncCost   =  NULL;   

    fLutMux = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCFADEWSqaflepmrsdbugyojikcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLutSize < 0 ) 
                goto usage;
            // if the LUT size is specified, disable library
            pPars->pLutLib = NULL; 
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCutsMax < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nFlowIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFlowIters < 0 ) 
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nAreaIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAreaIters < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->DelayTarget = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayTarget <= 0.0 ) 
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->Epsilon = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->Epsilon < 0.0 || pPars->Epsilon > 1.0 ) 
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->WireDelay = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->WireDelay < 0.0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by string.\n" );
                goto usage;
            }
            pPars->pLutStruct = argv[globalUtilOptind];
            globalUtilOptind++;
            if ( strlen(pPars->pLutStruct) != 2 && strlen(pPars->pLutStruct) != 3 ) 
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a 2- or 3-char string (e.g. \"44\" or \"555\").\n" );
                goto usage;
            }
            break;
        case 'q':
            pPars->fPreprocess ^= 1;
            break;
        case 'a':
            pPars->fArea ^= 1;
            break;
        case 'r':
            pPars->fExpRed ^= 1;
            break;
        case 'f':
            pPars->fFancy ^= 1;
            break;
        case 'l':
            pPars->fLatchPaths ^= 1;
            break;
        case 'e':
            pPars->fEdge ^= 1;
            break;
        case 'p':
            pPars->fPower ^= 1;
            break;
        case 'm':
            pPars->fCutMin ^= 1;
            break;
        case 's':
            pPars->fSeqMap ^= 1;
            break;
        case 'd':
            pPars->fBidec ^= 1;
            break;
        case 'b':
            pPars->fUseBat ^= 1;
            break;
        case 'u':
            fLutMux ^= 1;
            break;
        case 'g':
            pPars->fDelayOpt ^= 1;
            break;
        case 'y':
            pPars->fUserRecLib ^= 1;
            break;
        case 'o':
            pPars->fUseBuffs ^= 1;
            break;
        case 'j':
            pPars->fEnableCheck07 ^= 1;
            break;
        case 'i':
            pPars->fEnableCheck08 ^= 1;
            break;
        case 'k':
            pPars->fEnableCheck10 ^= 1;
            break;
        case 'c':
            pPars->fEnableRealPos ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
/*
    if ( pPars->fSeqMap )
    {
        Abc_Print( -1, "Sequential mapping is currently disabled.\n" );
        return 1;
    }
*/

    if ( pPars->fSeqMap && pPars->nLatches == 0 )
    {
        Abc_Print( -1, "The network has no latches. Use combinational mapping instead of sequential.\n" );
        return 1;
    }

    if ( pPars->nLutSize == -1 )
    {
        if ( pPars->pLutLib == NULL )
        {
            Abc_Print( -1, "The LUT library is not given.\n" );
            return 1;
        }
        // get LUT size from the library
        pPars->nLutSize = pPars->pLutLib->LutMax;
        // if variable pin delay, force truth table computation
//        if ( pPars->pLutLib->fVarPinDelays )
//            pPars->fTruth = 1;
    }

    if ( pPars->nLutSize < 3 || pPars->nLutSize > IF_MAX_LUTSIZE )
    {
        Abc_Print( -1, "Incorrect LUT size (%d).\n", pPars->nLutSize );
        return 1;
    }

    if ( pPars->nCutsMax < 1 || pPars->nCutsMax >= (1<<12) )
    {
        Abc_Print( -1, "Incorrect number of cuts.\n" );
        return 1;
    }

    if ( fLutMux )
    {
        extern int Abc_NtkCutCostMux( If_Cut_t * pCut );
        pPars->fCutMin   = 1;
        pPars->fTruth    = 1;
        pPars->pFuncCost = Abc_NtkCutCostMux;   
    }

    // enable truth table computation if choices are selected
    if ( (c = Abc_NtkGetChoiceNum( pNtk )) )
    {
        if ( !Abc_FrameReadFlag("silentmode") )
            Abc_Print( 0, "Performing LUT mapping with %d choices.\n", c );
        pPars->fExpRed = 0;
    }

    if ( pPars->fUseBat )
    {
        if ( pPars->nLutSize < 4 || pPars->nLutSize > 6 )
        {
            Abc_Print( -1, "This feature only works for {4,5,6}-LUTs.\n" );
            return 1;
        }
        pPars->fCutMin = 1;            
    }

    if ( pPars->fEnableCheck07 + pPars->fEnableCheck08 + pPars->fEnableCheck10 + (pPars->pLutStruct != NULL) > 1 )
    {
        Abc_Print( -1, "Only one additional check can be performed at the same time.\n" );
        return 1;
    }
    if ( pPars->fEnableCheck07 )
    {
        if ( pPars->nLutSize < 6 || pPars->nLutSize > 7 )
        {
            Abc_Print( -1, "This feature only works for {6,7}-LUTs.\n" );
            return 1;
        }
        pPars->pFuncCell = If_CutPerformCheck07;
        pPars->fCutMin = 1;            
    }
    if ( pPars->fEnableCheck08 )
    {
        if ( pPars->nLutSize < 6 || pPars->nLutSize > 8 )
        {
            Abc_Print( -1, "This feature only works for {6,7,8}-LUTs.\n" );
            return 1;
        }
        pPars->pFuncCell = If_CutPerformCheck08;
        pPars->fCutMin = 1;            
    }
    if ( pPars->fEnableCheck10 )
    {
        if ( pPars->nLutSize < 6 || pPars->nLutSize > 10 )
        {
            Abc_Print( -1, "This feature only works for {6,7,8,9,10}-LUTs.\n" );
            return 1;
        }
        pPars->pFuncCell = If_CutPerformCheck10;
        pPars->fCutMin = 1;            
    }
    if ( pPars->pLutStruct )
    {
        if ( pPars->nLutSize < 6 || pPars->nLutSize > 16 )
        {
            Abc_Print( -1, "This feature only works for [6;16]-LUTs.\n" );
            return 1;
        }
        pPars->pFuncCell = If_CutPerformCheck16;
        pPars->fCutMin = 1;            
    }

    // enable truth table computation if cut minimization is selected
    if ( pPars->fCutMin )
    {
        pPars->fTruth = 1;
        pPars->fExpRed = 0;
    }

    // modify for global delay optimization
    if ( pPars->fDelayOpt || pPars->fUserRecLib )
    {
        pPars->fTruth      =  1;
        pPars->fExpRed     =  0;
        pPars->fUsePerm    =  1;
        pPars->pLutLib     =  NULL;
    }
/*
    // modify for LUT structures
    if ( pPars->pLutStruct )
    {
        if ( pPars->nLutSize == -1 )
        {
            Abc_Print( -1, "Please specify the maximum cut size (-K <num>) when LUT structure is used.\n" );
            return 1;
        }
        pPars->fTruth      =  1;
        pPars->fExpRed     =  0;
        pPars->fUsePerm    =  1;
        pPars->pLutLib     =  NULL;
    }
*/
    // complain if truth tables are requested but the cut size is too large
    if ( pPars->fTruth && pPars->nLutSize > IF_MAX_FUNC_LUTSIZE )
    {
        Abc_Print( -1, "Truth tables cannot be computed for LUT larger than %d inputs.\n", IF_MAX_FUNC_LUTSIZE );
        return 1;
    }

    // disable cut-expansion if edge-based heuristics are selected
//    if ( pPars->fEdge )
//        pPars->fExpRed = 0;

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        // strash and balance the network
        pNtk = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Strashing before FPGA mapping has failed.\n" );
            return 1;
        }
        pNtk = Abc_NtkBalance( pNtkRes = pNtk, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Balancing before FPGA mapping has failed.\n" );
            return 1;
        }
        if ( !Abc_FrameReadFlag("silentmode") )
            Abc_Print( 1, "The network was strashed and balanced before FPGA mapping.\n" );
        // get the new network
        pNtkRes = Abc_NtkIf( pNtk, pPars );
        if ( pNtkRes == NULL )
        {
            Abc_NtkDelete( pNtk );
            Abc_Print( -1, "FPGA mapping has failed.\n" );
            return 0;
        }
        Abc_NtkDelete( pNtk );
    }
    else
    {
        // get the new network
        pNtkRes = Abc_NtkIf( pNtk, pPars );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "FPGA mapping has failed.\n" );
            return 0;
        }
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    if ( pPars->DelayTarget == -1 ) 
        sprintf( Buffer, "best possible" );
    else
        sprintf( Buffer, "%.2f", pPars->DelayTarget );
    if ( pPars->nLutSize == -1 ) 
        sprintf( LutSize, "library" );
    else
        sprintf( LutSize, "%d", pPars->nLutSize );
    Abc_Print( -2, "usage: if [-KCFA num] [-DEW float] [-S str] [-qarlepmsdbugyojikcvh]\n" );
    Abc_Print( -2, "\t           performs FPGA technology mapping of the network\n" );
    Abc_Print( -2, "\t-K num   : the number of LUT inputs (2 < num < %d) [default = %s]\n", IF_MAX_LUTSIZE+1, LutSize );
    Abc_Print( -2, "\t-C num   : the max number of priority cuts (0 < num < 2^12) [default = %d]\n", pPars->nCutsMax );
    Abc_Print( -2, "\t-F num   : the number of area flow recovery iterations (num >= 0) [default = %d]\n", pPars->nFlowIters );
    Abc_Print( -2, "\t-A num   : the number of exact area recovery iterations (num >= 0) [default = %d]\n", pPars->nAreaIters );
    Abc_Print( -2, "\t-D float : sets the delay constraint for the mapping [default = %s]\n", Buffer );  
    Abc_Print( -2, "\t-E float : sets epsilon used for tie-breaking [default = %f]\n", pPars->Epsilon );  
    Abc_Print( -2, "\t-W float : sets wire delay between adjects LUTs [default = %f]\n", pPars->WireDelay );  
    Abc_Print( -2, "\t-S str   : string representing the LUT structure [default = %s]\n", pPars->pLutStruct ? pPars->pLutStruct : "not used" );  
    Abc_Print( -2, "\t-q       : toggles preprocessing using several starting points [default = %s]\n", pPars->fPreprocess? "yes": "no" );
    Abc_Print( -2, "\t-a       : toggles area-oriented mapping [default = %s]\n", pPars->fArea? "yes": "no" );
//    Abc_Print( -2, "\t-f       : toggles one fancy feature [default = %s]\n", pPars->fFancy? "yes": "no" );
    Abc_Print( -2, "\t-r       : enables expansion/reduction of the best cuts [default = %s]\n", pPars->fExpRed? "yes": "no" );
    Abc_Print( -2, "\t-l       : optimizes latch paths for delay, other paths for area [default = %s]\n", pPars->fLatchPaths? "yes": "no" );
    Abc_Print( -2, "\t-e       : uses edge-based cut selection heuristics [default = %s]\n", pPars->fEdge? "yes": "no" );
    Abc_Print( -2, "\t-p       : uses power-aware cut selection heuristics [default = %s]\n", pPars->fPower? "yes": "no" );
    Abc_Print( -2, "\t-m       : enables cut minimization by removing vacuous variables [default = %s]\n", pPars->fCutMin? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggles sequential mapping [default = %s]\n", pPars->fSeqMap? "yes": "no" );
    Abc_Print( -2, "\t-d       : toggles deriving local AIGs using bi-decomposition [default = %s]\n", pPars->fBidec? "yes": "no" );
    Abc_Print( -2, "\t-b       : toggles the use of one special feature [default = %s]\n", pPars->fUseBat? "yes": "no" );
    Abc_Print( -2, "\t-u       : toggles the use of MUXes along with LUTs [default = %s]\n", fLutMux? "yes": "no" );
    Abc_Print( -2, "\t-g       : toggles global delay optimization [default = %s]\n", pPars->fDelayOpt? "yes": "no" );
    Abc_Print( -2, "\t-y       : toggles delay optimization with recorded library [default = %s]\n", pPars->fUserRecLib? "yes": "no" );
    Abc_Print( -2, "\t-o       : toggles using buffers to decouple combinational outputs [default = %s]\n", pPars->fUseBuffs? "yes": "no" );
    Abc_Print( -2, "\t-j       : toggles enabling additional check [default = %s]\n", pPars->fEnableCheck07? "yes": "no" );
    Abc_Print( -2, "\t-i       : toggles enabling additional check [default = %s]\n", pPars->fEnableCheck08? "yes": "no" );
    Abc_Print( -2, "\t-k       : toggles enabling additional check [default = %s]\n", pPars->fEnableCheck10? "yes": "no" );
    Abc_Print( -2, "\t-c       : toggles enabling additional feature [default = %s]\n", pPars->fEnableRealPos? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandInit( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t * pObj;
    int c, i;
    int fZeros;
    int fOnes;
    int fRandom;
    int fDontCare;
    // set defaults
    fZeros    = 0;
    fOnes     = 0;
    fRandom   = 0;
    fDontCare = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "zordh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'z':
            fZeros ^= 1;
            break;
        case 'o':
            fOnes ^= 1;
            break;
        case 'r':
            fRandom ^= 1;
            break;
        case 'd':
            fDontCare ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The current network is combinational.\n" );
        return 0;
    }

    if ( fZeros )
    {
        Abc_NtkForEachLatch( pNtk, pObj, i )
            Abc_LatchSetInit0( pObj );
    }
    else if ( fOnes )
    {
        Abc_NtkForEachLatch( pNtk, pObj, i )
            Abc_LatchSetInit1( pObj );
    }
    else if ( fRandom )
    {
        srand( time(NULL) );
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( rand() & 1 )
                Abc_LatchSetInit1( pObj );
            else
                Abc_LatchSetInit0( pObj );
    }
    else if ( fDontCare )
    {
        Abc_NtkForEachLatch( pNtk, pObj, i )
            Abc_LatchSetInitDc( pObj );
    }
    else
        Abc_Print( -1, "The initial states remain unchanged.\n" );
    return 0;

usage:
    Abc_Print( -2, "usage: init [-zordh]\n" );
    Abc_Print( -2, "\t        resets initial states of all latches\n" );
    Abc_Print( -2, "\t-z    : set zeros initial states [default = %s]\n", fZeros? "yes": "no" );
    Abc_Print( -2, "\t-o    : set ones initial states [default = %s]\n", fOnes? "yes": "no" );
    Abc_Print( -2, "\t-d    : set don't-care initial states [default = %s]\n", fDontCare? "yes": "no" );
    Abc_Print( -2, "\t-r    : set random initial states [default = %s]\n", fRandom? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandZero( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    extern Abc_Ntk_t * Abc_NtkRestrashZero( Abc_Ntk_t * pNtk, int fCleanup );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The current network is combinational.\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for AIGs.\n" );
        return 0;
    }

    // get the new network
    pNtkRes = Abc_NtkRestrashZero( pNtk, 0 );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Converting to sequential AIG has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: zero [-h]\n" );
    Abc_Print( -2, "\t        converts latches to have const-0 initial value\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandUndc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The current network is combinational.\n" );
        return 0;
    }

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command works only for logic networks.\n" );
        return 0;
    }

    // get the new network
    Abc_NtkConvertDcLatches( pNtk );
    return 0;

usage:
    Abc_Print( -2, "usage: undc [-h]\n" );
    Abc_Print( -2, "\t        converts latches with DC init values into free PIs\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandOneHot( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    extern Abc_Ntk_t * Abc_NtkConvertOnehot( Abc_Ntk_t * pNtk );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The current network is combinational.\n" );
        return 0;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command works only for logic networks.\n" );
        return 0;
    }
    // get the new network
    pNtkRes = Abc_NtkConvertOnehot( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Converting to one-hot encoding has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: onehot [-h]\n" );
    Abc_Print( -2, "\t        converts natural encoding into one-hot encoding\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPipe( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nLatches;
    extern void Abc_NtkLatchPipe( Abc_Ntk_t * pNtk, int nLatches );
    // set defaults
    nLatches = 5;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Lh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nLatches = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLatches < 0 ) 
                goto usage;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The current network is combinational.\n" );
        return 0;
    }

    // update the network
    Abc_NtkLatchPipe( pNtk, nLatches );
    return 0;

usage:
    Abc_Print( -2, "usage: pipe [-L num] [-h]\n" );
    Abc_Print( -2, "\t         inserts the given number of latches at each PI for pipelining\n" );
    Abc_Print( -2, "\t-L num : the number of latches to insert [default = %d]\n", nLatches );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSeq( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "The network has no latches.\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Conversion to sequential AIG works only for combinational AIGs (run \"strash\").\n" );
        return 1;
    }

    // get the new network
//    pNtkRes = Abc_NtkAigToSeq( pNtk );
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Converting to sequential AIG has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: seq [-h]\n" );
    Abc_Print( -2, "\t        converts AIG into sequential AIG\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandUnseq( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fShare;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fShare = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "sh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fShare ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
/*
    if ( !Abc_NtkIsSeq(pNtk) )
    {
        Abc_Print( -1, "Conversion to combinational AIG works only for sequential AIG (run \"seq\").\n" );
        return 1;
    }
*/
    // share the latches on the fanout edges
//    if ( fShare )
//        Seq_NtkShareFanouts(pNtk);

    // get the new network
//    pNtkRes = Abc_NtkSeqToLogicSop( pNtk );
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Converting sequential AIG into an SOP logic network has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: unseq [-sh]\n" );
    Abc_Print( -2, "\t        converts sequential AIG into an SOP logic network\n" );
    Abc_Print( -2, "\t-s    : toggle sharing latches [default = %s]\n", fShare? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandRetime( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nMaxIters;
    int fForward;
    int fBackward;
    int fOneStep;
    int fVerbose;
    int Mode;
    int nDelayLim;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Mode      =  5;
    nDelayLim =  0;
    fForward  =  0;
    fBackward =  0;
    fOneStep  =  0;
    fVerbose  =  0;
    nMaxIters = 15;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "MDfbsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a positive integer.\n" );
                goto usage;
            }
            Mode = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Mode < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nDelayLim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDelayLim < 0 ) 
                goto usage;
            break;
        case 'f':
            fForward ^= 1;
            break;
        case 'b':
            fBackward ^= 1;
            break;
        case 's':
            fOneStep ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( fForward && fBackward )
    {
        Abc_Print( -1, "Only one switch \"-f\" or \"-b\" can be selected at a time.\n" );
        return 1;
    }

    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network has no latches. Retiming is not performed.\n" );
        return 0;
    }

    if ( Mode < 0 || Mode > 6 )
    {
        Abc_Print( -1, "The mode (%d) is incorrect. Retiming is not performed.\n", Mode );
        return 0;
    }

    if ( Abc_NtkIsStrash(pNtk) )
    {
        if ( Abc_NtkGetChoiceNum(pNtk) )
        {
            Abc_Print( -1, "Retiming with choice nodes is not implemented.\n" );
            return 0;
        }
        // convert the network into an SOP network
        pNtkRes = Abc_NtkToLogic( pNtk );
        // perform the retiming
        Abc_NtkRetime( pNtkRes, Mode, nDelayLim, fForward, fBackward, fOneStep, fVerbose );
        // replace the current network
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        return 0;
    }

    // get the network in the SOP form
    if ( !Abc_NtkToSop(pNtk, 0) )
    {
        Abc_Print( -1, "Converting to SOPs has failed.\n" );
        return 0;
    }

    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "The network is not a logic network. Retiming is not performed.\n" );
        return 0;
    }

    // perform the retiming
    Abc_NtkRetime( pNtk, Mode, nDelayLim, fForward, fBackward, fOneStep, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: retime [-MD num] [-fbvh]\n" );
    Abc_Print( -2, "\t         retimes the current network using one of the algorithms:\n" );
    Abc_Print( -2, "\t             1: most forward retiming\n" );
    Abc_Print( -2, "\t             2: most backward retiming\n" );
    Abc_Print( -2, "\t             3: forward and backward min-area retiming\n" );
    Abc_Print( -2, "\t             4: forward and backward min-delay retiming\n" );
    Abc_Print( -2, "\t             5: mode 3 followed by mode 4\n" );
    Abc_Print( -2, "\t             6: Pan's optimum-delay retiming using binary search\n" );
    Abc_Print( -2, "\t-M num : the retiming algorithm to use [default = %d]\n", Mode );
    Abc_Print( -2, "\t-D num : the minimum delay target (0=unused) [default = %d]\n", nDelayLim );
    Abc_Print( -2, "\t-f     : enables forward-only retiming in modes 3,4,5 [default = %s]\n", fForward? "yes": "no" );
    Abc_Print( -2, "\t-b     : enables backward-only retiming in modes 3,4,5 [default = %s]\n", fBackward? "yes": "no" );
    Abc_Print( -2, "\t-s     : enables retiming one step only in mode 4 [default = %s]\n", fOneStep? "yes": "no" );
    Abc_Print( -2, "\t-v     : enables verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
//    Abc_Print( -2, "\t-I num : max number of iterations of l-value computation [default = %d]\n", nMaxIters );
//    Abc_Print( -2, "\t-f     : toggle forward retiming (for AIGs) [default = %s]\n", fForward? "yes": "no" );
//    Abc_Print( -2, "\t-b     : toggle backward retiming (for AIGs) [default = %s]\n", fBackward? "yes": "no" );
//    Abc_Print( -2, "\t-i     : toggle computation of initial state [default = %s]\n", fInitial? "yes": "no" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDRetime( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fMinArea;
    int fForwardOnly;
    int fBackwardOnly;
    int fInitial;
    int nStepsMax;
    int fFastAlgo;
    int fVerbose;
    int c, nMaxIters;
    extern Abc_Ntk_t * Abc_NtkDarRetime( Abc_Ntk_t * pNtk, int nStepsMax, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkDarRetimeF( Abc_Ntk_t * pNtk, int nStepsMax, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkDarRetimeMinArea( Abc_Ntk_t * pNtk, int nMaxIters, int fForwardOnly, int fBackwardOnly, int fInitial, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkDarRetimeMostFwd( Abc_Ntk_t * pNtk, int nMaxIters, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fMinArea  = 1;
    fForwardOnly = 0;
    fBackwardOnly = 0;
    fInitial = 1;
    nStepsMax = 100000;
    fFastAlgo = 0;
    nMaxIters = 20;
    fVerbose  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NSmfbiavh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nMaxIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMaxIters < 0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nStepsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nStepsMax < 0 ) 
                goto usage;
            break;
        case 'm':
            fMinArea ^= 1;
            break;
        case 'f':
            fForwardOnly ^= 1;
            break;
        case 'b':
            fBackwardOnly ^= 1;
            break;
        case 'i':
            fInitial ^= 1;
            break;
        case 'a':
            fFastAlgo ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network has no latches. Retiming is not performed.\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
        return 0;
    }

    // perform the retiming
    if ( fMinArea )
        pNtkRes = Abc_NtkDarRetimeMinArea( pNtk, nMaxIters, fForwardOnly, fBackwardOnly, fInitial, fVerbose );
    else if ( fFastAlgo )
        pNtkRes = Abc_NtkDarRetime( pNtk, nStepsMax, fVerbose );
    else
//        pNtkRes = Abc_NtkDarRetimeF( pNtk, nStepsMax, fVerbose );
        pNtkRes = Abc_NtkDarRetimeMostFwd( pNtk, nMaxIters, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Retiming has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: dretime [-NS num] [-mfbiavh]\n" );
    Abc_Print( -2, "\t         new implementation of min-area (or most-forward) retiming\n" );
    Abc_Print( -2, "\t-m     : toggle min-area retiming and most-forward retiming [default = %s]\n", fMinArea? "min-area": "most-fwd" );
    Abc_Print( -2, "\t-f     : enables forward-only retiming [default = %s]\n", fForwardOnly? "yes": "no" );
    Abc_Print( -2, "\t-b     : enables backward-only retiming [default = %s]\n", fBackwardOnly? "yes": "no" );
    Abc_Print( -2, "\t-i     : enables init state computation [default = %s]\n", fInitial? "yes": "no" );
    Abc_Print( -2, "\t-N num : the max number of one-frame iterations to perform [default = %d]\n", nMaxIters );
    Abc_Print( -2, "\t-S num : the max number of forward retiming steps to perform [default = %d]\n", nStepsMax );
    Abc_Print( -2, "\t-a     : enables a fast most-forward algorithm [default = %s]\n", fFastAlgo? "yes": "no" );
    Abc_Print( -2, "\t-v     : enables verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFlowRetime( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c, nMaxIters;
    int fForward;
    int fBackward;
    int fVerbose;
    int fComputeInit, fGuaranteeInit, fBlockConst;
    int fFastButConservative;
    int maxDelay;

    Abc_Print( -1, "This command is temporarily disabled.\n" );
    return 0;
//    extern Abc_Ntk_t* Abc_FlowRetime_MinReg( Abc_Ntk_t * pNtk, int fVerbose, 
//                                             int fComputeInit, int fGuaranteeInit, int fBlockConst,
//                                             int fForward, int fBackward, int nMaxIters,
//                                             int maxDelay, int fFastButConservative);

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fForward  =  0;
    fFastButConservative = 0;
    fBackward =  0;
    fComputeInit =  1;
    fGuaranteeInit =  0;
    fVerbose  =  0;
    fBlockConst  =  0;
    nMaxIters = 999;
    maxDelay  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "MDfcgbkivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nMaxIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMaxIters < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a positive integer.\n" );
                goto usage;
            }
            maxDelay = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( maxDelay < 0 ) 
                goto usage;
           break;
        case 'f':
            fForward ^= 1;
            break;
        case 'c':
            fFastButConservative ^= 1;
            break;
        case 'i':
            fComputeInit ^= 1;
            break;
        case 'b':
            fBackward ^= 1;
            break;
        case 'g':
            fGuaranteeInit ^= 1;
            break;
        case 'k':
            fBlockConst ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( fForward && fBackward )
    {
        Abc_Print( -1, "Only one switch \"-f\" or \"-b\" can be selected at a time.\n" );
        return 1;
    }
 
    if ( fGuaranteeInit && !fComputeInit )
    {
      Abc_Print( -1, "Initial state guarantee (-g) requires initial state computation (-i).\n" );
      return 1;
    }

    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network has no latches. Retiming is not performed.\n" );
        return 0;
    }

    if ( Abc_NtkGetChoiceNum(pNtk) )
      {
        Abc_Print( -1, "Retiming with choice nodes is not implemented.\n" );
        return 0;
      }

    // perform the retiming
//    pNtkRes = Abc_FlowRetime_MinReg( pNtk, fVerbose, fComputeInit,
//                                     fGuaranteeInit, fBlockConst, 
//                                     fForward, fBackward, 
//                                     nMaxIters, maxDelay, fFastButConservative );

    if (pNtkRes != pNtk)
      Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );

    return 0;

usage:
    Abc_Print( -2, "usage: fretime [-M num] [-D num] [-fbvih]\n" );
    Abc_Print( -2, "\t         retimes the current network using flow-based algorithm\n" );
    Abc_Print( -2, "\t-M num : the maximum number of iterations [default = %d]\n", nMaxIters );
    Abc_Print( -2, "\t-D num : the maximum delay [default = none]\n" );
    Abc_Print( -2, "\t-i     : enables init state computation [default = %s]\n", fComputeInit? "yes": "no" );
    Abc_Print( -2, "\t-k     : blocks retiming over const nodes [default = %s]\n", fBlockConst? "yes": "no" );
    Abc_Print( -2, "\t-g     : guarantees init state computation [default = %s]\n", fGuaranteeInit? "yes": "no" );
    Abc_Print( -2, "\t-c     : very fast (but conserv.) delay constraints [default = %s]\n", fFastButConservative? "yes": "no" );
    Abc_Print( -2, "\t-f     : enables forward-only retiming  [default = %s]\n", fForward? "yes": "no" );
    Abc_Print( -2, "\t-b     : enables backward-only retiming [default = %s]\n", fBackward? "yes": "no" );
    Abc_Print( -2, "\t-v     : enables verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCRetime( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkCRetime( Abc_Ntk_t * pNtk, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fVerbose    = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for logic networks.\n" );
        return 1;
    }
    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    // modify the current network
    pNtkRes = Abc_NtkCRetime( pNtk, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Sequential cleanup has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: cretime [-vh]\n" );
    Abc_Print( -2, "\t         performs most-forward retiming with equiv classes\n" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSeqFpga( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkNew, * pNtkRes;
    int c, nMaxIters;
    int fVerbose;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nMaxIters = 15;
    fVerbose  =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nMaxIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMaxIters < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkHasAig(pNtk) )
    {
/*
        // quit if there are choice nodes
        if ( Abc_NtkGetChoiceNum(pNtk) )
        {
            Abc_Print( -1, "Currently cannot map/retime networks with choice nodes.\n" );
            return 0;
        }
*/
//        if ( Abc_NtkIsStrash(pNtk) )
//            pNtkNew = Abc_NtkAigToSeq(pNtk);
//        else
//            pNtkNew = Abc_NtkDup(pNtk);
        pNtkNew = NULL;
    }
    else
    {
        // strash and balance the network
        pNtkNew = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtkNew == NULL )
        {
            Abc_Print( -1, "Strashing before FPGA mapping/retiming has failed.\n" );
            return 1;
        }

        pNtkNew = Abc_NtkBalance( pNtkRes = pNtkNew, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtkNew == NULL )
        {
            Abc_Print( -1, "Balancing before FPGA mapping has failed.\n" );
            return 1;
        }

        // convert into a sequential AIG
//        pNtkNew = Abc_NtkAigToSeq( pNtkRes = pNtkNew );
        pNtkNew = NULL;
        Abc_NtkDelete( pNtkRes );
        if ( pNtkNew == NULL )
        {
            Abc_Print( -1, "Converting into a seq AIG before FPGA mapping/retiming has failed.\n" );
            return 1;
        }

        Abc_Print( 1, "The network was strashed and balanced before FPGA mapping/retiming.\n" );
    }

    // get the new network
//    pNtkRes = Seq_NtkFpgaMapRetime( pNtkNew, nMaxIters, fVerbose );
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
//        Abc_Print( -1, "Sequential FPGA mapping has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return 0;
    }
    Abc_NtkDelete( pNtkNew );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: sfpga [-I num] [-vh]\n" );
    Abc_Print( -2, "\t         performs integrated sequential FPGA mapping/retiming\n" );
    Abc_Print( -2, "\t-I num : max number of iterations of l-value computation [default = %d]\n", nMaxIters );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSeqMap( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkNew, * pNtkRes;
    int c, nMaxIters;
    int fVerbose;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nMaxIters = 15;
    fVerbose  =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ivh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nMaxIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMaxIters < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkHasAig(pNtk) )
    {
/*
        // quit if there are choice nodes
        if ( Abc_NtkGetChoiceNum(pNtk) )
        {
            Abc_Print( -1, "Currently cannot map/retime networks with choice nodes.\n" );
            return 0;
        }
*/
//        if ( Abc_NtkIsStrash(pNtk) )
//            pNtkNew = Abc_NtkAigToSeq(pNtk);
//        else
//            pNtkNew = Abc_NtkDup(pNtk);
        pNtkNew = NULL;
    }
    else
    {
        // strash and balance the network
        pNtkNew = Abc_NtkStrash( pNtk, 0, 0, 0 );
        if ( pNtkNew == NULL )
        {
            Abc_Print( -1, "Strashing before SC mapping/retiming has failed.\n" );
            return 1;
        }

        pNtkNew = Abc_NtkBalance( pNtkRes = pNtkNew, 0, 0, 1 );
        Abc_NtkDelete( pNtkRes );
        if ( pNtkNew == NULL )
        {
            Abc_Print( -1, "Balancing before SC mapping/retiming has failed.\n" );
            return 1;
        }

        // convert into a sequential AIG
//        pNtkNew = Abc_NtkAigToSeq( pNtkRes = pNtkNew );
        pNtkNew = NULL;
        Abc_NtkDelete( pNtkRes );
        if ( pNtkNew == NULL )
        {
            Abc_Print( -1, "Converting into a seq AIG before SC mapping/retiming has failed.\n" );
            return 1;
        }

        Abc_Print( -1, "The network was strashed and balanced before SC mapping/retiming.\n" );
    }

    // get the new network
//    pNtkRes = Seq_MapRetime( pNtkNew, nMaxIters, fVerbose );
    pNtkRes = NULL;
    if ( pNtkRes == NULL )
    {
//        Abc_Print( -1, "Sequential FPGA mapping has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return 0;
    }
    Abc_NtkDelete( pNtkNew );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: smap [-I num] [-vh]\n" );
    Abc_Print( -2, "\t         performs integrated sequential standard-cell mapping/retiming\n" );
    Abc_Print( -2, "\t-I num : max number of iterations of l-value computation [default = %d]\n", nMaxIters );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSeqSweep( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Fra_Ssw_t Pars, * pPars = &Pars;
    int c;
    extern Abc_Ntk_t * Abc_NtkDarSeqSweep( Abc_Ntk_t * pNtk, Fra_Ssw_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    pPars->nPartSize  = 0;
    pPars->nOverSize  = 0;
    pPars->nFramesP   = 0;
    pPars->nFramesK   = 1;
    pPars->nMaxImps   = 5000;
    pPars->nMaxLevs   = 0;
    pPars->fUseImps   = 0;
    pPars->fRewrite   = 0;
    pPars->fFraiging  = 0;
    pPars->fLatchCorr = 0;
    pPars->fWriteImps = 0;
    pPars->fUse1Hot   = 0;
    pPars->fVerbose   = 0;
    pPars->TimeLimit  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PQNFILirfletvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPartSize < 2 ) 
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nOverSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nOverSize < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesP = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesP < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesK = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesK <= 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxImps = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxImps <= 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxLevs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxLevs <= 0 ) 
                goto usage;
            break;
        case 'i':
            pPars->fUseImps ^= 1;
            break;
        case 'r':
            pPars->fRewrite ^= 1;
            break;
        case 'f':
            pPars->fFraiging ^= 1;
            break;
        case 'l':
            pPars->fLatchCorr ^= 1;
            break;
        case 'e':
            pPars->fWriteImps ^= 1;
            break;
        case 't':
            pPars->fUse1Hot ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The network is combinational (run \"fraig\" or \"fraig_sweep\").\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
        return 0;
    }

    if ( pPars->nFramesK > 1 && pPars->fUse1Hot )
    {
        Abc_Print( -1, "Currrently can only use one-hotness for simple induction (K=1).\n" );
        return 0;
    }

    if ( pPars->nFramesP && pPars->fUse1Hot )
    {
        Abc_Print( -1, "Currrently can only use one-hotness without prefix.\n" );
        return 0;
    }

    // get the new network
    pNtkRes = Abc_NtkDarSeqSweep( pNtk, pPars );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Sequential sweeping has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: ssweep [-PQNFL <num>] [-lrfetvh]\n" );
    Abc_Print( -2, "\t         performs sequential sweep using K-step induction\n" );
    Abc_Print( -2, "\t-P num : max partition size (0 = no partitioning) [default = %d]\n", pPars->nPartSize );
    Abc_Print( -2, "\t-Q num : partition overlap (0 = no overlap) [default = %d]\n", pPars->nOverSize );
    Abc_Print( -2, "\t-N num : number of time frames to use as the prefix [default = %d]\n", pPars->nFramesP );
    Abc_Print( -2, "\t-F num : number of time frames for induction (1=simple) [default = %d]\n", pPars->nFramesK );
    Abc_Print( -2, "\t-L num : max number of levels to consider (0=all) [default = %d]\n", pPars->nMaxLevs );
//    Abc_Print( -2, "\t-I num : max number of implications to consider [default = %d]\n", pPars->nMaxImps );
//    Abc_Print( -2, "\t-i     : toggle using implications [default = %s]\n", pPars->fUseImps? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle latch correspondence only [default = %s]\n", pPars->fLatchCorr? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle AIG rewriting [default = %s]\n", pPars->fRewrite? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle fraiging (combinational SAT sweeping) [default = %s]\n", pPars->fFraiging? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle writing implications as assertions [default = %s]\n", pPars->fWriteImps? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle using one-hotness conditions [default = %s]\n", pPars->fUse1Hot? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSeqSweep2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    Ssw_Pars_t Pars, * pPars = &Pars;
    int nConstrs = 0;
    int c;
    extern Abc_Ntk_t * Abc_NtkDarSeqSweep2( Abc_Ntk_t * pNtk, Ssw_Pars_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Ssw_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PQFCLSIVMNcmplkofdsevwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPartSize < 2 ) 
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nOverSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nOverSize < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesK = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesK <= 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBTLimit <= 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxLevs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxLevs <= 0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesAddSim = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesAddSim < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nItersStop = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nItersStop < 0 ) 
                goto usage;
            break;
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSatVarMax2 = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSatVarMax2 < 0 ) 
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRecycleCalls2 = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRecycleCalls2 < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nConstrs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConstrs < 0 ) 
                goto usage;
            break;
        case 'c':
            pPars->fConstrs ^= 1;
            break;
        case 'm':
            pPars->fMergeFull ^= 1;
            break;
        case 'p':
            pPars->fPolarFlip ^= 1;
            break;
        case 'l':
            pPars->fLatchCorr ^= 1;
            break;
        case 'k':
            pPars->fConstCorr ^= 1;
            break;
        case 'o':
            pPars->fOutputCorr ^= 1;
            break;
        case 'f':
            pPars->fSemiFormal ^= 1;
            break;
        case 'd':
            pPars->fDynamic ^= 1;
            break;
        case 's':
            pPars->fLocalSim ^= 1;
            break;
        case 'e':
            pPars->fEquivDump ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fFlopVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The network is combinational (run \"fraig\" or \"fraig_sweep\").\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
        return 0;
    }

    // if constraints are to be used, network should have no constraints
    if ( nConstrs > 0 )
    {
        if ( Abc_NtkConstrNum(pNtk) > 0 )
        {
            Abc_Print( -1, "The network already has %d constraints.\n", Abc_NtkConstrNum(pNtk) );
            return 0;
        }
        else
        {
            Abc_Print( 0, "Setting the number of constraints to be %d.\n", nConstrs );
            pNtk->nConstrs = nConstrs;
        }
    }

    if ( pPars->fConstrs )
    {
        if ( Abc_NtkConstrNum(pNtk) > 0 )
            Abc_Print( 0, "Performing scorr with %d constraints.\n", Abc_NtkConstrNum(pNtk) );
        else
            Abc_Print( 0, "Performing constraint-based scorr without constraints.\n" );
    }

    // get the new network
    pNtkRes = Abc_NtkDarSeqSweep2( pNtk, pPars );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Sequential sweeping has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: scorr [-PQFCLSIVMN <num>] [-cmplkodsevwh]\n" );
    Abc_Print( -2, "\t         performs sequential sweep using K-step induction\n" );
    Abc_Print( -2, "\t-P num : max partition size (0 = no partitioning) [default = %d]\n", pPars->nPartSize );
    Abc_Print( -2, "\t-Q num : partition overlap (0 = no overlap) [default = %d]\n", pPars->nOverSize );
    Abc_Print( -2, "\t-F num : number of time frames for induction (1=simple) [default = %d]\n", pPars->nFramesK );
    Abc_Print( -2, "\t-C num : max number of conflicts at a node (0=inifinite) [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-L num : max number of levels to consider (0=all) [default = %d]\n", pPars->nMaxLevs );
    Abc_Print( -2, "\t-N num : number of last POs treated as constraints (0=none) [default = %d]\n", pPars->fConstrs );
    Abc_Print( -2, "\t-S num : additional simulation frames for c-examples (0=none) [default = %d]\n", pPars->nFramesAddSim );
    Abc_Print( -2, "\t-I num : iteration number to stop and output SR-model (-1=none) [default = %d]\n", pPars->nItersStop );
    Abc_Print( -2, "\t-V num : min var num needed to recycle the SAT solver [default = %d]\n", pPars->nSatVarMax2 );
    Abc_Print( -2, "\t-M num : min call num needed to recycle the SAT solver [default = %d]\n", pPars->nRecycleCalls2 );
    Abc_Print( -2, "\t-N num : set last <num> POs to be constraints (use with -c) [default = %d]\n", nConstrs );
    Abc_Print( -2, "\t-c     : toggle using explicit constraints [default = %s]\n", pPars->fConstrs? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle full merge if constraints are present [default = %s]\n", pPars->fMergeFull? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle alighning polarity of SAT variables [default = %s]\n", pPars->fPolarFlip? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle doing latch correspondence [default = %s]\n", pPars->fLatchCorr? "yes": "no" );
    Abc_Print( -2, "\t-k     : toggle doing constant correspondence [default = %s]\n", pPars->fConstCorr? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle doing \'PO correspondence\' [default = %s]\n", pPars->fOutputCorr? "yes": "no" );
//    Abc_Print( -2, "\t-f     : toggle filtering using iterative BMC [default = %s]\n", pPars->fSemiFormal? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle dynamic addition of constraints [default = %s]\n", pPars->fDynamic? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle local simulation in the cone of influence [default = %s]\n", pPars->fLocalSim? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle dumping disproved internal equivalences [default = %s]\n", pPars->fEquivDump? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printout of flop equivalences [default = %s]\n", pPars->fFlopVerbose? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestSeqSweep( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pFileName;
    Fra_Ssw_t Pars, * pPars = &Pars;
    int c;
//    extern Abc_Ntk_t * Abc_NtkDarSeqSweep( Abc_Ntk_t * pNtk, Fra_Ssw_t * pPars );
    extern int Fra_FraigInductionTest( char * pFileName, Fra_Ssw_t * pParams );

    // set defaults
    pPars->nPartSize  = 0;
    pPars->nOverSize  = 0;
    pPars->nFramesP   = 0;
    pPars->nFramesK   = 1;
    pPars->nMaxImps   = 5000;
    pPars->nMaxLevs   = 0;
    pPars->fUseImps   = 0;
    pPars->fRewrite   = 0;
    pPars->fFraiging  = 0;
    pPars->fLatchCorr = 0;
    pPars->fWriteImps = 0;
    pPars->fUse1Hot   = 0;
    pPars->fVerbose   = 0;
    pPars->TimeLimit  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PQNFILirfletvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPartSize < 2 ) 
                goto usage;
            break;
        case 'Q':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-Q\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nOverSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nOverSize < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesP = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesP < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesK = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesK <= 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxImps = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxImps <= 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMaxLevs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMaxLevs <= 0 ) 
                goto usage;
            break;
        case 'i':
            pPars->fUseImps ^= 1;
            break;
        case 'r':
            pPars->fRewrite ^= 1;
            break;
        case 'f':
            pPars->fFraiging ^= 1;
            break;
        case 'l':
            pPars->fLatchCorr ^= 1;
            break;
        case 'e':
            pPars->fWriteImps ^= 1;
            break;
        case 't':
            pPars->fUse1Hot ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    // get the input file name
    if ( argc == globalUtilOptind + 1 )
        pFileName = argv[globalUtilOptind];
    else
    {
        Abc_Print( -1, "File name should be given on the command line.\n" );
        return 1;
    }
    Fra_FraigInductionTest( pFileName, pPars );
    return 0;

usage:
    Abc_Print( -2, "usage: testssw [-PQNFL num] [-lrfetvh] <file>\n" );
    Abc_Print( -2, "\t         performs sequential sweep using K-step induction\n" );
    Abc_Print( -2, "\t         (outputs a file with a set of pairs of equivalent nodes)\n" );
    Abc_Print( -2, "\t-P num : max partition size (0 = no partitioning) [default = %d]\n", pPars->nPartSize );
    Abc_Print( -2, "\t-Q num : partition overlap (0 = no overlap) [default = %d]\n", pPars->nOverSize );
    Abc_Print( -2, "\t-N num : number of time frames to use as the prefix [default = %d]\n", pPars->nFramesP );
    Abc_Print( -2, "\t-F num : number of time frames for induction (1=simple) [default = %d]\n", pPars->nFramesK );
    Abc_Print( -2, "\t-L num : max number of levels to consider (0=all) [default = %d]\n", pPars->nMaxLevs );
//    Abc_Print( -2, "\t-I num : max number of implications to consider [default = %d]\n", pPars->nMaxImps );
//    Abc_Print( -2, "\t-i     : toggle using implications [default = %s]\n", pPars->fUseImps? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle latch correspondence only [default = %s]\n", pPars->fLatchCorr? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle AIG rewriting [default = %s]\n", pPars->fRewrite? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle fraiging (combinational SAT sweeping) [default = %s]\n", pPars->fFraiging? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle writing implications as assertions [default = %s]\n", pPars->fWriteImps? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle using one-hotness conditions [default = %s]\n", pPars->fUse1Hot? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestScorr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkTestScorr( char * pFileNameIn, char * pFileNameOut, int nStepsMax, int nBTLimit, int fNewAlgo, int fFlopOnly, int fFfNdOnly, int fVerbose );

    Abc_Ntk_t * pNtkRes;
    int c;
    int nConfMax;   
    int nStepsMax;
    int fNewAlgo;
    int fFlopOnly;
    int fFfNdOnly;
    int fVerbose;
    // set defaults
    nConfMax  = 100;   
    nStepsMax =  -1;
    fNewAlgo  =   0;
    fFlopOnly =   0;
    fFfNdOnly =   0;
    fVerbose  =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CSnfsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfMax < 0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nStepsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nStepsMax < 0 ) 
                goto usage;
            break;
        case 'n':
            fNewAlgo ^= 1;
            break;
        case 'f':
            fFlopOnly ^= 1;
            break;
        case 's':
            fFfNdOnly ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( argc != globalUtilOptind + 2 )
    {
        Abc_Print( -1, "Expecting two files names on the command line.\n" );
        goto usage;
    }
    if ( fFlopOnly && fFfNdOnly )
    {
        Abc_Print( -1, "These two options (-f and -s) are incompatible.\n" );
        goto usage;
    }
    // get the new network
    pNtkRes = Abc_NtkTestScorr( argv[globalUtilOptind], argv[globalUtilOptind+1], nStepsMax, nConfMax, fNewAlgo, fFlopOnly, fFfNdOnly, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Sequential sweeping has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: testscorr [-CS num] [-nfsvh] <file_in> <file_out>\n" );
    Abc_Print( -2, "\t             outputs the list of sequential equivalences into a file\n" );
    Abc_Print( -2, "\t             (if <file_in> is in BENCH, init state file should be the same directory)\n" );
    Abc_Print( -2, "\t-C num     : limit on the number of conflicts [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-S num     : limit on refinement iterations (-1=no limit, 0=after BMC, etc) [default = %d]\n", nStepsMax );
    Abc_Print( -2, "\t-n         : toggle between \"scorr\" and \"&scorr\" [default = %s]\n", fNewAlgo? "&scorr": "scorr" );
    Abc_Print( -2, "\t-f         : toggle reporting only flop/flop equivs [default = %s]\n", fFlopOnly? "yes": "no" );
    Abc_Print( -2, "\t-s         : toggle reporting only flop/flop and flop/node equivs [default = %s]\n", fFfNdOnly? "yes": "no" );
    Abc_Print( -2, "\t-v         : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h         : print the command usage\n");
    Abc_Print( -2, "\t<file_in>  : input file with design for sequential equivalence computation\n");
    Abc_Print( -2, "\t<file_out> : output file with the list of pairs of equivalent signals\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLcorr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nFramesP;
    int nConfMax;
    int nVarsMax;
    int fNewAlgor;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkDarLcorr( Abc_Ntk_t * pNtk, int nFramesP, int nConfMax, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkDarLcorrNew( Abc_Ntk_t * pNtk, int nVarsMax, int nConfMax, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);



    // set defaults
    nFramesP   =     0;
    nConfMax   =  1000;
    nVarsMax   =  1000;
    fNewAlgor  =     1;
    fVerbose   =     0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PCSnvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesP = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFramesP < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfMax < 0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nVarsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVarsMax < 0 ) 
                goto usage;
            break;
        case 'n':
            fNewAlgor ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The network is combinational (run \"fraig\" or \"fraig_sweep\").\n" );
        return 0;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
        return 0;
    }

    // get the new network
    if ( fNewAlgor )
        pNtkRes = Abc_NtkDarLcorrNew( pNtk, nVarsMax, nConfMax, fVerbose );
    else
        pNtkRes = Abc_NtkDarLcorr( pNtk, nFramesP, nConfMax, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Sequential sweeping has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: lcorr [-PCS num] [-nvh]\n" );
    Abc_Print( -2, "\t         computes latch correspondence using 1-step induction\n" );
    Abc_Print( -2, "\t-P num : number of time frames to use as the prefix [default = %d]\n", nFramesP );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-S num : the max number of SAT variables [default = %d]\n", nVarsMax );
    Abc_Print( -2, "\t-n     : toggle using new algorithm [default = %s]\n", fNewAlgor? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSeqCleanup( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int fLatchConst  =   1;
    int fLatchEqual  =   1;
    int fSaveNames   =   1;
    int fUseMvSweep  =   0;
    int nFramesSymb  =   1;
    int nFramesSatur = 512;
    int fVerbose     =   0;
    int fVeryVerbose =   0;
    extern Abc_Ntk_t * Abc_NtkDarLatchSweep( Abc_Ntk_t * pNtk, int fLatchConst, int fLatchEqual, int fSaveNames, int fUseMvSweep, int nFramesSymb, int nFramesSatur, int fVerbose, int fVeryVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cenmFSvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fLatchConst ^= 1;
            break;
        case 'e':
            fLatchEqual ^= 1;
            break;
        case 'n':
            fSaveNames ^= 1;
            break;
        case 'm':
            fUseMvSweep ^= 1;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesSymb = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFramesSymb < 0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesSatur = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFramesSatur < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for structrally hashed networks.\n" );
        return 1;
    }
    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    // modify the current network
    pNtkRes = Abc_NtkDarLatchSweep( pNtk, fLatchConst, fLatchEqual, fSaveNames, fUseMvSweep, nFramesSymb, nFramesSatur, fVerbose, fVeryVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Sequential cleanup has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: scleanup [-cenmFSvwh]\n" );
    Abc_Print( -2, "\t         performs sequential cleanup of the current network\n" );
    Abc_Print( -2, "\t         by removing nodes and latches that do not feed into POs\n" );
    Abc_Print( -2, "\t-c     : sweep stuck-at latches detected by ternary simulation [default = %s]\n", fLatchConst? "yes": "no" );
    Abc_Print( -2, "\t-e     : merge equal latches (same data inputs and init states) [default = %s]\n", fLatchEqual? "yes": "no" );
    Abc_Print( -2, "\t-n     : toggle preserving latch names [default = %s]\n", fSaveNames? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle using hybrid ternary/symbolic simulation [default = %s]\n", fUseMvSweep? "yes": "no" );
    Abc_Print( -2, "\t-F num : the number of first frames simulated symbolically [default = %d]\n", nFramesSymb );
    Abc_Print( -2, "\t-S num : the number of frames when symbolic saturation begins [default = %d]\n", nFramesSatur );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle very verbose output [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCycle( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nFrames;
    int fUseXval;
    int fVerbose;
    extern void Abc_NtkCycleInitState( Abc_Ntk_t * pNtk, int nFrames, int fUseXval, int fVerbose );
    extern void Abc_NtkCycleInitStateSop( Abc_Ntk_t * pNtk, int nFrames, int fVerbose );
    // set defaults
    nFrames    = 100;
    fUseXval   =   0;
    fVerbose   =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fxvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'x':
            fUseXval ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) && !Abc_NtkIsSopLogic(pNtk) )
    {
        Abc_Print( -1, "Only works for strashed networks or logic SOP networks.\n" );
        return 1;
    }
    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( fUseXval && !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "X-valued simulation only works for AIGs. Run \"strash\".\n" );
        return 0;
    }
    if ( fUseXval )
        Abc_NtkCycleInitState( pNtk, nFrames, 1, fVerbose );
    else if ( Abc_NtkIsStrash(pNtk) )
        Abc_NtkCycleInitState( pNtk, nFrames, 0, fVerbose );
    else
        Abc_NtkCycleInitStateSop( pNtk, nFrames, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: cycle [-F num] [-xvh]\n" );
    Abc_Print( -2, "\t         cycles sequential circuit for the given number of timeframes\n" );
    Abc_Print( -2, "\t         to derive a new initial state (which may be on the envelope)\n" );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-x     : use x-valued primary inputs [default = %s]\n", fUseXval? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandXsim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nFrames;
    int fXInputs;
    int fXState;
    int fVerbose;
    extern void Abc_NtkXValueSimulate( Abc_Ntk_t * pNtk, int nFrames, int fXInputs, int fXState, int fVerbose );
    // set defaults
    nFrames    = 10;
    fXInputs   =  0;
    fXState    =  0;
    fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fisvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'i':
            fXInputs ^= 1;
            break;
        case 's':
            fXState ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for strashed networks.\n" );
        return 1;
    }
    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    Abc_NtkXValueSimulate( pNtk, nFrames, fXInputs, fXState, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: xsim [-F num] [-isvh]\n" );
    Abc_Print( -2, "\t         performs X-valued simulation of the AIG\n" );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-i     : toggle X-valued representation of inputs [default = %s]\n", fXInputs? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle X-valued representation of state [default = %s]\n", fXState? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fNew;
    int fComb;
    int nFrames;
    int nWords;
    int TimeOut;
    int fMiter;
    int fVerbose;
    extern int Abc_NtkDarSeqSim( Abc_Ntk_t * pNtk, int nFrames, int nWords, int TimeOut, int fNew, int fComb, int fMiter, int fVerbose );
    // set defaults
    fNew       =  0;
    fComb      =  0;
    nFrames    = 32;
    nWords     =  8;
    TimeOut    = 30;
    fMiter     =  0;
    fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FWTncmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nWords < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            TimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( TimeOut < 0 ) 
                goto usage;
            break;
        case 'n':
            fNew ^= 1;
            break;
        case 'c':
            fComb ^= 1;
            break;
        case 'm':
            fMiter ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for strashed networks.\n" );
        return 1;
    }
    ABC_FREE( pNtk->pSeqModel );
    pAbc->Status = Abc_NtkDarSeqSim( pNtk, nFrames, nWords, TimeOut, fNew, fComb, fMiter, fVerbose );  
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    return 0;

usage:
    Abc_Print( -2, "usage: sim [-FWT num] [-ncmvh]\n" );
    Abc_Print( -2, "\t         performs random simulation of the sequential miter\n" );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n", nWords );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", TimeOut );
    Abc_Print( -2, "\t-n     : toggle new vs. old implementation [default = %s]\n", fNew? "new": "old" );
    Abc_Print( -2, "\t-c     : toggle comb vs. seq simulaton [default = %s]\n", fComb? "comb": "seq" );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", fMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSim3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nFrames;
    int nWords;
    int nBinSize;
    int nRounds;
    int nRandSeed;
    int TimeOut;
    int fVerbose;
    extern int Abc_NtkDarSeqSim3( Abc_Ntk_t * pNtk, int nFrames, int nWords, int nBinSize, int nRounds, int nRandSeed, int TimeOut, int fVerbose );
    // set defaults
    nFrames    =  20;
    nWords     =  50;
    nBinSize   =   8;
    nRounds    =  80;
    nRandSeed  =   0;
    TimeOut    =   0;
    fVerbose   =   0;
    // parse command line
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FWBRNTvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nWords < 0 ) 
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            nBinSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBinSize < 0 ) 
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRounds < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nRandSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRandSeed < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            TimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( TimeOut < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for strashed networks.\n" );
        return 1;
    }
    ABC_FREE( pNtk->pSeqModel );
    pAbc->Status = Abc_NtkDarSeqSim3( pNtk, nFrames, nWords, nBinSize, nRounds, nRandSeed, TimeOut, fVerbose );  
//    pAbc->nFrames = pAbc->pCex->iFrame;
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    return 0;

usage:
    Abc_Print( -2, "usage: sim3 [-FWBRNT num] [-vh]\n" );
    Abc_Print( -2, "\t         performs random simulation of the sequential miter\n" );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n",  nWords );
    Abc_Print( -2, "\t-B num : the number of flops in one bin [default = %d]\n",   nBinSize );
    Abc_Print( -2, "\t-R num : the number of simulation rounds [default = %d]\n",  nRounds );
    Abc_Print( -2, "\t-N num : random number seed (1 <= num <= 1000) [default = %d]\n", nRandSeed );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", TimeOut );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDarPhase( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int c;
    int nFrames, nPref;
    int fIgnore;
    int fPrint;
    int fVerbose;
    extern Abc_Ntk_t * Abc_NtkPhaseAbstract( Abc_Ntk_t * pNtk, int nFrames, int nPref, int fIgnore, int fPrint, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nFrames     = 0;
    nPref       = 0;
    fIgnore     = 0;
    fPrint      = 0;
    fVerbose    = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FPipvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPref = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPref < 0 ) 
                goto usage;
            break;
        case 'i':
            fIgnore ^= 1;
            break;
        case 'p':
            fPrint ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for structrally hashed networks.\n" );
        return 1;
    }
    if ( !Abc_NtkLatchNum(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( fPrint )
    {
        Abc_NtkPhaseAbstract( pNtk, 0, nPref, fIgnore, 1, fVerbose );
        return 0;
    }
    // modify the current network
    pNtkRes = Abc_NtkPhaseAbstract( pNtk, nFrames, nPref, fIgnore, 0, fVerbose );
    if ( pNtkRes == NULL )
    {
//        Abc_Print( -1, "Phase abstraction has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: phase [-FP <num>] [-ipvh]\n" );
    Abc_Print( -2, "\t         performs sequential cleanup of the current network\n" );
    Abc_Print( -2, "\t         by removing nodes and latches that do not feed into POs\n" );
    Abc_Print( -2, "\t-F num : the number of frames to abstract [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-P num : the number of prefix frames to skip [default = %d]\n", nPref );
    Abc_Print( -2, "\t-i     : toggle ignoring the initial state [default = %s]\n", fIgnore? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle printing statistics about generators [default = %s]\n", fPrint? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSynch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtkRes, * pNtk1, * pNtk2, * pNtk;
    char ** pArgvNew;
    int nArgcNew;
    int fDelete1, fDelete2;
    int c;
    int nWords;
    int fVerbose;

    extern Abc_Ntk_t * Abc_NtkDarSynch( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nWords, int fVerbose );
    extern Abc_Ntk_t * Abc_NtkDarSynchOne( Abc_Ntk_t * pNtk, int nWords, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nWords   =  32;
    fVerbose =   1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Wvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nWords <= 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew == 0 )
    {
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Empty network.\n" );
            return 1;
        }
        pNtkRes = Abc_NtkDarSynchOne( pNtk, nWords, fVerbose );
    }
    else
    {
        if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
            return 1;
        if ( Abc_NtkLatchNum(pNtk1) == 0 || Abc_NtkLatchNum(pNtk2) == 0 )
        {
            if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
            if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
            Abc_Print( -1, "The network has no latches..\n" );
            return 0;
        }

        // modify the current network
        pNtkRes = Abc_NtkDarSynch( pNtk1, pNtk2, nWords, fVerbose );
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Synchronization has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: synch [-W <num>] [-vh] <file1> <file2>\n" );
    Abc_Print( -2, "\t         derives and applies synchronization sequence\n" );
    Abc_Print( -2, "\t-W num : the number of simulation words [default = %d]\n", nWords );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tfile1  : (optional) the file with the first design\n");
    Abc_Print( -2, "\tfile2  : (optional) the file with the second design\n\n");
    Abc_Print( -2, "\t         If no designs are given on the command line,\n" );
    Abc_Print( -2, "\t         assumes the current network has no initial state,\n" );
    Abc_Print( -2, "\t         derives synchronization sequence and applies it.\n\n" );
    Abc_Print( -2, "\t         If two designs are given on the command line\n" );
    Abc_Print( -2, "\t         assumes both of them have no initial state,\n" );
    Abc_Print( -2, "\t         derives sequences for both designs, synchorinizes\n" );
    Abc_Print( -2, "\t         them, and creates SEC miter comparing two designs.\n\n" );
    Abc_Print( -2, "\t         If only one design is given on the command line,\n" );
    Abc_Print( -2, "\t         considers the second design to be the current network,\n" );
    Abc_Print( -2, "\t         and derives SEC miter for them, as described above.\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandClockGate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cgt_Par_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtkRes, * pNtk, * pNtkCare;
    int c;

    extern Abc_Ntk_t * Abc_NtkDarClockGate( Abc_Ntk_t * pNtk, Abc_Ntk_t * pCare, Cgt_Par_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Cgt_SetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "LNDCVKavwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLevelMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLevelMax <= 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCandMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCandMax <= 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nOdcMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nOdcMax <= 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfMax <= 0 ) 
                goto usage;
            break;
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nVarsMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nVarsMin <= 0 ) 
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFlopsMin = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFlopsMin <= 0 ) 
                goto usage;
            break;
        case 'a':
            pPars->fAreaOnly ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( argc == globalUtilOptind + 1 )
    {
        pNtkCare = Io_Read( argv[globalUtilOptind], Io_ReadFileType(argv[globalUtilOptind]), 1 );
        if ( pNtkCare == NULL )
        {
            Abc_Print( -1, "Reading care network has failed.\n" );
            return 1;
        }
        // modify the current network
        pNtkRes = Abc_NtkDarClockGate( pNtk, pNtkCare, pPars );
        Abc_NtkDelete( pNtkCare );
    }
    else if ( argc == globalUtilOptind )
    {
        pNtkRes = Abc_NtkDarClockGate( pNtk, NULL, pPars );
    }
    else
    {
        Abc_Print( -1, "Wrong number of arguments.\n" );
        return 0;
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Clock gating has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: clockgate [-LNDCVK <num>] [-avwh] <file>\n" );
    Abc_Print( -2, "\t         sequential clock gating with observability don't-cares\n" );
    Abc_Print( -2, "\t-L num : max level number of a clock gate [default = %d]\n", pPars->nLevelMax );
    Abc_Print( -2, "\t-N num : max number of candidates for a flop [default = %d]\n", pPars->nCandMax );
    Abc_Print( -2, "\t-D num : max number of ODC levels to consider [default = %d]\n", pPars->nOdcMax );
    Abc_Print( -2, "\t-C num : max number of conflicts at a node [default = %d]\n", pPars->nConfMax );
    Abc_Print( -2, "\t-V num : min number of vars to recycle SAT solver [default = %d]\n", pPars->nVarsMin );
    Abc_Print( -2, "\t-K num : min number of flops to recycle SAT solver [default = %d]\n", pPars->nFlopsMin );
    Abc_Print( -2, "\t-a     : toggle minimizing area-only [default = %s]\n", pPars->fAreaOnly? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle even more detailed output [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tfile   : (optional) constraints for primary inputs and register outputs\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandExtWin( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtkRes, * pNtk;
    int c;
    int nObjId;
    int nDist;
    int fVerbose;

    extern Abc_Ntk_t * Abc_NtkDarExtWin( Abc_Ntk_t * pNtk, int nObjId, int nDist, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nObjId   = -1;
    nDist    =  5;
    fVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NDvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nObjId = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nObjId <= 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nDist = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDist <= 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for structrally hashed networks.\n" );
        return 1;
    }

    if ( argc != globalUtilOptind )
    {
        Abc_Print( -1, "Not enough command-line arguments.\n" );
        return 1;
    }
    // modify the current network
    pNtkRes = Abc_NtkDarExtWin( pNtk, nObjId, nDist, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Extracting sequential window has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: extwin [-ND <num>] [-vh]\n" );
    Abc_Print( -2, "\t         extracts sequential window from the AIG\n" );
    Abc_Print( -2, "\t-N num : the ID of the object to use as the center [default = %d]\n", nObjId );
    Abc_Print( -2, "\t-D num : the \"radius\" of the window [default = %d]\n", nDist );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandInsWin( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtkRes, * pNtk, * pNtkCare;
    int c;
    int nObjId;
    int nDist;
    int fVerbose;

    extern Abc_Ntk_t * Abc_NtkDarInsWin( Abc_Ntk_t * pNtk, Abc_Ntk_t * pWnd, int nObjId, int nDist, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nObjId   = -1;
    nDist    =  5;
    fVerbose =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NDvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nObjId = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nObjId <= 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nDist = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDist <= 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Only works for structrally hashed networks.\n" );
        return 1;
    }

    if ( argc != globalUtilOptind + 1 )
    {
        Abc_Print( -1, "Not enough command-line arguments.\n" );
        return 1;
    }
    pNtkCare = Io_Read( argv[globalUtilOptind], Io_ReadFileType(argv[globalUtilOptind]), 1 );
    if ( pNtkCare == NULL )
    {
        Abc_Print( -1, "Reading care network has failed.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtkCare) )
    {
        Abc_Ntk_t * pNtkTemp;
        pNtkCare = Abc_NtkStrash( pNtkTemp = pNtkCare, 0, 1, 0 );
        Abc_NtkDelete( pNtkTemp );
    }
    // modify the current network
    pNtkRes = Abc_NtkDarInsWin( pNtk, pNtkCare, nObjId, nDist, fVerbose );
    Abc_NtkDelete( pNtkCare );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Inserting sequential window has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: inswin [-ND <num>] [-vh] <file>\n" );
    Abc_Print( -2, "\t         inserts sequential window into the AIG\n" );
    Abc_Print( -2, "\t-N num : the ID of the object to use as the center [default = %d]\n", nObjId );
    Abc_Print( -2, "\t-D num : the \"radius\" of the window [default = %d]\n", nDist );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tfile   : file with the AIG to be inserted\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPermute( Abc_Frame_t * pAbc, int argc, char ** argv )
{   
    Abc_Ntk_t * pNtk = pAbc->pNtkCur, * pNtkRes = NULL;
    int fInputs = 1;
    int fOutputs = 1;
    int c, fFlops = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "iofh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'i':
            fInputs ^= 1;
            break;
        case 'o':
            fOutputs ^= 1;
            break;
        case 'f':
            fFlops ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDup( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command \"permute\" has failed.\n" );
        return 1;
    }
    Abc_NtkPermute( pNtkRes, fInputs, fOutputs, fFlops );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: permute [-iofh]\n" );
    Abc_Print( -2, "\t        performs random permutation of inputs/outputs/flops\n" );
    Abc_Print( -2, "\t-i    : toggle permuting primary inputs [default = %s]\n", fInputs? "yes": "no" );
    Abc_Print( -2, "\t-o    : toggle permuting primary outputs [default = %s]\n", fOutputs? "yes": "no" );
    Abc_Print( -2, "\t-f    : toggle permuting flip-flops [default = %s]\n", fFlops? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandUnpermute( Abc_Frame_t * pAbc, int argc, char ** argv )
{   
    Abc_Ntk_t * pNtk = pAbc->pNtkCur, * pNtkRes = NULL;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    pNtkRes = Abc_NtkDup( pNtk );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Command \"unpermute\" has failed.\n" );
        return 1;
    }
    Abc_NtkUnpermute( pNtkRes );
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: unpermute [-h]\n" );
    Abc_Print( -2, "\t        restores inputs/outputs/flops before the last permutation\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[16];
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fSat;
    int fVerbose;
    int nSeconds;
    int nPartSize;
    int nConfLimit;
    int nInsLimit;
    int fPartition;
    int fIgnoreNames;

    extern void Abc_NtkCecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConfLimit, int nInsLimit );
    extern void Abc_NtkCecFraig( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int fVerbose );
    extern void Abc_NtkCecFraigPart( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int nPartSize, int fVerbose );
    extern void Abc_NtkCecFraigPartAuto( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fSat     =  0;
    fVerbose =  0;
    nSeconds = 20;
    nPartSize  = 0;
    nConfLimit = 10000;   
    nInsLimit  = 0;
    fPartition = 0;
    fIgnoreNames = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TCIPpsnvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nSeconds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSeconds < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nInsLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInsLimit < 0 ) 
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPartSize < 0 ) 
                goto usage;
            break;
        case 'p':
            fPartition ^= 1;
            break;
        case 's':
            fSat ^= 1;
            break;
        case 'n':
            fIgnoreNames ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
        return 1;
    
    if ( fIgnoreNames )
    {
        Abc_NtkShortNames( pNtk1 );
        Abc_NtkShortNames( pNtk2 );
    }

    // perform equivalence checking
    if ( fPartition )
        Abc_NtkCecFraigPartAuto( pNtk1, pNtk2, nSeconds, fVerbose );
    else if ( nPartSize )
        Abc_NtkCecFraigPart( pNtk1, pNtk2, nSeconds, nPartSize, fVerbose );
    else if ( fSat )
        Abc_NtkCecSat( pNtk1, pNtk2, nConfLimit, nInsLimit );
    else
        Abc_NtkCecFraig( pNtk1, pNtk2, nSeconds, fVerbose );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    if ( nPartSize == 0 )
        strcpy( Buffer, "unused" );
    else
        sprintf( Buffer, "%d", nPartSize );
    Abc_Print( -2, "usage: cec [-T num] [-C num] [-I num] [-P num] [-psnvh] <file1> <file2>\n" );
    Abc_Print( -2, "\t         performs combinational equivalence checking\n" );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", nSeconds );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    Abc_Print( -2, "\t-I num : limit on the number of clause inspections [default = %d]\n", nInsLimit );
    Abc_Print( -2, "\t-P num : partition size for multi-output networks [default = %s]\n", Buffer );
    Abc_Print( -2, "\t-p     : toggle automatic partitioning [default = %s]\n", fPartition? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle \"SAT only\" and \"FRAIG + SAT\" [default = %s]\n", fSat? "SAT only": "FRAIG + SAT" );
    Abc_Print( -2, "\t-n     : toggle ignoring names when matching CIs/COs [default = %s]\n", fIgnoreNames? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tfile1  : (optional) the file with the first network\n");
    Abc_Print( -2, "\tfile2  : (optional) the file with the second network\n");
    Abc_Print( -2, "\t         if no files are given, uses the current network and its spec\n");
    Abc_Print( -2, "\t         if one file is given, uses the current network and the file\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDCec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fSat;
    int fVerbose;
    int nSeconds;
    int nConfLimit;
    int nInsLimit;
    int fPartition;
    int fMiter;

    extern int Abc_NtkDSat( Abc_Ntk_t * pNtk, ABC_INT64_T nConfLimit, ABC_INT64_T nInsLimit, int fAlignPol, int fAndOuts, int fNewSolver, int fVerbose );
    extern int Abc_NtkDarCec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConfLimit, int fPartition, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fSat     =  0;
    fVerbose =  0;
    nSeconds = 20;
    nConfLimit = 10000;   
    nInsLimit  = 0;
    fPartition = 0;
    fMiter     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TCIpmsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nSeconds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSeconds < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nInsLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInsLimit < 0 ) 
                goto usage;
            break;
        case 'p':
            fPartition ^= 1;
            break;
        case 'm':
            fMiter ^= 1;
            break;
        case 's':
            fSat ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( fMiter )
    {
        if ( pNtk == NULL )
        {
            Abc_Print( -1, "Empty network.\n" );
            return 1;
        }
        if ( Abc_NtkIsStrash(pNtk) )
        {
            pNtk1 = pNtk;
            fDelete1 = 0;
        }
        else
        {
            pNtk1 = Abc_NtkStrash( pNtk, 0, 1, 0 );
            fDelete1 = 1;
        }
        pNtk2 = NULL;
        fDelete2 = 0;
    }
    else
    {
        if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
            return 1;
    }

    if ( Abc_NtkLatchNum(pNtk1) || Abc_NtkLatchNum(pNtk2) )
    {
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "Currently this command only works for networks without latches. Run \"comb\".\n" );
        return 1;
    }

    // perform equivalence checking
    if ( fSat && fMiter )
        Abc_NtkDSat( pNtk1, nConfLimit, nInsLimit, 0, 0, 0, fVerbose );
    else
        Abc_NtkDarCec( pNtk1, pNtk2, nConfLimit, fPartition, fVerbose );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    Abc_Print( -2, "usage: dcec [-T num] [-C num] [-I num] [-mpsvh] <file1> <file2>\n" );
    Abc_Print( -2, "\t         performs combinational equivalence checking\n" );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", nSeconds );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    Abc_Print( -2, "\t-I num : limit on the number of clause inspections [default = %d]\n", nInsLimit );
    Abc_Print( -2, "\t-m     : toggle working on two networks or a miter [default = %s]\n", fMiter? "miter": "two networks" );
    Abc_Print( -2, "\t-p     : toggle automatic partitioning [default = %s]\n", fPartition? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle \"SAT only\" (miter) or \"FRAIG + SAT\" [default = %s]\n", fSat? "SAT only": "FRAIG + SAT" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tfile1  : (optional) the file with the first network\n");
    Abc_Print( -2, "\tfile2  : (optional) the file with the second network\n");
    Abc_Print( -2, "\t         if no files are given, uses the current network and its spec\n");
    Abc_Print( -2, "\t         if one file is given, uses the current network and the file\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fRetime;
    int fSat;
    int fVerbose;
    int nFrames;
    int nSeconds;
    int nConfLimit;
    int nInsLimit;

    extern void Abc_NtkSecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConfLimit, int nInsLimit, int nFrames );
    extern int Abc_NtkSecFraig( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int nFrames, int fVerbose );

    Abc_Print( 0, "This command is no longer used.\n" );
    return 0;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fRetime  =  0; // verification after retiming
    fSat     =  0;
    fVerbose =  0;
    nFrames  =  5;
    nSeconds = 20;
    nConfLimit = 10000;   
    nInsLimit  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FTCIsrvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames <= 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nSeconds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSeconds < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nInsLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInsLimit < 0 ) 
                goto usage;
            break;
        case 'r':
            fRetime ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 's':
            fSat ^= 1;
            break;
        default:
            goto usage;
        }
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
        return 1;

    if ( Abc_NtkLatchNum(pNtk1) == 0 || Abc_NtkLatchNum(pNtk2) == 0 )
    {
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "The network has no latches. Used combinational command \"cec\".\n" );
        return 0;
    }

    // perform equivalence checking
    if ( fSat )
        Abc_NtkSecSat( pNtk1, pNtk2, nConfLimit, nInsLimit, nFrames );
    else
        Abc_NtkSecFraig( pNtk1, pNtk2, nSeconds, nFrames, fVerbose );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    Abc_Print( -2, "usage: sec [-F num] [-T num] [-C num] [-I num] [-srvh] <file1> <file2>\n" );
    Abc_Print( -2, "\t         performs bounded sequential equivalence checking\n" );
    Abc_Print( -2, "\t         (there is also an unbounded SEC commands, \"dsec\" and \"dprove\")\n" );
    Abc_Print( -2, "\t-s     : toggle \"SAT only\" and \"FRAIG + SAT\" [default = %s]\n", fSat? "SAT only": "FRAIG + SAT" );
    Abc_Print( -2, "\t-r     : toggles retiming verification [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t-F num : the number of time frames to use [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", nSeconds );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    Abc_Print( -2, "\t-I num : limit on the number of inspections [default = %d]\n", nInsLimit );
    Abc_Print( -2, "\tfile1  : (optional) the file with the first network\n");
    Abc_Print( -2, "\tfile2  : (optional) the file with the second network\n");
    Abc_Print( -2, "\t         if no files are given, uses the current network and its spec\n");
    Abc_Print( -2, "\t         if one file is given, uses the current network and the file\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDSec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Fra_Sec_t SecPar, * pSecPar = &SecPar;
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fIgnoreNames;

    extern void Fra_SecSetDefaultParams( Fra_Sec_t * p );
    extern int Abc_NtkDarSec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, Fra_Sec_t * p );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Fra_SecSetDefaultParams( pSecPar );
    pSecPar->TimeLimit = 0;
    fIgnoreNames = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FTarmfnwvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nFramesMax < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->TimeLimit < 0 ) 
                goto usage;
            break;
        case 'a':
            pSecPar->fPhaseAbstract ^= 1;
            break;
        case 'r':
            pSecPar->fRetimeFirst ^= 1;
            break;
        case 'm':
            pSecPar->fRetimeRegs ^= 1;
            break;
        case 'f':
            pSecPar->fFraiging ^= 1;
            break;
        case 'n':
            fIgnoreNames ^= 1;
            break;
        case 'w':
            pSecPar->fVeryVerbose ^= 1;
            break;
        case 'v':
            pSecPar->fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
        return 1;
    if ( Abc_NtkLatchNum(pNtk1) == 0 || Abc_NtkLatchNum(pNtk2) == 0 )
    {
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
        Abc_Print( -1, "The network has no latches. Used combinational command \"cec\".\n" );
        return 0;
    }
    
    if ( fIgnoreNames )
    {
        Abc_NtkShortNames( pNtk1 );
        Abc_NtkShortNames( pNtk2 );
    }

    // perform verification
    Abc_NtkDarSec( pNtk1, pNtk2, pSecPar );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return 0;

usage:
    Abc_Print( -2, "usage: dsec [-F num] [-T num] [-armfnwvh] <file1> <file2>\n" );
    Abc_Print( -2, "\t         performs inductive sequential equivalence checking\n" );
    Abc_Print( -2, "\t-F num : the limit on the depth of induction [default = %d]\n", pSecPar->nFramesMax );
    Abc_Print( -2, "\t-T num : the approximate runtime limit (in seconds) [default = %d]\n", pSecPar->TimeLimit );
    Abc_Print( -2, "\t-a     : toggles the use of phase abstraction [default = %s]\n", pSecPar->fPhaseAbstract? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggles forward retiming at the beginning [default = %s]\n", pSecPar->fRetimeFirst? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggles min-register retiming [default = %s]\n", pSecPar->fRetimeRegs? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggles the internal use of fraiging [default = %s]\n", pSecPar->fFraiging? "yes": "no" );
    Abc_Print( -2, "\t-n     : toggle ignoring names when matching PIs/POs [default = %s]\n", fIgnoreNames? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", pSecPar->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggles additional verbose output [default = %s]\n", pSecPar->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\tfile1  : (optional) the file with the first network\n");
    Abc_Print( -2, "\tfile2  : (optional) the file with the second network\n");
    Abc_Print( -2, "\t         if no files are given, uses the current network and its spec\n");
    Abc_Print( -2, "\t         if one file is given, uses the current network and the file\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDProve( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Fra_Sec_t SecPar, * pSecPar = &SecPar;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    char * pLogFileName = NULL;
    int nBmcFramesMax = 20;
    int nBmcConfMax = 2000;

    extern void Fra_SecSetDefaultParams( Fra_Sec_t * p );
    extern int Abc_NtkDarProve( Abc_Ntk_t * pNtk, Fra_Sec_t * pSecPar, int nBmcFramesMax, int nBmcConfMax );
    // set defaults
    Fra_SecSetDefaultParams( pSecPar );
//    pSecPar->TimeLimit = 300;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cbAEFCGDVBRTLarmfijkoupwvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            pSecPar->fTryComb ^= 1;
            break;
        case 'b':
            pSecPar->fTryBmc ^= 1;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            nBmcFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBmcFramesMax < 0 ) 
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by an integer.\n" );
                goto usage;
            }
            nBmcConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBmcConfMax < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nFramesMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nBTLimit < 0 ) 
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nBTLimitGlobal = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nBTLimitGlobal < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nBTLimitInter = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nBTLimitInter < 0 ) 
                goto usage;
            break;
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nBddVarsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nBddVarsMax < 0 ) 
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nBddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nBddMax < 0 ) 
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nBddIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nBddIterMax < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pSecPar->nPdrTimeout = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pSecPar->nPdrTimeout < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'a':
            pSecPar->fPhaseAbstract ^= 1;
            break;
        case 'r':
            pSecPar->fRetimeFirst ^= 1;
            break;
        case 'm':
            pSecPar->fRetimeRegs ^= 1;
            break;
        case 'f':
            pSecPar->fFraiging ^= 1;
            break;
        case 'i':
            pSecPar->fInduction ^= 1;
            break;
        case 'j':
            pSecPar->fInterpolation ^= 1;
            break;
        case 'k':
            pSecPar->fInterSeparate ^= 1;
            break;
        case 'o':
            pSecPar->fReorderImage ^= 1;
            break;
        case 'u':
            pSecPar->fReadUnsolved ^= 1;
            break;
        case 'p':
            pSecPar->fUsePdr ^= 1;
            break;
        case 'w':
            pSecPar->fVeryVerbose ^= 1;
            break;
        case 'v':
            pSecPar->fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
        return 0;
    }

    // perform verification
    pAbc->Status = Abc_NtkDarProve( pNtk, pSecPar, nBmcFramesMax, nBmcConfMax );
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "dprove" );

    // read back the resulting unsolved reduced sequential miter
    if ( pSecPar->fReadUnsolved && pSecPar->nSMnumber >= 0 )
    {
        char FileName[100];
        sprintf( FileName, "sm%02d.aig", pSecPar->nSMnumber );
        pNtk = Io_Read( FileName, Io_ReadFileType(FileName), 1 );
        if ( pNtk == NULL )
            Abc_Print( -1, "Cannot read back unsolved reduced sequential miter \"%s\",\n", FileName );
        else
            Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: dprove [-AEFCGDVBRT num] [-L file] [-cbarmfijoupvwh]\n" );
    Abc_Print( -2, "\t         performs SEC on the sequential miter\n" );
    Abc_Print( -2, "\t-A num : the limit on the depth of BMC [default = %d]\n", nBmcFramesMax );
    Abc_Print( -2, "\t-E num : the conflict limit during BMC [default = %d]\n", nBmcConfMax );
    Abc_Print( -2, "\t-F num : the limit on the depth of induction [default = %d]\n", pSecPar->nFramesMax );
    Abc_Print( -2, "\t-C num : the conflict limit at a node during induction [default = %d]\n", pSecPar->nBTLimit );
    Abc_Print( -2, "\t-G num : the global conflict limit during induction [default = %d]\n", pSecPar->nBTLimitGlobal );
    Abc_Print( -2, "\t-D num : the conflict limit during interpolation [default = %d]\n", pSecPar->nBTLimitInter );
    Abc_Print( -2, "\t-V num : the flop count limit for BDD-based reachablity [default = %d]\n", pSecPar->nBddVarsMax );
    Abc_Print( -2, "\t-B num : the BDD size limit in BDD-based reachablity [default = %d]\n", pSecPar->nBddMax );
    Abc_Print( -2, "\t-R num : the max number of reachability iterations [default = %d]\n", pSecPar->nBddIterMax );
    Abc_Print( -2, "\t-T num : the timeout for property directed reachability [default = %d]\n", pSecPar->nPdrTimeout );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-c     : toggles using CEC before attempting SEC [default = %s]\n", pSecPar->fTryComb? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggles using BMC before attempting SEC [default = %s]\n", pSecPar->fTryBmc? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggles the use of phase abstraction [default = %s]\n", pSecPar->fPhaseAbstract? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggles forward retiming at the beginning [default = %s]\n", pSecPar->fRetimeFirst? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggles min-register retiming [default = %s]\n", pSecPar->fRetimeRegs? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggles the internal use of fraiging [default = %s]\n", pSecPar->fFraiging? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggles the use of induction [default = %s]\n", pSecPar->fInduction? "yes": "no" );
    Abc_Print( -2, "\t-j     : toggles the use of interpolation [default = %s]\n", pSecPar->fInterpolation? "yes": "no" );
    Abc_Print( -2, "\t-k     : toggles applying interpolation to each output [default = %s]\n", pSecPar->fInterSeparate? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggles using BDD variable reordering during image computation [default = %s]\n", pSecPar->fReorderImage? "yes": "no" );
    Abc_Print( -2, "\t-u     : toggles reading back unsolved reduced sequential miter [default = %s]\n", pSecPar->fReadUnsolved? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggles trying property directed reachability in the end [default = %s]\n", pSecPar->fUsePdr? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", pSecPar->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggles additional verbose output [default = %s]\n", pSecPar->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
} 


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDProve2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int nConfLast;
    int fSeparate;
    int fVeryVerbose;
    int fVerbose;
    int c;

//    extern int Abc_NtkDProve2( Abc_Ntk_t * pNtk, int nConfLast, int fSeparate, int fVeryVerbose, int fVerbose );
    // set defaults
    nConfLast    = 75000;
    fSeparate    = 0;
    fVeryVerbose = 0;
    fVerbose     = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ckwvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLast = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLast < 0 ) 
                goto usage;
            break;
        case 'k':
            fSeparate ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "This command works only for sequential networks.\n" );
        return 0;
    }
    // perform verification
//    Abc_NtkDProve2( pNtk, nConfLast, fSeparate, fVeryVerbose, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: dprove2 [-C num] [-kwvh]\n" );
    Abc_Print( -2, "\t         improved integrated solver of sequential miters\n" );
    Abc_Print( -2, "\t-C num : the conflict limit during final BMC [default = %d]\n", nConfLast );
    Abc_Print( -2, "\t-k     : toggles solving each output separately [default = %s]\n", fSeparate? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggles very verbose output [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbSec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int fMiter, nFrames, fVerbose, c;

    extern int Abc_NtkDarAbSec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nFrames, int fVerbose );
 
    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fMiter   = 1;
    nFrames  = 2;
    fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'm': 
            fMiter ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }

    if ( fMiter ) 
    {
//        pNtk = Io_Read( argv[globalUtilOptind], Io_ReadFileType(argv[globalUtilOptind]), 1 );
        if ( argc == globalUtilOptind + 1 )
        {
            Abc_Print( -1, "The miter cannot be given on the command line. Use \"read\".\n" );
            return 0;
        }
        if ( !Abc_NtkIsStrash(pNtk) )
        {
            Abc_Print( -1, "The miter should be structurally hashed. Use \"st\"\n" );
            return 0;
        }
        if ( Abc_NtkDarAbSec( pNtk, NULL, nFrames, fVerbose ) == 1 )
            pAbc->Status = 1;
        else
            pAbc->Status = -1;
    }
    else 
    {
        pArgvNew = argv + globalUtilOptind;
        nArgcNew = argc - globalUtilOptind;
        if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
            return 1;
        if ( Abc_NtkLatchNum(pNtk1) == 0 || Abc_NtkLatchNum(pNtk2) == 0 )
        {
            if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
            if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
            Abc_Print( -1, "The network has no latches. Used combinational command \"cec\".\n" );
            return 0;
        }
        // perform verification
        if ( Abc_NtkDarAbSec( pNtk1, pNtk2, nFrames, fVerbose ) == 1 )
            pAbc->Status = 1;
        else
            pAbc->Status = -1;
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: absec [-F num] [-mv] <file1> <file2>\n" );
    Abc_Print( -2, "\t         performs SEC by applying CEC to several timeframes\n" );
    Abc_Print( -2, "\t-F num : the total number of timeframes to use [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-m     : toggles miter vs. two networks [default = %s]\n", fMiter? "miter": "two networks" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\tfile1  : (optional) the file with the first network\n");
    Abc_Print( -2, "\tfile2  : (optional) the file with the second network\n");
    Abc_Print( -2, "\t         if no files are given, uses the current network and its spec\n");
    Abc_Print( -2, "\t         if one file is given, uses the current network and the file\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSimSec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Ssw_Pars_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew, c;
    int fMiter;

    extern int Abc_NtkDarSimSec( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, Ssw_Pars_t * pPars );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fMiter = 1;
    Ssw_ManSetDefaultParams( pPars );
    pPars->fPartSigCorr = 1;
    pPars->fVerbose     = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FDcymvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesK = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesK < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIsleDist = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIsleDist < 0 ) 
                goto usage;
            break;
        case 'm':
            fMiter ^= 1;
            break;
        case 'c':
            pPars->fPartSigCorr ^= 1;
            break;
        case 'y':
            pPars->fDumpSRInit ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }

    if ( fMiter )
    {
//        Abc_Ntk_t * pNtkA, * pNtkB;
        if ( !Abc_NtkIsStrash(pNtk) )
        {
            Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
            return 0;
        }
        Abc_NtkDarSimSec( pNtk, NULL, pPars );
/*
        pNtkA = Abc_NtkDup( pNtk );
        pNtkB = Abc_NtkDup( pNtk );
        Abc_NtkDarSimSec( pNtkA, pNtkB, pPars );
        Abc_NtkDelete( pNtkA );
        Abc_NtkDelete( pNtkB );
*/
    }
    else
    {
        pArgvNew = argv + globalUtilOptind;
        nArgcNew = argc - globalUtilOptind;
        if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
            return 1;
        if ( Abc_NtkLatchNum(pNtk1) == 0 || Abc_NtkLatchNum(pNtk2) == 0 )
        {
            if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
            if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
            Abc_Print( -1, "The network has no latches. Used combinational command \"cec\".\n" );
            return 0;
        }
        // perform verification
        Abc_NtkDarSimSec( pNtk1, pNtk2, pPars );
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: simsec [-FD num] [-mcyv] <file1> <file2>\n" );
    Abc_Print( -2, "\t         performs SEC using structural similarity\n" );
    Abc_Print( -2, "\t-F num : the limit on the depth of induction [default = %d]\n", pPars->nFramesK );
    Abc_Print( -2, "\t-D num : the distance for extending islands [default = %d]\n", pPars->nIsleDist );
    Abc_Print( -2, "\t-m     : toggles miter vs. two networks [default = %s]\n", fMiter? "miter": "two networks" );
    Abc_Print( -2, "\t-c     : uses partial vs. full signal correspondence [default = %s]\n", pPars->fPartSigCorr? "partial": "full" );
    Abc_Print( -2, "\t-y     : dumps speculatively reduced miter of the classes [default = %s]\n", pPars->fDumpSRInit? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\tfile1  : (optional) the file with the first network\n");
    Abc_Print( -2, "\tfile2  : (optional) the file with the second network\n");
    Abc_Print( -2, "\t         if no files are given, uses the current network and its spec\n");
    Abc_Print( -2, "\t         if one file is given, uses the current network and the file\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandMatch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2, * pNtkRes;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew, c;
    int fMiter;
    int nDist;
    int fVerbose;

    extern Abc_Ntk_t * Abc_NtkDarMatch( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nDist, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fMiter = 0;
    nDist = 0;
    fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Dmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nDist = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDist < 0 ) 
                goto usage;
            break;
        case 'm':
            fMiter ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }

    if ( fMiter )
    {
//        Abc_Ntk_t * pNtkA, * pNtkB;
        if ( !Abc_NtkIsStrash(pNtk) )
        {
            Abc_Print( -1, "This command works only for structrally hashed networks. Run \"st\".\n" );
            return 0;
        }
        pNtkRes = Abc_NtkDarMatch( pNtk, NULL, nDist, fVerbose );
/*
        pNtkA = Abc_NtkDup( pNtk );
        pNtkB = Abc_NtkDup( pNtk );
        Abc_NtkDarSimSec( pNtkA, pNtkB, pPars );
        Abc_NtkDelete( pNtkA );
        Abc_NtkDelete( pNtkB );
*/
    }
    else
    {
        pArgvNew = argv + globalUtilOptind;
        nArgcNew = argc - globalUtilOptind;
        if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
            return 1;
        if ( Abc_NtkLatchNum(pNtk1) == 0 || Abc_NtkLatchNum(pNtk2) == 0 )
        {
            if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
            if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
            Abc_Print( -1, "The network has no latches. Used combinational command \"cec\".\n" );
            return 0;
        }
        // perform verification
        pNtkRes = Abc_NtkDarMatch( pNtk1, pNtk2, nDist, fVerbose );
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    }
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Matching has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: match [-D num] [-mv] <file1> <file2>\n" );
    Abc_Print( -2, "\t         detects structural similarity using simulation\n" );
    Abc_Print( -2, "\t         replaces the current network by the miter of differences\n" );
    Abc_Print( -2, "\t-D num : the distance for extending differences [default = %d]\n", nDist );
    Abc_Print( -2, "\t-m     : toggles miter vs. two networks [default = %s]\n", fMiter? "miter": "two networks" );
    Abc_Print( -2, "\t-v     : toggles verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\tfile1  : (optional) the file with the first network\n");
    Abc_Print( -2, "\tfile2  : (optional) the file with the second network\n");
    Abc_Print( -2, "\t         if no files are given, uses the current network and its spec\n");
    Abc_Print( -2, "\t         if one file is given, uses the current network and the file\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int RetValue;
    int fVerbose;
    int nConfLimit;
    int nInsLimit;
    int clk;
    // set defaults
    fVerbose   = 0;
    nConfLimit = 100000;   
    nInsLimit  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CIvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nInsLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInsLimit < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Currently can only solve the miter for combinational circuits.\n" );
        return 0;
    } 

    clk = clock();
    if ( Abc_NtkIsStrash(pNtk) )
    {
        RetValue = Abc_NtkMiterSat( pNtk, (ABC_INT64_T)nConfLimit, (ABC_INT64_T)nInsLimit, fVerbose, NULL, NULL );
    }
    else
    {
        assert( Abc_NtkIsLogic(pNtk) );
        Abc_NtkToBdd( pNtk );
        RetValue = Abc_NtkMiterSat( pNtk, (ABC_INT64_T)nConfLimit, (ABC_INT64_T)nInsLimit, fVerbose, NULL, NULL );
    }

    // verify that the pattern is correct
    if ( RetValue == 0 && Abc_NtkPoNum(pNtk) == 1 )
    {
        //int i;
        //Abc_Obj_t * pObj;
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pNtk->pModel );
        if ( pSimInfo[0] != 1 )
            Abc_Print( 1, "ERROR in Abc_NtkMiterSat(): Generated counter example is invalid.\n" );
        ABC_FREE( pSimInfo );
        /*
        // print model
        Abc_NtkForEachPi( pNtk, pObj, i )
        {
            Abc_Print( -1, "%d", (int)(pNtk->pModel[i] > 0) );
            if ( i == 70 )
                break;
        }
        Abc_Print( -1, "\n" );
        */
    }
    pAbc->Status = RetValue;
    if ( RetValue == -1 )
        Abc_Print( 1, "UNDECIDED      " );
    else if ( RetValue == 0 )
        Abc_Print( 1, "SATISFIABLE    " );
    else
        Abc_Print( 1, "UNSATISFIABLE  " );
    //Abc_Print( -1, "\n" );
    Abc_PrintTime( 1, "Time", clock() - clk );
    return 0;

usage:
    Abc_Print( -2, "usage: sat [-C num] [-I num] [-vh]\n" );
    Abc_Print( -2, "\t         solves the combinational miter using SAT solver MiniSat-1.14\n" );
    Abc_Print( -2, "\t         derives CNF from the current network and leave it unchanged\n" );
    Abc_Print( -2, "\t         (there is also a newer SAT solving command \"dsat\")\n" );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    Abc_Print( -2, "\t-I num : limit on the number of inspections [default = %d]\n", nInsLimit );
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int RetValue;
    int fAlignPol;
    int fAndOuts;
    int fNewSolver;
    int fVerbose;
    int nConfLimit;
    int nInsLimit;
    int clk;

    extern int Abc_NtkDSat( Abc_Ntk_t * pNtk, ABC_INT64_T nConfLimit, ABC_INT64_T nInsLimit, int fAlignPol, int fAndOuts, int fNewSolver, int fVerbose );
    // set defaults
    fAlignPol  = 0;
    fAndOuts   = 0;
    fNewSolver = 0;
    fVerbose   = 0;
    nConfLimit = 100000;   
    nInsLimit  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CIpanvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nInsLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInsLimit < 0 ) 
                goto usage;
            break;
        case 'p':
            fAlignPol ^= 1;
            break;
        case 'a':
            fAndOuts ^= 1;
            break;
        case 'n':
            fNewSolver ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Currently can only solve the miter for combinational circuits.\n" );
        return 0;
    } 
/*
    if ( Abc_NtkPoNum(pNtk) != 1 )
    {
        Abc_Print( -1, "Currently expects a single-output miter.\n" );
        return 0;
    } 
*/
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }

    clk = clock();
    RetValue = Abc_NtkDSat( pNtk, (ABC_INT64_T)nConfLimit, (ABC_INT64_T)nInsLimit, fAlignPol, fAndOuts, fNewSolver, fVerbose );
    // verify that the pattern is correct
    if ( RetValue == 0 && Abc_NtkPoNum(pNtk) == 1 )
    {
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pNtk->pModel );
        if ( pSimInfo[0] != 1 )
            Abc_Print( 1, "ERROR in Abc_NtkMiterSat(): Generated counter example is invalid.\n" );
        ABC_FREE( pSimInfo );
        pAbc->pCex = Abc_CexCreate( 0, Abc_NtkPiNum(pNtk), pNtk->pModel, 0, 0, 0 );
    }
    pAbc->Status = RetValue;
    if ( RetValue == -1 )
        Abc_Print( 1, "UNDECIDED      " );
    else if ( RetValue == 0 )
        Abc_Print( 1, "SATISFIABLE    " );
    else
        Abc_Print( 1, "UNSATISFIABLE  " );
    //Abc_Print( -1, "\n" );
    Abc_PrintTime( 1, "Time", clock() - clk );
    return 0;

usage:
    Abc_Print( -2, "usage: dsat [-C num] [-I num] [-panvh]\n" );
    Abc_Print( -2, "\t         solves the combinational miter using SAT solver MiniSat-1.14\n" );
    Abc_Print( -2, "\t         derives CNF from the current network and leave it unchanged\n" );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    Abc_Print( -2, "\t-I num : limit on the number of inspections [default = %d]\n", nInsLimit );
    Abc_Print( -2, "\t-p     : alighn polarity of SAT variables [default = %s]\n", fAlignPol? "yes": "no" );  
    Abc_Print( -2, "\t-a     : toggle ANDing/ORing of miter outputs [default = %s]\n", fAndOuts? "ANDing": "ORing" );  
    Abc_Print( -2, "\t-n     : toggle using new solver [default = %s]\n", fNewSolver? "yes": "no" );  
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int RetValue;
    int c, clk;
    int nAlgo;
    int nPartSize;
    int nConfPart;
    int nConfTotal;
    int fAlignPol;
    int fSynthesize;
    int fVerbose;

    extern int Abc_NtkPartitionedSat( Abc_Ntk_t * pNtk, int nAlgo, int nPartSize, int nConfPart, int nConfTotal, int fAlignPol, int fSynthesize, int fVerbose );
    // set defaults
    nAlgo       =        0;
    nPartSize   =    10000;
    nConfPart   =        0;
    nConfTotal  =  1000000;
    fAlignPol   =        1;
    fSynthesize =        0;
    fVerbose    =        1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "APCpsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by an integer.\n" );
                goto usage;
            }
            nAlgo = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nAlgo < 0 ) 
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPartSize < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfTotal = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfTotal < 0 ) 
                goto usage;
            break;
        case 'p':
            fAlignPol ^= 1;
            break;
        case 's':
            fSynthesize ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Currently can only solve the miter for combinational circuits.\n" );
        return 0;
    } 
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }

    clk = clock();
    RetValue = Abc_NtkPartitionedSat( pNtk, nAlgo, nPartSize, nConfPart, nConfTotal, fAlignPol, fSynthesize, fVerbose );
    // verify that the pattern is correct
    if ( RetValue == 0 && Abc_NtkPoNum(pNtk) == 1 )
    {
        //int i;
        //Abc_Obj_t * pObj;
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pNtk->pModel );
        if ( pSimInfo[0] != 1 )
            Abc_Print( 1, "ERROR in Abc_NtkMiterSat(): Generated counter example is invalid.\n" );
        ABC_FREE( pSimInfo );
        /*
        // print model
        Abc_NtkForEachPi( pNtk, pObj, i )
        {
            Abc_Print( -1, "%d", (int)(pNtk->pModel[i] > 0) );
            if ( i == 70 )
                break;
        }
        Abc_Print( -1, "\n" );
        */
    }

    if ( RetValue == -1 )
        Abc_Print( 1, "UNDECIDED      " );
    else if ( RetValue == 0 )
        Abc_Print( 1, "SATISFIABLE    " );
    else
        Abc_Print( 1, "UNSATISFIABLE  " );
    //Abc_Print( -1, "\n" );
    Abc_PrintTime( 1, "Time", clock() - clk );
    return 0;

usage:
    Abc_Print( -2, "usage: psat [-APC num] [-psvh]\n" );
    Abc_Print( -2, "\t         solves the combinational miter using partitioning\n" );
    Abc_Print( -2, "\t         (derives CNF from the current network and leave it unchanged)\n" );
    Abc_Print( -2, "\t         for multi-output miters, tries to prove that the AND of POs is always 0\n" );
    Abc_Print( -2, "\t         (if POs should be ORed instead of ANDed, use command \"orpos\")\n" );
    Abc_Print( -2, "\t-A num : partitioning algorithm [default = %d]\n", nAlgo );
    Abc_Print( -2, "\t         0 : no partitioning\n" );
    Abc_Print( -2, "\t         1 : partitioning by level\n" );
    Abc_Print( -2, "\t         2 : DFS post-order\n" );
    Abc_Print( -2, "\t         3 : DFS pre-order\n" );
    Abc_Print( -2, "\t         4 : bit-slicing\n" );
    Abc_Print( -2, "\t         partitions are ordered by level (high level first)\n" );
    Abc_Print( -2, "\t-P num : limit on the partition size [default = %d]\n", nPartSize );
    Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n", nConfTotal );
    Abc_Print( -2, "\t-p     : align polarity of SAT variables [default = %s]\n", fAlignPol? "yes": "no" );  
    Abc_Print( -2, "\t-s     : apply logic synthesis to each partition [default = %s]\n", fSynthesize? "yes": "no" );  
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandProve( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkTemp;
    Prove_Params_t Params, * pParams = &Params;
    int c, clk, RetValue;

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    Prove_ParamsSetDefault( pParams );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NCFGLIrfbvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nItersMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nItersMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nMiteringLimitStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nMiteringLimitStart < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nFraigingLimitStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nFraigingLimitStart < 0 ) 
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nFraigingLimitMulti = (float)atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nFraigingLimitMulti < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nMiteringLimitLast = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nMiteringLimitLast < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pParams->nTotalInspectLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pParams->nTotalInspectLimit < 0 ) 
                goto usage;
            break;
        case 'r':
            pParams->fUseRewriting ^= 1;
            break;
        case 'f':
            pParams->fUseFraiging ^= 1;
            break;
        case 'b':
            pParams->fUseBdds ^= 1;
            break;
        case 'v':
            pParams->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkLatchNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Currently can only solve the miter for combinational circuits.\n" );
        return 0;
    } 
    if ( Abc_NtkCoNum(pNtk) != 1 )
    {
        Abc_Print( -1, "Currently can only solve the miter with one output.\n" );
        return 0;
    } 
    clk = clock();

    if ( Abc_NtkIsStrash(pNtk) )
        pNtkTemp = Abc_NtkDup( pNtk );
    else
        pNtkTemp = Abc_NtkStrash( pNtk, 0, 0, 0 );

    RetValue = Abc_NtkMiterProve( &pNtkTemp, pParams );

    // verify that the pattern is correct
    if ( RetValue == 0 )
    {
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pNtk, pNtkTemp->pModel );
        if ( pSimInfo[0] != 1 )
            Abc_Print( 1, "ERROR in Abc_NtkMiterProve(): Generated counter-example is invalid.\n" );
        ABC_FREE( pSimInfo );
    }
    pAbc->Status = RetValue;
    if ( RetValue == -1 ) 
        Abc_Print( 1, "UNDECIDED      " );
    else if ( RetValue == 0 )
        Abc_Print( 1, "SATISFIABLE    " );
    else
        Abc_Print( 1, "UNSATISFIABLE  " );
    //Abc_Print( -1, "\n" );

    Abc_PrintTime( 1, "Time", clock() - clk );
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: prove [-NCFGLI num] [-rfbvh]\n" );
    Abc_Print( -2, "\t         solves combinational miter by rewriting, FRAIGing, and SAT\n" );
    Abc_Print( -2, "\t         replaces the current network by the cone modified by rewriting\n" );
    Abc_Print( -2, "\t         (there is also newer CEC command \"iprove\")\n" );
    Abc_Print( -2, "\t-N num : max number of iterations [default = %d]\n", pParams->nItersMax );
    Abc_Print( -2, "\t-C num : max starting number of conflicts in mitering [default = %d]\n", pParams->nMiteringLimitStart );
    Abc_Print( -2, "\t-F num : max starting number of conflicts in fraiging [default = %d]\n", pParams->nFraigingLimitStart );
    Abc_Print( -2, "\t-G num : multiplicative coefficient for fraiging [default = %d]\n", (int)pParams->nFraigingLimitMulti );
    Abc_Print( -2, "\t-L num : max last-gasp number of conflicts in mitering [default = %d]\n", pParams->nMiteringLimitLast );
    Abc_Print( -2, "\t-I num : max number of clause inspections in all SAT calls [default = %d]\n", (int)pParams->nTotalInspectLimit );
    Abc_Print( -2, "\t-r     : toggle the use of rewriting [default = %s]\n", pParams->fUseRewriting? "yes": "no" );  
    Abc_Print( -2, "\t-f     : toggle the use of FRAIGing [default = %s]\n", pParams->fUseFraiging? "yes": "no" );  
    Abc_Print( -2, "\t-b     : toggle the use of BDDs [default = %s]\n", pParams->fUseBdds? "yes": "no" );  
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pParams->fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDebug( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    extern void Abc_NtkAutoDebug( Abc_Ntk_t * pNtk, int (*pFuncError) (Abc_Ntk_t *) );
    extern int Abc_NtkRetimeDebug( Abc_Ntk_t * pNtk );
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsLogic(pNtk) )
    {
        Abc_Print( -1, "This command is applicable to logic networks.\n" );
        return 1;
    }

    Abc_NtkAutoDebug( pNtk, Abc_NtkRetimeDebug );
    return 0;

usage:
    Abc_Print( -2, "usage: debug [-h]\n" );
    Abc_Print( -2, "\t        performs automated debugging of the given procedure\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects [] 

  SeeAlso     []

***********************************************************************/
int Abc_CommandBmc( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nFrames;
    int nSizeMax;
    int nBTLimit;
    int nBTLimitAll;
    int nNodeDelta;
    int fRewrite;
    int fNewAlgo;
    int nCofFanLit;
    int fVerbose;
    int iFrames;
    char * pLogFileName = NULL;

    extern int Abc_NtkDarBmc( Abc_Ntk_t * pNtk, int nStart, int nFrames, int nSizeMax, int nNodeDelta, int nTimeOut, int nBTLimit, int nBTLimitAll, int fRewrite, int fNewAlgo, int nCofFanLit, int fVerbose, int * piFrames );
    // set defaults
    nFrames     =       20;
    nSizeMax    =   100000;
    nBTLimit    =    10000;
    nBTLimitAll = 10000000;
    nNodeDelta  =     1000;
    fRewrite    =        0;
    fNewAlgo    =        1;
    nCofFanLit  =        0;
    fVerbose    =        0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FNCGDLrvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSizeMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBTLimit < 0 ) 
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            nBTLimitAll = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBTLimitAll < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodeDelta = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodeDelta < 0 ) 
                goto usage;
            break;
/*
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nCofFanLit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCofFanLit < 0 ) 
                goto usage;
            break;
*/
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'r':
            fRewrite ^= 1;
            break;
        case 'a':
            fNewAlgo ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    { 
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "Does not work for combinational networks.\n" );
        return 0;
    }
    pAbc->Status = Abc_NtkDarBmc( pNtk, 0, nFrames, nSizeMax, nNodeDelta, 0, nBTLimit, nBTLimitAll, fRewrite, fNewAlgo, nCofFanLit, fVerbose, &iFrames );
    pAbc->nFrames = iFrames;
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "bmc" );
    return 0;

usage:
    Abc_Print( -2, "usage: bmc [-FNC num] [-L file] [-rcvh]\n" );
    Abc_Print( -2, "\t         performs bounded model checking with static unrolling\n" );
    Abc_Print( -2, "\t-F num : the number of time frames [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-N num : the max number of nodes in the frames [default = %d]\n", nSizeMax );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nBTLimit );
//    Abc_Print( -2, "\t-L num : the limit on fanout count of resets/enables to cofactor [default = %d]\n", nCofFanLit );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-r     : toggle the use of rewriting [default = %s]\n", fRewrite? "yes": "no" );
//    Abc_Print( -2, "\t-a     : toggle SAT sweeping and SAT solving [default = %s]\n", fNewAlgo? "SAT solving": "SAT sweeping" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects [] 

  SeeAlso     []

***********************************************************************/
int Abc_CommandBmc2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int nStart;
    int nFrames;
    int nSizeMax;
    int nBTLimit;
    int nBTLimitAll;
    int nNodeDelta;
    int nTimeOut;
    int fRewrite;
    int fNewAlgo;
    int fVerbose;
    int iFrames;
    char * pLogFileName = NULL;

    extern int Abc_NtkDarBmc( Abc_Ntk_t * pNtk, int nStart, int nFrames, int nSizeMax, int nNodeDelta, int nTimeOut, int nBTLimit, int nBTLimitAll, int fRewrite, int fNewAlgo, int nCofFanLit, int fVerbose, int * piFrames );

    // set defaults
    nStart      =        0;
    nFrames     =     2000;
    nSizeMax    =   200000;
    nBTLimit    =     2000;
    nBTLimitAll =  2000000;
    nNodeDelta  =     2000;
    nTimeOut    =        0;
    fRewrite    =        0;
    fNewAlgo    =        0;
    fVerbose    =        0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SFNTCGDLrvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nStart < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nSizeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSizeMax < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeOut < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBTLimit < 0 ) 
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            nBTLimitAll = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBTLimitAll < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodeDelta = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodeDelta < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'r':
            fRewrite ^= 1;
            break;
        case 'a':
            fNewAlgo ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    { 
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "Does not work for combinational networks.\n" );
        return 0;
    }
    pAbc->Status = Abc_NtkDarBmc( pNtk, nStart, nFrames, nSizeMax, nNodeDelta, nTimeOut, nBTLimit, nBTLimitAll, fRewrite, fNewAlgo, 0, fVerbose, &iFrames );
    pAbc->nFrames = iFrames;
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "bmc2" );
    return 0;

usage:
//    Abc_Print( -2, "usage: bmc2 [-FNCGD num] [-ravh]\n" );
    Abc_Print( -2, "usage: bmc2 [-SFTCGD num] [-L file] [-vh]\n" );
    Abc_Print( -2, "\t         performs bounded model checking with dynamic unrolling\n" );
    Abc_Print( -2, "\t-S num : the starting time frame [default = %d]\n", nStart );
    Abc_Print( -2, "\t-F num : the max number of time frames [default = %d]\n", nFrames );
//    Abc_Print( -2, "\t-N num : the max number of nodes in the frames [default = %d]\n", nSizeMax );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", nTimeOut );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nBTLimit );
    Abc_Print( -2, "\t-G num : the max number of conflicts globally [default = %d]\n", nBTLimitAll );
    Abc_Print( -2, "\t-D num : the delta in the number of nodes [default = %d]\n", nNodeDelta );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
//    Abc_Print( -2, "\t-r     : toggle the use of rewriting [default = %s]\n", fRewrite? "yes": "no" );
//    Abc_Print( -2, "\t-a     : toggle SAT sweeping and SAT solving [default = %s]\n", fNewAlgo? "SAT solving": "SAT sweeping" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects [] 

  SeeAlso     []

***********************************************************************/
int Abc_CommandBmc3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkDarLatchSweep( Abc_Ntk_t * pNtk, int fLatchConst, int fLatchEqual, int fSaveNames, int fUseMvSweep, int nFramesSymb, int nFramesSatur, int fVerbose, int fVeryVerbose );
    extern int Abc_NtkDarBmc3( Abc_Ntk_t * pNtk, Saig_ParBmc_t * pPars );
    Saig_ParBmc_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtkRes, * pNtk = Abc_FrameReadNtk(pAbc);
    char * pLogFileName = NULL;
    int c;
    Saig_ParBmcSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SFTCDJILsdrvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nStart < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesMax < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTimeOut < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfLimit < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfLimitJump = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfLimitJump < 0 ) 
                goto usage;
            break;
        case 'J':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-J\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesJump = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesJump < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPisAbstract = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPisAbstract < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 's':
            pPars->fSolveAll ^= 1;
            break;
        case 'd':
            pPars->fDropSatOuts ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    { 
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "Does not work for combinational networks.\n" );
        return 0;
    }
    pAbc->Status = Abc_NtkDarBmc3( pNtk, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "bmc3" );
    if ( pPars->fSolveAll && pPars->fDropSatOuts )
    {
        if ( pNtk->vSeqModelVec == NULL )
            printf( "The array of counter-examples is not available.\n" );
        else if ( Vec_PtrSize(pNtk->vSeqModelVec) != Abc_NtkPoNum(pNtk) )
            printf( "The array size does not match the number of outputs.\n" );
        else
        {
            extern void Abc_NtkDropSatOutputs( Abc_Ntk_t * pNtk, Vec_Ptr_t * vCexes, int fVerbose );
            Abc_NtkDropSatOutputs( pNtk, pNtk->vSeqModelVec, pPars->fVerbose );
            pNtkRes = Abc_NtkDarLatchSweep( pNtk, 1, 1, 1, 0, -1, -1, 0, 0 );
            if ( pNtkRes == NULL )
            {
                Abc_Print( -1, "Removing SAT outputs has failed.\n" );
                return 1;
            }
            Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        }
    }
    if ( pNtk->vSeqModelVec )
        Abc_FrameReplaceCexVec( pAbc, &pNtk->vSeqModelVec );
    return 0;

usage:
    Abc_Print( -2, "usage: bmc3 [-SFTCDJI num] [-L file] [-sdvh]\n" );
    Abc_Print( -2, "\t         performs bounded model checking with dynamic unrolling\n" );
    Abc_Print( -2, "\t-S num : the starting time frame [default = %d]\n", pPars->nStart );
    Abc_Print( -2, "\t-F num : the max number of time frames [default = %d]\n", pPars->nFramesMax );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", pPars->nTimeOut );
    Abc_Print( -2, "\t-C num : max conflicts at an output [default = %d]\n", pPars->nConfLimit );
    Abc_Print( -2, "\t-D num : max conflicts after jumping (0 = infinity) [default = %d]\n", pPars->nConfLimitJump );
    Abc_Print( -2, "\t-J num : the number of timeframes to jump (0 = not used) [default = %d]\n", pPars->nFramesJump );
    Abc_Print( -2, "\t-I num : the number of PIs to abstract [default = %d]\n", pPars->nPisAbstract );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-s     : solve all outputs (do not stop when one is SAT) [default = %s]\n", pPars->fSolveAll? "yes": "no" );
    Abc_Print( -2, "\t-d     : drops (replaces by 0) satisfiable outputs [default = %s]\n", pPars->fDropSatOuts? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBmcInter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Inter_ManParams_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtkRes, * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    char * pLogFileName = NULL;

    extern int Abc_NtkDarBmcInter( Abc_Ntk_t * pNtk, Inter_ManParams_t * pPars, Abc_Ntk_t ** ppNtkRes );
    // set defaults
    Inter_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CFTKLrtpomcgbkdfvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBTLimit < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesMax < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSecLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSecLimit < 0 ) 
                goto usage;
            break;
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesK = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesK < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'r':
            pPars->fRewrite ^= 1;
            break;
        case 't':
            pPars->fTransLoop ^= 1;
            break;
        case 'p':
            pPars->fUsePudlak ^= 1;
            break;
        case 'o':
            pPars->fUseOther ^= 1;
            break;
        case 'm':
            pPars->fUseMiniSat ^= 1;
            break;
        case 'c':
            pPars->fCheckKstep ^= 1;
            break;
        case 'g':
            pPars->fUseBias ^= 1;
            break;
        case 'b':
            pPars->fUseBackward ^= 1;
            break;
        case 'k':
            pPars->fUseSeparate ^= 1;
            break;
        case 'd':
            pPars->fDropSatOuts ^= 1;
            break;
        case 'f':
            pPars->fDropInvar ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    { 
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    } 
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -1, "Does not work for combinational networks.\n" );
        return 0;
    }
    if ( Abc_NtkConstrNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Cannot run interpolation with constraints. Use \"fold\".\n" );
        return 0;
    }
    if ( Abc_NtkPoNum(pNtk)-Abc_NtkConstrNum(pNtk) != 1 )
    {
        if ( Abc_NtkConstrNum(pNtk) > 0 )
        {
            printf( "Cannot solve multiple-output miter with constraints.\n" );
            return 0;
        }
        if ( pPars->fUseSeparate )
        {
            Abc_Print( 0, "Each of %d outputs will be solved separately.\n", Abc_NtkPoNum(pNtk) );
            pAbc->Status = Abc_NtkDarBmcInter( pNtk, pPars, &pNtkRes );
            Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
            if ( pNtkRes == NULL )
            {
                Abc_Print( -1, "Generating resulting network has failed.\n" );
                return 0;
            }
            Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
        }
        else
        {
            Abc_Ntk_t * pNtkNew = Abc_NtkDup( pNtk );
            Abc_Print( 0, "All %d outputs will be ORed together.\n", Abc_NtkPoNum(pNtk) );
            if ( !Abc_NtkCombinePos( pNtkNew, 0 ) )
            {
                Abc_NtkDelete( pNtkNew );
                Abc_Print( -1, "ORing outputs has failed.\n" ); 
                return 0;
            }
            pAbc->Status = Abc_NtkDarBmcInter( pNtkNew, pPars, NULL );
            Abc_FrameReplaceCex( pAbc, &pNtkNew->pSeqModel );
            Abc_NtkDelete( pNtkNew );
        }
        pAbc->nFrames = -1;
    }
    else
    {
        pAbc->Status  = Abc_NtkDarBmcInter( pNtk, pPars, NULL );
        pAbc->nFrames = pPars->iFrameMax;
        Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
    }
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "int" );
    return 0;

usage:
    Abc_Print( -2, "usage: int [-CFTK num] [-L file] [-rtpomcgbkdfvh]\n" );
    Abc_Print( -2, "\t         uses interpolation to prove the property\n" );
    Abc_Print( -2, "\t-C num : the limit on conflicts for one SAT run [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-F num : the limit on number of frames to unroll [default = %d]\n", pPars->nFramesMax );
    Abc_Print( -2, "\t-T num : the limit on runtime per output in seconds [default = %d]\n", pPars->nSecLimit );
    Abc_Print( -2, "\t-K num : the number of steps in inductive checking [default = %d]\n", pPars->nFramesK );
    Abc_Print( -2, "\t         (K = 1 works in all cases; K > 1 works without -t and -b)\n" );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-r     : toggle rewriting of the unrolled timeframes [default = %s]\n", pPars->fRewrite? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle adding transition into the initial state [default = %s]\n", pPars->fTransLoop? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle using original Pudlak's interpolation procedure [default = %s]\n", pPars->fUsePudlak? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle using optimized Pudlak's interpolation procedure [default = %s]\n", pPars->fUseOther? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle using MiniSat-1.14p (now, Windows-only) [default = %s]\n", pPars->fUseMiniSat? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using inductive containment check [default = %s]\n", pPars->fCheckKstep? "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle using bias for global variables using SAT [default = %s]\n", pPars->fUseBias? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle using backward interpolation (works with -t) [default = %s]\n", pPars->fUseBackward? "yes": "no" );
    Abc_Print( -2, "\t-k     : toggle solving each output separately [default = %s]\n", pPars->fUseSeparate? "yes": "no" );
    Abc_Print( -2, "\t-d     : drops (replaces by 0) sat outputs (with -k is used) [default = %s]\n", pPars->fDropSatOuts? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle dumping inductive invariant into a file [default = %s]\n", pPars->fDropInvar? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandIndcut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int nFrames;
    int nPref;
    int nClauses;
    int nLutSize;
    int nLevels;
    int nCutsMax;
    int nBatches;
    int fStepUp;
    int fBmc;
    int fRegs;
    int fTarget;
    int fVerbose;
    int fVeryVerbose;
    int c;
    extern int Abc_NtkDarClau( Abc_Ntk_t * pNtk, int nFrames, int nPref, int nClauses, int nLutSize, int nLevels, int nCutsMax, int nBatches, int fStepUp, int fBmc, int fRegs, int fTarget, int fVerbose, int fVeryVerbose );
    // set defaults
    nFrames      =    1;
    nPref        =    0;
    nClauses     = 5000;
    nLutSize     =    4;
    nLevels      =    8;
    nCutsMax     =   16;
    nBatches     =    1;
    fStepUp      =    0;
    fBmc         =    1;
    fRegs        =    1;
    fTarget      =    1;
    fVerbose     =    0;
    fVeryVerbose =    0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FPCMLNBsbrtvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPref = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPref < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nClauses = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nClauses < 0 ) 
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by an integer.\n" );
                goto usage;
            }
            nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLutSize < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nLevels = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLevels < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCutsMax < 0 ) 
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            nBatches = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBatches < 0 ) 
                goto usage;
            break;
        case 's':
            fStepUp ^= 1;
            break;
        case 'b':
            fBmc ^= 1;
            break;
        case 'r':
            fRegs ^= 1;
            break;
        case 't':
            fTarget ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( nLutSize > 12 )
    {
        Abc_Print( -1, "The cut size should be not exceed 12.\n" );
        return 0;
    }
    Abc_NtkDarClau( pNtk, nFrames, nPref, nClauses, nLutSize, nLevels, nCutsMax, nBatches, fStepUp, fBmc, fRegs, fTarget, fVerbose, fVeryVerbose );
    return 0;
usage:
    Abc_Print( -2, "usage: indcut [-FPCMLNB num] [-sbrtvh]\n" );
    Abc_Print( -2, "\t         K-step induction strengthened with cut properties\n" );
    Abc_Print( -2, "\t-F num : number of time frames for induction (1=simple) [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-P num : number of time frames in the prefix (0=no prefix) [default = %d]\n", nPref );
    Abc_Print( -2, "\t-C num : the max number of clauses to use for strengthening [default = %d]\n", nClauses );
    Abc_Print( -2, "\t-M num : the cut size (2 <= M <= 12) [default = %d]\n", nLutSize );
    Abc_Print( -2, "\t-L num : the max number of levels for cut computation [default = %d]\n", nLevels );
    Abc_Print( -2, "\t-N num : the max number of cuts to compute at a node [default = %d]\n", nCutsMax );
    Abc_Print( -2, "\t-B num : the max number of invariant batches to try [default = %d]\n", nBatches );
    Abc_Print( -2, "\t-s     : toggle increment cut size in each batch [default = %s]\n", fStepUp? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle enabling BMC check [default = %s]\n", fBmc? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle enabling register clauses [default = %s]\n", fRegs? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle proving target / computing don't-cares [default = %s]\n", fTarget? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
//    Abc_Print( -2, "\t-w     : toggle printing very verbose information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandEnlarge( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int nFrames;
    int fVerbose;
    int c;
    extern Abc_Ntk_t * Abc_NtkDarEnlarge( Abc_Ntk_t * pNtk, int nFrames, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nFrames      = 5;
    fVerbose     = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 1 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }

    // modify the current network
    pNtkRes = Abc_NtkDarEnlarge( pNtk, nFrames, fVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Target enlargement has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;
usage:
    Abc_Print( -2, "usage: enlarge [-F <num>] [-vh]\n" );
    Abc_Print( -2, "\t           performs structural K-step target enlargement\n" );
    Abc_Print( -2, "\t-F <num> : the number of timeframes to unroll (<num> > 0) [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-v       : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTempor( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkDarTempor( Abc_Ntk_t * pNtk, int nFrames, int TimeOut, int nConfLimit, int fUseBmc, int fUseTransSigs, int fVerbose, int fVeryVerbose );
    Abc_Ntk_t * pNtkRes, * pNtk = Abc_FrameReadNtk(pAbc);
    int nFrames       =       0;
    int TimeOut       =     300;
    int nConfMax      =  100000;
    int fUseBmc       =       1;
    int fUseTransSigs =       0;
    int fVerbose      =       0;
    int fVeryVerbose  =       0;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FTCbsvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            TimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( TimeOut < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfMax < 0 ) 
                goto usage;
            break;
        case 'b':
            fUseBmc ^= 1;
            break;
        case 's':
            fUseTransSigs ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -2, "There is no current network.\n");
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -2, "The current network is combinational.\n");
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -2, "The current network is not an AIG (run \"strash\").\n");
        return 0;
    }
    // modify the current network
    pNtkRes = Abc_NtkDarTempor( pNtk, nFrames, TimeOut, nConfMax, fUseBmc, fUseTransSigs, fVerbose, fVeryVerbose );
    if ( pNtkRes == NULL )
    {
        Abc_Print( -1, "Temporal decomposition has failed.\n" );
        return 1;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;

usage:
    Abc_Print( -2, "usage: tempor [-FTC <num>] [-bsvwh]\n" );
    Abc_Print( -2, "\t           performs temporal decomposition\n" );
    Abc_Print( -2, "\t-F <num> : init logic timeframe count (0 = use leading length) [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-T <num> : runtime limit in seconds for BMC (0=unused) [default = %d]\n", TimeOut );
    Abc_Print( -2, "\t-C <num> : max number of SAT conflicts in BMC (0=unused) [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-b       : toggle running BMC2 on the init frames [default = %s]\n", fUseBmc? "yes": "no" );
    Abc_Print( -2, "\t-s       : toggle using transient signals [default = %s]\n", fUseTransSigs? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggle printing verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing ternary state space [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1; 
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandInduction( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int nFramesMax;
    int nConfMax;
    int fUnique;
    int fUniqueAll;
    int fGetCex;
    int fVerbose;
    int fVeryVerbose;
    int c;
    extern int Abc_NtkDarInduction( Abc_Ntk_t * pNtk, int nFramesMax, int nConfMax, int fUnique, int fUniqueAll, int fGetCex, int fVerbose, int fVeryVerbose );
    // set defaults
    nFramesMax   =   100;
    nConfMax     =  1000;
    fUnique      =     0;
    fUniqueAll   =     0;
    fGetCex      =     0;
    fVerbose     =     0;
    fVeryVerbose =     0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCuaxvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFramesMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfMax < 0 ) 
                goto usage;
            break;
        case 'u':
            fUnique ^= 1;
            break;
        case 'a':
            fUniqueAll ^= 1;
            break;
        case 'x':
            fGetCex ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( Abc_NtkPoNum(pNtk) != 1 )
    {
        Abc_Print( -1, "Currently this command works only for single-output miter.\n" );
        return 0;
    }
    if ( fUnique && fUniqueAll )
    {
        Abc_Print( -1, "Only one of the options, \"-u\" or \"-a\", should be selected.\n" );
        return 0;
    }

    // modify the current network
    pAbc->Status = Abc_NtkDarInduction( pNtk, nFramesMax, nConfMax, fUnique, fUniqueAll, fGetCex, fVerbose, fVeryVerbose );
    if ( fGetCex )
    {
        Abc_FrameReplaceCex( pAbc, &pNtk->pSeqModel );
        printf( "The current CEX in ABC is set to be the CEX to induction.\n" );
    }
    return 0;
usage:
    Abc_Print( -2, "usage: ind [-FC num] [-uaxvwh]\n" );
    Abc_Print( -2, "\t         runs the inductive case of the K-step induction\n" );
    Abc_Print( -2, "\t-F num : the max number of timeframes [default = %d]\n", nFramesMax );
    Abc_Print( -2, "\t-C num : the max number of conflicts by SAT solver [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-u     : toggle adding uniqueness constraints on demand [default = %s]\n", fUnique? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle adding uniqueness constraints always [default = %s]\n", fUniqueAll? "yes": "no" );
    Abc_Print( -2, "\t-x     : toggle returning CEX to induction for the top frame [default = %s]\n", fGetCex? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing additional verbose information [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandConstr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk;
    int c;
    int nFrames;
    int nConfs; 
    int nProps; 
    int fRemove;
    int fStruct;
    int fInvert;
    int fOldAlgo;
    int fVerbose;
    int nConstrs;
    extern void Abc_NtkDarConstr( Abc_Ntk_t * pNtk, int nFrames, int nConfs, int nProps, int fStruct, int fOldAlgo, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nFrames   =      1;
    nConfs    =   1000;
    nProps    =   1000;
    fRemove   =      0;
    fStruct   =      0;
    fInvert   =      0;    
    fOldAlgo  =      0;
    fVerbose  =      0;
    nConstrs  =      0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCPNrsiavh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfs < 0 ) 
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nProps = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nProps < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nConstrs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConstrs < 0 ) 
                goto usage;
            break;
        case 'r':
            fRemove ^= 1;
            break;
        case 's':
            fStruct ^= 1;
            break;
        case 'i':
            fInvert ^= 1;
            break;
        case 'a':
            fOldAlgo ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( fRemove )
    {
        if ( Abc_NtkConstrNum(pNtk) == 0 )
        {
            Abc_Print( -1, "Constraints are not defined.\n" );
            return 0;
        }
        Abc_Print( 1, "Constraints are converted to be primary outputs.\n" );
        pNtk->nConstrs = 0;
        return 0;
    }
    // consider the case of already defined constraints
    if ( Abc_NtkConstrNum(pNtk) > 0 )
    {
        extern void Abc_NtkDarConstrProfile( Abc_Ntk_t * pNtk, int fVerbose );
        if ( fInvert )
        {
            Abc_NtkInvertConstraints( pNtk );
            if ( Abc_NtkConstrNum(pNtk) == 1 )
                Abc_Print( 1, "The output of %d constraint is complemented.\n", Abc_NtkConstrNum(pNtk) );
            else
                Abc_Print( 1, "The outputs of %d constraints are complemented.\n", Abc_NtkConstrNum(pNtk) );
        }
        if ( fVerbose )
            Abc_NtkDarConstrProfile( pNtk, fVerbose );
        return 0;
    } 
    // consider the case of manual constraint definition
    if ( nConstrs > 0 )
    {
        if ( Abc_NtkConstrNum(pNtk) > 0 )
        {
            Abc_Print( -1, "The network already has constraints.\n" );
            return 0;
        }
        if ( nConstrs >= Abc_NtkPoNum(pNtk) )
        {
            Abc_Print( -1, "The number of constraints specified (%d) should be less than POs (%d).\n", nConstrs, Abc_NtkPoNum(pNtk) );
            return 0;
        }
        Abc_Print( 0, "Considering the last %d POs as constraint outputs.\n", nConstrs );
        pNtk->nConstrs = nConstrs;
        return 0;
    }
    // detect constraints using functional/structural methods
    Abc_NtkDarConstr( pNtk, nFrames, nConfs, nProps, fStruct, fOldAlgo, fVerbose );
    return 0;
usage:
    Abc_Print( -2, "usage: constr [-FCPN num] [-risavh]\n" );
    Abc_Print( -2, "\t         a toolkit for constraint manipulation\n" );
    Abc_Print( -2, "\t         if constraints are absent, detect them functionally\n" );
    Abc_Print( -2, "\t         if constraints are present, profiles them using random simulation\n" );
    Abc_Print( -2, "\t-F num : the max number of timeframes to consider [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-C num : the max number of conflicts in SAT solving [default = %d]\n", nConfs );
    Abc_Print( -2, "\t-P num : the max number of propagations in SAT solving [default = %d]\n", nProps );
    Abc_Print( -2, "\t-N num : manually set the last <num> POs to be constraints [default = %d]\n", nConstrs );
    Abc_Print( -2, "\t-r     : manually remove the constraints [default = %s]\n", fRemove? "yes": "no" );
    Abc_Print( -2, "\t-i     : toggle inverting already defined constraints [default = %s]\n", fInvert? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle using structural detection methods [default = %s]\n", fStruct? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle fast implication detection [default = %s]\n", !fOldAlgo? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandUnfold( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int nFrames;
    int nConfs; 
    int nProps; 
    int fStruct;
    int fOldAlgo;
    int fVerbose;
    int c;
    extern Abc_Ntk_t * Abc_NtkDarUnfold( Abc_Ntk_t * pNtk, int nFrames, int nConfs, int nProps, int fStruct, int fOldAlgo, int fVerbose );
    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    nFrames   =      1;
    nConfs    =   1000;
    nProps    =   1000;
    fStruct   =      0;
    fOldAlgo  =      0;
    fVerbose  =      0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCPsavh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfs < 0 ) 
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nProps = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nProps < 0 ) 
                goto usage;
            break;
        case 's':
            fStruct ^= 1;
            break;
        case 'a':
            fOldAlgo ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( Abc_NtkConstrNum(pNtk) > 0 )
    {
        Abc_Print( -1, "Constraints are already extracted.\n" );
        return 0;
    }
    if ( Abc_NtkPoNum(pNtk) > 1 )
    {
        Abc_Print( -1, "Constraint extraction works for single-output miters (use \"orpos\").\n" );
        return 0;
    }
    // modify the current network
    pNtkRes = Abc_NtkDarUnfold( pNtk, nFrames, nConfs, nProps, fStruct, fOldAlgo, fVerbose );
    if ( pNtkRes == NULL )
    {
        printf( "Transformation has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;
usage:
    Abc_Print( -2, "usage: unfold [-FCP num] [-savh]\n" );
    Abc_Print( -2, "\t         unfold hidden constraints as separate outputs\n" );
    Abc_Print( -2, "\t-F num : the max number of timeframes to consider [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-C num : the max number of conflicts in SAT solving [default = %d]\n", nConfs );
    Abc_Print( -2, "\t-P num : the max number of constraint propagations [default = %d]\n", nProps );
    Abc_Print( -2, "\t-s     : toggle detecting structural constraints [default = %s]\n", fStruct? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle fast implication detection [default = %s]\n", !fOldAlgo? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandFold( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk, * pNtkRes;
    int fCompl;
    int fVerbose;
    int c;
    extern Abc_Ntk_t * Abc_NtkDarFold( Abc_Ntk_t * pNtk, int fCompl, int fVerbose );
    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fCompl    =   0;
    fVerbose  =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fCompl ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Abc_NtkIsComb(pNtk) )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "Currently only works for structurally hashed circuits.\n" );
        return 0;
    }
    if ( Abc_NtkConstrNum(pNtk) == 0 )
    {
        Abc_Print( -1, "The network has no constraints.\n" );
        return 0;
    }
    // modify the current network
    pNtkRes = Abc_NtkDarFold( pNtk, fCompl, fVerbose );
    if ( pNtkRes == NULL )
    {
        printf( "Transformation has failed.\n" );
        return 0;
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    return 0;
usage:
    Abc_Print( -2, "usage: fold [-cvh]\n" );
    Abc_Print( -2, "\t         folds constraints represented as separate outputs\n" );
    Abc_Print( -2, "\t-c     : toggle complementing constraints while folding [default = %s]\n", fCompl? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBm( Abc_Frame_t * pAbc, int argc, char ** argv )
{   
    FILE * pOut, * pErr;
    Abc_Ntk_t *pNtk, *pNtk1, *pNtk2;
    int fDelete1, fDelete2; 
    char ** pArgvNew;
    int c, nArgcNew;        
    int p_equivalence = FALSE;
    extern void bmGateWay( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int p_equivalence );

    pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);  
    
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ph" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        case 'P':
            p_equivalence = 1;          
            break;        
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }
    
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( pErr, pNtk, pArgvNew, nArgcNew , &pNtk1, &pNtk2, &fDelete1, &fDelete2 ) )
        return 1;
        
    if( (unsigned)Abc_NtkPiNum(pNtk1) != (unsigned)Abc_NtkPiNum(pNtk2) || (unsigned)Abc_NtkPoNum(pNtk1) != (unsigned)Abc_NtkPoNum(pNtk2) )
    {
        Abc_Print( -2, "Mismatch in the number of inputs or outputs\n");
        if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
        if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
        return 1;
    }

    bmGateWay( pNtk1, pNtk2, p_equivalence );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );     
    return 0;

usage:
    Abc_Print( -2, "usage: bm [-P] <file1> <file2>\n" );
    Abc_Print( -2, "\t        performs Boolean matching (P-equivalence & PP-equivalence)\n" );
    Abc_Print( -2, "\t        for equivalent circuits, I/O matches are printed in IOmatch.txt\n" );
    Abc_Print( -2, "\t-P    : performs P-equivalnce checking\n");    
    Abc_Print( -2, "\t        default is PP-equivalence checking (when -P is not provided)\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    Abc_Print( -2, "\tfile1 : the file with the first network\n");
    Abc_Print( -2, "\tfile2 : the file with the second network\n");

    Abc_Print( -2, "\t        \n" );
    Abc_Print( -2, "\t        This command was contributed by Hadi Katebi from U Michigan.\n" );
    Abc_Print( -2, "\t        The paper describing the method: H. Katebi and I. L. Markov.\n" );
    Abc_Print( -2, "\t        \"Large-scale Boolean matching\". Proc. DATE 2010. \n" );
    Abc_Print( -2, "\t        http://www.eecs.umich.edu/~imarkov/pubs/conf/date10-match.pdf\n" );
    Abc_Print( -2, "\t        \n" );
  
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTestCex( Abc_Frame_t * pAbc, int argc, char ** argv )
{   
    Abc_Ntk_t * pNtk;
    int c;
    int nOutputs = 0;
    int fCheckAnd = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Oah" ) ) != EOF )
    {
        switch ( c )
        {
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            nOutputs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nOutputs < 0 ) 
                goto usage;
            break;
        case 'a':
            fCheckAnd ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }

    if ( pAbc->pCex == NULL )
    {
        Abc_Print( 1, "There is no current cex.\n");
        return 0;
    }

    if ( !fCheckAnd )
    {
        // check the main AIG
        pNtk = Abc_FrameReadNtk(pAbc);
        if ( pNtk == NULL )
            Abc_Print( 1, "Main AIG: There is no current network.\n");
        else if ( !Abc_NtkIsStrash(pNtk) )
            Abc_Print( 1, "Main AIG: The current network is not an AIG.\n");
        else if ( Abc_NtkPiNum(pNtk) != pAbc->pCex->nPis )
            Abc_Print( 1, "Main AIG: The number of PIs (%d) is different from cex (%d).\n", Abc_NtkPiNum(pNtk), pAbc->pCex->nPis );
//      else if ( Abc_NtkLatchNum(pNtk) != pAbc->pCex->nRegs )
//          Abc_Print( 1, "Main AIG: The number of registers (%d) is different from cex (%d).\n", Abc_NtkLatchNum(pNtk), pAbc->pCex->nRegs );
//      else if ( Abc_NtkPoNum(pNtk) <= pAbc->pCex->iPo )
//          Abc_Print( 1, "Main AIG: The number of POs (%d) is less than the PO index in cex (%d).\n", Abc_NtkPoNum(pNtk), pAbc->pCex->iPo );
        else 
        {
            extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
            Aig_Man_t * pAig = Abc_NtkToDar( pNtk, 0, 1 );
            Gia_Man_t * pGia = Gia_ManFromAigSimple( pAig );
    //        if ( !Gia_ManVerifyCex( pGia, pAbc->pCex, 0 ) )
            int iPoOld = pAbc->pCex->iPo;
            pAbc->pCex->iPo = Gia_ManFindFailedPoCex( pGia, pAbc->pCex, nOutputs );
            if ( pAbc->pCex->iPo == -1 )
            {
//                pAbc->pCex->iPo = iPoOld;
                Abc_Print( 1, "Main AIG: The cex does not fail any outputs.\n" );
            }
            else if ( iPoOld != pAbc->pCex->iPo )
                Abc_Print( 1, "Main AIG: The cex refined PO %d instead of PO %d.\n", pAbc->pCex->iPo, iPoOld );
            else 
                Abc_Print( 1, "Main AIG: The cex is correct.\n" );
            Gia_ManStop( pGia );
            Aig_ManStop( pAig );
        }
    }
    else
    {
        // check the AND AIG
        if ( pAbc->pGia == NULL )
            Abc_Print( 1, "And  AIG: There is no current network.\n");
        else if ( Gia_ManPiNum(pAbc->pGia) != pAbc->pCex->nPis )
            Abc_Print( 1, "And  AIG: The number of PIs (%d) is different from cex (%d).\n", Gia_ManPiNum(pAbc->pGia), pAbc->pCex->nPis );
//      else if ( Gia_ManRegNum(pAbc->pGia) != pAbc->pCex->nRegs )
//          Abc_Print( 1, "And  AIG: The number of registers (%d) is different from cex (%d).\n", Gia_ManRegNum(pAbc->pGia), pAbc->pCex->nRegs );
//      else if ( Gia_ManPoNum(pAbc->pGia) <= pAbc->pCex->iPo )
//          Abc_Print( 1, "And  AIG: The number of POs (%d) is less than the PO index in cex (%d).\n", Gia_ManPoNum(pAbc->pGia), pAbc->pCex->iPo );
        else 
        {
    //        if ( !Gia_ManVerifyCex( pAbc->pGia, pAbc->pCex, 0 ) )
            int iPoOld = pAbc->pCex->iPo;
            pAbc->pCex->iPo = Gia_ManFindFailedPoCex( pAbc->pGia, pAbc->pCex, nOutputs );
            if ( pAbc->pCex->iPo == -1 )
            {
//                pAbc->pCex->iPo = iPoOld;
                Abc_Print( 1, "And  AIG: The cex does not fail any outputs.\n" );
            }
            else if ( iPoOld != pAbc->pCex->iPo )
                Abc_Print( 1, "And  AIG: The cex refined PO %d instead of PO %d.\n", pAbc->pCex->iPo, iPoOld );
            else 
                Abc_Print( 1, "And  AIG: The cex is correct.\n" );
        }
    }
    return 0;

usage:
    Abc_Print( -2, "usage: testcex [-O num] [-ah]\n" );
    Abc_Print( -2, "\t         tests the current cex against the current AIG or the &-AIG\n" );
    Abc_Print( -2, "\t-O num : the number of real POs in the PO list [default = %d]\n", nOutputs );
    Abc_Print( -2, "\t-a     : toggle checking the current AIG or the &-AIG [default = %s]\n", fCheckAnd ? "&-AIG": "current AIG" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandPdr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_NtkDarPdr( Abc_Ntk_t * pNtk, Pdr_Par_t * pPars, Abc_Cex_t ** ppCex );
    Pdr_Par_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Cex_t * pCex = NULL;
    int c;
    Pdr_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "OMFCTrmsdgvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'O':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-O\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->iOutput = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->iOutput < 0 ) 
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRecycle = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRecycle < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFrameMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFrameMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfLimit < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTimeOut < 0 ) 
                goto usage;
            break;
        case 'r':
            pPars->fTwoRounds ^= 1;
            break;
        case 'm':
            pPars->fMonoCnf ^= 1;
            break;
        case 's':
            pPars->fShortest ^= 1;
            break;
        case 'd':
            pPars->fDumpInv ^= 1;
            break;
        case 'g':
            pPars->fSkipGeneral ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( pNtk == NULL )
    {
        Abc_Print( -2, "There is no current network.\n");
        return 0;
    }
    if ( Abc_NtkLatchNum(pNtk) == 0 )
    {
        Abc_Print( -2, "The current network is combinational.\n");
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -2, "The current network is not an AIG (run \"strash\").\n");
        return 0;
    }
    if ( pPars->iOutput != -1 && (pPars->iOutput < 0 || pPars->iOutput >= Abc_NtkPoNum(pNtk)) )
    {
        Abc_Print( -2, "Output index (%d) is incorrect (can be 0 through %d).\n", 
            pPars->iOutput, Abc_NtkPoNum(pNtk)-1 );
        return 0;
    }
    if ( Abc_NtkPoNum(pNtk) != 1 && pPars->fVerbose )
    {
        if ( pPars->iOutput == -1 )
            Abc_Print( -2, "The %d property outputs are ORed together.\n", Abc_NtkPoNum(pNtk) );
        else 
            Abc_Print( -2, "Working on the primary output with zero-based number %d (out of %d).\n", 
                pPars->iOutput, Abc_NtkPoNum(pNtk) );
    }
    // run the procedure
    pAbc->Status  = Abc_NtkDarPdr( pNtk, pPars, &pCex );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pCex );
    return 0;

usage:
    Abc_Print( -2, "usage: pdr [-OMFCT<num] [-rmsdgvwh]\n" );
    Abc_Print( -2, "\t         model checking using property directed reachability (aka ic3)\n" );
    Abc_Print( -2, "\t         pioneered by Aaron Bradley (http://ecee.colorado.edu/~bradleya/ic3/)\n" );
    Abc_Print( -2, "\t         with improvements by Niklas Een (http://een.se/niklas/)\n" );
    Abc_Print( -2, "\t-O num : the zero-based number of the primary output to solve [default = all]\n" );
    Abc_Print( -2, "\t-M num : number of unused vars to trigger SAT solver recycling [default = %d]\n", pPars->nRecycle );
    Abc_Print( -2, "\t-F num : number of timeframes explored to stop computation [default = %d]\n", pPars->nFrameMax );
    Abc_Print( -2, "\t-C num : number of conflicts in a SAT call (0 = no limit) [default = %d]\n", pPars->nConfLimit );
    Abc_Print( -2, "\t-T num : approximate timeout in seconds (0 = no limit) [default = %d]\n", pPars->nTimeOut );
    Abc_Print( -2, "\t-r     : toggle using more effort in generalization [default = %s]\n", pPars->fTwoRounds? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle using monolythic CNF computation [default = %s]\n", pPars->fMonoCnf? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle creating only shortest counter-examples [default = %s]\n", pPars->fShortest? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle dumping inductive invariant [default = %s]\n", pPars->fDumpInv? "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle skipping expensive generalization step [default = %s]\n", pPars->fSkipGeneral? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing optimization summary [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing detailed stats default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1; 
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandReconcile( Abc_Frame_t * pAbc, int argc, char ** argv )
{   
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    extern Abc_Cex_t * Llb4_Nonlin4NormalizeCex( Aig_Man_t * pAigOrg, Aig_Man_t * pAigRpm, Abc_Cex_t * pCexRpm );
    Abc_Cex_t * pCex;
    Abc_Ntk_t * pNtk1, * pNtk2;
    Aig_Man_t * pAig1, * pAig2;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }
    if ( argc != globalUtilOptind + 2 ) 
    {
        printf( "Does not seen to have two files names as arguments.\n" );
        return 1;
    }
    if ( pAbc->pCex == NULL )
    {
        printf( "There is no current counter-example.\n" );
        return 1;
    }

    // derive networks
    pNtk1 = Io_Read( argv[globalUtilOptind], Io_ReadFileType(argv[globalUtilOptind]), 1 );
    if ( pNtk1 == NULL )
        return 1;
    pNtk2 = Io_Read( argv[globalUtilOptind+1], Io_ReadFileType(argv[globalUtilOptind+1]), 1 );
    if ( pNtk2 == NULL )
    {
        Abc_NtkDelete( pNtk1 );
        return 1;
    }
    // create counter-examples
    pAig1 = Abc_NtkToDar( pNtk1, 0, 0 );
    pAig2 = Abc_NtkToDar( pNtk2, 0, 0 );
    pCex = Llb4_Nonlin4NormalizeCex( pAig1, pAig2, pAbc->pCex );
    Aig_ManStop( pAig1 );
    Aig_ManStop( pAig2 );
    Abc_NtkDelete( pNtk2 );
    if ( pCex == NULL )
    {
        printf( "Counter-example computation has failed.\n" );
        Abc_NtkDelete( pNtk1 );
        return 1;
    }

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtk1 );
    // update the counter-example
    pAbc->nFrames = pCex->iFrame;
    Abc_FrameReplaceCex( pAbc, &pCex );
    return 0;

usage:
    Abc_Print( -2, "usage: reconcile [-h] <fileOrigin> <fileReparam>\n" );
    Abc_Print( -2, "\t        reconciles current CEX with <fileOrigin>\n" );
    Abc_Print( -2, "\t        More specifically:\n" );
    Abc_Print( -2, "\t        (i) assumes that <fileReparam> is an AIG derived by input\n" );
    Abc_Print( -2, "\t        reparametrization of <fileOrigin> without seq synthesis;\n" );
    Abc_Print( -2, "\t        (ii) assumes that current CEX is valid for <fileReparam>;\n" );
    Abc_Print( -2, "\t        (iii) derives new CEX for <fileOrigin> and sets this CEX\n" );
    Abc_Print( -2, "\t        and <fileOrigin> to be current CEX and current network\n" );
    Abc_Print( -2, "\t<fileOrigin>   : file name with the original AIG\n");
    Abc_Print( -2, "\t<fileReparam>  : file name with the reparametrized AIG\n");
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandCexMin( Abc_Frame_t * pAbc, int argc, char ** argv )
{   
    Abc_Ntk_t * pNtk;
    Abc_Cex_t * vCexNew = NULL;
    int c;
    int nConfLimit = 1000;
    int nRounds    =    1;
    int fVerbose   =    0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CRvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 ) 
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRounds < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }

    if ( pAbc->pCex == NULL )
    {
        Abc_Print( 1, "There is no current cex.\n");
        return 0;
    }

    // check the main AIG
    pNtk = Abc_FrameReadNtk(pAbc);
    if ( pNtk == NULL )
        Abc_Print( 1, "Main AIG: There is no current network.\n");
    else if ( !Abc_NtkIsStrash(pNtk) )
        Abc_Print( 1, "Main AIG: The current network is not an AIG.\n");
    else if ( Abc_NtkPiNum(pNtk) != pAbc->pCex->nPis )
        Abc_Print( 1, "Main AIG: The number of PIs (%d) is different from cex (%d).\n", Abc_NtkPiNum(pNtk), pAbc->pCex->nPis );
//      else if ( Abc_NtkLatchNum(pNtk) != pAbc->pCex->nRegs )
//          Abc_Print( 1, "Main AIG: The number of registers (%d) is different from cex (%d).\n", Abc_NtkLatchNum(pNtk), pAbc->pCex->nRegs );
//      else if ( Abc_NtkPoNum(pNtk) <= pAbc->pCex->iPo )
//          Abc_Print( 1, "Main AIG: The number of POs (%d) is less than the PO index in cex (%d).\n", Abc_NtkPoNum(pNtk), pAbc->pCex->iPo );
    else 
    {
        extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
        Aig_Man_t * pAig = Abc_NtkToDar( pNtk, 0, 1 );
        Gia_Man_t * pGia = Gia_ManFromAigSimple( pAig );
//        if ( !Gia_ManVerifyCex( pGia, pAbc->pCex, 0 ) )
        int iPoOld = pAbc->pCex->iPo;
        pAbc->pCex->iPo = Gia_ManFindFailedPoCex( pGia, pAbc->pCex, 0 );
        Gia_ManStop( pGia );
        if ( pAbc->pCex->iPo == -1 )
        {
            pAbc->pCex->iPo = iPoOld;
            Abc_Print( -1, "Main AIG: The cex does not fail any outputs.\n" );
            return 0;
        }
        else if ( iPoOld != pAbc->pCex->iPo )
            Abc_Print( 0, "Main AIG: The cex refined PO %d instead of PO %d.\n", pAbc->pCex->iPo, iPoOld );
        // perform minimization
        vCexNew = Saig_ManCexMinPerform( pAig, pAbc->pCex );
        Aig_ManStop( pAig );
        Abc_CexFree( vCexNew );
//        Abc_FrameReplaceCex( pAbc, &vCexNew );

//        printf( "Implementation of this command is not finished.\n" );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: cexmin [-CR num] [-vh]\n" );
    Abc_Print( -2, "\t         reduces the length of the counter-example\n" );
    Abc_Print( -2, "\t-C num : the maximum number of conflicts [default = %d]\n", nConfLimit );
    Abc_Print( -2, "\t-R num : the number of minimization rounds [default = %d]\n", nRounds );
    Abc_Print( -2, "\t-v     : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandDualRail( Abc_Frame_t * pAbc, int argc, char ** argv )
{   
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
    Abc_Ntk_t * pNtk, * pNtkNew = NULL;
    Aig_Man_t * pAig, * pAigNew;
    int c;
    int nDualPis  = 0;
    int fDualFfs  = 0;
    int fMiterFfs = 0;
    int fComplPo  = 0;
    int fVerbose  = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Itfcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nDualPis = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nDualPis < 0 ) 
                goto usage;
            break;
        case 't':
            fDualFfs ^= 1;
            break;
        case 'f':
            fMiterFfs ^= 1;
            break;
        case 'c':
            fComplPo ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }

    // check the main AIG
    pNtk = Abc_FrameReadNtk(pAbc);
    if ( pNtk == NULL )
    {
        Abc_Print( 1, "Main AIG: There is no current network.\n");
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( 1, "Main AIG: The current network is not an AIG.\n");
        return 0;
    }

    // tranform    
    pAig = Abc_NtkToDar( pNtk, 0, 1 );
    pAigNew = Saig_ManDupDual( pAig, nDualPis, fDualFfs, fMiterFfs, fComplPo );
    Aig_ManStop( pAig );
    pNtkNew = Abc_NtkFromAigPhase( pAigNew );
    pNtkNew->pName = Extra_UtilStrsav(pNtk->pName);
    Aig_ManStop( pAigNew );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkNew );
    return 0;

usage:
    Abc_Print( -2, "usage: dualrail [-I num] [-tfcvh]\n" );
    Abc_Print( -2, "\t         transforms the current AIG into a dual-rail miter\n" );
    Abc_Print( -2, "\t         expressing the property \"at least one PO has ternary value\"\n" );
    Abc_Print( -2, "\t         (to compute an initialization sequence, use switches \"-tfc\")\n" );
    Abc_Print( -2, "\t-I num : the number of first PIs interpreted as ternary [default = %d]\n", nDualPis );
    Abc_Print( -2, "\t-t     : toggle ternary flop init values [default = %s]\n", fDualFfs? "yes": "const0 init values" );
    Abc_Print( -2, "\t-f     : toggle mitering flops instead of POs [default = %s]\n", fMiterFfs? "flops": "POs" );
    Abc_Print( -2, "\t-c     : toggle complementing the miter output [default = %s]\n", fComplPo? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandBlockPo( Abc_Frame_t * pAbc, int argc, char ** argv )
{   
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
    Abc_Ntk_t * pNtk, * pNtkNew = NULL;
    Aig_Man_t * pAig;
    int c;
    int nCycles = 0;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nCycles = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCycles < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            Abc_Print( -2, "Unknown switch.\n");
            goto usage;
        }
    }

    // check the main AIG
    pNtk = Abc_FrameReadNtk(pAbc);
    if ( pNtk == NULL )
    {
        Abc_Print( 1, "Main AIG: There is no current network.\n");
        return 0;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( 1, "Main AIG: The current network is not an AIG.\n");
        return 0;
    }
    if ( nCycles == 0 )
    {
        Abc_Print( 1, "The number of time frame is 0. The circuit is left unchanged.\n" );
        return 0;
    }

    // transform
    pAig = Abc_NtkToDar( pNtk, 0, 1 );
    Saig_ManBlockPo( pAig, nCycles );
    pNtkNew = Abc_NtkFromAigPhase( pAig );
    Aig_ManStop( pAig );

    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtkNew );
    return 0;

usage:
    Abc_Print( -2, "usage: blockpo [-F num] [-fvh]\n" );
    Abc_Print( -2, "\t         forces the miter outputs to be \"true\" in the first F frames\n" );
    Abc_Print( -2, "\t-F num : the number of time frames [default = %d]\n", nCycles );
    Abc_Print( -2, "\t-v     : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTraceStart( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command is applicable to AIGs.\n" );
        return 1;
    }
/*
    Abc_HManStart();
    if ( !Abc_HManPopulate( pNtk ) )
    {
        Abc_Print( -1, "Failed to start the tracing database.\n" );
        return 1;
    }
*/
    return 0;

usage:
    Abc_Print( -2, "usage: trace_start [-h]\n" );
    Abc_Print( -2, "\t        starts verification tracing\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandTraceCheck( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        Abc_Print( -1, "This command is applicable to AIGs.\n" );
        return 1;
    }
/*
    if ( !Abc_HManIsRunning(pNtk) )
    {
        Abc_Print( -1, "The tracing database is not available.\n" );
        return 1;
    }

    if ( !Abc_HManVerify( 1, pNtk->Id ) )
        Abc_Print( -1, "Verification failed.\n" );
    Abc_HManStop();
*/
    return 0;

usage:
    Abc_Print( -2, "usage: trace_check [-h]\n" );
    Abc_Print( -2, "\t        checks the current network using verification trace\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbcTestNew( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Abc_NtkTestProcedure( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2 );

    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;

    pNtk = Abc_FrameReadNtk(pAbc);

    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsStrash( pNtk) )
    {
        Abc_Print( -1, "The current network is not an AIG. Cannot continue.\n" );
        return 1;
    }

//    Abc_NtkTestProcedure( pNtk, NULL );

    return 0;

usage:
    Abc_Print( -2, "usage: testnew [-h]\n" );
    Abc_Print( -2, "\t        new testing procedure\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Read( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pAig;
    FILE * pFile;
    char ** pArgvNew;
    char * FileName, * pTemp;
    int nArgcNew;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "There is no file name.\n" );
        return 1;
    }

    // get the input file name
    FileName = pArgvNew[0];
    // fix the wrong symbol
    for ( pTemp = FileName; *pTemp; pTemp++ )
        if ( *pTemp == '>' )
            *pTemp = '\\';
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".aig", ".blif", ".pla", ".eqn", ".bench" )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );

    pAig = Gia_ReadAiger( FileName, 0 );
    Abc_CommandUpdate9( pAbc, pAig );
    return 0;

usage:
    Abc_Print( -2, "usage: &r [-vh] <file>\n" );
    Abc_Print( -2, "\t         reads the current AIG from the AIGER file\n" );
    Abc_Print( -2, "\t-v     : toggles additional verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReadBlif( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Abc_NtkHieCecTest( char * pFileName, int fVerbose );
    Gia_Man_t * pAig;
    FILE * pFile;
    char ** pArgvNew;
    char * FileName, * pTemp;
    int nArgcNew;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "There is no file name.\n" );
        return 1;
    }

    // get the input file name
    FileName = pArgvNew[0];
    // fix the wrong symbol
    for ( pTemp = FileName; *pTemp; pTemp++ )
        if ( *pTemp == '>' )
            *pTemp = '\\';
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".blif", NULL, NULL, NULL, NULL )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );

    pAig = Abc_NtkHieCecTest( FileName, fVerbose );
    Abc_CommandUpdate9( pAbc, pAig );
    return 0;

usage:
    Abc_Print( -2, "usage: &read_blif [-vh] <file>\n" );
    Abc_Print( -2, "\t         reads the current AIG from a hierarchical BLIF file\n" );
    Abc_Print( -2, "\t-v     : toggles additional verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReadCBlif( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Abc_NtkHieCecTest2( char * pFileName, char * pModelName, int fVerbose );
    Gia_Man_t * pAig;
    FILE * pFile;
    char ** pArgvNew;
    char * FileName, * pTemp;
    char * pModelName = NULL;
    int nArgcNew;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Mvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a file name.\n" );
                goto usage;
            }
            pModelName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "There is no file name.\n" );
        return 1;
    }

    // get the input file name
    FileName = pArgvNew[0];
    // fix the wrong symbol
    for ( pTemp = FileName; *pTemp; pTemp++ )
        if ( *pTemp == '>' )
            *pTemp = '\\';
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".cblif", NULL, NULL, NULL, NULL )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );

    pAig = Abc_NtkHieCecTest2( FileName, pModelName, fVerbose );
    Abc_CommandUpdate9( pAbc, pAig );
    return 0;

usage:
    Abc_Print( -2, "usage: &read_cblif [-M name] [-vh] <file>\n" );
    Abc_Print( -2, "\t         reads CBLIF file and collapse it into an AIG\n" );
    Abc_Print( -2, "\t-M name: module name to collapse [default = <root_module>]\n" );
    Abc_Print( -2, "\t-v     : toggles additional verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Get( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    extern Aig_Man_t * Abc_NtkToDarChoices( Abc_Ntk_t * pNtk );
    extern Vec_Ptr_t * Abc_NtkCollectCiNames( Abc_Ntk_t * pNtk );
    extern Vec_Ptr_t * Abc_NtkCollectCoNames( Abc_Ntk_t * pNtk );
    Gia_Man_t * pAig;
    Aig_Man_t * pMan;
    int c, fVerbose = 0;
    int fNames = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "nvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'n':
            fNames ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pNtkCur == NULL )
    {
        Abc_Print( -1, "There is no current network\n" );
        return 1;
    }
    if ( !Abc_NtkIsStrash( pAbc->pNtkCur ) )
    {
        Abc_Print( -1, "The current network should be strashed.\n" );
        return 1;
    }
//    if ( Abc_NtkGetChoiceNum(pAbc->pNtkCur) )
//    {
//        Abc_Print( -1, "Removing %d choices from the AIG.\n", Abc_NtkGetChoiceNum(pAbc->pNtkCur) );
//        Abc_AigCleanup(pAbc->pNtkCur->pManFunc);
//    }
    if ( Abc_NtkGetChoiceNum(pAbc->pNtkCur) )
        pMan = Abc_NtkToDarChoices( pAbc->pNtkCur );
    else
        pMan = Abc_NtkToDar( pAbc->pNtkCur, 0, 1 );
    pAig = Gia_ManFromAig( pMan );
    Aig_ManStop( pMan );
    Abc_CommandUpdate9( pAbc, pAig );
    if ( fNames )
    {
        pAig->vNamesIn  = Abc_NtkCollectCiNames( pAbc->pNtkCur );
        pAig->vNamesOut = Abc_NtkCollectCoNames( pAbc->pNtkCur );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &get [-nvh] <file>\n" );
    Abc_Print( -2, "\t         converts the network into an AIG and moves to the new ABC\n" );
    Abc_Print( -2, "\t-n     : toggles saving CI/CO names of the AIG [default = %s]\n", fNames? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggles additional verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Put( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkFromAigPhase( Aig_Man_t * pMan );
    extern Abc_Ntk_t * Abc_NtkFromDarChoices( Abc_Ntk_t * pNtkOld, Aig_Man_t * pMan );
    Aig_Man_t * pMan;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c, fVerbose = 0;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }
    if ( Gia_ManHasDangling(pAbc->pGia) == 0 )
    {
        pMan = Gia_ManToAig( pAbc->pGia, 0 );
        pNtk = Abc_NtkFromAigPhase( pMan );
        pNtk->pName = Extra_UtilStrsav(pMan->pName);
        Aig_ManStop( pMan );
    }
    else
    {
        Abc_Ntk_t * pNtkNoCh;
//        Abc_Print( -1, "Transforming AIG with %d choice nodes.\n", Gia_ManEquivCountClasses(pAbc->pGia) );
        // create network without choices
        pMan = Gia_ManToAig( pAbc->pGia, 0 );
        pNtkNoCh = Abc_NtkFromAigPhase( pMan );
        pNtkNoCh->pName = Extra_UtilStrsav(pMan->pName);
        Aig_ManStop( pMan );
        // derive network with choices
        pMan = Gia_ManToAig( pAbc->pGia, 1 );
        pNtk = Abc_NtkFromDarChoices( pNtkNoCh, pMan );
        Abc_NtkDelete( pNtkNoCh );
        Aig_ManStop( pMan );
    }
    // transfer PI names to pNtk
    if ( pAbc->pGia->vNamesIn ) 
    {
        Abc_Obj_t * pObj;
        int i;
        Abc_NtkForEachCi( pNtk, pObj, i ) {
            if (i < Vec_PtrSize(pAbc->pGia->vNamesIn)) {
                Nm_ManDeleteIdName(pNtk->pManName, pObj->Id);
                Abc_ObjAssignName( pObj, (char *)Vec_PtrEntry(pAbc->pGia->vNamesIn, i), NULL );
            }
        }
    }
    // replace the current network
    Abc_FrameReplaceCurrentNetwork( pAbc, pNtk );
    Abc_FrameClearVerifStatus( pAbc );
    return 0;

usage:
    Abc_Print( -2, "usage: &put [-vh]\n" );
    Abc_Print( -2, "\t         transfer the current network into the old ABC\n" );
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Write( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pFileName;
    char ** pArgvNew;
    int c, nArgcNew;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "There is no file name.\n" );
        return 1;
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Write(): There is no AIG to write.\n" );
        return 1;
    } 
    // create the design to write
    pFileName = argv[globalUtilOptind];
    Gia_WriteAiger( pAbc->pGia, pFileName, 0, 0 );
    return 0;

usage:
    Abc_Print( -2, "usage: &w [-h] <file>\n" );
    Abc_Print( -2, "\t        writes the current AIG into the AIGER file\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    Abc_Print( -2, "\t<file> : the file name\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Ps( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    int fSwitch = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ph" ) ) != EOF )
    {
        switch ( c )
        {
        case 'p':
            fSwitch ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Ps(): There is no AIG.\n" );
        return 1;
    } 
    Gia_ManPrintStats( pAbc->pGia, fSwitch );
    return 0;

usage:
    Abc_Print( -2, "usage: &ps [-ph]\n" );
    Abc_Print( -2, "\t        prints stats of the current AIG\n" );
    Abc_Print( -2, "\t-p    : toggle printing switching activity [default = %s]\n", fSwitch? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9PFan( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    int nNodes = 40;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nNodes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nNodes < 0 ) 
                goto usage;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9PFan(): There is no AIG.\n" );
        return 1;
    } 
    Gia_ManPrintFanio( pAbc->pGia, nNodes );
    return 0;

usage:
    Abc_Print( -2, "usage: &pfan [-N num] [-h]\n" );
    Abc_Print( -2, "\t         prints fanin/fanout statistics\n" );
    Abc_Print( -2, "\t-N num : the number of high-fanout nodes to explore [default = %d]\n", nNodes );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9PSig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    int fSetReset = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'r':
            fSetReset ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9PSigs(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9PSigs(): Works only for sequential circuits.\n" );
        return 1;
    } 
    Gia_ManDetectSeqSignals( pAbc->pGia, fSetReset, 1 );
    return 0;

usage:
    Abc_Print( -2, "usage: &psig [-rh]\n" );
    Abc_Print( -2, "\t         prints enable/set/reset statistics\n" );
    Abc_Print( -2, "\t-r     : toggle printing set/reset signals [default = %s]\n", fSetReset? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Status( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Status(): There is no AIG.\n" );
        return 1;
    } 
    Gia_ManPrintMiterStatus( pAbc->pGia );
    return 0;

usage:
    Abc_Print( -2, "usage: &status [-h]\n" );
    Abc_Print( -2, "\t         prints status of the miter\n" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Show( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Aig_Man_t * pMan;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Show(): There is no AIG.\n" );
        return 1;
    } 
    pMan = Gia_ManToAig( pAbc->pGia, 0 );
    Aig_ManShow( pMan, 0, NULL );
    Aig_ManStop( pMan );
    return 0;

usage:
    Abc_Print( -2, "usage: &show [-h]\n" );
    Abc_Print( -2, "\t        shows the current AIG using GSView\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Hash( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c;
    int fAddStrash = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ah" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fAddStrash ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Hash(): There is no AIG.\n" );
        return 1;
    } 
    pTemp = Gia_ManRehash( pAbc->pGia, fAddStrash );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &st [-ah]\n" );
    Abc_Print( -2, "\t        performs structural hashing\n" );
    Abc_Print( -2, "\t-a    : toggle additional hashing [default = %s]\n", fAddStrash? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Topand( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, fVerbose = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Topand(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) > 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Topand(): Can only be applied to a combinational miter.\n" );
        return 1;
    } 
    pTemp = Gia_ManDupTopAnd( pAbc->pGia, fVerbose );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &topand [-vh]\n" );
    Abc_Print( -2, "\t        performs AND decomposition for combinational miter\n" );
    Abc_Print( -2, "\t-v    : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Cof( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, fVerbose = 0;
    int iVar = 0, nLimFan = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "VLvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'V':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-V\" should be followed by an integer.\n" );
                goto usage;
            }
            iVar = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iVar < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            } 
            nLimFan = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nLimFan < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Cof(): There is no AIG.\n" );
        return 1;
    } 
    if ( nLimFan )
    {
        Abc_Print( -1, "Cofactoring all variables whose fanout count is higher than %d.\n", nLimFan );
        pTemp = Gia_ManDupCofAll( pAbc->pGia, nLimFan, fVerbose );
        Abc_CommandUpdate9( pAbc, pTemp );
    }
    else if ( iVar )
    {
        Abc_Print( -1, "Cofactoring one variable with object ID %d.\n", iVar );
        pTemp = Gia_ManDupCof( pAbc->pGia, iVar );
        Abc_CommandUpdate9( pAbc, pTemp );
    }
    else
    {
        Abc_Print( -1, "One of the paramters, -V <num> or -L <num>, should be set on the command line.\n" );
        goto usage;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &cof [-VL num] [-vh]\n" );
    Abc_Print( -2, "\t         performs cofactoring w.r.t. variable(s)\n" );
    Abc_Print( -2, "\t-V num : the zero-based ID of one variable to cofactor [default = %d]\n", iVar );
    Abc_Print( -2, "\t-L num : cofactor vars with fanout count higher than this [default = %d]\n", nLimFan );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Trim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c;
    int fTrimCis = 1;
    int fTrimCos = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "ioh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'i':
            fTrimCis ^= 1;
            break;
        case 'o':
            fTrimCos ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Trim(): There is no AIG.\n" );
        return 1;
    } 
    pTemp = Gia_ManDupTrimmed( pAbc->pGia, fTrimCis, fTrimCos );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &trim [-ioh]\n" );
    Abc_Print( -2, "\t         removes PIs without fanout and PO driven by constants\n" );
    Abc_Print( -2, "\t-i     : toggle removing PIs [default = %s]\n", fTrimCis? "yes": "no" );
    Abc_Print( -2, "\t-o     : toggle removing POs [default = %s]\n", fTrimCos? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Dfs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c;
    int fNormal  = 0;
    int fReverse = 0;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "nrvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'n':
            fNormal ^= 1;
            break;
        case 'r':
            fReverse ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Dfs(): There is no AIG.\n" );
        return 1;
    } 
    if ( fNormal )
    {
        pTemp = Gia_ManDupOrderAiger( pAbc->pGia );
        if ( fVerbose )
            Abc_Print( -1, "AIG objects are reordered as follows: CIs, ANDs, COs.\n" );
    }
    else if ( fReverse )
    {
        pTemp = Gia_ManDupOrderDfsReverse( pAbc->pGia );
        if ( fVerbose )
            Abc_Print( -1, "AIG objects are reordered in the reserve DFS order.\n" );
    }
    else 
    {
        pTemp = Gia_ManDupOrderDfs( pAbc->pGia );
        if ( fVerbose )
            Abc_Print( -1, "AIG objects are reordered in the DFS order.\n" );
    }
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &dfs [-nrvh]\n" );
    Abc_Print( -2, "\t        orders objects in the DFS order\n" );
    Abc_Print( -2, "\t-n    : toggle using normalized ordering [default = %s]\n", fNormal? "yes": "no" );
    Abc_Print( -2, "\t-r    : toggle using reverse DFS ordering [default = %s]\n", fReverse? "yes": "no" );
    Abc_Print( -2, "\t-v    : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Sim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_ParSim_t Pars, * pPars = &Pars;
    int c;
    Gia_ManSimSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FWNTmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIters < 0 ) 
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWords < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->RandSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->RandSeed < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeLimit < 0 ) 
                goto usage;
            break;
        case 'm':
            pPars->fCheckMiter ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Sim(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    pAbc->nFrames = -1;
    if ( Gia_ManSimSimulate( pAbc->pGia, pPars ) )
        pAbc->Status =  0;
    else
        pAbc->Status = -1;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
//    if ( pLogFileName )
//        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "&sim" );
    return 0;

usage:
    Abc_Print( -2, "usage: &sim [-FWNT num] [-mvh]\n" );
    Abc_Print( -2, "\t         performs random simulation of the sequential miter\n" );
    Abc_Print( -2, "\t         (if candidate equivalences are defined, performs refinement)\n" );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", pPars->nIters );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-N num : random number seed (1 <= num <= 1000) [default = %d]\n", pPars->RandSeed );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", pPars->fCheckMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Sim3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    int nFrames;
    int nWords;
    int nBinSize;
    int nRounds;
    int nRandSeed;
    int TimeOut;
    int fVerbose;
    extern int Ssw_RarSimulateGia( Gia_Man_t * p, int nFrames, int nWords, int nBinSize, int nRounds, int nRandSeed, int TimeOut, int fVerbose );
    // set defaults
    nFrames    =  20;
    nWords     =  50;
    nBinSize   =   8;
    nRounds    =  80;
    nRandSeed  =   0;
    TimeOut    =   0;
    fVerbose   =   0;
    // parse command line
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FWBRNTvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nWords < 0 ) 
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            nBinSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBinSize < 0 ) 
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRounds < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nRandSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRandSeed < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            TimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( TimeOut < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Sim3(): There is no AIG.\n" );
        return 1;
    }
    pAbc->Status = Ssw_RarSimulateGia( pAbc->pGia, nFrames, nWords, nBinSize, nRounds, nRandSeed, TimeOut, fVerbose );  
//    pAbc->nFrames = pAbc->pGia->pCexSeq->iFrame;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &sim3 [-FWBRNT num] [-vh]\n" );
    Abc_Print( -2, "\t         performs random simulation of the sequential miter\n" );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n",  nWords );
    Abc_Print( -2, "\t-B num : the number of flops in one bin [default = %d]\n",   nBinSize );
    Abc_Print( -2, "\t-R num : the number of simulation rounds [default = %d]\n",  nRounds );
    Abc_Print( -2, "\t-N num : random number seed (1 <= num <= 1000) [default = %d]\n", nRandSeed );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", TimeOut );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Resim( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParSim_t Pars, * pPars = &Pars;
    int c, RetValue;
    Cec_ManSimSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Fmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFrames < 0 ) 
                goto usage;
            break;
        case 'm':
            pPars->fCheckMiter ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Resim(): There is no AIG.\n" );
        return 1;
    } 
    RetValue = Cec_ManSeqResimulateCounter( pAbc->pGia, pPars, pAbc->pCex );
    pAbc->Status  = RetValue ? 0 : -1;
    pAbc->nFrames = pAbc->pCex->iFrame;
//    Abc_FrameReplaceCex( pAbc, &pAbc->pCex );
    return 0;

usage:
    Abc_Print( -2, "usage: &resim [-F num] [-mvh]\n" );
    Abc_Print( -2, "\t         resimulates equivalence classes using counter-example\n" );
    Abc_Print( -2, "\t-F num : the number of additinal frames to simulate [default = %d]\n", pPars->nFrames );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", pPars->fCheckMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9SpecI( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Gia_CommandSpecI( Gia_Man_t * pGia, int nFrames, int nBTLimit, int fUseStart, int fCheckMiter, int fVerbose );
    int nFrames     =   100;
    int nBTLimit    = 25000;
    int fUseStart   =     1;
    int fCheckMiter =     1;
    int fVerbose    =     0;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCfmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBTLimit < 0 ) 
                goto usage;
            break;
        case 'f':
            fUseStart ^= 1;
            break;
        case 'm':
            fCheckMiter ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9SpecI(): There is no AIG.\n" );
        return 1;
    } 
    Gia_CommandSpecI( pAbc->pGia, nFrames, nBTLimit, fUseStart, fCheckMiter, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &speci [-FC num] [-fmvh]\n" );
    Abc_Print( -2, "\t         refines equivalence classes using speculative reduction\n" );
    Abc_Print( -2, "\t-F num : the max number of time frames [default = %d]\n", nFrames );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nBTLimit );
    Abc_Print( -2, "\t-f     : toggle starting BMC from a later frame [default = %s]\n", fUseStart? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", fCheckMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Equiv( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParSim_t Pars, * pPars = &Pars;
    int c;
    Cec_ManSimSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WFRSTsmdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWords < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFrames < 0 ) 
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRounds < 0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nNonRefines = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nNonRefines < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeLimit < 0 ) 
                goto usage;
            break;
        case 's':
            pPars->fSeqSimulate ^= 1;
            break;
        case 'm':
            pPars->fCheckMiter ^= 1;
            break;
        case 'd':
            pPars->fDualOut ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Equiv(): There is no AIG.\n" );
        return 1;
    } 
    Cec_ManSimulation( pAbc->pGia, pPars );
    return 0;

usage:
    Abc_Print( -2, "usage: &equiv [-WFRST num] [-smdvh]\n" );
    Abc_Print( -2, "\t         computes candidate equivalence classes\n" );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-F num : the number of frames to simulate [default = %d]\n", pPars->nFrames );
    Abc_Print( -2, "\t-R num : the max number of simulation rounds [default = %d]\n", pPars->nRounds );
    Abc_Print( -2, "\t-S num : the max number of rounds w/o refinement to stop [default = %d]\n", pPars->nNonRefines );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-s     : toggle seq vs. comb simulation [default = %s]\n", pPars->fSeqSimulate? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", pPars->fCheckMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-d     : toggle using two POs intead of XOR [default = %s]\n", pPars->fDualOut? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Equiv2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Ssw_SignalFilterGia( Gia_Man_t * p, int nFramesMax, int nConfMax, int nRounds, int TimeLimit, int TimeLimit2, Abc_Cex_t * pCex, int fLatchOnly, int fVerbose );
    int nFramesMax =   20;
    int nConfMax   =  500;
    int nRounds    =   10;
    int TimeLimit  =    0;
    int TimeLimit2 =    0;
    int fUseCex    =    0;
    int fLatchOnly =    0;
    int fVerbose   =    0;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCRTSxlvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFramesMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfMax < 0 ) 
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRounds < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( TimeLimit < 0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            TimeLimit2 = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( TimeLimit2 < 0 ) 
                goto usage;
            break;
        case 'x':
            fUseCex ^= 1;
            break;
        case 'l':
            fLatchOnly ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Equiv2(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( 0, "Abc_CommandAbc9Equiv2(): There is no flops. Nothing is done.\n" );
        return 0;
    }
    if ( fUseCex )
    {
        if ( pAbc->pCex == NULL )
        {
            Abc_Print( 0, "Abc_CommandAbc9Equiv2(): Counter-example is not available.\n" );
            return 0;
        }
        if ( pAbc->pCex->nPis != Gia_ManPiNum(pAbc->pGia) )
        {
            Abc_Print( -1, "Abc_CommandAbc9Equiv2(): The number of PIs differs in cex (%d) and in AIG (%d).\n", 
                pAbc->pCex->nPis, Gia_ManPiNum(pAbc->pGia) );
            return 1;
        }
    }
    Ssw_SignalFilterGia( pAbc->pGia, nFramesMax, nConfMax, nRounds, TimeLimit, TimeLimit2, fUseCex? pAbc->pCex: NULL, fLatchOnly, fVerbose );
    pAbc->Status  = -1;
//    pAbc->nFrames = pAbc->pCex->iFrame;
//    Abc_FrameReplaceCex( pAbc, &pAbc->pCex );
    return 0;

usage:
    Abc_Print( -2, "usage: &equiv2 [-FCRTS num] [-xlvh]\n" );
    Abc_Print( -2, "\t         computes candidate equivalence classes\n" );
    Abc_Print( -2, "\t-F num : the max number of frames for BMC [default = %d]\n", nFramesMax );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-R num : the max number of BMC rounds [default = %d]\n", nRounds );
    Abc_Print( -2, "\t-T num : runtime limit in seconds for all rounds [default = %d]\n", TimeLimit );
    Abc_Print( -2, "\t-S num : runtime limit in seconds for one round [default = %d]\n", TimeLimit2 );
    Abc_Print( -2, "\t-x     : toggle using the current cex to perform refinement [default = %s]\n", fUseCex? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle considering only latch output equivalences [default = %s]\n", fLatchOnly? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Equiv3( Abc_Frame_t * pAbc, int argc, char ** argv )
{
//    extern int Ssw_RarSignalFilterGia2( Gia_Man_t * p, int nFrames, int nWords, int nBinSize, int nRounds, int TimeOut, Abc_Cex_t * pCex, int fLatchOnly, int fVerbose );
    extern int Ssw_RarSignalFilterGia( Gia_Man_t * p, int nFrames, int nWords, int nBinSize, int nRounds, int nRandSeed, int TimeOut, int fMiter, Abc_Cex_t * pCex, int fLatchOnly, int fVerbose );
    int c;
    int nFrames    =   20;
    int nWords     =   50;
    int nBinSize   =    8;
    int nRounds    =   80;
    int nRandSeed  =    0;
    int TimeOut    =    0;
    int fMiter     =    0;
    int fUseCex    =    0;
    int fLatchOnly =    0;
    int fNewAlgo   =    1;
    int fVerbose   =    0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FWBRNTmxlavh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrames < 0 ) 
                goto usage;
            break;
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nWords < 0 ) 
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            nBinSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nBinSize < 0 ) 
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRounds < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nRandSeed = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nRandSeed < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            TimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( TimeOut < 0 ) 
                goto usage;
            break;
        case 'm':
            fMiter ^= 1;
            break;
        case 'x':
            fUseCex ^= 1;
            break;
        case 'l':
            fLatchOnly ^= 1;
            break;
        case 'a':
            fNewAlgo ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    } 
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Equiv3(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( 0, "Abc_CommandAbc9Equiv3(): There is no flops. Nothing is done.\n" );
        return 0;
    }
    if ( fUseCex )
    {
        if ( fMiter )
        {
            Abc_Print( 0, "Abc_CommandAbc9Equiv3(): Considering the miter as a circuit because the CEX is given.\n" );
            fMiter = 0;
        }
        if ( pAbc->pCex == NULL )
        {
            Abc_Print( 0, "Abc_CommandAbc9Equiv3(): Counter-example is not available.\n" );
            return 0;
        }
        if ( pAbc->pCex->nPis != Gia_ManPiNum(pAbc->pGia) )
        {
            Abc_Print( -1, "Abc_CommandAbc9Equiv3(): The number of PIs differs in cex (%d) and in AIG (%d).\n", 
                pAbc->pCex->nPis, Gia_ManPiNum(pAbc->pGia) );
            return 1;
        }
    }
//    if ( fNewAlgo )
        pAbc->Status = Ssw_RarSignalFilterGia( pAbc->pGia, nFrames, nWords, nBinSize, nRounds, nRandSeed, TimeOut, fMiter, fUseCex? pAbc->pCex: NULL, fLatchOnly, fVerbose );
//    else
//        pAbc->Status = Ssw_RarSignalFilterGia2( pAbc->pGia, nFrames, nWords, nBinSize, nRounds, TimeOut, fUseCex? pAbc->pCex: NULL, fLatchOnly, fVerbose );
//    pAbc->nFrames = pAbc->pGia->pCexSeq->iFrame;
    if ( pAbc->pGia->pCexSeq )
        Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &equiv3 [-FWRNT num] [-mxlvh]\n" );
    Abc_Print( -2, "\t         computes candidate equivalence classes\n" );
    Abc_Print( -2, "\t-F num : the max number of frames for BMC [default = %d]\n",    nFrames );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n",     nWords );
//    Abc_Print( -2, "\t-B num : the number of flops in one bin [default = %d]\n",      nBinSize );
    Abc_Print( -2, "\t-R num : the max number of simulation rounds [default = %d]\n", nRounds );
    Abc_Print( -2, "\t-N num : random number seed (1 <= num <= 1000) [default = %d]\n", nRandSeed );
    Abc_Print( -2, "\t-T num : runtime limit in seconds for all rounds [default = %d]\n", TimeOut );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n",        fMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-x     : toggle using the current CEX to perform refinement [default = %s]\n", fUseCex? "yes": "no" );
    Abc_Print( -2, "\t-l     : toggle considering only latch output equivalences [default = %s]\n", fLatchOnly? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle using a new algorithm [default = %s]\n",        fNewAlgo? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Semi( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParSmf_t Pars, * pPars = &Pars;
    int c;
    Cec_ManSmfSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WRFSMCTmdvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWords < 0 ) 
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRounds < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFrames < 0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nNonRefines = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nNonRefines < 0 ) 
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nMinOutputs = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nMinOutputs < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBTLimit < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeLimit < 0 ) 
                goto usage;
            break;
        case 'm':
            pPars->fCheckMiter ^= 1;
            break;
        case 'd':
            pPars->fDualOut ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Resim(): There is no AIG.\n" );
        return 1;
    } 
    Cec_ManSeqSemiformal( pAbc->pGia, pPars );
    return 0;

usage:
    Abc_Print( -2, "usage: &semi [-WRFSMCT num] [-mdvh]\n" );
    Abc_Print( -2, "\t         performs semiformal refinement of equivalence classes\n" );
    Abc_Print( -2, "\t-W num : the number of words to simulate [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-R num : the max number of rounds to simulate [default = %d]\n", pPars->nRounds );
    Abc_Print( -2, "\t-F num : the max number of frames to unroll [default = %d]\n", pPars->nFrames );
    Abc_Print( -2, "\t-S num : the max number of rounds w/o refinement to stop [default = %d]\n", pPars->nNonRefines );
    Abc_Print( -2, "\t-M num : the min number of outputs of bounded SRM [default = %d]\n", pPars->nMinOutputs );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", pPars->fCheckMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-d     : toggle using two POs intead of XOR [default = %s]\n", pPars->fDualOut? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Times( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, nTimes = 2, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimes = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimes < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Times(): There is no AIG.\n" );
        return 1;
    } 
    pTemp = Gia_ManDupTimes( pAbc->pGia, nTimes );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &times [-N <num>] [-vh]\n" );
    Abc_Print( -2, "\t         creates several \"parallel\" copies of the design\n" );
    Abc_Print( -2, "\t-N num : number of copies to create [default = %d]\n", nTimes );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Frames( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManFrames2( Gia_Man_t * pAig, Gia_ParFra_t * pPars );

    Gia_Man_t * pTemp;
    Gia_ParFra_t Pars, * pPars = &Pars;
    int c;
    int nCofFanLit = 0;
    int nNewAlgo = 1;
    Gia_ManFraSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FLiavh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFrames < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            nCofFanLit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nCofFanLit < 0 ) 
                goto usage;
            break;
        case 'i':
            pPars->fInit ^= 1;
            break;
        case 'a':
            nNewAlgo ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Frames(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( nCofFanLit )
        pTemp = Gia_ManUnrollAndCofactor( pAbc->pGia, pPars->nFrames, nCofFanLit, pPars->fVerbose );
    else if ( nNewAlgo )
        pTemp = Gia_ManFrames2( pAbc->pGia, pPars );
    else 
        pTemp = Gia_ManFrames( pAbc->pGia, pPars );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &frames [-FL <num>] [-aivh]\n" );
    Abc_Print( -2, "\t         unrolls the design for several timeframes\n" );
    Abc_Print( -2, "\t-F num : the number of frames to unroll [default = %d]\n", pPars->nFrames );
    Abc_Print( -2, "\t-L num : the limit on fanout count of resets/enables to cofactor [default = %d]\n", nCofFanLit );
    Abc_Print( -2, "\t-i     : toggle initializing registers [default = %s]\n", pPars->fInit? "yes": "no" );
    Abc_Print( -2, "\t-a     : toggle using new algorithm [default = %s]\n", nNewAlgo? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Retime( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c;
    int nMaxIters = 100;
    int fVerbose  =   0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nMaxIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nMaxIters < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Retime(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    pTemp = Gia_ManRetimeForward( pAbc->pGia, nMaxIters, fVerbose );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &retime [-N <num>] [-vh]\n" );
    Abc_Print( -2, "\t         performs most-forward retiming\n" );
    Abc_Print( -2, "\t-N num : the number of incremental iterations [default = %d]\n", nMaxIters );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Enable( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c;
    int fRemove  = 0;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "rvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'r':
            fRemove ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Enable(): There is no AIG.\n" );
        return 1;
    } 
    if ( fRemove )
        pTemp = Gia_ManRemoveEnables( pAbc->pGia );
    else
        pTemp = Gia_ManDupSelf( pAbc->pGia );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &enable [-rvh]\n" );
    Abc_Print( -2, "\t         adds or removes flop enable signals\n" );
    Abc_Print( -2, "\t-r     : toggle adding vs. removing enables [default = %s]\n", fRemove? "remove": "add" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Dc2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, fVerbose = 0;
    int fUpdateLevel = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Dc2(): There is no AIG.\n" );
        return 1;
    } 
    pTemp = Gia_ManCompress2( pAbc->pGia, fUpdateLevel, fVerbose );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &dc2 [-lvh]\n" );
    Abc_Print( -2, "\t         performs heavy rewriting of the AIG\n" );
    Abc_Print( -2, "\t-l     : toggle level update during rewriting [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Bidec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c, fVerbose = 0;
    int fUpdateLevel = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUpdateLevel ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Bidec(): There is no AIG.\n" );
        return 1;
    } 
    if ( pAbc->pGia->pMapping == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Bidec(): Mapping of the AIG is not defined.\n" );
        return 1;
    }
    pTemp = Gia_ManPerformBidec( pAbc->pGia, fVerbose );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &bidec [-vh]\n" );
    Abc_Print( -2, "\t         performs heavy rewriting of the AIG\n" );
//    Abc_Print( -2, "\t-l     : toggle level update during rewriting [default = %s]\n", fUpdateLevel? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Shrink( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c,fVerbose = 0;
    int fKeepLevel = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fKeepLevel ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Shrink(): There is no AIG.\n" );
        return 1;
    } 
    if ( pAbc->pGia->pMapping == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Shrink(): Mapping of the AIG is not defined.\n" );
        return 1;
    }
    pTemp = Gia_ManPerformMapShrink( pAbc->pGia, fKeepLevel, fVerbose );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &shrink [-lvh]\n" );
    Abc_Print( -2, "\t         performs fast shrinking using current mapping\n" );
    Abc_Print( -2, "\t-l     : toggle level update during shrinking [default = %s]\n", fKeepLevel? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Miter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    FILE * pFile;
    Gia_Man_t * pAux;
    Gia_Man_t * pSecond;
    char * FileName, * pTemp;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fDualOut = 0;
    int fSeq     = 0;
    int fTrans   = 0;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "dstvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDualOut ^= 1;
            break;
        case 's':
            fSeq ^= 1;
            break;
        case 't':
            fTrans ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( fTrans )
    {
        if ( (Gia_ManPoNum(pAbc->pGia) & 1) == 1 )
        {
            Abc_Print( -1, "Abc_CommandAbc9Miter(): The number of outputs should be even.\n" );
            return 0;
        }
        pAbc->pGia = Gia_ManTransformMiter( pAux = pAbc->pGia );
        Gia_ManStop( pAux );
        Abc_Print( 1, "The miter (current AIG) is transformed by XORing POs pair-wise.\n" );
        return 0;
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "File name is not given on the command line.\n" );
        return 1;
    }

    // get the input file name
    FileName = pArgvNew[0];
    // fix the wrong symbol
    for ( pTemp = FileName; *pTemp; pTemp++ )
        if ( *pTemp == '>' )
            *pTemp = '\\';
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".aig", NULL, NULL, NULL, NULL )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );
    pSecond = Gia_ReadAiger( FileName, 0 );
    if ( pSecond == NULL )
    {
        Abc_Print( -1, "Reading AIGER has failed.\n" );
        return 0;
    }
    // compute the miter
    pAux = Gia_ManMiter( pAbc->pGia, pSecond, fDualOut, fSeq, fVerbose );
    Gia_ManStop( pSecond );
    Abc_CommandUpdate9( pAbc, pAux );
    return 0;

usage:
    Abc_Print( -2, "usage: &miter [-dstvh] <file>\n" );
    Abc_Print( -2, "\t         creates miter of two designs (current AIG vs. <file>)\n" );
    Abc_Print( -2, "\t-d     : toggle creating dual output miter [default = %s]\n", fDualOut? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle creating sequential miter [default = %s]\n", fSeq? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle XORing pair-wise POs of the miter [default = %s]\n", fTrans? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    Abc_Print( -2, "\t<file> : AIGER file with the design to miter\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Scl( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int c;
    int fConst = 1;
    int fEquiv = 1;
    int fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "cevh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'c':
            fConst ^= 1;
            break;
        case 'e':
            fEquiv ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Scl(): There is no AIG.\n" );
        return 1;
    } 
    pTemp = Gia_ManSeqStructSweep( pAbc->pGia, fConst, fEquiv, fVerbose );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &scl [-cevh]\n" );
    Abc_Print( -2, "\t         performs structural sequential cleanup\n" );
    Abc_Print( -2, "\t-c     : toggle removing stuck-at constant registers [default = %s]\n", fConst? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle removing equivalent-driver registers [default = %s]\n", fEquiv? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Lcorr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParCor_t Pars, * pPars = &Pars;
    Gia_Man_t * pTemp;
    int c;
    Cec_ManCorSetDefaultParams( pPars );
    pPars->fLatchCorr = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCPrcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFrames < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBTLimit < 0 ) 
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPrefix = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPrefix < 0 ) 
                goto usage;
            break;
        case 'r':
            pPars->fUseRings ^= 1;
            break;
        case 'c':
            pPars->fUseCSat ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Lcorr(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    pTemp = Cec_ManLSCorrespondence( pAbc->pGia, pPars );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &lcorr [-FCP num] [-rcvh]\n" );
    Abc_Print( -2, "\t         performs latch correpondence computation\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-F num : the number of timeframes in inductive case [default = %d]\n", pPars->nFrames );
    Abc_Print( -2, "\t-P num : the number of timeframes in the prefix [default = %d]\n", pPars->nPrefix );
    Abc_Print( -2, "\t-r     : toggle using implication rings during refinement [default = %s]\n", pPars->fUseRings? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using circuit-based SAT solver [default = %s]\n", pPars->fUseCSat? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Scorr( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParCor_t Pars, * pPars = &Pars;
    Gia_Man_t * pTemp;
    int c;
    Cec_ManCorSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCPkrecwvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFrames = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFrames < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBTLimit < 0 ) 
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPrefix = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPrefix < 0 ) 
                goto usage;
            break;
        case 'k':
            pPars->fConstCorr ^= 1;
            break;
        case 'r':
            pPars->fUseRings ^= 1;
            break;
        case 'e':
            pPars->fMakeChoices ^= 1;
            break;
        case 'c':
            pPars->fUseCSat ^= 1;
            break;
        case 'w':
            pPars->fVerboseFlops ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Scorr(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    pTemp = Cec_ManLSCorrespondence( pAbc->pGia, pPars );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &scorr [-FCP num] [-krecwvh]\n" );
    Abc_Print( -2, "\t         performs signal correpondence computation\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-F num : the number of timeframes in inductive case [default = %d]\n", pPars->nFrames );
    Abc_Print( -2, "\t-P num : the number of timeframes in the prefix [default = %d]\n", pPars->nPrefix );
    Abc_Print( -2, "\t-k     : toggle using constant correspondence [default = %s]\n", pPars->fConstCorr? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle using implication rings during refinement [default = %s]\n", pPars->fUseRings? "yes": "no" );
    Abc_Print( -2, "\t-e     : toggle using equivalences as choices [default = %s]\n", pPars->fMakeChoices? "yes": "no" );
    Abc_Print( -2, "\t-c     : toggle using circuit-based SAT solver [default = %s]\n", pPars->fUseCSat? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing verbose info about equivalent flops [default = %s]\n", pPars->fVerboseFlops? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Choice( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParChc_t Pars, * pPars = &Pars;
    Gia_Man_t * pTemp;
    int c;
    Cec_ManChcSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Ccvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBTLimit < 0 ) 
                goto usage;
            break;
        case 'c':
            pPars->fUseCSat ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Choice(): There is no AIG.\n" );
        return 1;
    } 
    pTemp = Cec_ManChoiceComputation( pAbc->pGia, pPars );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &choice [-C num] [-cvh]\n" );
    Abc_Print( -2, "\t         performs computation of structural choices\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-c     : toggle using circuit-based SAT solver [default = %s]\n", pPars->fUseCSat? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Sat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParSat_t ParsSat, * pPars = &ParsSat;
    Gia_Man_t * pTemp;
    int c;
    int fCSat = 0;
    Cec_ManSatSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CSNnmtcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBTLimit < 0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSatVarMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSatVarMax < 0 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nCallsRecycle = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCallsRecycle < 0 ) 
                goto usage;
            break;
        case 'n':
            pPars->fNonChrono ^= 1;
            break;
        case 'm':
            pPars->fCheckMiter ^= 1;
            break;
        case 't':
            pPars->fLearnCls ^= 1;
            break;
        case 'c':
            fCSat ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Sat(): There is no AIG.\n" );
        return 1;
    } 
    if ( fCSat )
    {
        Vec_Int_t * vCounters;
        Vec_Str_t * vStatus;
        if ( pPars->fLearnCls )
            vCounters = Tas_ManSolveMiterNc( pAbc->pGia, pPars->nBTLimit, &vStatus, pPars->fVerbose );
        else if ( pPars->fNonChrono )
            vCounters = Cbs_ManSolveMiterNc( pAbc->pGia, pPars->nBTLimit, &vStatus, pPars->fVerbose );
        else
            vCounters = Cbs_ManSolveMiter( pAbc->pGia, pPars->nBTLimit, &vStatus, pPars->fVerbose );
        Vec_IntFree( vCounters );
        Vec_StrFree( vStatus );
    }
    else
    {
        pTemp = Cec_ManSatSolving( pAbc->pGia, pPars );
        Abc_CommandUpdate9( pAbc, pTemp );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &sat [-CSN <num>] [-nmctvh]\n" );
    Abc_Print( -2, "\t         performs SAT solving for the combinational outputs\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-S num : the min number of variables to recycle the solver [default = %d]\n", pPars->nSatVarMax );
    Abc_Print( -2, "\t-N num : the min number of calls to recycle the solver [default = %d]\n", pPars->nCallsRecycle );
    Abc_Print( -2, "\t-n     : toggle using non-chronological backtracking [default = %s]\n", pPars->fNonChrono? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", pPars->fCheckMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-c     : toggle using circuit-based SAT solver [default = %s]\n", fCSat? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle using learning in curcuit-based solver [default = %s]\n", pPars->fLearnCls? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Fraig( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParFra_t ParsFra, * pPars = &ParsFra;
    Gia_Man_t * pTemp;
    int c;
    Cec_ManFraSetDefaultParams( pPars );
    pPars->fSatSweeping = 1;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WRILDCrmdwvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWords < 0 ) 
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRounds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRounds < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nItersMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nItersMax < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nLevelMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLevelMax < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nDepthMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDepthMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBTLimit < 0 ) 
                goto usage;
            break;
        case 'r':
            pPars->fRewriting ^= 1;
            break;
        case 'm':
            pPars->fCheckMiter ^= 1;
            break;
        case 'd':
            pPars->fDualOut ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Fraig(): There is no AIG.\n" );
        return 1;
    } 
    pTemp = Cec_ManSatSweeping( pAbc->pGia, pPars );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &fraig [-WRILDC <num>] [-rmdwvh]\n" );
    Abc_Print( -2, "\t         performs combinational SAT sweeping\n" );
    Abc_Print( -2, "\t-W num : the number of simulation words [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-R num : the number of simulation rounds [default = %d]\n", pPars->nRounds );
    Abc_Print( -2, "\t-I num : the number of sweeping iterations [default = %d]\n", pPars->nItersMax );
    Abc_Print( -2, "\t-L num : the max number of levels of nodes to consider [default = %d]\n", pPars->nLevelMax );
    Abc_Print( -2, "\t-D num : the max number of steps of speculative reduction [default = %d]\n", pPars->nDepthMax );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-r     : toggle the use of AIG rewriting [default = %s]\n", pPars->fRewriting? "yes": "no" );
    Abc_Print( -2, "\t-m     : toggle miter vs. any circuit [default = %s]\n", pPars->fCheckMiter? "miter": "circuit" );
    Abc_Print( -2, "\t-d     : toggle using double output miters [default = %s]\n", pPars->fDualOut? "yes": "no" );
    Abc_Print( -2, "\t-w     : toggle printing even more verbose information [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Srm( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char pFileName[10] = "gsrm.aig", pFileName2[10] = "gsyn.aig";
    Gia_Man_t * pTemp, * pAux;
    int c, fVerbose = 0;
    int fSynthesis = 0;
    int fSpeculate = 1;
    int fSkipSome = 0;
    int fDualOut = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "drsfvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'd':
            fDualOut ^= 1;
            break;
        case 'r':
            fSynthesis ^= 1;
            break;
        case 's':
            fSpeculate ^= 1;
            break;
        case 'f':
            fSkipSome ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Srm(): There is no AIG.\n" );
        return 1;
    } 
    sprintf( pFileName,  "gsrm%s.aig", fSpeculate? "" : "s" );
    sprintf( pFileName2, "gsyn%s.aig", fSpeculate? "" : "s" );
    pTemp = Gia_ManSpecReduce( pAbc->pGia, fDualOut, fSynthesis, fSpeculate, fSkipSome, fVerbose );
    if ( pTemp )
    {
        if ( fSpeculate )
        {
            pTemp = Gia_ManSeqStructSweep( pAux = pTemp, 1, 1, 0 );
            Gia_ManStop( pAux );
        }
        Gia_WriteAiger( pTemp, pFileName, 0, 0 );
        Abc_Print( 1, "Speculatively reduced model was written into file \"%s\".\n", pFileName );
        Gia_ManPrintStatsShort( pTemp );
        Gia_ManStop( pTemp );
    }
    if ( fSynthesis )
    {
        pTemp = Gia_ManEquivReduce( pAbc->pGia, 1, fDualOut, fVerbose );
        if ( pTemp )
        {
            pTemp = Gia_ManSeqStructSweep( pAux = pTemp, 1, 1, 0 );
            Gia_ManStop( pAux );

            Gia_WriteAiger( pTemp, pFileName2, 0, 0 );
            Abc_Print( 1, "Reduced original network was written into file \"%s\".\n", pFileName2 );
            Gia_ManPrintStatsShort( pTemp );
            Gia_ManStop( pTemp );
        }
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &srm [-drsfvh]\n" );
    Abc_Print( -2, "\t         writes speculatively reduced model into file \"%s\"\n", pFileName );
    Abc_Print( -2, "\t-d     : toggle creating dual output miter [default = %s]\n", fDualOut? "yes": "no" );
    Abc_Print( -2, "\t-r     : toggle writing reduced network for synthesis [default = %s]\n", fSynthesis? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle using speculation at the internal nodes [default = %s]\n", fSpeculate? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle filtering to remove redundant equivalences [default = %s]\n", fSkipSome? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Srm2( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char pFileName[10], * pFileName1, * pFileName2;
    Gia_Man_t * pTemp, * pAux;
    int fLatchA = 0, fLatchB = 0;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "abvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fLatchA ^= 1;
            break;
        case 'b':
            fLatchB ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Srm2(): There is no AIG.\n" );
        return 1;
    }
    if ( pAbc->pGia->pReprs == NULL || pAbc->pGia->pNexts == NULL )
    {
        Abc_Print( -1, "Equivalences are not defined.\n" );
        return 0;
    }
    if ( argc != globalUtilOptind + 2 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Srm2(): Expecting two file names on the command line.\n" );
        return 1;
    }
    // get the input file name
    pFileName1 = argv[globalUtilOptind];
    pFileName2 = argv[globalUtilOptind+1];
    // create file name 
    sprintf( pFileName,  "gsrm.aig" );
    pTemp = Gia_ManDup( pAbc->pGia );
    // copy equivalences
    pTemp->pReprs = ABC_ALLOC( Gia_Rpr_t, Gia_ManObjNum(pTemp) );
    memcpy( pTemp->pReprs, pAbc->pGia->pReprs, sizeof(Gia_Rpr_t) * Gia_ManObjNum(pTemp) );
    pTemp->pNexts = ABC_ALLOC( int, Gia_ManObjNum(pTemp) );
    memcpy( pTemp->pNexts, pAbc->pGia->pNexts, sizeof(int) * Gia_ManObjNum(pTemp) );
//Gia_ManPrintStats( pTemp, 0 );
    // filter the classes
    if ( !Gia_ManFilterEquivsForSpeculation( pTemp, pFileName1, pFileName2, fLatchA, fLatchB ) )
    {
        Gia_ManStop( pTemp );
        Abc_Print( -1, "Filtering equivalences has failed.\n" );
        return 1;
    }
//Gia_ManPrintStats( pTemp, 0 );
    pTemp = Gia_ManSpecReduce( pAux = pTemp, 0, 0, 1, 0, 0 );
    Gia_ManStop( pAux );
    if ( pTemp )
    {
        pTemp = Gia_ManSeqStructSweep( pAux = pTemp, 1, 1, 0 );
        Gia_ManStop( pAux );

        Gia_WriteAiger( pTemp, pFileName, 0, 0 );
        Abc_Print( 1, "Speculatively reduced model was written into file \"%s\".\n", pFileName );
        Gia_ManPrintStatsShort( pTemp );
        Gia_ManStop( pTemp );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &srm2 [-abvh] <PartA_FileName> <PartB_FileName>\n" );
    Abc_Print( -2, "\t         writes speculatively reduced model into file \"%s\"\n", pFileName );
    Abc_Print( -2, "\t         only preserves equivalences across PartA and PartB\n" );
    Abc_Print( -2, "\t-a     : toggle using latches only in PartA [default = %s]\n", fLatchA? "yes": "no" );
    Abc_Print( -2, "\t-b     : toggle using latches only in PartB [default = %s]\n", fLatchB? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Filter( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pFileName1 = NULL, * pFileName2 = NULL;
    int fFlopsOnly = 0, fFlopsWith = 0;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "fgvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            fFlopsOnly ^= 1;
            break;
        case 'g':
            fFlopsWith ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Srm2(): There is no AIG.\n" );
        return 1;
    }
    if ( pAbc->pGia->pReprs == NULL || pAbc->pGia->pNexts == NULL )
    {
        Abc_Print( -1, "Equivalences are not defined.\n" );
        return 0;
    }
    if ( argc != globalUtilOptind && argc != globalUtilOptind + 2 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Srm2(): Expecting two file names on the command line.\n" );
        return 1;
    }
    // filter using one of the choices
    if ( fFlopsOnly ^ fFlopsWith )
        Gia_ManFilterEquivsUsingLatches( pAbc->pGia, fFlopsOnly, fFlopsWith );
    // get the input file name
    if ( argc == globalUtilOptind + 2 )
    {
        pFileName1 = argv[globalUtilOptind];
        pFileName2 = argv[globalUtilOptind+1];
        if ( !Gia_ManFilterEquivsUsingParts( pAbc->pGia, pFileName1, pFileName2 ) )
        {
            Abc_Print( -1, "Filtering equivalences using PartA and PartB has failed.\n" );
            return 1;
        }
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &filter [-fgvh] <PartA_FileName> <PartB_FileName>\n" );
    Abc_Print( -2, "\t         performs filtering of equivalence classes\n" );
    Abc_Print( -2, "\t         (if Parts A/B are given, removes classes composed of one part)\n" );
    Abc_Print( -2, "\t-f     : toggle removing all elements except flops [default = %s]\n", fFlopsOnly? "yes": "no" );
    Abc_Print( -2, "\t-g     : toggle removing removing classes without flops [default = %s]\n", fFlopsWith? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Reduce( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp, * pTemp2;
    int c, fVerbose = 0;
    int fUseAll = 0;
    int fDualOut = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "advh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fUseAll ^= 1;
            break;
        case 'd':
            fDualOut ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Reduce(): There is no AIG.\n" );
        return 1;
    } 
    if ( fUseAll )
    {
        pTemp = Gia_ManEquivReduce( pAbc->pGia, fUseAll, fDualOut, fVerbose );
        pTemp = Gia_ManSeqStructSweep( pTemp2 = pTemp, 1, 1, 0 );
        Gia_ManStop( pTemp2 );
    }
    else
        pTemp = Gia_ManEquivReduceAndRemap( pAbc->pGia, 1, fDualOut );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &reduce [-advh]\n" );
    Abc_Print( -2, "\t         reduces the circuit using equivalence classes\n" );
    Abc_Print( -2, "\t-a     : toggle merging all equivalences [default = %s]\n", fUseAll? "yes": "no" );
    Abc_Print( -2, "\t-d     : toggle using dual-output merging [default = %s]\n", fDualOut? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9EquivMark( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern void Gia_ManEquivMark( Gia_Man_t * p, char * pFileName, int fSkipSome, int fVerbose );
    char * pFileName;
    int c, fVerbose = 0;
    int fSkipSome = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "fvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'f':
            fSkipSome ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Reduce(): There is no AIG.\n" );
        return 1;
    } 
    if ( argc != globalUtilOptind + 1 )
        goto usage;
    // get the input file name
    pFileName = argv[globalUtilOptind];
    // mark equivalences
    Gia_ManEquivMark( pAbc->pGia, pFileName, fSkipSome, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &equiv_mark [-fvh] <miter.aig>\n" );
    Abc_Print( -2, "\t              marks equivalences using an external miter\n" );
    Abc_Print( -2, "\t-f          : toggle the use of filtered equivalences [default = %s]\n", fSkipSome? "yes": "no" );
    Abc_Print( -2, "\t-v          : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h          : print the command usage\n");
    Abc_Print( -2, "\t<miter.aig> : file with the external miter to read\n");
    Abc_Print( -2, "\t              \n" );
    Abc_Print( -2, "\t              The external miter should be generated by &srm -s\n" );
    Abc_Print( -2, "\t              and (partially) solved by any verification engine(s).\n" );
    Abc_Print( -2, "\t              The external miter should have as many POs as\n" );
    Abc_Print( -2, "\t              the number of POs in the current AIG plus\n" );
    Abc_Print( -2, "\t              the number of equivalences in the current AIG.\n" );
    Abc_Print( -2, "\t              If some POs are proved, the corresponding equivs\n" );
    Abc_Print( -2, "\t              are marked as proved, to be reduced by &reduce.\n" );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Cec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Cec_ParCec_t ParsCec, * pPars = &ParsCec;
    FILE * pFile;
    Gia_Man_t * pSecond, * pMiter;
    char * FileName, * pTemp;
    char ** pArgvNew;
    int c, nArgcNew, fMiter = 0;
    Cec_ManCecSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "CTmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBTLimit < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeLimit < 0 ) 
                goto usage;
            break;
        case 'm':
            fMiter ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( fMiter )
    {
        if ( Gia_ManPoNum(pAbc->pGia) & 1 )
        {
            Abc_Print( -1, "The dual-output miter should have an even number of outputs.\n" );
            return 1;
        }
        Abc_Print( 1, "Assuming the current network is a double-output miter. (Conflict limit = %d.)\n", pPars->nBTLimit );
        Cec_ManVerify( pAbc->pGia, pPars );
        return 0;
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( nArgcNew != 1 )
    {
        Abc_Print( -1, "File name is not given on the command line.\n" );
        return 1;
    }

    // get the input file name
    FileName = pArgvNew[0];
    // fix the wrong symbol
    for ( pTemp = FileName; *pTemp; pTemp++ )
        if ( *pTemp == '>' )
            *pTemp = '\\';
    if ( (pFile = fopen( FileName, "r" )) == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\". ", FileName );
        if ( (FileName = Extra_FileGetSimilarName( FileName, ".aig", NULL, NULL, NULL, NULL )) )
            Abc_Print( 1, "Did you mean \"%s\"?", FileName );
        Abc_Print( 1, "\n" );
        return 1;
    }
    fclose( pFile );
    pSecond = Gia_ReadAiger( FileName, 0 );
    if ( pSecond == NULL )
    {
        Abc_Print( -1, "Reading AIGER has failed.\n" );
        return 0;
    }
    // compute the miter
    pMiter = Gia_ManMiter( pAbc->pGia, pSecond, 1, 0, pPars->fVerbose );
    if ( pMiter )
    {
        Cec_ManVerify( pMiter, pPars );
        Gia_ManStop( pMiter );
    }
    Gia_ManStop( pSecond );
    return 0;

usage:
    Abc_Print( -2, "usage: &cec [-CT num] [-mvh]\n" );
    Abc_Print( -2, "\t         new combinational equivalence checker\n" );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-m     : toggle miter vs. two circuits [default = %s]\n", fMiter? "miter":"two circuits");
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes":"no");
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Force( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int nIters     = 20;
    int fClustered =  1;
    int fVerbose   =  1;
    int c;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Icvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nIters < 0 ) 
                goto usage;
            break;
        case 'c':
            fClustered ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Force(): There is no AIG.\n" );
        return 1;
    } 
    For_ManExperiment( pAbc->pGia, nIters, fClustered, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &force [-I <num>] [-cvh]\n" );
    Abc_Print( -2, "\t         one-dimensional placement algorithm FORCE introduced by\n" );
    Abc_Print( -2, "\t         F. A. Aloul, I. L. Markov, and K. A. Sakallah (GLSVLSI�03).\n" );
    Abc_Print( -2, "\t-I num : the number of refinement iterations [default = %d]\n", nIters );
    Abc_Print( -2, "\t-c     : toggle clustered representation [default = %s]\n", fClustered? "yes":"no");
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes":"no");
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Embed( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Emb_Par_t Pars, * pPars = &Pars;
    int c;
    pPars->nDims      = 30;
    pPars->nIters     = 10;
    pPars->nSols      =  2;
    pPars->fRefine    =  0; 
    pPars->fCluster   =  0;
    pPars->fDump      =  0; 
    pPars->fDumpLarge =  0; 
    pPars->fShowImage =  0;
    pPars->fVerbose   =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "DIrcdlsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nDims = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nDims < 0 ) 
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIters < 0 ) 
                goto usage;
            break;
        case 'r':
            pPars->fRefine ^= 1;
            break;
        case 'c':
            pPars->fCluster ^= 1;
            break;
        case 'd':
            pPars->fDump ^= 1;
            break;
        case 'l':
            pPars->fDumpLarge ^= 1;
            break;
        case 's': 
            pPars->fShowImage ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Embed(): There is no AIG.\n" );
        return 1;
    } 
    Gia_ManSolveProblem( pAbc->pGia, pPars );
    return 0;

usage:
    Abc_Print( -2, "usage: &embed [-DI <num>] [-rdlscvh]\n" );
    Abc_Print( -2, "\t         fast placement based on high-dimensional embedding from\n" );
    Abc_Print( -2, "\t         D. Harel and Y. Koren, \"Graph drawing by high-dimensional\n" );
    Abc_Print( -2, "\t         embedding\", J. Graph Algs & Apps, 2004, Vol 8(2), pp. 195-217\n" );
    Abc_Print( -2, "\t-D num : the number of dimensions for embedding [default = %d]\n", pPars->nDims );
    Abc_Print( -2, "\t-I num : the number of refinement iterations [default = %d]\n", pPars->nIters );
    Abc_Print( -2, "\t-r     : toggle the use of refinement [default = %s]\n", pPars->fRefine? "yes":"no");
    Abc_Print( -2, "\t-c     : toggle clustered representation [default = %s]\n", pPars->fCluster? "yes":"no");
    Abc_Print( -2, "\t-d     : toggle dumping placement into a Gnuplot file [default = %s]\n", pPars->fDump? "yes":"no");
    Abc_Print( -2, "\t-l     : toggle dumping Gnuplot for large placement [default = %s]\n", pPars->fDumpLarge? "yes":"no");
    Abc_Print( -2, "\t-s     : toggle showing image if Gnuplot is installed [default = %s]\n", pPars->fShowImage? "yes":"no");
    Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", pPars->fVerbose? "yes":"no");
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9If( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[200];
    char LutSize[200];
    If_Par_t Pars, * pPars = &Pars;
    int c;
    extern void Gia_ManSetIfParsDefault( If_Par_t * pPars );
    extern int Gia_MappingIf( Gia_Man_t * p, If_Par_t * pPars );
    // set defaults
    Gia_ManSetIfParsDefault( pPars );
//    if ( pAbc->pAbc8Lib == NULL )
//    {
//        Abc_Print( -1, "LUT library is not given. Using default LUT library.\n" );
//        pAbc->pAbc8Lib = If_SetSimpleLutLib( 6 );
//    }
//    pPars->pLutLib = pAbc->pAbc8Lib;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "KCFADEqaflepmrsdbvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'K':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-K\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nLutSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nLutSize < 0 ) 
                goto usage;
            // if the LUT size is specified, disable library
            pPars->pLutLib = NULL; 
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nCutsMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nCutsMax < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nFlowIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFlowIters < 0 ) 
                goto usage;
            break;
        case 'A':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-A\" should be followed by a positive integer.\n" );
                goto usage;
            }
            pPars->nAreaIters = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nAreaIters < 0 ) 
                goto usage;
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->DelayTarget = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->DelayTarget <= 0.0 ) 
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-E\" should be followed by a floating point number.\n" );
                goto usage;
            }
            pPars->Epsilon = (float)atof(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->Epsilon < 0.0 || pPars->Epsilon > 1.0 ) 
                goto usage;
            break;
        case 'q':
            pPars->fPreprocess ^= 1;
            break;
        case 'a':
            pPars->fArea ^= 1;
            break;
        case 'r':
            pPars->fExpRed ^= 1;
            break;
        case 'f':
            pPars->fFancy ^= 1;
            break;
        case 'l':
            pPars->fLatchPaths ^= 1;
            break;
        case 'e':
            pPars->fEdge ^= 1;
            break;
        case 'p':
            pPars->fPower ^= 1;
            break;
        case 'm':
            pPars->fCutMin ^= 1;
            break;
        case 's':
            pPars->fSeqMap ^= 1;
            break;
        case 'd':
            pPars->fBidec ^= 1;
            break;
        case 'b':
            pPars->fUseBat ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9If(): There is no AIG to map.\n" );
        return 1;
    }

    if ( pPars->nLutSize < 3 || pPars->nLutSize > IF_MAX_LUTSIZE )
    {
        Abc_Print( -1, "Incorrect LUT size (%d).\n", pPars->nLutSize );
        return 1;
    }

    if ( pPars->nCutsMax < 1 || pPars->nCutsMax >= (1<<12) )
    {
        Abc_Print( -1, "Incorrect number of cuts.\n" );
        return 1;
    }

    // enable truth table computation if choices are selected
    if ( (c = Gia_ManCountChoiceNodes( pAbc->pGia )) )
    {
        Abc_Print( 0, "Performing LUT mapping with %d choices.\n", c );
        pPars->fExpRed = 0;
    }

    if ( pPars->fUseBat )
    {
        if ( pPars->nLutSize < 4 || pPars->nLutSize > 6 )
        {
            Abc_Print( -1, "This feature only works for {4,5,6}-LUTs.\n" );
            return 1;
        }
        pPars->fCutMin = 1;            
    }

    // enable truth table computation if cut minimization is selected
    if ( pPars->fCutMin )
    {
        pPars->fTruth = 1;
        pPars->fExpRed = 0;
    }

    // complain if truth tables are requested but the cut size is too large
    if ( pPars->fTruth && pPars->nLutSize > IF_MAX_FUNC_LUTSIZE )
    {
        Abc_Print( -1, "Truth tables cannot be computed for LUT larger than %d inputs.\n", IF_MAX_FUNC_LUTSIZE );
        return 1;
    }

    if ( !Gia_MappingIf( pAbc->pGia, pPars ) )
    {
        Abc_Print( -1, "Abc_CommandAbc9If(): Mapping of the AIG has failed.\n" );
        return 1;
    }
    return 0;

usage:
    if ( pPars->DelayTarget == -1 ) 
        sprintf( Buffer, "best possible" );
    else
        sprintf( Buffer, "%.2f", pPars->DelayTarget );
    if ( pPars->nLutSize == -1 ) 
        sprintf( LutSize, "library" );
    else
        sprintf( LutSize, "%d", pPars->nLutSize );
    Abc_Print( -2, "usage: &if [-KCFA num] [-DE float] [-qarlepmdbvh]\n" );
    Abc_Print( -2, "\t           performs FPGA technology mapping of the network\n" );
    Abc_Print( -2, "\t-K num   : the number of LUT inputs (2 < num < %d) [default = %s]\n", IF_MAX_LUTSIZE+1, LutSize );
    Abc_Print( -2, "\t-C num   : the max number of priority cuts (0 < num < 2^12) [default = %d]\n", pPars->nCutsMax );
    Abc_Print( -2, "\t-F num   : the number of area flow recovery iterations (num >= 0) [default = %d]\n", pPars->nFlowIters );
    Abc_Print( -2, "\t-A num   : the number of exact area recovery iterations (num >= 0) [default = %d]\n", pPars->nAreaIters );
    Abc_Print( -2, "\t-D float : sets the delay constraint for the mapping [default = %s]\n", Buffer );  
    Abc_Print( -2, "\t-E float : sets epsilon used for tie-breaking [default = %f]\n", pPars->Epsilon );  
    Abc_Print( -2, "\t-q       : toggles preprocessing using several starting points [default = %s]\n", pPars->fPreprocess? "yes": "no" );
    Abc_Print( -2, "\t-a       : toggles area-oriented mapping [default = %s]\n", pPars->fArea? "yes": "no" );
//    Abc_Print( -2, "\t-f       : toggles one fancy feature [default = %s]\n", pPars->fFancy? "yes": "no" );
    Abc_Print( -2, "\t-r       : enables expansion/reduction of the best cuts [default = %s]\n", pPars->fExpRed? "yes": "no" );
    Abc_Print( -2, "\t-l       : optimizes latch paths for delay, other paths for area [default = %s]\n", pPars->fLatchPaths? "yes": "no" );
    Abc_Print( -2, "\t-e       : uses edge-based cut selection heuristics [default = %s]\n", pPars->fEdge? "yes": "no" );
    Abc_Print( -2, "\t-p       : uses power-aware cut selection heuristics [default = %s]\n", pPars->fPower? "yes": "no" );
    Abc_Print( -2, "\t-m       : enables cut minimization by removing vacuous variables [default = %s]\n", pPars->fCutMin? "yes": "no" );
//    Abc_Print( -2, "\t-s       : toggles sequential mapping [default = %s]\n", pPars->fSeqMap? "yes": "no" );
    Abc_Print( -2, "\t-d       : toggles deriving local AIGs using bi-decomposition [default = %s]\n", pPars->fBidec? "yes": "no" );
    Abc_Print( -2, "\t-b       : toggles the use of one special feature [default = %s]\n", pPars->fUseBat? "yes": "no" );
    Abc_Print( -2, "\t-v       : toggles verbose output [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : prints the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Trace( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int fUseLutLib;
    int fVerbose;
    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fUseLutLib = 0;
    fVerbose   = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "lvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'l':
            fUseLutLib ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Speedup(): There is no AIG to map.\n" );
        return 1;
    }
    if ( pAbc->pGia->pMapping == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Speedup(): Mapping of the AIG is not defined.\n" );
        return 1;
    }
    pAbc->pGia->pLutLib = fUseLutLib ? pAbc->pLibLut : NULL;
    Gia_ManDelayTraceLutPrint( pAbc->pGia, fVerbose );
    return 0;

usage:
    Abc_Print( -2, "usage: &trace [-lvh]\n" );
    Abc_Print( -2, "\t           performs delay trace of LUT-mapped network\n" );
    Abc_Print( -2, "\t-l       : toggle using unit- or LUT-library-delay model [default = %s]\n", fUseLutLib? "lib": "unit" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Speedup( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    int fUseLutLib;
    int Percentage;
    int Degree;
    int fVerbose;
    int c, fVeryVerbose;

    // set defaults
    fUseLutLib   = 0;
    Percentage   = 5;
    Degree       = 2;
    fVerbose     = 0;
    fVeryVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "PNlvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            Percentage = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Percentage < 1 || Percentage > 100 ) 
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            Degree = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( Degree < 1 || Degree > 5 ) 
                goto usage;
            break;
        case 'l':
            fUseLutLib ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'w':
            fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Speedup(): There is no AIG to map.\n" );
        return 1;
    }
    if ( pAbc->pGia->pMapping == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Speedup(): Mapping of the AIG is not defined.\n" );
        return 1;
    }
    pAbc->pGia->pLutLib = fUseLutLib ? pAbc->pLibLut : NULL;
    pTemp = Gia_ManSpeedup( pAbc->pGia, Percentage, Degree, fVerbose, fVeryVerbose );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &speedup [-P num] [-N num] [-lvwh]\n" );
    Abc_Print( -2, "\t           transforms LUT-mapped network into an AIG with choices;\n" );
    Abc_Print( -2, "\t           the choices are added to speedup the next round of mapping\n" );
    Abc_Print( -2, "\t-P <num> : delay delta defining critical path for library model [default = %d%%]\n", Percentage );
    Abc_Print( -2, "\t-N <num> : the max critical path degree for resynthesis (0 < num < 6) [default = %d]\n", Degree );
    Abc_Print( -2, "\t-l       : toggle using unit- or LUT-library-delay model [default = %s]\n", fUseLutLib? "lib" : "unit" );
    Abc_Print( -2, "\t-v       : toggle printing optimization summary [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-w       : toggle printing detailed stats for each node [default = %s]\n", fVeryVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h       : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Era( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp = NULL;
    int c, fVerbose = 0;
    int fUseCubes = 1;
    int fMiter = 0;
    int nStatesMax = 1000000000;
    extern int Gia_ManCollectReachable( Gia_Man_t * pAig, int nStatesMax, int fMiter, int fVerbose );
    extern int Gia_ManArePerform( Gia_Man_t * pAig, int nStatesMax, int fMiter, int fVerbose );

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Smcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by a positive integer.\n" );
                goto usage;
            }
            nStatesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nStatesMax < 0 ) 
                goto usage;
            break;
        case 'm':
            fMiter ^= 1;
            break;
        case 'c':
            fUseCubes ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Era(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Era(): The network is combinational.\n" );
        return 1;
    }
    if ( !fUseCubes && Gia_ManPiNum(pAbc->pGia) > 12 )
    {
        Abc_Print( -1, "Abc_CommandAbc9Era(): The number of PIs (%d) should be no more than 12 when cubes are not used.\n", Gia_ManPiNum(pAbc->pGia) );
        return 1;
    }
    if ( fUseCubes )
        pAbc->Status = Gia_ManArePerform( pAbc->pGia, nStatesMax, fMiter, fVerbose );
    else
        pAbc->Status = Gia_ManCollectReachable( pAbc->pGia, nStatesMax, fMiter, fVerbose );
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &era [-S num] [-mcvh]\n" );
//    Abc_Print( -2, "usage: &era [-S num] [-mvh]\n" );
    Abc_Print( -2, "\t          explicit reachability analysis for small sequential AIGs\n" );
    Abc_Print( -2, "\t-S num  : the max number of states (num > 0) [default = %d]\n", nStatesMax );
    Abc_Print( -2, "\t-m      : stop when the miter output is 1 [default = %s]\n", fMiter? "yes": "no" );
    Abc_Print( -2, "\t-c      : use state cubes instead of state minterms [default = %s]\n", fUseCubes? "yes": "no" );
    Abc_Print( -2, "\t-v      : print verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h      : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Dch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp;
    Dch_Pars_t Pars, * pPars = &Pars;
    int c;
    // set defaults
    Dch_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "WCSsptfvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'W':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nWords = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nWords < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBTLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBTLimit < 0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nSatVarMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nSatVarMax < 0 ) 
                goto usage;
            break;
        case 's':
            pPars->fSynthesis ^= 1;
            break;
        case 'p':
            pPars->fPower ^= 1;
            break;
        case 't':
            pPars->fSimulateTfo ^= 1;
            break;
        case 'f':
            pPars->fLightSynth ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Test(): There is no AIG.\n" );
        return 1;
    } 
    pTemp = Gia_ManPerformDch( pAbc->pGia, pPars );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &dch [-WCS num] [-sptfvh]\n" );
    Abc_Print( -2, "\t         computes structural choices using a new approach\n" );
    Abc_Print( -2, "\t-W num : the max number of simulation words [default = %d]\n", pPars->nWords );
    Abc_Print( -2, "\t-C num : the max number of conflicts at a node [default = %d]\n", pPars->nBTLimit );
    Abc_Print( -2, "\t-S num : the max number of SAT variables [default = %d]\n", pPars->nSatVarMax );
    Abc_Print( -2, "\t-s     : toggle synthesizing three snapshots [default = %s]\n", pPars->fSynthesis? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle power-aware rewriting [default = %s]\n", pPars->fPower? "yes": "no" );
    Abc_Print( -2, "\t-t     : toggle simulation of the TFO classes [default = %s]\n", pPars->fSimulateTfo? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle using lighter logic synthesis [default = %s]\n", pPars->fLightSynth? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle verbose printout [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9AbsStart( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_ParAbs_t Pars, * pPars = &Pars;
    int c;
    // set defaults
    Gia_ManAbsSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCRrpfvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesBmc = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesBmc < 0 ) 
                goto usage;
            break;
/*
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nStableMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nStableMax < 0 ) 
                goto usage;
            break;
*/
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfMaxBmc = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfMaxBmc < 0 ) 
                goto usage;
            break;
        case 'R':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-R\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nRatio = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nRatio < 0 ) 
                goto usage;
            break;
        case 'r':
            pPars->fUseBdds ^= 1;
            break;
        case 'p':
            pPars->fUseDprove ^= 1;
            break;
        case 'f':
            pPars->fUseStart ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9AbsStart(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9AbsStart(): The AIG is combinational.\n" );
        return 0;
    }
    if ( !(0 <= pPars->nRatio && pPars->nRatio <= 100) )
    {
        Abc_Print( -1, "Abc_CommandAbc9AbsStart(): Wrong value of parameter \"-R <num>\".\n" );
        return 0;
    }
    Gia_ManCexAbstractionStart( pAbc->pGia, pPars );
    pAbc->Status  = pPars->Status;
    pAbc->nFrames = pPars->nFramesDone;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;
usage:
    Abc_Print( -2, "usage: &abs_start [-FCR num] [-rpfvh]\n" );
    Abc_Print( -2, "\t         initializes flop map using cex-based abstraction\n" );
    Abc_Print( -2, "\t-F num : the max number of timeframes for BMC [default = %d]\n", pPars->nFramesBmc );
//    Abc_Print( -2, "\t-S num : the max number of stable frames for BMC [default = %d]\n", pPars->nStableMax );
    Abc_Print( -2, "\t-C num : the max number of conflicts by SAT solver for BMC [default = %d]\n", pPars->nConfMaxBmc );
    Abc_Print( -2, "\t-R num : the %% of abstracted flops when refinement stops (0<=num<=100) [default = %d]\n", pPars->nRatio );
    Abc_Print( -2, "\t-r     : toggle using BDD-based reachability for filtering [default = %s]\n", pPars->fUseBdds? "yes": "no" );
//    Abc_Print( -2, "\t-p     : toggle using \"dprove\" for filtering [default = %s]\n", pPars->fUseDprove? "yes": "no" );
    Abc_Print( -2, "\t-p     : toggle using \"pdr\" for filtering [default = %s]\n", pPars->fUseDprove? "yes": "no" );
    Abc_Print( -2, "\t-f     : toggle starting BMC from a later frame [default = %s]\n", pPars->fUseStart? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9AbsDerive( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp = NULL;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9AbsDerive(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( pAbc->pGia->vFlopClasses == NULL )
    {
        Abc_Print( -1, "Abstraction flop map is missing.\n" );
        return 0;
    }
    pTemp = Gia_ManDupAbsFlops( pAbc->pGia, pAbc->pGia->vFlopClasses );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &abs_derive [-vh]\n" );
    Abc_Print( -2, "\t        derives abstracted model using the pre-computed flop map\n" );
    Abc_Print( -2, "\t-v    : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9AbsRefine( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp = NULL;
    int c;
    int nFfToAddMax = 0;
    int fTryFour    = 1;
    int fSensePath  = 0;
    int fVerbose    = 0;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Mtsvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            nFfToAddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFfToAddMax < 0 ) 
                goto usage;
            break;
        case 't':
            fTryFour ^= 1;
            break;
        case 's':
            fSensePath ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9AbsRefine(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( pAbc->pCex == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9AbsRefine(): There is no counter-example.\n" );
        return 1;
    } 
    pAbc->Status = Gia_ManCexAbstractionRefine( pAbc->pGia, pAbc->pCex, nFfToAddMax, fTryFour, fSensePath, fVerbose );
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &abs_refine [-M <num>] [-tsvh]\n" );
    Abc_Print( -2, "\t         refines the pre-computed flop map using the counter-example\n" );
    Abc_Print( -2, "\t-M num : the max number of flops to add (0 = not used) [default = %d]\n", nFfToAddMax );
    Abc_Print( -2, "\t-t     : toggle trying four abstractions instead of one [default = %s]\n", fTryFour? "yes": "no" );
    Abc_Print( -2, "\t-s     : toggle using the path sensitization algorithm [default = %s]\n", fSensePath? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9AbsCba( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Saig_ParBmc_t Pars, * pPars = &Pars;
    int c;
    Saig_ParBmcSetDefaultParams( pPars );
    pPars->nStart     = (pAbc->nFrames >= 0) ? pAbc->nFrames : 0;
    pPars->nFramesMax = pPars->nStart + 10;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SFCMTvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nStart < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfLimit < 0 ) 
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFfToAddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFfToAddMax < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTimeOut < 0 ) 
                goto usage;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9AbsCba(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    pAbc->Status = Gia_ManCbaPerform( pAbc->pGia, pPars );
    if ( pPars->nStart == 0 )
        pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &abs_cba [-SFCT num] [-vh]\n" );
    Abc_Print( -2, "\t         refines abstracted flop map with CEX-based abstraction\n" );
    Abc_Print( -2, "\t-S num : the starting time frame [default = %d]\n", pPars->nStart );
    Abc_Print( -2, "\t-F num : the max number of timeframes to unroll [default = %d]\n", pPars->nFramesMax );
    Abc_Print( -2, "\t-C num : the max number of SAT solver conflicts [default = %d]\n", pPars->nConfLimit );
//    Abc_Print( -2, "\t-M num : the max number of flops to add (0 = not used) [default = %d]\n", pPars->nFfToAddMax );
    Abc_Print( -2, "\t-T num : an approximate timeout, in seconds [default = %d]\n", pPars->nTimeOut );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9AbsPba( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int nStart     =        0;
    int nFramesMax = (pAbc->nFrames >= 0) ? pAbc->nFrames : 20;
    int nConfMax   = 10000000;
    int nTimeLimit =        0;
    int fVerbose   =        0;
    int iFrame     =       -1;
    int c;

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SFCTvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            nStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nStart < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFramesMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfMax < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeLimit < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9AbsRefine(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( pAbc->pGia->vFlopClasses == NULL )
    {
        Abc_Print( -1, "The flop map is not given.\n" );
        return 0;
    }
    if ( nStart >= nFramesMax )
    {
        Abc_Print( -1, "The starting frame (%d) should be less than the total number of frames (%d).\n", nStart, nFramesMax );
        return 0;
    }
    Gia_ManPbaPerform( pAbc->pGia, nStart, nFramesMax, nConfMax, nTimeLimit, fVerbose, &iFrame );
    if ( iFrame >= 0 )
        pAbc->nFrames = iFrame;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &abs_pba [-SFCT num] [-vh]\n" );
    Abc_Print( -2, "\t         refines abstracted flop map with proof-based abstraction\n" );
    Abc_Print( -2, "\t-S num : the starting timeframe for SAT check [default = %d]\n", nStart );
    Abc_Print( -2, "\t-F num : the max number of timeframes to unroll [default = %d]\n", nFramesMax );
    Abc_Print( -2, "\t-C num : the max number of SAT solver conflicts [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-T num : an approximate timeout, in seconds [default = %d]\n", nTimeLimit );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GlaDerive( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp = NULL;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9GlaDerive(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
/*
    {
        int i;
        assert( pAbc->pGia->vGateClasses == NULL );
        pAbc->pGia->vGateClasses = Vec_IntStart( Gia_ManObjNum(pAbc->pGia) );
        for ( i = 0; i < Gia_ManObjNum(pAbc->pGia); i++ )
        {
            if ( rand() % 3 == i % 3 )
            {
                Vec_IntWriteEntry( pAbc->pGia->vGateClasses, i, rand() % 5 );
            }
        }
    }
*/
    if ( pAbc->pGia->vGateClasses == NULL )
    {
        Abc_Print( -1, "Abstraction gate map is missing.\n" );
        return 0;
    }
    pTemp = Gia_ManDupAbsGates( pAbc->pGia, pAbc->pGia->vGateClasses );
    Abc_CommandUpdate9( pAbc, pTemp );
//    printf( "This command is currently not enabled.\n" );
    return 0;

usage:
    Abc_Print( -2, "usage: &gla_derive [-vh]\n" );
    Abc_Print( -2, "\t        derives abstracted model using the pre-computed gate map\n" );
    Abc_Print( -2, "\t-v    : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GlaCba( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Saig_ParBmc_t Pars, * pPars = &Pars;
    int c, fNaiveCnf = 0;
    Saig_ParBmcSetDefaultParams( pPars );
    pPars->nStart     =  (pAbc->nFrames >= 0) ? pAbc->nFrames : 0;
    pPars->nFramesMax =  0;  
    pPars->nConfLimit =  0;
    pPars->nTimeOut   = 60;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SFCMTcvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nStart < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfLimit < 0 ) 
                goto usage;
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFfToAddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFfToAddMax < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTimeOut < 0 ) 
                goto usage;
            break;
        case 'c':
            fNaiveCnf ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9AbsCba(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( Gia_ManPoNum(pAbc->pGia) > 1 )
    {
        Abc_Print( 1, "The network is more than one PO (run \"orpos\").\n" );
        return 0;
    }
    if ( pPars->nFramesMax < 0 )
    {
        Abc_Print( 1, "The number of frames should be a positive integer.\n" );
        return 0;
    }
    if ( pPars->nStart > 0 && pPars->nFramesMax > 0 && pPars->nStart >= pPars->nFramesMax )
    {
        Abc_Print( 1, "The starting frame is larger than the max number of frames.\n" );
        return 0;
    }
    pAbc->Status = Gia_ManGlaCbaPerform( pAbc->pGia, pPars, fNaiveCnf );
//    if ( pPars->nStart == 0 )
       pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &gla_cba [-SFCT num] [-cvh]\n" );
    Abc_Print( -2, "\t         refines abstracted object map with CEX-based abstraction\n" );
    Abc_Print( -2, "\t-S num : the starting time frame (0=unused) [default = %d]\n", pPars->nStart );
    Abc_Print( -2, "\t-F num : the max number of timeframes to unroll (0=unused) [default = %d]\n", pPars->nFramesMax );
    Abc_Print( -2, "\t-C num : the max number of SAT solver conflicts (0=unused) [default = %d]\n", pPars->nConfLimit );
//    Abc_Print( -2, "\t-M num : the max number of flops to add (0 = not used) [default = %d]\n", pPars->nFfToAddMax );
    Abc_Print( -2, "\t-T num : an approximate timeout in seconds (0=unused) [default = %d]\n", pPars->nTimeOut );
    Abc_Print( -2, "\t-c     : toggle using naive CNF computation [default = %s]\n", fNaiveCnf? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9GlaPba( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Saig_ParBmc_t Pars, * pPars = &Pars;
    int c;
    int fNewSolver = 0;
    Saig_ParBmcSetDefaultParams( pPars );
    pPars->nStart     =  0;  
    pPars->nFramesMax = (pAbc->nFrames >= 0) ? pAbc->nFrames : 10;
    pPars->nConfLimit =  0;
    pPars->fSkipRand  =  0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SFCTrnvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nStart < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfLimit < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTimeOut < 0 ) 
                goto usage;
            break;
        case 'r':
            pPars->fSkipRand ^= 1;
            break;
        case 'n':
            fNewSolver ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9AbsCba(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( Gia_ManPoNum(pAbc->pGia) > 1 )
    {
        Abc_Print( 1, "The network is more than one PO (run \"orpos\").\n" );
        return 0;
    }
    if ( pPars->nFramesMax < 1 )
    {
        Abc_Print( 1, "The number of frames should be a positive integer.\n" );
        return 0;
    }
    if ( pPars->nStart >= pPars->nFramesMax )
    {
        Abc_Print( 1, "The starting frame is larger than the max number of frames.\n" );
        return 0;
    }
    if ( pPars->nStart )
        Abc_Print( 0, "The starting frame is specified. The resulting abstraction may be unsound.\n" );
    pAbc->Status = Gia_ManGlaPbaPerform( pAbc->pGia, pPars, fNewSolver );
//    if ( pPars->nStart == 0 )
       pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &gla_pba [-SFCT num] [-rnvh]\n" );
    Abc_Print( -2, "\t         refines abstracted object map with proof-based abstraction\n" );
    Abc_Print( -2, "\t-S num : the starting time frame (0=unused) [default = %d]\n", pPars->nStart );
    Abc_Print( -2, "\t-F num : the max number of timeframes to unroll [default = %d]\n", pPars->nFramesMax );
    Abc_Print( -2, "\t-C num : the max number of SAT solver conflicts (0=unused) [default = %d]\n", pPars->nConfLimit );
    Abc_Print( -2, "\t-T num : an approximate timeout, in seconds [default = %d]\n", pPars->nTimeOut );
    Abc_Print( -2, "\t-r     : toggle using random decisiont during SAT solving [default = %s]\n", !pPars->fSkipRand? "yes": "no" );
    Abc_Print( -2, "\t-n     : toggle using on-the-fly proof-logging [default = %s]\n", fNewSolver? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Vta( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_ParVta_t Pars, * pPars = &Pars;
    int c;
    Gia_VtaSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "SFPCTtvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesStart < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesMax < 0 ) 
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nFramesOver = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nFramesOver < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nConfLimit < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nTimeOut = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nTimeOut < 0 ) 
                goto usage;
            break;
        case 't':
            pPars->fUseTermVars ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9AbsCba(): There is no AIG.\n" );
        return 1;
    } 
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( Gia_ManPoNum(pAbc->pGia) > 1 )
    {
        Abc_Print( 1, "The network is more than one PO (run \"orpos\").\n" );
        return 0;
    }
    if ( pPars->nFramesMax < 0 )
    {
        Abc_Print( 1, "The number of starting frames should be a positive integer.\n" );
        return 0;
    }
    if ( pPars->nFramesMax && pPars->nFramesStart > pPars->nFramesMax )
    {
        Abc_Print( 1, "The starting frame is larger than the max number of frames.\n" );
        return 0;
    }
    pAbc->Status  = Gia_VtaPerform( pAbc->pGia, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &vta [-SFPCT num] [-tvh]\n" );
    Abc_Print( -2, "\t         refines abstracted object map with proof-based abstraction\n" );
    Abc_Print( -2, "\t-S num : the starting time frame (0=unused) [default = %d]\n", pPars->nFramesStart );
    Abc_Print( -2, "\t-F num : the max number of timeframes to unroll [default = %d]\n", pPars->nFramesMax );
    Abc_Print( -2, "\t-P num : the number of previous frames for UNSAT core [default = %d]\n", pPars->nFramesOver );
    Abc_Print( -2, "\t-C num : the max number of SAT solver conflicts (0=unused) [default = %d]\n", pPars->nConfLimit );
    Abc_Print( -2, "\t-T num : an approximate timeout, in seconds [default = %d]\n", pPars->nTimeOut );
    Abc_Print( -2, "\t-t     : toggle using terminal variables [default = %s]\n", pPars->fUseTermVars? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Vta2Gla( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Vta2Gla(): There is no AIG.\n" );
        return 1;
    }
    if ( pAbc->pGia->vObjClasses == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Vta2Gla(): There is no variable-time-frame abstraction defines.\n" );
        return 1;
    }
    Vec_IntFreeP( &pAbc->pGia->vGateClasses );
    pAbc->pGia->vGateClasses = Gia_VtaConvertToGla( pAbc->pGia, pAbc->pGia->vObjClasses );
    Vec_IntFreeP( &pAbc->pGia->vObjClasses );
    return 0;

usage:
    Abc_Print( -2, "usage: &vta_gla [-vh]\n" );
    Abc_Print( -2, "\t        maps variable- into fixed-time-frame abstraction\n" );
    Abc_Print( -2, "\t-v    : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Reparam( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp = NULL;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "vh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Reparam(): There is no AIG.\n" );
        return 1;
    } 
    pTemp = Gia_ManReparam( pAbc->pGia, fVerbose );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &reparam [-vh]\n" );
    Abc_Print( -2, "\t        performs input trimming and reparameterization\n" );
    Abc_Print( -2, "\t-v    : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9BackReach( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Gia_Man_t * Gia_ManCofTest( Gia_Man_t * pGia, int nFrameMax, int nConfMax, int nTimeMax, int fVerbose );

    Gia_Man_t * pTemp = NULL;
    int c, fVerbose = 0;
    int nFrameMax = 1000000;
    int nConfMax  = 1000000;
    int nTimeMax  =      10;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FCTvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            nFrameMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nFrameMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfMax < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nTimeMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nTimeMax < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9BackReach(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManPoNum(pAbc->pGia) != 1 )
    {
        Abc_Print( -1, "Abc_CommandAbc9BackReach(): The number of POs is different from 1.\n" );
        return 1;
    }
    pTemp = Gia_ManCofTest( pAbc->pGia, nFrameMax, nConfMax, nTimeMax, fVerbose );
    Abc_CommandUpdate9( pAbc, pTemp );
    return 0;

usage:
    Abc_Print( -2, "usage: &back_reach [-FCT <num>] [-vh]\n" );
    Abc_Print( -2, "\t         performs input trimming and reparameterization\n" );
    Abc_Print( -2, "\t-F num : the limit on the depth of induction [default = %d]\n", nFrameMax );
    Abc_Print( -2, "\t-C num : the conflict limit at a node during induction [default = %d]\n", nConfMax );
    Abc_Print( -2, "\t-T num : the timeout for property directed reachability [default = %d]\n", nTimeMax );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Posplit( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Aig_Man_t * Aig_ManSplit( Aig_Man_t * p, int nVars, int fVerbose );
    Aig_Man_t * pMan, * pAux;
    Gia_Man_t * pTemp = NULL;
    int c, nVars = 5, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "Nvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            nVars = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nVars < 0 ) 
                goto usage;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Posplit(): There is no AIG.\n" );
        return 1;
    } 
    pMan = Gia_ManToAigSimple( pAbc->pGia );
    pMan = Aig_ManSplit( pAux = pMan, nVars, fVerbose );
    Aig_ManStop( pAux );
    if ( pMan != NULL )
    {
        pTemp = Gia_ManFromAigSimple( pMan );
        Aig_ManStop( pMan );
        Abc_CommandUpdate9( pAbc, pTemp );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: &posplit [-N num] [-vh]\n" );
    Abc_Print( -2, "\t         cofactors the property output w.r.t. a support subset\n" );
    Abc_Print( -2, "\t         (the OR of new PO functions is equal to the original property)\n" );
    Abc_Print( -2, "\t-N num : the number of random cofactoring variables [default = %d]\n", nVars );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReachM( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_ParLlb_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    char * pLogFileName = NULL;
    int c;
    extern int Llb_ManModelCheckGia( Gia_Man_t * pGia, Gia_ParLlb_t * pPars );

    // set defaults
    Llb_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TBFCHSLripcsyzvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeLimit < 0 ) 
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBddMax < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nClusterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nClusterMax < 0 ) 
                goto usage;
            break;
        case 'H':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-H\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nHintDepth = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nHintDepth < 0 ) 
                goto usage;
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-S\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->HintFirst = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->HintFirst < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'r':
            pPars->fReorder ^= 1;
            break;
        case 'i':
            pPars->fIndConstr ^= 1;
            break;
        case 'p':
            pPars->fUsePivots ^= 1;
            break;
        case 'c':
            pPars->fCluster ^= 1;
            break;
        case 's':
            pPars->fSchedule ^= 1;
            break;
        case 'y':
            pPars->fSkipOutCheck ^= 1;
            break;
        case 'z':
            pPars->fSkipReach ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachM(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachM(): The current AIG has no latches.\n" );
        return 0;
    } 
    if ( Gia_ManObjNum(pAbc->pGia) >= (1<<16) )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachM(): Currently cannot handle AIGs with more than %d objects.\n", (1<<16) );
        return 0;
    }
    pAbc->Status  = Llb_ManModelCheckGia( pAbc->pGia, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "&reachm" );
    return 0;

usage:
    Abc_Print( -2, "usage: &reachm [-TBFCHS num] [-L file] [-ripcsyzvwh]\n" );
    Abc_Print( -2, "\t         model checking via BDD-based reachability (dependence-matrix-based)\n" );
    Abc_Print( -2, "\t-T num : approximate time limit in seconds (0=infinite) [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-B num : max number of nodes in the intermediate BDDs [default = %d]\n", pPars->nBddMax );
    Abc_Print( -2, "\t-F num : max number of reachability iterations [default = %d]\n", pPars->nIterMax );
    Abc_Print( -2, "\t-C num : max number of variables in a cluster [default = %d]\n", pPars->nClusterMax );
    Abc_Print( -2, "\t-H num : max number of hints to use [default = %d]\n", pPars->nHintDepth );
    Abc_Print( -2, "\t-S num : the number of the starting hint [default = %d]\n", pPars->HintFirst );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-r     : enable dynamic BDD variable reordering [default = %s]\n", pPars->fReorder? "yes": "no" );  
    Abc_Print( -2, "\t-i     : enable extraction of inductive constraints [default = %s]\n", pPars->fIndConstr? "yes": "no" );  
    Abc_Print( -2, "\t-p     : enable partitions for internal cut-points [default = %s]\n", pPars->fUsePivots? "yes": "no" );  
    Abc_Print( -2, "\t-c     : enable clustering of partitions [default = %s]\n", pPars->fCluster? "yes": "no" );  
    Abc_Print( -2, "\t-s     : enable scheduling of clusters [default = %s]\n", pPars->fSchedule? "yes": "no" );  
    Abc_Print( -2, "\t-y     : skip checking property outputs [default = %s]\n", pPars->fSkipOutCheck? "yes": "no" );  
    Abc_Print( -2, "\t-z     : skip reachability (run preparation phase only) [default = %s]\n", pPars->fSkipReach? "yes": "no" );  
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-w     : prints dependency matrix [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReachP( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_ParLlb_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Aig_Man_t * pMan;
    char * pLogFileName = NULL;
    int c;
    extern int Llb_ManReachMinCut( Aig_Man_t * pAig, Gia_ParLlb_t * pPars );

    // set defaults
    Llb_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "NBFTLrbyzdvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nPartValue = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nPartValue < 0 ) 
                goto usage;
            break;
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBddMax < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterMax < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeLimit < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'r':
            pPars->fReorder ^= 1;
            break;
        case 'b':
            pPars->fBackward ^= 1;
            break;
        case 'y':
            pPars->fSkipOutCheck ^= 1;
            break;
        case 'z':
            pPars->fSkipReach ^= 1;
            break;
        case 'd':
            pPars->fDumpReached ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachP(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachP(): The current AIG has no latches.\n" );
        return 0;
    }
    if ( Gia_ManObjNum(pAbc->pGia) >= (1<<16) )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachP(): Currently cannot handle AIGs with more than %d objects.\n", (1<<16) );
        return 0;
    }
    pMan          = Gia_ManToAigSimple( pAbc->pGia );
    pAbc->Status  = Llb_ManReachMinCut( pMan, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pMan->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "&reachp" );
    Aig_ManStop( pMan );
    return 0;

usage:
    Abc_Print( -2, "usage: &reachp [-NFT num] [-L file] [-rbyzdvwh]\n" );
    Abc_Print( -2, "\t         model checking via BDD-based reachability (partitioning-based)\n" );
    Abc_Print( -2, "\t-N num : partitioning value (MinVol=nANDs/N/2; MaxVol=nANDs/N) [default = %d]\n", pPars->nPartValue );
//    Abc_Print( -2, "\t-B num : the BDD node increase when hints kick in [default = %d]\n", pPars->nBddMax );
    Abc_Print( -2, "\t-F num : max number of reachability iterations [default = %d]\n", pPars->nIterMax );
    Abc_Print( -2, "\t-T num : approximate time limit in seconds (0=infinite) [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-r     : enable additional BDD var reordering before image [default = %s]\n", pPars->fReorder? "yes": "no" );  
    Abc_Print( -2, "\t-b     : perform backward reachability analysis [default = %s]\n", pPars->fBackward? "yes": "no" );  
    Abc_Print( -2, "\t-y     : skip checking property outputs [default = %s]\n", pPars->fSkipOutCheck? "yes": "no" );  
    Abc_Print( -2, "\t-z     : skip reachability (run preparation phase only) [default = %s]\n", pPars->fSkipReach? "yes": "no" );  
    Abc_Print( -2, "\t-d     : dump BDD of reached states into file \"reached.blif\" [default = %s]\n", pPars->fDumpReached? "yes": "no" );  
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-w     : prints additional information [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReachN( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_ParLlb_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Aig_Man_t * pMan;
    char * pLogFileName = NULL;
    int c;
    extern int Llb_NonlinCoreReach( Aig_Man_t * pAig, Gia_ParLlb_t * pPars );

    // set defaults
    Llb_ManSetDefaultParams( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "BFTLryzvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBddMax < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterMax < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeLimit < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'r':
            pPars->fReorder ^= 1;
            break;
        case 'y':
            pPars->fSkipOutCheck ^= 1;
            break;
        case 'z':
            pPars->fSkipReach ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachN(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachN(): The current AIG has no latches.\n" );
        return 0;
    }
    if ( Gia_ManObjNum(pAbc->pGia) >= (1<<16) )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachN(): Currently cannot handle AIGs with more than %d objects.\n", (1<<16) );
        return 0;
    }
    pMan          = Gia_ManToAigSimple( pAbc->pGia );
    pAbc->Status  = Llb_NonlinCoreReach( pMan, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pMan->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "&reachn" );
    Aig_ManStop( pMan );
    return 0;

usage:
    Abc_Print( -2, "usage: &reachn [-BFT num] [-L file] [-ryzvh]\n" );
    Abc_Print( -2, "\t         model checking via BDD-based reachability (non-linear-QS-based)\n" );
    Abc_Print( -2, "\t-B num : the BDD node increase when hints kick in [default = %d]\n", pPars->nBddMax );
    Abc_Print( -2, "\t-F num : max number of reachability iterations [default = %d]\n", pPars->nIterMax );
    Abc_Print( -2, "\t-T num : approximate time limit in seconds (0=infinite) [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-r     : enable additional BDD var reordering before image [default = %s]\n", pPars->fReorder? "yes": "no" );  
    Abc_Print( -2, "\t-y     : skip checking property outputs [default = %s]\n", pPars->fSkipOutCheck? "yes": "no" );  
    Abc_Print( -2, "\t-z     : skip reachability (run preparation phase only) [default = %s]\n", pPars->fSkipReach? "yes": "no" );  
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );  
//    Abc_Print( -2, "\t-w     : prints additional information [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9ReachY( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_ParLlb_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    Aig_Man_t * pMan;
    char * pLogFileName = NULL;
    int c;

    // set defaults
    Llb_ManSetDefaultParams( pPars );
    pPars->fCluster = 0;
    pPars->fReorder = 0;
    pPars->nBddMax     = 100;
    pPars->nClusterMax = 500;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "BCFTLbcryzvwh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'B':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-B\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nBddMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nBddMax < 0 ) 
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nClusterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nClusterMax < 0 ) 
                goto usage;
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nIterMax = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->nIterMax < 0 ) 
                goto usage;
            break;
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->TimeLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( pPars->TimeLimit < 0 ) 
                goto usage;
            break;
        case 'L':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-L\" should be followed by a file name.\n" );
                goto usage;
            }
            pLogFileName = argv[globalUtilOptind];
            globalUtilOptind++;
            break;
        case 'b':
            pPars->fBackward ^= 1;
            break;
        case 'c':
            pPars->fCluster ^= 1;
            break;
        case 'r':
            pPars->fReorder ^= 1;
            break;
        case 'y':
            pPars->fSkipOutCheck ^= 1;
            break;
        case 'z':
            pPars->fSkipReach ^= 1;
            break;
        case 'v':
            pPars->fVerbose ^= 1;
            break;
        case 'w':
            pPars->fVeryVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachN(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachN(): The current AIG has no latches.\n" );
        return 0;
    }
    if ( Gia_ManObjNum(pAbc->pGia) >= (1<<16) )
    {
        Abc_Print( -1, "Abc_CommandAbc9ReachN(): Currently cannot handle AIGs with more than %d objects.\n", (1<<16) );
        return 0;
    }
    pMan          = Gia_ManToAigSimple( pAbc->pGia );
    pAbc->Status  = Llb_Nonlin4CoreReach( pMan, pPars );
    pAbc->nFrames = pPars->iFrame;
    Abc_FrameReplaceCex( pAbc, &pMan->pSeqModel );
    if ( pLogFileName )
        Abc_NtkWriteLogFile( pLogFileName, pAbc->pCex, pAbc->Status, pAbc->nFrames, "&reachy" );
    Aig_ManStop( pMan );
    return 0;

usage:
    Abc_Print( -2, "usage: &reachy [-BCFT num] [-L file] [-bcryzvh]\n" );
    Abc_Print( -2, "\t         model checking via BDD-based reachability (non-linear-QS-based)\n" );
    Abc_Print( -2, "\t-B num : the max BDD size to introduce cut points [default = %d]\n", pPars->nBddMax );
    Abc_Print( -2, "\t-C num : the max BDD size to reparameterize/cluster [default = %d]\n", pPars->nClusterMax );
    Abc_Print( -2, "\t-F num : max number of reachability iterations [default = %d]\n", pPars->nIterMax );
    Abc_Print( -2, "\t-T num : approximate time limit in seconds (0=infinite) [default = %d]\n", pPars->TimeLimit );
    Abc_Print( -2, "\t-L file: the log file name [default = %s]\n", pLogFileName ? pLogFileName : "no logging" );
    Abc_Print( -2, "\t-b     : enable using backward enumeration [default = %s]\n", pPars->fBackward? "yes": "no" );  
    Abc_Print( -2, "\t-c     : enable reparametrization clustering [default = %s]\n", pPars->fCluster? "yes": "no" );  
    Abc_Print( -2, "\t-r     : enable additional BDD var reordering before image [default = %s]\n", pPars->fReorder? "yes": "no" );  
    Abc_Print( -2, "\t-y     : skip checking property outputs [default = %s]\n", pPars->fSkipOutCheck? "yes": "no" );  
    Abc_Print( -2, "\t-z     : skip reachability (run preparation phase only) [default = %s]\n", pPars->fSkipReach? "yes": "no" );  
    Abc_Print( -2, "\t-v     : prints verbose information [default = %s]\n", pPars->fVerbose? "yes": "no" );  
//    Abc_Print( -2, "\t-w     : prints additional information [default = %s]\n", pPars->fVeryVerbose? "yes": "no" );  
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Undo( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    // set defaults
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "h" ) ) != EOF )
    {
        switch ( c )
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Undo(): There is no design.\n" );
        return 1;
    } 
    if ( pAbc->pGia2 == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Undo(): There is no previously saved network.\n" );
        return 1;
    } 
    Gia_ManStop( pAbc->pGia );
    pAbc->pGia = pAbc->pGia2;
    pAbc->pGia2 = NULL;
    return 0;

usage:
    Abc_Print( -2, "usage: &undo [-h]\n" );
    Abc_Print( -2, "\t        reverses the previous AIG transformation\n" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandAbc9Test( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Gia_Man_t * pTemp = NULL;
    int c, fVerbose = 0;
    int fSwitch = 0;
//    extern Gia_Man_t * Gia_VtaTest( Gia_Man_t * p );
//    extern int Gia_ManSuppSizeTest( Gia_Man_t * p );
//    extern void Gia_VtaTest( Gia_Man_t * p, int nFramesStart, int nFramesMax, int nConfMax, int nTimeMax, int fVerbose );

    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "svh" ) ) != EOF )
    {
        switch ( c )
        {
        case 's':
            fSwitch ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9Test(): There is no AIG.\n" );
        return 1;
    } 
//    Gia_ManFrontTest( pAbc->pGia );
//    Gia_ManReduceConst( pAbc->pGia, 1 );
//    Sat_ManTest( pAbc->pGia, Gia_ManCo(pAbc->pGia, 0), 0 );
//    Gia_ManTestDistance( pAbc->pGia );
//    Gia_SatSolveTest( pAbc->pGia );
//    For_ManExperiment( pAbc->pGia, 20, 1, 1 );
//    Gia_ManUnrollSpecial( pAbc->pGia, 5, 100, 1 );
//    pAbc->pGia = Gia_ManDupSelf( pTemp = pAbc->pGia );
//    pAbc->pGia = Gia_ManRemoveEnables( pTemp = pAbc->pGia );
//    Cbs_ManSolveTest( pAbc->pGia );
//    pAbc->pGia = Gia_VtaTest( pTemp = pAbc->pGia );
//    Gia_ManStopP( &pTemp );
//    Gia_ManSuppSizeTest( pAbc->pGia );

//    Gia_VtaTest( pAbc->pGia, 10, 100000, 0, 0, 1 );
    return 0;
usage:
    Abc_Print( -2, "usage: &test [-svh]\n" );
    Abc_Print( -2, "\t        testing various procedures\n" );
    Abc_Print( -2, "\t-s    : toggle enable (yes) vs. disable (no) [default = %s]\n", fSwitch? "yes": "no" );
    Abc_Print( -2, "\t-v    : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h    : print the command usage\n");
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

