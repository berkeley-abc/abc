
#include "misc/util/abc_namespaces.h"

#ifdef _WIN32
#include "../lib/pthread.h"
#else
#include <pthread.h>
#include <unistd.h>
#endif

#include "sat/bmc/bmc.h"
#include "proof/pdr/pdr.h"
#include "aig/gia/giaAig.h"
#include "opt/util/util.h"
#include "opt/untk/NtkNtk.h"
#include "UfarPth.h"

ABC_NAMESPACE_HEADER_START
    Abc_Ntk_t *   Abc_NtkFromAigPhase( Aig_Man_t * pAig );
    int           Abc_NtkDarBmc3( Abc_Ntk_t * pAbcNtk, Saig_ParBmc_t * pBmcPars, int fOrDecomp );
    Wla_Man_t * Wla_ManStart( Wlc_Ntk_t * pNtk, Wlc_Par_t * pPars );
    void Wla_ManStop( Wla_Man_t * pWla );
    int Wla_ManSolve( Wla_Man_t * pWla, Wlc_Par_t * pPars );
ABC_NAMESPACE_HEADER_END

ABC_NAMESPACE_IMPL_START

static volatile int  g_nRunIds = 0;             // the number of the last prover instance
int Ufar_CallBackToStop( int RunId ) { assert( RunId <= g_nRunIds ); return RunId < g_nRunIds; }
int Ufar_GetGlobalRunId() { return g_nRunIds; }

using namespace std;

namespace UFAR {

// mutext to control access to shared variables
pthread_mutex_t g_mutex;
// cv to control timer
pthread_cond_t  g_cond;

struct Pth_Data_t
{
    Pth_Data_t () : RunId(-1), pGia(NULL), pWlc(NULL), ppCex(NULL), RetValue(-1), engine(NULL) {}
    void set ( const string * eng, int id, Wlc_Ntk_t * pWL, Gia_Man_t * pBL, Abc_Cex_t ** pp ) { engine = eng; RunId = id; pWlc = pWL; pGia = pBL; ppCex = pp; }
    int          RunId;
    Gia_Man_t *  pGia;
    Wlc_Ntk_t *  pWlc;
    Abc_Cex_t ** ppCex;
    int          RetValue;
    const string *     engine; 
};

class Solver {
public:
    virtual ~Solver() {}
    virtual int Solve() = 0;
    virtual void SetCex( Abc_Cex_t ** ppCex ) = 0;
};

class PDR : public Solver {
    public:
    PDR( void * pArg ) {
        Pth_Data_t * pData = (Pth_Data_t *)pArg;

        _pAig = Gia_ManToAigSimple( pData->pGia );

        Pdr_Par_t * pPdrPars = &_PdrPars;
        Pdr_ManSetDefaultParams(pPdrPars);
        pPdrPars->nConfLimit = 0;
        pPdrPars->RunId = pData->RunId;
        pPdrPars->pFuncStop = Ufar_CallBackToStop;
    }
    ~PDR() { Aig_ManStop(_pAig); }

    virtual int Solve() {
        return Pdr_ManSolve( _pAig, &_PdrPars ); 
    }

    virtual void SetCex( Abc_Cex_t ** ppCex ) {
        assert( _pAig->pSeqModel );
        *(ppCex) = _pAig->pSeqModel;
        _pAig->pSeqModel = NULL;
    }

    private:
        Aig_Man_t * _pAig;
        Pdr_Par_t   _PdrPars;
};

class PDRA : public Solver {
    public:
    PDRA( void * pArg ) {
        Pth_Data_t * pData = (Pth_Data_t *)pArg;

        _pAig = Gia_ManToAigSimple( pData->pGia );

        Pdr_Par_t * pPdrPars = &_PdrPars;
        Pdr_ManSetDefaultParams(pPdrPars);
        pPdrPars->nConfLimit = 0;
        pPdrPars->RunId = pData->RunId;
        pPdrPars->pFuncStop = Ufar_CallBackToStop;
        pPdrPars->fUseAbs    = 1;   // use 'pdr -t'  (on-the-fly abstraction)
        pPdrPars->fCtgs      = 1;   // use 'pdr -c' (improved generalization)
        pPdrPars->fSkipDown  = 0;   // use 'pdr -n' (improved generalization)
        pPdrPars->nRestLimit = 500; // reset queue or proof-obligations when it gets larger than this
    }
    ~PDRA() { Aig_ManStop(_pAig); }

    virtual int Solve() {
        return Pdr_ManSolve( _pAig, &_PdrPars ); 
    }

    virtual void SetCex( Abc_Cex_t ** ppCex ) {
        assert( _pAig->pSeqModel );
        *(ppCex) = _pAig->pSeqModel;
        _pAig->pSeqModel = NULL;
    }

    private:
        Aig_Man_t * _pAig;
        Pdr_Par_t   _PdrPars;
};

class BMC3 : public Solver {
    public:
        BMC3 ( void * pArg ) {
            Pth_Data_t * pData = (Pth_Data_t *)pArg;
            Aig_Man_t * pAig = Gia_ManToAigSimple( pData->pGia );
            _pNtk = Abc_NtkFromAigPhase( pAig );
            Aig_ManStop( pAig );

            Saig_ParBmc_t * pBmcPars = &_Pars;
            Saig_ParBmcSetDefaultParams( pBmcPars );
            pBmcPars->RunId = pData->RunId;
            pBmcPars->pFuncStop = Ufar_CallBackToStop;
        }
        ~BMC3() { Abc_NtkDelete(_pNtk); }

        virtual int Solve() {
            return Abc_NtkDarBmc3( _pNtk, &_Pars, 0 );
        }

        virtual void SetCex( Abc_Cex_t ** ppCex ) {
            assert( _pNtk->pSeqModel );
            *(ppCex) = _pNtk->pSeqModel;
            _pNtk->pSeqModel = NULL;
        }
    private:
        Abc_Ntk_t *    _pNtk;
        Saig_ParBmc_t  _Pars;
};

class PDRWLA : public Solver {
    public:
        PDRWLA( void * pArg ) {
            Pth_Data_t * pData = (Pth_Data_t *)pArg;
            Wlc_Ntk_t * pNtk = pData->pWlc;

            Wlc_Par_t * pWlcPars = &_Pars;
            Wlc_ManSetDefaultParams( pWlcPars );
            pWlcPars->nBitsAdd = 8;
            pWlcPars->nBitsMul = 4;
            pWlcPars->nBitsMux = 8;
            pWlcPars->fXorOutput = 0;
            pWlcPars->nLimit = 50;
            pWlcPars->fVerbose = 1;
            pWlcPars->fProofRefine = 1;
            pWlcPars->fHybrid = 0;
            pWlcPars->fCheckCombUnsat = 1;
            pWlcPars->RunId = pData->RunId; 
            pWlcPars->pFuncStop = Ufar_CallBackToStop;

            _pWla = Wla_ManStart( pNtk, pWlcPars );
        }
        ~PDRWLA() { Wla_ManStop(_pWla); }

        virtual int Solve() {
            return Wla_ManSolve( _pWla, &_Pars );
        }

        virtual void SetCex( Abc_Cex_t ** ppCex ) {
            assert( _pWla->pCex );
            *(ppCex) = _pWla->pCex;
            _pWla->pCex = NULL;
        }
    private:
        Wla_Man_t * _pWla;
        Wlc_Par_t   _Pars;
};

#if defined(__wasm)
static void pthread_exit(void *retval) __attribute__((noreturn)) { }
#endif

void KillOthers() {
    pthread_cond_signal( &g_cond );
    ++g_nRunIds;
}

void * RunSolver( void * pArg ) {
    Pth_Data_t * pData = (Pth_Data_t *)pArg;
    Solver * pSolver = NULL;
    int status;

    if ( *(pData->engine) == "pdr" )
        pSolver = new PDR( pArg );
    else if ( *(pData->engine) == "pdra" )
        pSolver = new PDRA( pArg );
    else if ( *(pData->engine) == "bmc3" )
        pSolver = new BMC3( pArg );
    else if ( *(pData->engine) == "wla" )
        pSolver = new PDRWLA( pArg );
    else {
        pthread_exit( NULL );
        assert(0);
        return 0;
    }

    pData->RetValue = pSolver->Solve();
    int ret = pData->RetValue;

    status = pthread_mutex_lock(&g_mutex);  assert( status == 0 );
    if ( ret == 0 ) {
        pSolver->SetCex( pData->ppCex );
        LOG(2) << *(pData->engine) << " found CEX. RunId = " << pData->RunId;

        KillOthers();
    } else if ( ret == 1 ) {
        LOG(2) << *(pData->engine) << " proved the problem. RunId = " << pData->RunId;
        KillOthers();
    } else {
        if ( pData->RunId < g_nRunIds ) {
            LOG(2) << *(pData->engine) << " was cancelled. RunId = " << pData->RunId;
        }
    }
    status = pthread_mutex_unlock(&g_mutex);  assert( status == 0 );

    delete pSolver;

    pthread_exit( NULL );
    assert(0);
    return 0;
}

void * Timer ( void * pArg ) {
    struct timespec * pTimeout = ( struct timespec * )pArg;
    int retcode = 0;
    int status;

    status = pthread_mutex_lock(&g_mutex);  assert( status == 0 );
    retcode = pthread_cond_timedwait(&g_cond, &g_mutex, pTimeout);
    if ( retcode == ETIMEDOUT ) {
        LOG(2) << "Timer reached timeout.";
        KillOthers();
    } else {
        LOG(2) << "Timer was cancelled.";
    }
    status = pthread_mutex_unlock(&g_mutex);  assert( status == 0 );

    pthread_exit( NULL );
    assert(0);
    return 0;
}

int RunConcurrentSolver( Wlc_Ntk_t * pNtk, const vector<string>& vSolvers, Abc_Cex_t ** ppCex, struct timespec * pTimeout ) {
    assert( pTimeout );

    int status;
    vector<Pth_Data_t> vDatas   ( vSolvers.size() );
    vector<pthread_t>  vThreads ( vSolvers.size() );
    pthread_t timer;

    Gia_Man_t * pGia = BitBlast( pNtk );

    status = pthread_create( &timer, NULL, Timer, pTimeout );
    assert( status == 0 );

    for ( size_t i = 0; i < vSolvers.size(); ++i ) {
        vDatas[i].set( &vSolvers[i], g_nRunIds, pNtk, pGia, ppCex );
        status = pthread_create( &vThreads[i], NULL, RunSolver, &vDatas[i] );
        assert( status == 0 );
    }

    status = pthread_join( timer, NULL );
    assert( status == 0 );
    for ( size_t i = 0; i < vSolvers.size(); ++i ) {
        status = pthread_join( vThreads[i], NULL );
        assert( status == 0 );
    }

    Gia_ManStop( pGia );

    for( auto& x : vDatas ) {
        if ( x.RetValue != -1 )
            return x.RetValue;
    }
    return -1;
}



}

ABC_NAMESPACE_IMPL_END
