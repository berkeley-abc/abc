// Isolated CEX reconstruction experiment. Included after the existing builders.
// All state is scoped to one immutable ODC round; never used in strict passes.
static Cec_TranSim_t * s_CexLong, * s_CexAug;
static int s_CexMode, s_CexRound, s_CexProjectAll;
static long long s_CexRoots, s_CexTriggered, s_CexPoints, s_CexAdded;
static abctime s_CexTime;
static long long s_CexCoreConflicts, s_CexRefinedLabels;
#include "cecTranCexCompress.h"

// Refine only the selected core's <=256 minterms using the already computed
// reachable source. A conflicting ON/OFF label is an exact infeasibility
// witness for this support. It does not refute the root or any other support.
static int Cec_TranCexRefineIsf(int root, Vec_Int_t * pool, Vec_Int_t * core,
    int nCore, word * care, unsigned * off, unsigned * on)
{
    int s,i,key,label,k,period=1<<nCore,nBits=nCore<5?32:1<<nCore;
    for(s=0;s<64*s_CexLong->nSlots;++s) {
        if(!((care[s>>6]>>(s&63))&1)) continue;
        key=0;
        for(i=0;i<nCore;++i)
            key |= Cec_TranTeachSampleValue(s_CexLong,
                Vec_IntEntry(pool,Vec_IntEntry(core,i)),s)<<i;
        label=Cec_TranTeachSampleValue(s_CexLong,root,s);
        if(Abc_InfoHasBit(label?off:on,key)) {
            s_CexCoreConflicts++; return 0;
        }
        if(!Abc_InfoHasBit(label?on:off,key)) {
            s_CexRefinedLabels++;
            for(k=key;k<nBits;k+=period) Abc_InfoSetBit(label?on:off,k);
        }
    }
    return 1;
}

static word Cec_TranCexDiff(Cec_TranSim_t * pSim,
    Cec_TranCand_t const * c, word const * care, int s)
{
    word gates[CEC_TRAN_RECIPE_NODES_MAX];
    int i;
    for (i=0; i<c->nGates; ++i)
        gates[i] = Cec_TranRecipeSimCode(pSim,c->Recipe[2*i],gates,i,s) &
            Cec_TranRecipeSimCode(pSim,c->Recipe[2*i+1],gates,i,s);
    return (Cec_TranRecipeSimCode(pSim,c->iOut,gates,c->nGates,s) ^
        Cec_TranSimObj(pSim,c->iTarget)[s]) & care[s];
}

static void Cec_TranCexReconstruct(Cec_TranSim_t * old, Cec_ParTran_t * pars,
    Cec_TranRoot_t * root, Vec_Int_t * pool, Cec_TranDivRank_t * ranks,
    word * oldCare, Cec_TranCandVec_t const * known,
    Cec_TranCandVec_t * out, Cec_TranProf_t * prof)
{
    Cec_TranCandVec_t extra={0}, seen={0};
    Cec_TranCand_t rep;
    Vec_Int_t * primary, * core;
    word * longCare, * care, * compactCare=NULL;
    Cec_TranSim_t * buildSim;
    word * buildCare;
    int points[64], n=0, s, lane, i, j, obj, nCore, trial, nTrials;
    int oldN=out->nSize;
    abctime clk;
    if (!s_CexMode || !oldCare || !oldN || !Vec_IntSize(pool)) return;
    assert(old->pGia == s_CexLong->pGia && old->pGia == s_CexAug->pGia);
    assert(s_CexAug->nSlots == old->nSlots+1);
    clk=Abc_Clock(); s_CexRoots++;
    // One deterministic highest-ranked incumbent per root, fixed across arms.
    rep=out->pArray[0];
    longCare=Cec_TranWindowCare(s_CexLong,root->iObj,pars,NULL);
    // At most one first failing lane per frame, avoiding a whole budget of
    // coincident lanes from just one frame. This is an explicit 64-point cap.
    for (s=0; s<s_CexLong->nSlots && n<64; ++s)
    {
        word diff=Cec_TranCexDiff(s_CexLong,&rep,longCare,s);
        if (!diff) continue;
        for (lane=0; !((diff>>lane)&1); ++lane) {}
        points[n++]=64*s+lane;
    }
    if (!n) { ABC_FREE(longCare); s_CexTime+=Abc_Clock()-clk; return; }
    s_CexTriggered++; s_CexPoints+=n;
    // out was sorted by the caller, so its index hash no longer identifies
    // array positions. Build a fresh lookup instead of consulting that hash.
    // Normalize only the comparison tag: a strict-tag twin is the very same
    // recipe under the unchanged downstream ODC obligation contract.
    for(i=0;i<oldN;++i) {
        Cec_TranCand_t c=out->pArray[i]; c.fStrict=0;
        if(!Cec_TranCandVecContains(&seen,&c)) Cec_TranCandVecPush(&seen,c);
    }
    care=ABC_CALLOC(word,old->nSlots+1);
    memcpy(care,oldCare,sizeof(word)*old->nSlots);
    // All old observations remain. Extra rows are scalar reachable states,
    // not fabricated reset traces. The long source has reset provenance.
    for (i=-1; i<Vec_IntSize(pool); ++i)
    {
        word * dst;
        obj=i<0?root->iObj:Vec_IntEntry(pool,i);
        dst=Cec_TranSimObj(s_CexAug,obj);
        memcpy(dst,Cec_TranSimObj(old,obj),sizeof(word)*old->nSlots);
        dst[old->nSlots]=0;
        for (j=0; j<n; ++j)
        {
            int bit=points[j], value;
            if (s_CexMode==1)
                value=Cec_TranTeachSampleValue(old,obj,j%(64*old->nSlots));
            else {
                if (s_CexMode==3) bit=(bit&~63)+((bit+1)&63);
                value=Cec_TranTeachSampleValue(s_CexLong,obj,bit);
            }
            dst[old->nSlots] |= (word)value<<j;
        }
    }
    for (j=0; j<n; ++j)
    {
        int bit=points[j], value;
        if (s_CexMode==1) value=(oldCare[(j%(64*old->nSlots))>>6]>>(j&63))&1;
        else {
            if (s_CexMode==3) bit=(bit&~63)+((bit+1)&63);
            value=(longCare[bit>>6]>>(bit&63))&1;
        }
        care[old->nSlots] |= (word)value<<j;
    }
    memset(Cec_TranSimObj(s_CexAug,0),0,sizeof(word)*s_CexAug->nSlots);
    if (s_CexMode==2) assert(!Cec_TranRecipeMatchesRoot(s_CexAug,&rep,care));
    buildSim=s_CexAug; buildCare=care;
    if(s_CexCompress) {
        compactCare=Cec_TranCexCompact(s_CexCompress>=3?old:s_CexAug,
            s_CexCompress>=3?oldCare:care,
            s_CexCompress>=3?s_CexLong:NULL,
            s_CexCompress>=3?longCare:NULL,root->iObj,pool);
        buildSim=s_CexPacked; buildCare=compactCare;
    }
    primary=Vec_IntAlloc(pars->nKitCoreMax);
    { abctime cs=Abc_Clock();
    nCore=(s_CexCompress==1?Cec_TranCexSelectWeighted:Cec_TranSelectCareObservedCoreExcept)(buildSim,root->iObj,pool,
        pars->nKitCoreMax,primary,-1,buildCare);
    s_CexSelectTime+=Abc_Clock()-cs;
    }
    nTrials=nCore>0 ? 1+Vec_IntSize(primary) : 1;
    for (trial=0; trial<nTrials; ++trial)
    {
        unsigned off[8]={0}, on[8]={0};
        core=trial ? Vec_IntAlloc(pars->nKitCoreMax) : primary;
        if (trial) {
            abctime cs=Abc_Clock();
            nCore=(s_CexCompress==1?Cec_TranCexSelectWeighted:Cec_TranSelectCareObservedCoreExcept)(buildSim,
                root->iObj,pool,pars->nKitCoreMax,core,
                Vec_IntEntry(primary,trial-1),buildCare);
            s_CexSelectTime+=Abc_Clock()-cs;
        }
        if(s_CexCompress==1) {
            Vec_Int_t * check=Vec_IntAlloc(8);
            int nc=Cec_TranSelectCareObservedCoreExcept(s_CexAug,root->iObj,pool,
                pars->nKitCoreMax,check,trial?Vec_IntEntry(primary,trial-1):-1,care);
            assert(nc==nCore && Vec_IntSize(check)==Vec_IntSize(core));
            for(j=0;j<Vec_IntSize(core);++j) assert(Vec_IntEntry(check,j)==Vec_IntEntry(core,j));
            Vec_IntFree(check);
        }
        if (nCore>0) {
            Cec_TranProjectRootIsfCareRaw(buildSim,root,pool,core,nCore,off,on,buildCare);
            if(s_CexProjectAll &&
                !Cec_TranCexRefineIsf(root->iObj,pool,core,nCore,longCare,off,on))
                goto core_done;
            Cec_TranCollectRootIsfCandidate(buildSim,pars,root,pool,ranks,
                known,&seen,&extra,prof,core,nCore,off,on,0,buildCare);
            if (pars->fBdcPortfolio)
                Cec_TranCollectRootIsfCandidate(buildSim,pars,root,pool,ranks,
                    known,&seen,&extra,prof,core,nCore,off,on,1,buildCare);
        }
core_done:
        if (getenv("ABC_CEX_DETAIL")) {
            Abc_Print(1,"cex-core round=%d root=%d trial=%d n=%d pool=",s_CexRound,root->iObj,trial,nCore);
            Vec_IntForEachEntry(pool,obj,i) Abc_Print(1,"%s%d",i?",":"",obj);
            Abc_Print(1," core=");
            Vec_IntForEachEntry(core,obj,i) Abc_Print(1,"%s%d",i?",":"",Vec_IntEntry(pool,obj));
            Abc_Print(1,"\n");
        }
        if (trial) Vec_IntFree(core);
    }
    for (i=0; i<extra.nSize; ++i) {
        Cec_TranCand_t * c=extra.pArray+i;
        assert(!Cec_TranCandVecContains(&seen,c));
        assert(Cec_TranRecipeMatchesRoot(old,c,oldCare));
        assert(Cec_TranRecipeMatchesRoot(s_CexAug,c,care));
        if(s_CexProjectAll)
            assert(Cec_TranRecipeMatchesRoot(s_CexLong,c,longCare));
        Cec_TranCandVecPush(out,*c);
    }
    s_CexAdded+=extra.nSize;
    if (getenv("ABC_CEX_DETAIL")) {
        Vec_Int_t * nodes=Vec_IntAlloc(32), * ends=Vec_IntAlloc(16);
        int overflow;
        Cec_TranWindowCollect(old->pGia,root->iObj,Cec_TranWindowDepth(pars),
            100-pars->nDepNodesMax,nodes,ends,&overflow);
        Abc_Print(1,"cex-window root=%d nodes=",root->iObj);
        Vec_IntForEachEntry(nodes,obj,i) Abc_Print(1,"%s%d",i?",":"",obj);
        Abc_Print(1," ends=");
        Vec_IntForEachEntry(ends,obj,i) Abc_Print(1,"%s%d",i?",":"",obj);
        Abc_Print(1,"\n"); Vec_IntFree(nodes); Vec_IntFree(ends);
        Abc_Print(1,"cex-reconstruct round=%d mode=%d root=%d old=%d points=%d added=%d rep-hash=%u out=%d recipe=",
            s_CexRound,s_CexMode,root->iObj,oldN,n,extra.nSize,Cec_TranCandHash(&rep),rep.iOut);
        for(i=0;i<2*rep.nGates;++i) Abc_Print(1,"%s%d",i?",":"",rep.Recipe[i]);
        Abc_Print(1," samples=");
        for(i=0;i<n;++i) Abc_Print(1,"%s%d",i?",":"",points[i]);
        Abc_Print(1,"\n");
        for(i=0;i<extra.nSize;++i) {
            Cec_TranCand_t * c=extra.pArray+i;
            Abc_Print(1,"cex-new round=%d root=%d hash=%u gain=%d out=%d recipe=",s_CexRound,root->iObj,Cec_TranCandHash(c),c->Gain,c->iOut);
            for(j=0;j<2*c->nGates;++j) Abc_Print(1,"%s%d",j?",":"",c->Recipe[j]);
            Abc_Print(1,"\n");
        }
    }
    Vec_IntFree(primary); Cec_TranCandVecStop(&extra); Cec_TranCandVecStop(&seen);
    ABC_FREE(compactCare); ABC_FREE(care); ABC_FREE(longCare); s_CexTime+=Abc_Clock()-clk;
}
