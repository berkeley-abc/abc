// Pool-local observational quotient. Rows merge only when all divisor bits
// AND the target bit match; multiplicity is retained separately. Only care=1
// rows enter. No state projection or cross-snapshot equivalence is assumed.
static int s_CexCompress, s_CexThisConflict, s_CexNarrowing;
static int s_CexPackDefault;
static long long s_CexNarrowRoots, s_CexNarrowDivsBefore, s_CexNarrowDivsAfter;
static abctime s_CexNativeTime, s_CexDiscoveryTime;
static Cec_TranSim_t * s_CexPacked;
static int * s_CexWeights;
static long long s_CexRawRows, s_CexUniqueRows, s_CexTables, s_CexPoolConflict;
static abctime s_CexPackTime, s_CexSelectTime, s_CexConstructTime;
// Same bit transpose as Extra_Transpose64 (extraUtilMisc.c), with reversed
// input/output indices below to preserve natural lane and divisor numbering.
static void Cec_TranCexTranspose(word a[64])
{
    int j,k; word t,m=ABC_CONST(0x00000000ffffffff);
    for(j=32;j;j>>=1,m^=m<<j)
        for(k=0;k<64;k=(k+j+1)&~j) {
            t=(a[k]^(a[k+j]>>j))&m; a[k]^=t; a[k+j]^=t<<j;
        }
}
// Source and destination may alias: all source rows are read before writing
// the compacted signatures. The caller owns destination capacity and care.
static word * Cec_TranCexCompactInto(Cec_TranSim_t * a, word const * ca,
    Cec_TranSim_t * b, word const * cb, int target, Vec_Int_t * pool,
    Cec_TranSim_t * pPacked, int * pfConflict)
{
    int nDiv=Vec_IntSize(pool), nKey=(nDiv+63)/64;
    int maxRows=64*(a->nSlots+(b?b->nSlots:0)), cap=1, n=0;
    int side,s,i,j,obj,keyRow,lab,slot, fConflict=0;
    int * hash, * labels;
    word * keys, * key, * care, * rows;
    int fast=getenv("ABC_CEX_PACK_FAST")?atoi(getenv("ABC_CEX_PACK_FAST")):s_CexPackDefault;
    abctime clk=Abc_Clock();
    while(cap<2*maxRows) cap*=2;
    hash=ABC_CALLOC(int,cap); labels=ABC_ALLOC(int,maxRows);
    keys=ABC_CALLOC(word,(size_t)maxRows*nKey); key=ABC_ALLOC(word,nKey);
    ABC_FREE(s_CexWeights); s_CexWeights=ABC_CALLOC(int,maxRows);
    rows=fast?ABC_ALLOC(word,(size_t)maxRows*nKey):NULL;
    for(side=0;side<(b?2:1);++side) {
        Cec_TranSim_t * sim=side?b:a; word const * mask=side?cb:ca;
        if(fast) {
            int block,wordSlot,lane,d;
            for(wordSlot=0;wordSlot<sim->nSlots;++wordSlot)
                for(block=0;block<nKey;++block) {
                    word matrix[64]={0};
                    for(d=0;d<64 && 64*block+d<nDiv;++d)
                        matrix[63-d]=Cec_TranSimObj(sim,Vec_IntEntry(pool,64*block+d))[wordSlot];
                    Cec_TranCexTranspose(matrix);
                    for(lane=0;lane<64;++lane)
                        rows[(size_t)(64*wordSlot+lane)*nKey+block]=matrix[63-lane];
                }
        }
        for(s=0;s<64*sim->nSlots;++s) {
            word h=ABC_CONST(0x9e3779b97f4a7c15);
            if(mask && !((mask[s>>6]>>(s&63))&1)) continue;
            if(fast) memcpy(key,rows+(size_t)s*nKey,nKey*sizeof(word));
            else {
                memset(key,0,nKey*sizeof(word));
                Vec_IntForEachEntry(pool,obj,i)
                    key[i>>6] |= (word)Cec_TranTeachSampleValue(sim,obj,s)<<(i&63);
            }
            if(fast && getenv("ABC_CEX_PACK_AUDIT"))
                Vec_IntForEachEntry(pool,obj,i)
                    assert(((key[i>>6]>>(i&63))&1)==Cec_TranTeachSampleValue(sim,obj,s));
            lab=Cec_TranTeachSampleValue(sim,target,s);
            for(i=0;i<nKey;++i) h=Cec_TranResidualMix(h^key[i]);
            { int other=Cec_TranResidualMix(h^(1-lab))&(cap-1);
              while(hash[other]) {
                int row=hash[other]-1;
                if(labels[row]!=lab && !memcmp(keys+(size_t)row*nKey,key,nKey*sizeof(word))) {
                    fConflict=1; break;
                }
                other=(other+1)&(cap-1);
              }
            }
            h=Cec_TranResidualMix(h^lab); slot=h&(cap-1);
            while(hash[slot]) {
                keyRow=hash[slot]-1;
                if(labels[keyRow]==lab && !memcmp(keys+(size_t)keyRow*nKey,key,nKey*sizeof(word))) break;
                slot=(slot+1)&(cap-1);
            }
            if(!hash[slot]) {
                hash[slot]=n+1; labels[n]=lab;
                memcpy(keys+(size_t)n*nKey,key,nKey*sizeof(word)); n++;
            }
            s_CexWeights[hash[slot]-1]++; s_CexRawRows++;
        }
    }
    pPacked->nSlots=Abc_MaxInt(1,(n+63)/64);
    pPacked->nWords=pPacked->nSlots; pPacked->nFrames=1;
    care=ABC_CALLOC(word,pPacked->nSlots);
    if(fast>=2) {
        int block,wordSlot,lane,d;
        word * dst=Cec_TranSimObj(pPacked,target);
        memset(dst,0,pPacked->nSlots*sizeof(word));
        for(j=0;j<n;++j) dst[j>>6]|=(word)labels[j]<<(j&63);
        for(wordSlot=0;wordSlot<pPacked->nSlots;++wordSlot)
            for(block=0;block<nKey;++block) {
                word matrix[64]={0};
                for(lane=0;lane<64 && 64*wordSlot+lane<n;++lane)
                    matrix[63-lane]=keys[(size_t)(64*wordSlot+lane)*nKey+block];
                Cec_TranCexTranspose(matrix);
                for(d=0;d<64 && 64*block+d<nDiv;++d)
                    Cec_TranSimObj(pPacked,Vec_IntEntry(pool,64*block+d))[wordSlot]=matrix[63-d];
            }
        if(getenv("ABC_CEX_PACK_AUDIT"))
            for(j=0;j<n;++j)
                Vec_IntForEachEntry(pool,obj,i)
                    assert(Cec_TranTeachSampleValue(pPacked,obj,j)==((keys[(size_t)j*nKey+(i>>6)]>>(i&63))&1));
    }
    else {
    for(i=-1;i<nDiv;++i) {
        word * dst=Cec_TranSimObj(pPacked,i<0?target:Vec_IntEntry(pool,i));
        memset(dst,0,pPacked->nSlots*sizeof(word));
        for(j=0;j<n;++j) {
            int value=i<0?labels[j]:((keys[(size_t)j*nKey+(i>>6)]>>(i&63))&1);
            dst[j>>6] |= (word)value<<(j&63);
        }
    }
    }
    memset(Cec_TranSimObj(pPacked,0),0,pPacked->nSlots*sizeof(word));
    for(j=0;j<n;++j) care[j>>6]|=(word)1<<(j&63);
    s_CexTables++; s_CexUniqueRows+=n; s_CexPoolConflict+=fConflict;
    *pfConflict=fConflict;
    if(getenv("ABC_CEX_DETAIL") && s_CexCompress>=4 && !s_CexNarrowing && Cec_TranResidualMix(target)%64==0) {
        int raw=0;
        for(j=0;j<n;++j) raw+=s_CexWeights[j];
        Abc_Print(1,"cex-quotient root=%d raw=%d rows=%d conflict=%d pool=",target,raw,n,fConflict);
        Vec_IntForEachEntry(pool,obj,i) Abc_Print(1,"%s%d",i?",":"",obj);
        Abc_Print(1,"\n");
        for(j=0;j<n;++j) {
            Abc_Print(1,"cex-qrow root=%d row=%d label=%d weight=%d key=",target,j,labels[j],s_CexWeights[j]);
            for(i=0;i<nKey;++i) Abc_Print(1,"%s%llx",i?",":"",(unsigned long long)keys[(size_t)j*nKey+i]);
            Abc_Print(1,"\n");
        }
    }
    ABC_FREE(hash); ABC_FREE(labels); ABC_FREE(keys); ABC_FREE(key); ABC_FREE(rows);
    s_CexPackTime+=Abc_Clock()-clk;
    return care;
}
static word * Cec_TranCexCompact(Cec_TranSim_t * a, word const * ca,
    Cec_TranSim_t * b, word const * cb, int target, Vec_Int_t * pool)
{
    return Cec_TranCexCompactInto(a,ca,b,cb,target,pool,s_CexPacked,&s_CexThisConflict);
}
static int Cec_TranCexWeightedCount(int slot, word bits)
{
    int count=0, bit=0;
    for ( ; bits; bits >>= 1, bit++ )
        if ( bits & 1 ) count += s_CexWeights[64*slot+bit];
    return count;
}

static int Cec_TranCexSelectWeighted( Cec_TranSim_t * pSim,
    int iTarget, Vec_Int_t * vPool, int nCoreMax, Vec_Int_t * vCoreRanks,
    int iForbiddenRank, word const * pCare )
{
    int Totals[256][2] = {{0}}, NextTotals[256][2] = {{0}};
    int nSlots = pSim->nSlots, nDivs = Vec_IntSize(vPool);
    int nGroups = 1, nCore = 0, nGroupsMax = 1 << nCoreMax;
    word * pCurrent = ABC_CALLOC( word, 2 * nGroupsMax * nSlots );
    word * pNext = ABC_CALLOC( word, 2 * nGroupsMax * nSlots );
    char * pSelected = ABC_CALLOC( char, nDivs );
    word * pTarget = Cec_TranSimObj( pSim, iTarget );
    int g, i, k, s, iBest, nNextGroups;
    assert( nCoreMax > 0 && nCoreMax <= 8 );
    Vec_IntClear( vCoreRanks );
    for ( s = 0; s < nSlots; s++ )
    {
        pCurrent[s] = ~pTarget[s] & (pCare ? pCare[s] : ~(word)0);
        pCurrent[nSlots + s] = pTarget[s] & (pCare ? pCare[s] : ~(word)0);
        Totals[0][0] += Cec_TranCexWeightedCount(s,  pCurrent[s] );
        Totals[0][1] += Cec_TranCexWeightedCount(s,  pCurrent[nSlots + s] );
    }
    if ( Totals[0][0] == 0 || Totals[0][1] == 0 )
        nGroups = 0;
    while ( nGroups && nCore < nCoreMax )
    {
        long long BestScore = 0;
        iBest = -1;
        for ( i = 0; i < nDivs; i++ )
            if ( i != iForbiddenRank && !pSelected[i] )
            {
                long long Score = 0;
                word * pDiv = Cec_TranSimObj( pSim,
                    Vec_IntEntry(vPool, i) );
                for ( g = 0; g < nGroups; g++ )
                {
                    int nOff1 = 0, nOn1 = 0;
                    for ( s = 0; s < nSlots; s++ )
                    {
                        nOff1 += Cec_TranCexWeightedCount(s,
                            pCurrent[(2*g)*nSlots + s] & pDiv[s] );
                        nOn1 += Cec_TranCexWeightedCount(s,
                            pCurrent[(2*g+1)*nSlots + s] & pDiv[s] );
                    }
                    Score += (long long)nOff1 *
                        (Totals[g][1] - nOn1) +
                        (long long)nOn1 * (Totals[g][0] - nOff1);
                }
                if ( Score > BestScore )
                    iBest = i, BestScore = Score;
            }
        if ( iBest < 0 )
            break;
        pSelected[iBest] = 1;
        Vec_IntPush( vCoreRanks, iBest );
        nCore++;
        nNextGroups = 0;
        memset( NextTotals, 0, sizeof(NextTotals) );
        for ( g = 0; g < nGroups; g++ )
            for ( k = 0; k < 2; k++ )
            {
                int nOff = 0, nOn = 0;
                word * pDiv = Cec_TranSimObj( pSim,
                    Vec_IntEntry(vPool, iBest) );
                for ( s = 0; s < nSlots; s++ )
                {
                    word Phase = k ? pDiv[s] : ~pDiv[s];
                    word Off = pCurrent[(2*g)*nSlots + s] & Phase;
                    word On = pCurrent[(2*g+1)*nSlots + s] & Phase;
                    pNext[(2*nNextGroups)*nSlots + s] = Off;
                    pNext[(2*nNextGroups+1)*nSlots + s] = On;
                    nOff += Cec_TranCexWeightedCount(s,  Off );
                    nOn += Cec_TranCexWeightedCount(s,  On );
                }
                if ( nOff && nOn )
                {
                    NextTotals[nNextGroups][0] = nOff;
                    NextTotals[nNextGroups][1] = nOn;
                    nNextGroups++;
                    assert( nNextGroups <= nGroupsMax );
                }
            }
        {
            word * pTemp = pCurrent;
            pCurrent = pNext;
            pNext = pTemp;
        }
        memcpy( Totals, NextTotals, sizeof(Totals) );
        nGroups = nNextGroups;
    }
    ABC_FREE( pSelected );
    ABC_FREE( pNext );
    ABC_FREE( pCurrent );
    return nGroups ? -1 : nCore;
}
