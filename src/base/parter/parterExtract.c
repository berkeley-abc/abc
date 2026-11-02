/**CFile****************************************************************

  FileName    [parterExtract.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Acyclic word-level partitioning.]

  Synopsis    [Transactional extraction of assigned SN partitions.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: parterExtract.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "parterExtract.h"
#include "base/sn/snCheck.h"
#include <stdarg.h>
ABC_NAMESPACE_IMPL_START

typedef struct Prtx_Input_t_
{
    unsigned Part, Signal, Copy;
} Prtx_Input_t;

typedef struct Prtx_Part_t_
{
    sn_module_t * pModule;
    sn_vec_t Outputs;
    unsigned Begin, End, Count, InputPorts, OutputPorts;
    uint64_t Fanins;
} Prtx_Part_t;

/**Function*************************************************************

  Synopsis    [Formats a bounded extraction diagnostic.]

***********************************************************************/
static int Prtx_Error( char * pError, unsigned nError, const char * pFormat, ... )
{
    va_list Args;
    if ( pError && nError )
    {
        va_start( Args, pFormat );
        vsnprintf( pError, nError, pFormat, Args );
        va_end( Args );
        pError[nError-1] = 0;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Identifies constants duplicated into each consuming part.]

***********************************************************************/
static int Prtx_Constant( sn_obj_type_t Type )
{
    return Type == SN_CONST0 || Type == SN_CONST1 || Type == SN_CONST;
}

/**Function*************************************************************

  Synopsis    [Chooses a generated name distinct from all existing source names.]

***********************************************************************/
static void Prtx_Name( const sn_module_t * p, const char * pRole, unsigned Id, char * pName, unsigned nName )
{
    unsigned Suffix = 0;
    snprintf(pName,nName,"parter_%s_%u",pRole,Id);
    if ( sn_name_find(&p->design->names,pName) == SN_INVALID_ID ) return;
    do { snprintf(pName,nName,"parter_%s_%u_m%u_%u",pRole,Id,p->id,Suffix++); }
    while ( sn_name_find(&p->design->names,pName) != SN_INVALID_ID );
}

/**Function*************************************************************

  Synopsis    [Sorts interface entries by destination part and original net.]

***********************************************************************/
static int Prtx_Compare( const void * pA, const void * pB )
{
    const Prtx_Input_t * a = (const Prtx_Input_t *)pA;
    const Prtx_Input_t * b = (const Prtx_Input_t *)pB;
    if ( a->Part != b->Part ) return a->Part < b->Part ? -1 : 1;
    return a->Signal < b->Signal ? -1 : a->Signal > b->Signal;
}

/**Function*************************************************************

  Synopsis    [Finds a local copy of a crossing signal or constant.]

***********************************************************************/
static unsigned Prtx_InputCopy( const Prtx_Input_t * pInputs, const Prtx_Part_t * pPart, unsigned Signal )
{
    unsigned Lo = pPart->Begin, Hi = pPart->End;
    while ( Lo < Hi )
    {
        unsigned Mid = Lo + (Hi-Lo)/2;
        if ( pInputs[Mid].Signal < Signal ) Lo = Mid + 1;
        else Hi = Mid;
    }
    return Lo < pPart->End && pInputs[Lo].Signal == Signal ? pInputs[Lo].Copy : SN_INVALID_ID;
}

/**Function*************************************************************

  Synopsis    [Checks labels and groups required by the SN representation.]

***********************************************************************/
static int Prtx_Labels( const sn_module_t * p, const unsigned * pLabels, unsigned nParts,
    Prtx_Part_t * pParts, char * pError, unsigned nError )
{
    unsigned i, k, Other;
    for ( i = 0; i < p->obj_types.size; ++i )
    {
        sn_obj_type_t Type = sn_obj_type( p, i );
        int External = Type == SN_PI || Type == SN_PO || Prtx_Constant( Type );
        if ( External ? pLabels[i] != SN_INVALID_ID : pLabels[i] >= nParts )
            return Prtx_Error( pError, nError, "Invalid partition label on object %u.", i );
        if ( !External ) ++pParts[pLabels[i]].Count;
    }
    for ( i = 0; i < nParts; ++i )
        if ( !pParts[i].Count ) return Prtx_Error( pError, nError, "Partition %u is empty.", i );
    for ( i = 0; i < p->obj_types.size; ++i )
    {
        sn_obj_type_t Type = sn_obj_type( p, i );
        Other = SN_INVALID_ID;
        if ( Type == SN_FAN ) Other = sn_fan_owner( p, i );
        else if ( sn_obj_type_is_pair_out(Type) ) Other = sn_obj_pair_in( p, i );
        else if ( Type == SN_MEM_READ ) Other = sn_obj_fanin( p, i, SN_MEM_READ_MEMORY );
        if ( Other != SN_INVALID_ID && pLabels[i] != pLabels[Other] )
            return Prtx_Error( pError, nError, "Objects %u and %u belong to one mandatory group.", i, Other );
        if ( Type == SN_MEM_IN )
            for ( k = SN_MEM_IN_FIXED_FANIN_COUNT; k < sn_obj_fanin_count(p,i); ++k )
            {
                Other = sn_obj_fanin( p, i, k );
                if ( pLabels[i] != pLabels[Other] )
                    return Prtx_Error( pError, nError, "Memory %u and write port %u cannot be split.", i, Other );
            }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks representation limits before any SN constructor can assert.]

***********************************************************************/
static int Prtx_Limits( const sn_module_t * p, const unsigned * pLabels,
    const unsigned char * pNeeded, const Prtx_Input_t * pInputs, unsigned nInputs,
    Prtx_Part_t * pParts, unsigned nParts, char * pError, unsigned nError )
{
    uint64_t WrapperObjects = p->type_objects[SN_PI].size + p->type_objects[SN_PO].size;
    uint64_t WrapperFanins = p->type_objects[SN_PO].size;
    unsigned i;
    for ( i = 0; i < nInputs; ++i )
        if ( !Prtx_Constant(sn_obj_type(p,pInputs[i].Signal)) ) ++pParts[pInputs[i].Part].InputPorts;
    for ( i = 0; i < p->obj_types.size; ++i )
    {
        if ( pLabels[i] != SN_INVALID_ID )
        {
            pParts[pLabels[i]].Fanins += sn_obj_fanin_count(p,i);
            if ( pNeeded[i] ) ++pParts[pLabels[i]].OutputPorts;
        }
        else if ( pNeeded[i] && Prtx_Constant(sn_obj_type(p,i)) ) ++WrapperObjects;
    }
    for ( i = 0; i < nParts; ++i )
    {
        const Prtx_Part_t * q = pParts+i;
        uint64_t Objects = (uint64_t)q->Count + (q->End-q->Begin) + q->OutputPorts;
        uint64_t Fanins = q->Fanins + q->OutputPorts;
        if ( q->InputPorts > UINT16_MAX )
            return Prtx_Error(pError,nError,"Partition %u needs %u input ports; SN instances support at most %u.",i,q->InputPorts,(unsigned)UINT16_MAX);
        if ( !q->OutputPorts ) { Objects += 2; ++Fanins; }
        if ( Objects >= SN_INVALID_ID || Fanins > UINT32_MAX ||
             Objects > SIZE_MAX/sizeof(unsigned) || Fanins > SIZE_MAX/sizeof(unsigned) )
            return Prtx_Error(pError,nError,"Partition %u exceeds SN object or fanin storage limits.",i);
        ++WrapperObjects;
        WrapperFanins += q->InputPorts;
        if ( q->OutputPorts > 1 ) { WrapperObjects += q->OutputPorts; WrapperFanins += q->OutputPorts; }
    }
    if ( WrapperObjects >= SN_INVALID_ID || WrapperFanins > UINT32_MAX ||
         WrapperObjects > SIZE_MAX/sizeof(unsigned) || WrapperFanins > SIZE_MAX/sizeof(unsigned) )
        return Prtx_Error(pError,nError,"Partition wrapper exceeds SN object or fanin storage limits.");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Topologically orders the complete quotient, counting every input once.]

***********************************************************************/
static int Prtx_Order( const Prtx_Input_t * pInputs, unsigned nInputs, const unsigned * pLabels,
    unsigned nParts, unsigned * pOrder, char * pError, unsigned nError )
{
    unsigned * pDegree = (unsigned *)calloc( nParts, sizeof(unsigned) );
    unsigned * pStart = (unsigned *)calloc( (size_t)nParts+1, sizeof(unsigned) );
    unsigned * pEdges = (unsigned *)malloc( (size_t)(nInputs ? nInputs : 1)*sizeof(unsigned) );
    unsigned * pNext = (unsigned *)calloc( nParts, sizeof(unsigned) );
    unsigned i, nUsed = 0, Head = 0;
    int Ok = 0;
    if ( !pDegree || !pStart || !pEdges || !pNext )
    { Prtx_Error(pError,nError,"Cannot allocate partition order."); goto cleanup; }
    for ( i = 0; i < nInputs; ++i )
    {
        unsigned Driver = pLabels[pInputs[i].Signal];
        if ( Driver == SN_INVALID_ID ) continue;
        ++pDegree[pInputs[i].Part];
        ++pStart[Driver+1];
    }
    for ( i = 0; i < nParts; ++i ) pStart[i+1] += pStart[i];
    memcpy( pNext, pStart, (size_t)nParts*sizeof(unsigned) );
    for ( i = 0; i < nInputs; ++i )
    {
        unsigned Driver = pLabels[pInputs[i].Signal];
        if ( Driver != SN_INVALID_ID ) pEdges[pNext[Driver]++] = pInputs[i].Part;
    }
    for ( i = 0; i < nParts; ++i ) if ( !pDegree[i] ) pOrder[nUsed++] = i;
    while ( Head < nUsed )
    {
        unsigned Part = pOrder[Head++];
        for ( i = pStart[Part]; i < pStart[Part+1]; ++i )
            if ( --pDegree[pEdges[i]] == 0 ) pOrder[nUsed++] = pEdges[i];
    }
    if ( nUsed != nParts ) Prtx_Error(pError,nError,"Partition dependencies contain a cycle; no new loop boundaries are introduced.");
    else Ok = 1;
cleanup:
    free(pDegree); free(pStart); free(pEdges); free(pNext);
    return Ok;
}

/**Function*************************************************************

  Synopsis    [Preserves each source type-list order within every extracted master.]

***********************************************************************/
static void Prtx_TypeOrder( const sn_module_t * pOld, Prtx_Part_t * pParts,
    unsigned nParts, const unsigned * pLabels, const unsigned * pCopies, unsigned * pCounts )
{
    unsigned Type, i;
    for ( Type = 0; Type < SN_OBJ_TYPE_COUNT; ++Type )
    {
        memset(pCounts,0,(size_t)nParts*sizeof(unsigned));
        for ( i = 0; i < pOld->type_objects[Type].size; ++i )
        {
            unsigned Obj = sn_vec_at(unsigned,&pOld->type_objects[Type],i), Part = pLabels[Obj], Index;
            sn_module_t * p;
            if ( Part == SN_INVALID_ID ) continue;
            p = pParts[Part].pModule;
            Index = pCounts[Part]++;
            sn_vec_at(unsigned,&p->type_objects[Type],Index) = pCopies[Obj];
            if ( sn_obj_type_has_dense_index((sn_obj_type_t)Type) ) sn_vec_at(unsigned,&p->obj_data,pCopies[Obj]) = Index;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Copies sparse annotations once, including replicated constants.]

***********************************************************************/
static void Prtx_Annotations( const sn_module_t * pOld, sn_module_t * pWrapper,
    Prtx_Part_t * pParts, unsigned nParts, const unsigned * pLabels,
    const unsigned * pCopies, const unsigned * pWrapperCopies, const Prtx_Input_t * pInputs )
{
    size_t i;
    unsigned j;
    sn_module_dup_module_metadata( pWrapper, pOld );
    for ( i = 0; i < pOld->source_records.size; ++i )
    {
        sn_source_record_t Record = sn_vec_at(sn_source_record_t,&pOld->source_records,i);
        unsigned Obj = Record.object;
        if ( Obj == SN_INVALID_ID ) continue;
        if ( pLabels[Obj] != SN_INVALID_ID )
        { Record.object = pCopies[Obj]; *sn_vec_push(sn_source_record_t,&pParts[pLabels[Obj]].pModule->source_records) = Record; }
        else
        {
            if ( pWrapperCopies[Obj] != SN_INVALID_ID )
            { Record.object = pWrapperCopies[Obj]; *sn_vec_push(sn_source_record_t,&pWrapper->source_records) = Record; }
            if ( Prtx_Constant(sn_obj_type(pOld,Obj)) )
                for ( j = 0; j < nParts; ++j )
                {
                    unsigned Copy = Prtx_InputCopy(pInputs,pParts+j,Obj);
                    if ( Copy != SN_INVALID_ID )
                    { Record.object = Copy; *sn_vec_push(sn_source_record_t,&pParts[j].pModule->source_records) = Record; }
                }
        }
    }
    for ( i = 0; i < pOld->attribute_records.size; ++i )
    {
        sn_attribute_record_t Record = sn_vec_at(sn_attribute_record_t,&pOld->attribute_records,i);
        unsigned Obj = Record.object;
        if ( Obj == SN_INVALID_ID ) continue;
        if ( pLabels[Obj] != SN_INVALID_ID )
        { Record.object = pCopies[Obj]; *sn_vec_push(sn_attribute_record_t,&pParts[pLabels[Obj]].pModule->attribute_records) = Record; }
        else
        {
            if ( pWrapperCopies[Obj] != SN_INVALID_ID )
            { Record.object = pWrapperCopies[Obj]; *sn_vec_push(sn_attribute_record_t,&pWrapper->attribute_records) = Record; }
            if ( Prtx_Constant(sn_obj_type(pOld,Obj)) )
                for ( j = 0; j < nParts; ++j )
                {
                    unsigned Copy = Prtx_InputCopy(pInputs,pParts+j,Obj);
                    if ( Copy != SN_INVALID_ID )
                    { Record.object = Copy; *sn_vec_push(sn_attribute_record_t,&pParts[j].pModule->attribute_records) = Record; }
                }
        }
    }
}

/**Function*************************************************************

  Synopsis    [Extracts an acyclic assignment on a private clone, preserving the master interface.]

***********************************************************************/
static int Prtx_Extract( const sn_design_t * pDesign, int fPrivate, unsigned Master,
    const unsigned * pLabels, unsigned nParts, sn_design_t ** ppResult,
    Prt_ExtractStats_t * pStats, Prt_ExtractMap_t ** ppMap, char * pError, unsigned nError )
{
    const sn_module_t * pSource;
    sn_module_t * pOld = NULL, * pWrapper = NULL;
    sn_design_t * pCopy = NULL;
    Prtx_Part_t * pParts = NULL;
    Prtx_Input_t * pInputs = NULL;
    unsigned * pCopies = NULL, * pWrapperCopies = NULL, * pOrder = NULL, * pInstInputs = NULL;
    unsigned char * pNeeded = NULL;
    unsigned nObjects, nInputs = 0, i, j, k;
    Prt_ExtractStats_t Stats;
    Prt_ExtractMap_t * pMap = NULL;
    int Ok = 0;
    if ( ppResult ) *ppResult = NULL;
    if ( ppMap ) *ppMap = NULL;
    if ( pError && nError ) pError[0] = 0;
    memset( &Stats, 0, sizeof(Stats) );
    if ( !ppResult || !pDesign || Master >= pDesign->modules.size || !pLabels || !nParts )
        return Prtx_Error(pError,nError,"Invalid partition extraction arguments.");
    if ( !fPrivate && !sn_design_check_output(pDesign,NULL,false) ) return Prtx_Error(pError,nError,"Input SN design is invalid.");
    pSource = sn_design_get_module_const( pDesign, Master );
    nObjects = (unsigned)pSource->obj_types.size;
    if ( sn_module_is_blackbox(pSource) || nParts > nObjects ||
         pDesign->modules.size >= (size_t)SN_INVALID_ID - nParts ||
         pSource->fanins.size > UINT32_MAX ||
         pSource->fanins.size > SIZE_MAX / sizeof(Prtx_Input_t) ||
         (nObjects && sizeof(unsigned) > SIZE_MAX / nObjects) ||
         sizeof(Prtx_Part_t) > SIZE_MAX / nParts )
        return Prtx_Error(pError,nError,"Cannot extract this master or partition count.");
    pParts = (Prtx_Part_t *)calloc(nParts,sizeof(Prtx_Part_t));
    pCopies = (unsigned *)malloc((size_t)nObjects*sizeof(unsigned));
    pWrapperCopies = (unsigned *)malloc((size_t)nObjects*sizeof(unsigned));
    pNeeded = (unsigned char *)calloc(nObjects,1);
    pOrder = (unsigned *)malloc((size_t)nParts*sizeof(unsigned));
    pInputs = (Prtx_Input_t *)malloc((pSource->fanins.size ? pSource->fanins.size : 1)*sizeof(Prtx_Input_t));
    pInstInputs = (unsigned *)malloc((size_t)(nObjects ? nObjects : 1)*sizeof(unsigned));
    if ( !pParts || !pCopies || !pWrapperCopies || !pNeeded || !pOrder || !pInputs || !pInstInputs )
    { Prtx_Error(pError,nError,"Cannot allocate extraction workspace."); goto cleanup; }
    memset(pCopies,255,(size_t)nObjects*sizeof(unsigned));
    memset(pWrapperCopies,255,(size_t)nObjects*sizeof(unsigned));
    if ( !Prtx_Labels(pSource,pLabels,nParts,pParts,pError,nError) ) goto cleanup;
    // Bit 1 preserves an unused constant in the wrapper, including its annotations.
    for ( i = 0; i < nObjects; ++i )
        if ( Prtx_Constant(sn_obj_type(pSource,i)) ) pNeeded[i] = 2;
    for ( i = 0; i < nObjects; ++i )
    {
        sn_obj_type_t Type = sn_obj_type(pSource,i);
        if ( Type == SN_PO ) pNeeded[sn_obj_fanin(pSource,i,0)] = 1;
        if ( pLabels[i] == SN_INVALID_ID ) continue;
        for ( j = 0; j < sn_obj_fanin_count(pSource,i); ++j )
        {
            unsigned Signal = sn_obj_fanin(pSource,i,j);
            if ( Signal == SN_INVALID_ID || pLabels[Signal] == pLabels[i] ) continue;
            if ( Prtx_Constant(sn_obj_type(pSource,Signal)) ) pNeeded[Signal] &= 1;
            if ( sn_obj_type(pSource,Signal) == SN_PO || !sn_obj_width(pSource,Signal) )
            { Prtx_Error(pError,nError,"Object %u cannot cross a partition boundary.",Signal); goto cleanup; }
            pInputs[nInputs].Part = pLabels[i]; pInputs[nInputs].Signal = Signal;
            pInputs[nInputs++].Copy = SN_INVALID_ID;
            if ( pLabels[Signal] != SN_INVALID_ID ) pNeeded[Signal] = 1;
        }
    }
    qsort(pInputs,nInputs,sizeof(Prtx_Input_t),Prtx_Compare);
    for ( i = k = 0; i < nInputs; ++i )
        if ( !k || Prtx_Compare(pInputs+i,pInputs+k-1) ) pInputs[k++] = pInputs[i];
    nInputs = k;
    for ( i = k = 0; i < nParts; ++i )
    {
        pParts[i].Begin = k;
        while ( k < nInputs && pInputs[k].Part == i ) ++k;
        pParts[i].End = k;
    }
    if ( !Prtx_Limits(pSource,pLabels,pNeeded,pInputs,nInputs,pParts,nParts,pError,nError) ||
         !Prtx_Order(pInputs,nInputs,pLabels,nParts,pOrder,pError,nError) ) goto cleanup;
    pCopy = fPrivate ? (sn_design_t *)pDesign : sn_design_dup(pDesign);
    if ( !pCopy ) { Prtx_Error(pError,nError,"Cannot clone extraction design."); goto cleanup; }
    pOld = sn_design_get_module(pCopy,Master);
    pWrapper = (sn_module_t *)calloc(1,sizeof(sn_module_t));
    if ( !pWrapper ) { Prtx_Error(pError,nError,"Cannot allocate partition wrapper."); goto cleanup; }
    sn_module_init(pWrapper,pCopy,Master,pOld->name);
    pWrapper->flags = pOld->flags;
    for ( i = 0; i < nParts; ++i )
    {
        char Name[96];
        unsigned Suffix = 0, Id;
        do { snprintf(Name,sizeof(Name),"parter_m%u_p%u_%u",Master,i,Suffix++); }
        while ( sn_name_find(&pCopy->names,Name) != SN_INVALID_ID );
        Id = sn_design_add_module(pCopy,Name);
        pParts[i].pModule = sn_design_get_module(pCopy,Id);
        sn_vec_init(&pParts[i].Outputs);
        for ( j = pParts[i].Begin; j < pParts[i].End; ++j )
        {
            unsigned Signal = pInputs[j].Signal;
            if ( Prtx_Constant(sn_obj_type(pOld,Signal)) ) continue;
            Prtx_Name(pParts[i].pModule,"in",Signal,Name,sizeof(Name));
            pInputs[j].Copy = sn_module_add_pi(pParts[i].pModule,sn_obj_width(pOld,Signal),sn_obj_is_signed(pOld,Signal),Name);
            ++Stats.nInputPorts; Stats.InputBits += sn_obj_width(pOld,Signal);
        }
        for ( j = pParts[i].Begin; j < pParts[i].End; ++j )
        {
            unsigned Signal = pInputs[j].Signal;
            if ( !Prtx_Constant(sn_obj_type(pOld,Signal)) ) continue;
            pInputs[j].Copy = sn_module_dup_obj_skeleton(pParts[i].pModule,pOld,Signal);
            sn_module_dup_obj_data(pParts[i].pModule,pInputs[j].Copy,pOld,Signal);
        }
    }
    for ( i = 0; i < nObjects; ++i )
        if ( pLabels[i] != SN_INVALID_ID )
        {
            sn_module_t * pPart = pParts[pLabels[i]].pModule;
            pCopies[i] = sn_module_dup_obj_skeleton(pPart,pOld,i);
            sn_module_dup_obj_data(pPart,pCopies[i],pOld,i);
        }
    for ( i = 0; i < nObjects; ++i )
        if ( pLabels[i] != SN_INVALID_ID )
        {
            unsigned Part = pLabels[i];
            for ( j = 0; j < sn_obj_fanin_count(pOld,i); ++j )
            {
                unsigned Signal = sn_obj_fanin(pOld,i,j), Copy;
                Copy = Signal == SN_INVALID_ID ? SN_INVALID_ID : pLabels[Signal] == Part ? pCopies[Signal] :
                    Prtx_InputCopy(pInputs,pParts+Part,Signal);
                assert( Signal == SN_INVALID_ID || Copy != SN_INVALID_ID );
                sn_obj_connect(pParts[Part].pModule,pCopies[i],j,Copy);
            }
            if ( pNeeded[i] ) *sn_vec_push(unsigned,&pParts[Part].Outputs) = i;
        }
    Prtx_TypeOrder(pOld,pParts,nParts,pLabels,pCopies,pInstInputs);
    for ( i = 0; i < nParts; ++i )
    {
        sn_module_t * pPart = pParts[i].pModule;
        sn_module_link_pairs(pPart);
        for ( j = 0; j < pParts[i].Outputs.size; ++j )
        {
            unsigned Signal = sn_vec_at(unsigned,&pParts[i].Outputs,j);
            char Name[64];
            Prtx_Name(pPart,"out",Signal,Name,sizeof(Name));
            sn_module_add_po(pPart,sn_obj_width(pOld,Signal),sn_obj_is_signed(pOld,Signal),Name,pCopies[Signal]);
            ++Stats.nOutputPorts; Stats.OutputBits += sn_obj_width(pOld,Signal);
        }
        if ( !pParts[i].Outputs.size )
        {
            uint32_t Word = 0;
            unsigned Zero = sn_module_add_const(pPart,1,false,&Word,NULL);
            char Name[64];
            Prtx_Name(pPart,"unused",0,Name,sizeof(Name));
            sn_module_add_po(pPart,1,false,Name,Zero);
            ++Stats.nDummyOutputs; ++Stats.nOutputPorts; ++Stats.OutputBits;
        }
    }
    for ( i = 0; i < pOld->type_objects[SN_PI].size; ++i )
    {
        unsigned Obj = sn_vec_at(unsigned,&pOld->type_objects[SN_PI],i);
        pWrapperCopies[Obj] = sn_module_dup_obj_skeleton(pWrapper,pOld,Obj);
    }
    for ( i = 0; i < nObjects; ++i )
        if ( Prtx_Constant(sn_obj_type(pOld,i)) && pNeeded[i] )
        {
            pWrapperCopies[i] = sn_module_dup_obj_skeleton(pWrapper,pOld,i);
            sn_module_dup_obj_data(pWrapper,pWrapperCopies[i],pOld,i);
        }
    for ( i = 0; i < nParts; ++i )
    {
        unsigned Part = pOrder[i], nActual = 0, Inst;
        char Name[64];
        for ( j = pParts[Part].Begin; j < pParts[Part].End; ++j )
            if ( !Prtx_Constant(sn_obj_type(pOld,pInputs[j].Signal)) )
            {
                unsigned Copy = pWrapperCopies[pInputs[j].Signal];
                assert(Copy != SN_INVALID_ID);
                pInstInputs[nActual++] = Copy;
            }
        Prtx_Name(pWrapper,"part",Part,Name,sizeof(Name));
        Inst = sn_module_add_inst(pWrapper,pParts[Part].pModule->id,nActual,pInstInputs,Name,NULL);
        for ( j = 0; j < pParts[Part].Outputs.size; ++j )
        {
            unsigned Signal = sn_vec_at(unsigned,&pParts[Part].Outputs,j);
            pWrapperCopies[Signal] = pParts[Part].Outputs.size == 1 ? Inst : Inst+1+j;
        }
    }
    for ( i = 0; i < pOld->type_objects[SN_PO].size; ++i )
    {
        unsigned Obj = sn_vec_at(unsigned,&pOld->type_objects[SN_PO],i);
        unsigned Signal = sn_obj_fanin(pOld,Obj,0);
        pWrapperCopies[Obj] = sn_module_dup_obj_skeleton(pWrapper,pOld,Obj);
        sn_obj_connect(pWrapper,pWrapperCopies[Obj],0,pWrapperCopies[Signal]);
    }
    Prtx_Annotations(pOld,pWrapper,pParts,nParts,pLabels,pCopies,pWrapperCopies,pInputs);
    if ( ppMap )
    {
        pMap = (Prt_ExtractMap_t *)calloc(1,sizeof(Prt_ExtractMap_t));
        if ( !pMap ) { Prtx_Error(pError,nError,"Cannot allocate object correspondence."); goto cleanup; }
        pMap->nObjects = nObjects;
        pMap->pModule = (unsigned *)malloc((size_t)nObjects*sizeof(unsigned));
        pMap->pObject = (unsigned *)malloc((size_t)nObjects*sizeof(unsigned));
        if ( !pMap->pModule || !pMap->pObject ) { Prtx_Error(pError,nError,"Cannot allocate object correspondence."); goto cleanup; }
        for ( i = 0; i < nObjects; ++i )
        {
            unsigned Part = pLabels[i];
            if ( Prtx_Constant(sn_obj_type(pOld,i)) ) pMap->pModule[i] = pMap->pObject[i] = SN_INVALID_ID;
            else
            {
                pMap->pModule[i] = Part == SN_INVALID_ID ? Master : pParts[Part].pModule->id;
                pMap->pObject[i] = Part == SN_INVALID_ID ? pWrapperCopies[i] : pCopies[i];
            }
        }
    }
    pWrapper->interface_locked = pOld->interface_locked;
    sn_design_invalidate_copies_to_module(pCopy,Master);
    sn_vec_at(sn_module_t *,&pCopy->modules,Master) = pWrapper;
    pWrapper = NULL;
    sn_module_destroy(pOld); free(pOld); pOld = NULL;
    if ( fPrivate )
    {
        if ( !sn_module_check_local(sn_design_get_module_const(pCopy,Master),NULL) )
        { Prtx_Error(pError,nError,"Extracted wrapper failed SN validation."); goto cleanup; }
        for ( i = 0; i < nParts; ++i )
            if ( !sn_module_check_local(pParts[i].pModule,NULL) )
            { Prtx_Error(pError,nError,"Extracted part failed SN validation."); goto cleanup; }
    }
    else if ( !sn_design_check_output(pCopy,NULL,false) )
    { Prtx_Error(pError,nError,"Extracted hierarchy failed SN validation."); goto cleanup; }
    Stats.nParts = nParts;
    *ppResult = pCopy; pCopy = NULL;
    if ( pStats ) *pStats = Stats;
    if ( ppMap ) { *ppMap = pMap; pMap = NULL; }
    Ok = 1;
cleanup:
    Prt_ExtractMapFree(pMap);
    if ( pWrapper ) { sn_module_destroy(pWrapper); free(pWrapper); }
    if ( pCopy && !fPrivate ) sn_design_destroy(pCopy);
    if ( pParts ) for ( i = 0; i < nParts; ++i ) sn_vec_destroy(&pParts[i].Outputs);
    free(pParts); free(pCopies); free(pWrapperCopies); free(pNeeded);
    free(pOrder); free(pInputs); free(pInstInputs);
    return Ok;
}

/**Function*************************************************************

  Synopsis    [Extracts on a clone and publishes only a fully checked design.]

***********************************************************************/
int Prt_SnExtractMapped( const sn_design_t * pDesign, unsigned Master,
    const unsigned * pLabels, unsigned nParts, sn_design_t ** ppResult,
    Prt_ExtractStats_t * pStats, Prt_ExtractMap_t ** ppMap, char * pError, unsigned nError )
{
    return Prtx_Extract(pDesign,0,Master,pLabels,nParts,ppResult,pStats,ppMap,pError,nError);
}

/**Function*************************************************************

  Synopsis    [Updates a private checked design; failure requires discarding that design.]

***********************************************************************/
int Prt_SnExtractPrivateMapped( sn_design_t * pDesign, unsigned Master,
    const unsigned * pLabels, unsigned nParts, sn_design_t ** ppResult,
    Prt_ExtractStats_t * pStats, Prt_ExtractMap_t ** ppMap, char * pError, unsigned nError )
{
    return Prtx_Extract(pDesign,1,Master,pLabels,nParts,ppResult,pStats,ppMap,pError,nError);
}

/**Function*************************************************************

  Synopsis    [Releases a caller-owned extraction correspondence.]

***********************************************************************/
void Prt_ExtractMapFree( Prt_ExtractMap_t * pMap )
{
    if ( !pMap ) return;
    free(pMap->pModule); free(pMap->pObject); free(pMap);
}

/**Function*************************************************************

  Synopsis    [Extracts a partition assignment when no explicit correspondence is needed.]

***********************************************************************/
int Prt_SnExtract( const sn_design_t * pDesign, unsigned Master,
    const unsigned * pLabels, unsigned nParts, sn_design_t ** ppResult,
    Prt_ExtractStats_t * pStats, char * pError, unsigned nError )
{
    return Prt_SnExtractMapped(pDesign,Master,pLabels,nParts,ppResult,pStats,NULL,pError,nError);
}

ABC_NAMESPACE_IMPL_END
