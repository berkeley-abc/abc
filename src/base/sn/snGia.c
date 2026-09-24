/**CFile****************************************************************

  FileName    [snGia.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Reusable SN extraction and ordered GIA interfaces.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snGia.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#include "snGia.h"
#include "snStitch.h"
#include "misc/util/utilNam.h"
ABC_NAMESPACE_IMPL_START

extern Gia_Man_t * Gia_ManFromMiniAig( Mini_Aig_t * p, Vec_Int_t ** pvCopies, int fGiaSimple );

Gia_Man_t * Sn_DesignToGia( const sn_design_t * pDesign, sn_module_id_t Top,
    const sn_blast_options_t * pOptions, sn_blast_boundary_t * pBoundary, Sn_GiaResult_t * pResult )
{
    Sn_GiaResult_t Result = {0};
    Gia_Man_t * pGia;
    Mini_Aig_t * pMini;
    abctime Start;
    if ( pResult ) memset(pResult, 0, sizeof(*pResult));
    if ( !pDesign || Top >= pDesign->modules.size || !pOptions || !pBoundary ||
         pBoundary->occurrences.size || pBoundary->cis.size || pBoundary->cos.size )
        return NULL;
    Start = Abc_Clock();
    pMini = sn_design_blast_hier_boundary_options(pDesign, Top, *pOptions, &Result.Stats, pBoundary);
    Result.BlastTime = Abc_Clock() - Start;
    if ( !pMini ) return NULL;
    Result.MiniAnds = Mini_AigAndNum(pMini);
    Start = Abc_Clock();
    pGia = Gia_ManFromMiniAig(pMini, NULL, 0);
    Result.ImportTime = Abc_Clock() - Start;
    Mini_AigStop(pMini);
    if ( pResult ) *pResult = Result;
    return pGia;
}

void Sn_GiaSetNames( Gia_Man_t * pGia, const sn_design_t * pDesign,
                     sn_module_id_t Top, const sn_blast_boundary_t * pBoundary, int fOmitLoops,
                            int * pNonCanonical, int * pDuplicates )
{
    Abc_Nam_t * pNam = Abc_NamStart( (int)(pBoundary->cis.size + pBoundary->cos.size) + 16, 32 );
    int nNonCanonical = 0, nDuplicates = 0;
    size_t i;
    assert( pGia && (fOmitLoops || (size_t)Gia_ManCiNum(pGia) == pBoundary->cis.size) );
    assert( fOmitLoops || (size_t)Gia_ManCoNum(pGia) == pBoundary->cos.size );
    if ( pGia->vNamesIn )
        Vec_PtrFreeFree( pGia->vNamesIn );
    if ( pGia->vNamesOut )
        Vec_PtrFreeFree( pGia->vNamesOut );
    pGia->vNamesIn = Vec_PtrAlloc( Gia_ManCiNum(pGia) );
    pGia->vNamesOut = Vec_PtrAlloc( Gia_ManCoNum(pGia) );
    for ( i = 0; i < pBoundary->cis.size + pBoundary->cos.size; i++ )
    {
        int fCi = i < pBoundary->cis.size;
        const sn_blast_boundary_bit_t * pBit = fCi
            ? &sn_vec_at(sn_blast_boundary_bit_t, &pBoundary->cis, i)
            : &sn_vec_at(sn_blast_boundary_bit_t, &pBoundary->cos, i - pBoundary->cis.size);
        if ( fOmitLoops && (pBit->kind == SN_BLAST_BOUNDARY_LOOP_INPUT || pBit->kind == SN_BLAST_BOUNDARY_LOOP_OUTPUT) )
            continue;
        bool fCanonical = true;
        char * pName = sn_blast_boundary_bit_name( pDesign, pBoundary, pBit, &fCanonical );
        int fFound = 0, nSuffix = 1;
        Abc_NamStrFindOrAdd( pNam, pName, &fFound );
        if ( fFound )
        {
            size_t Length = strlen( pName );
            char * pUnique = ABC_ALLOC( char, Length + 24 );
            do
                snprintf( pUnique, Length + 24, "%s#%d", pName, ++nSuffix );
            while ( Abc_NamStrFindOrAdd(pNam, pUnique, &fFound), fFound );
            free( pName );
            pName = Abc_UtilStrsav( pUnique );
            ABC_FREE( pUnique );
            nDuplicates++;
        }
        else
        {
            char * pCopy = Abc_UtilStrsav( pName );
            free( pName );
            pName = pCopy;
        }
        nNonCanonical += !fCanonical;
        Vec_PtrPush( fCi ? pGia->vNamesIn : pGia->vNamesOut, pName );
    }
    Abc_NamStop( pNam );
    assert( Vec_PtrSize(pGia->vNamesIn) == Gia_ManCiNum(pGia) );
    assert( Vec_PtrSize(pGia->vNamesOut) == Gia_ManCoNum(pGia) );
    ABC_FREE( pGia->pName );
    pGia->pName = Abc_UtilStrsav(
        (char *)sn_name_get(&pDesign->names, sn_design_get_module_const(pDesign, Top)->name) );
    if ( pNonCanonical )
        *pNonCanonical = nNonCanonical;
    if ( pDuplicates )
        *pDuplicates = nDuplicates;
}

typedef struct Sn_CutContext_t_
{
    const Sn_GiaOptions_t * pOptions;
    const sn_design_t * pDesign;
    unsigned char * pModules, * pInstances;
    int fCovered;
} Sn_CutContext_t;

// Names are used solely to resolve the user's selection, never to order endpoints.
static char * Sn_GiaInstanceName( const sn_module_t * pModule, sn_obj_id_t Inst )
{
    char Buffer[32];
    const char * pName = sn_obj_name_id(pModule, Inst) == SN_INVALID_ID ? "" : sn_obj_name(pModule, Inst);
    if (*pName) return Abc_UtilStrsav((char *)pName);
    // An unnamed instance remains selectable by its module-local object ID.
    snprintf(Buffer, sizeof(Buffer), "@%u", (unsigned)Inst);
    return Abc_UtilStrsav(Buffer);
}

static bool Sn_GiaSelectInstance( void * pUser, const void * pFrame, sn_obj_id_t Inst )
{
    Sn_CutContext_t * p = (Sn_CutContext_t *)pUser;
    const sn_blast_hier_frame_t * pCurrent = (const sn_blast_hier_frame_t *)pFrame;
    const sn_module_t * pModule = pCurrent->blast.module;
    const sn_module_t * pChild = sn_design_get_module_const(p->pDesign, sn_inst_module_id(pModule, Inst));
    const char * pDefinition = NULL;
    for (size_t k = 0; k < pChild->attribute_records.size; ++k)
    {
        const sn_attribute_record_t * pRecord = &sn_vec_at(sn_attribute_record_t, &pChild->attribute_records, k);
        if (pRecord->object == SN_INVALID_ID &&
            !strcmp(sn_name_get(&p->pDesign->names, pRecord->name), "sn_source_module"))
            pDefinition = sn_name_get(&p->pDesign->names, pRecord->value);
    }
    char * pPattern;
    int i, Selected = 0;
    if ( p->pOptions->vModules )
        Vec_PtrForEachEntry(char *, p->pOptions->vModules, pPattern, i)
            if ( !strcmp(pPattern, sn_name_get(&p->pDesign->names, pChild->name)) ||
                 (pDefinition && !strcmp(pPattern, pDefinition)) )
                p->pModules[i] = 1, Selected = 1;
    if ( p->pOptions->vInstances )
    {
        Vec_Ptr_t * vChain = Vec_PtrAlloc(8);
        const sn_blast_hier_frame_t * pWalk = pCurrent;
        char * pLeaf = Sn_GiaInstanceName(pModule, Inst);
        size_t Length = strlen(pLeaf) + 2;
        char * pPath;
        while ( pWalk->parent )
        {
            char * pName = Sn_GiaInstanceName(pWalk->parent->blast.module, pWalk->parent_inst);
            Vec_PtrPush(vChain, (void *)pName);
            Length += strlen(pName) + 1;
            pWalk = pWalk->parent;
        }
        const char * pRoot = sn_name_get(&p->pDesign->names, pWalk->blast.module->name);
        Length += strlen(pRoot);
        pPath = ABC_ALLOC(char, Length);
        strcpy(pPath, pRoot);
        for ( i = Vec_PtrSize(vChain) - 1; i >= 0; --i )
        { strcat(pPath, "/"); strcat(pPath, (char *)Vec_PtrEntry(vChain, i)); }
        strcat(pPath, "/");
        strcat(pPath, pLeaf);
        Vec_PtrForEachEntry(char *, p->pOptions->vInstances, pPattern, i)
            if ( !strcmp(pPattern, pPath) || !strcmp(pPattern, pPath + strlen(pRoot) + 1) )
                p->pInstances[i] = 1, Selected = 1;
        ABC_FREE(pPath);
        ABC_FREE(pLeaf);
        Vec_PtrForEachEntry(char *, vChain, pPattern, i) ABC_FREE(pPattern);
        Vec_PtrFree(vChain);
    }
    // An ancestor cut subsumes descendant selections, but still validate those paths: typos must not be hidden.
    int Pending = 0;
    for (i = 0; p->pOptions->vModules && i < Vec_PtrSize(p->pOptions->vModules); ++i)
        Pending |= !p->pModules[i];
    for (i = 0; p->pOptions->vInstances && i < Vec_PtrSize(p->pOptions->vInstances); ++i)
        Pending |= !p->pInstances[i];
    if ((Selected || p->fCovered) && Pending)
    {
        sn_blast_hier_frame_t Child;
        int Saved = p->fCovered;
        memset(&Child, 0, sizeof(Child));
        Child.parent = (sn_blast_hier_frame_t *)pCurrent;
        Child.parent_inst = Inst;
        Child.blast.module = pChild;
        p->fCovered = 1;
        for (size_t k = 0; k < pChild->type_objects[SN_INST].size; ++k)
            Sn_GiaSelectInstance(p, &Child, sn_vec_at(sn_obj_id_t, &pChild->type_objects[SN_INST], k));
        p->fCovered = Saved;
    }
    return Selected != 0;
}

static void Sn_GiaDescribeObject( Vec_Int_t * v, const sn_module_t * p, sn_obj_id_t Obj )
{
    Vec_IntPush(v, sn_obj_type(p, Obj));
    Vec_IntPush(v, sn_obj_width(p, Obj));
    Vec_IntPush(v, sn_obj_is_signed(p, Obj));
    Vec_IntPush(v, sn_obj_fanin_count(p, Obj));
    for ( uint32_t k = 0; k < sn_obj_fanin_count(p, Obj); ++k )
    {
        sn_obj_id_t In = sn_obj_fanin(p, Obj, k);
        Vec_IntPush(v, In == SN_INVALID_ID ? -1 : (int)sn_obj_width(p, In));
        Vec_IntPush(v, In == SN_INVALID_ID ? -1 : (int)sn_obj_is_signed(p, In));
    }
}

typedef struct Sn_CutOrder_t_ { uint32_t Index, Ci, Co; } Sn_CutOrder_t;
static int Sn_GiaCompareCutOrder( const void * pLeft, const void * pRight )
{
    const Sn_CutOrder_t * p = (const Sn_CutOrder_t *)pLeft, * q = (const Sn_CutOrder_t *)pRight;
    if (p->Ci != q->Ci) return (p->Ci > q->Ci) - (p->Ci < q->Ci);
    if (p->Co != q->Co) return (p->Co > q->Co) - (p->Co < q->Co);
    return (p->Index > q->Index) - (p->Index < q->Index);
}

// Validate only the retained hierarchy, before allocating any AIG or per-bit boundary vectors.
static int Sn_GiaPreflight( Sn_CutContext_t * p, sn_blast_hier_frame_t * pFrame, uint8_t * pModules,
                           FILE * pError )
{
    const sn_module_t * pModule = pFrame->blast.module;
    if (!pModules[pModule->id])
    {
        const char * pReason = sn_module_is_blackbox(pModule) ? "unselected black box" : NULL;
        sn_obj_id_t Obj = SN_INVALID_ID;
        // Instance-level cycles need not be logic cycles. Join their LOOP wires after
        // extraction, when output-specific dependencies are visible, and check there.
        for (size_t i = 0; !pReason && i < pModule->type_objects[SN_REG_OUT].size; ++i)
        {
            Obj = sn_vec_at(sn_obj_id_t, &pModule->type_objects[SN_REG_OUT], i);
            uint32_t Flags = sn_obj_reg_flags(pModule, Obj);
            if (Flags & SN_REG_LATCH) pReason = "level-sensitive latch";
            else if (Flags & (SN_REG_RESET_ASYNC | SN_REG_SET_ASYNC)) pReason = "asynchronous flop control";
        }
        for (size_t i = 0; !pReason && i < pModule->type_objects[SN_MEM_OUT].size; ++i)
        {
            Obj = sn_vec_at(sn_obj_id_t, &pModule->type_objects[SN_MEM_OUT], i);
            if (!p->pOptions->fMemory) pReason = "memory requires explicit -A mem abstraction";
            else if (sn_obj_mem_init_data(pModule, Obj) != SN_INVALID_ID)
                pReason = "initialized memory is outside the current verification contract";
        }
        for (size_t i = 0; !pReason && i < pModule->type_objects[SN_GATE].size; ++i)
        {
            Obj = sn_vec_at(sn_obj_id_t, &pModule->type_objects[SN_GATE], i);
            uint32_t Cell = sn_obj_gate_id(pModule, Obj);
            if (sn_library_ff_boundary(p->pDesign->library, Cell)) pReason = "sequential library FF";
            else if (sn_library_latch_boundary(p->pDesign->library, Cell)) pReason = "sequential library latch";
        }
        if (pReason)
        {
            fprintf(pError, "SN extraction: module '%s'", sn_name_get(&p->pDesign->names, pModule->name));
            if (Obj != SN_INVALID_ID)
                fprintf(pError, ", object %u ('%s')", (unsigned)Obj,
                    sn_obj_name_id(pModule, Obj) == SN_INVALID_ID ? "unnamed" : sn_obj_name(pModule, Obj));
            fprintf(pError, ": %s; comparison not performed.\n", pReason);
            return 0;
        }
        pModules[pModule->id] = 1;
    }
    for (size_t i = 0; i < pModule->type_objects[SN_INST].size; ++i)
    {
        sn_obj_id_t Inst = sn_vec_at(sn_obj_id_t, &pModule->type_objects[SN_INST], i);
        sn_blast_hier_frame_t Child;
        if (Sn_GiaSelectInstance(p, pFrame, Inst)) continue;
        memset(&Child, 0, sizeof(Child));
        Child.parent = pFrame;
        Child.parent_inst = Inst;
        Child.blast.module = sn_design_get_module_const(p->pDesign, sn_inst_module_id(pModule, Inst));
        if (!Sn_GiaPreflight(p, &Child, pModules, pError)) return 0;
    }
    return 1;
}

Gia_Man_t * Sn_DesignExtractGia( const sn_design_t * pDesign, sn_module_id_t Top,
    const Sn_GiaOptions_t * pOptions, Vec_Int_t * vDescriptor, FILE * pError )
{
    sn_blast_boundary_t Boundary;
    Sn_GiaResult_t Result;
    sn_blast_options_t Options;
    Sn_CutContext_t Context;
    Gia_Man_t * pGia = NULL;
    uint8_t * pModules;
    Sn_CutOrder_t * pCutOrder = NULL;
    sn_blast_hier_frame_t Root;
    int Good = 1;
    if ( !pError ) pError = stderr;
    if ( !pOptions || !vDescriptor || !pDesign || Top >= pDesign->modules.size ) return NULL;
    Vec_IntClear(vDescriptor);
    memset(&Context, 0, sizeof(Context));
    Context.pDesign = pDesign;
    Context.pOptions = pOptions;
    Context.pModules = ABC_CALLOC(unsigned char, pOptions->vModules ? Vec_PtrSize(pOptions->vModules) + 1 : 1);
    Context.pInstances = ABC_CALLOC(unsigned char, pOptions->vInstances ? Vec_PtrSize(pOptions->vInstances) + 1 : 1);
    Options = pOptions->Blast;
    Options.mode = SN_BLAST_SEQ;
    Options.raw_state = true;
    Options.abstract_memories = true;
    Options.abstract_mul_operators = pOptions->fMultiply != 0;
    Options.abstract_memory_primitives = Options.abstract_multipliers = Options.abstract_carries = false;
    Options.cut_instance = Sn_GiaSelectInstance;
    Options.cut_context = &Context;
    pModules = ABC_CALLOC(uint8_t, pDesign->modules.size);
    memset(&Root, 0, sizeof(Root));
    Root.blast.module = sn_design_get_module_const(pDesign, Top);
    Options.verification_modules = pModules;
    sn_blast_boundary_init(&Boundary);
    if (!Sn_GiaPreflight(&Context, &Root, pModules, pError)) goto done;
    pGia = Sn_DesignToGia(pDesign, Top, &Options, &Boundary, &Result);
    if ( !pGia ) goto done;
    if ( Boundary.loops.size )
    {
        const char * pReason = NULL;
        int CycleCi = -1, nRegs = Gia_ManRegNum(pGia);
        // Stitch the combinational transition relation. State remains in the trailing
        // CI/CO slots, unchanged; only transparent LOOP endpoints are removed.
        pGia->nRegs = 0;
        Gia_Man_t * pJoined = sn_gia_stitch_loops(pGia, &Boundary, &pReason, &CycleCi);
        Gia_ManStop(pGia);
        pGia = pJoined;
        if ( !pGia )
        {
            fprintf(pError, "SN extraction: %s; comparison not performed.\n", pReason);
            goto done;
        }
        Gia_ManSetRegNum(pGia, nRegs);
    }
    for ( int i = 0; pOptions->vModules && i < Vec_PtrSize(pOptions->vModules); ++i )
        if ( !Context.pModules[i] ) { fprintf(pError, "SN extraction: unmatched module cut '%s'.\n",
            (char *)Vec_PtrEntry(pOptions->vModules, i)); Good = 0; }
    for ( int i = 0; pOptions->vInstances && i < Vec_PtrSize(pOptions->vInstances); ++i )
        if ( !Context.pInstances[i] ) { fprintf(pError, "SN extraction: unmatched instance cut '%s'.\n",
            (char *)Vec_PtrEntry(pOptions->vInstances, i)); Good = 0; }
    Vec_IntPush(vDescriptor, (int)Result.Stats.primary_input_bits);
    Vec_IntPush(vDescriptor, (int)Result.Stats.primary_output_bits);
    Vec_IntPush(vDescriptor, Gia_ManRegNum(pGia));
    for ( size_t i = 0; i < Boundary.occurrences.size; ++i )
    {
        const sn_module_t * pModule = sn_design_get_module_const(pDesign,
            sn_vec_at(sn_blast_occurrence_t, &Boundary.occurrences, i).module);
        // Record ownership by stable memory/port ordinals, not by object IDs (which change with logic edits).
        int Count = pModule->type_objects[SN_MEM_OUT].size ? (int)pModule->obj_types.size : 0;
        Vec_Int_t * vOwners = Vec_IntStartFull(Count);
        Vec_Int_t * vPorts = Vec_IntStartFull(Count);
        for ( size_t k = 0; k < pModule->type_objects[SN_MEM_OUT].size; ++k )
        {
            sn_obj_id_t Mem = sn_vec_at(sn_obj_id_t, &pModule->type_objects[SN_MEM_OUT], k);
            Vec_IntWriteEntry(vOwners, Mem, (int)k);
            for ( uint32_t j = 0; j < sn_obj_mem_write_count(pModule, Mem); ++j )
            {
                sn_obj_id_t Write = sn_obj_mem_write(pModule, Mem, j);
                Vec_IntWriteEntry(vOwners, Write, (int)k);
                Vec_IntWriteEntry(vPorts, Write, (int)j);
            }
        }
        for ( size_t k = 0; k < pModule->type_objects[SN_MEM_OUT].size; ++k )
        {
            sn_obj_id_t Mem = sn_vec_at(sn_obj_id_t, &pModule->type_objects[SN_MEM_OUT], k);
            Vec_IntPush(vDescriptor, SN_MEM_OUT);
            Vec_IntPush(vDescriptor, sn_obj_width(pModule, Mem));
            Vec_IntPush(vDescriptor, sn_obj_mem_depth(pModule, Mem));
        }
        const sn_obj_type_t Types[] = {SN_MEM_READ, SN_MEM_WRITE};
        for ( size_t t = 0; t < 2; ++t )
        {
            for ( size_t k = 0; k < pModule->type_objects[Types[t]].size; ++k )
            {
                sn_obj_id_t Obj = sn_vec_at(sn_obj_id_t, &pModule->type_objects[Types[t]], k);
                Sn_GiaDescribeObject(vDescriptor, pModule, Obj);
                sn_obj_id_t Owner = Types[t] == SN_MEM_READ ?
                    sn_obj_fanin(pModule, Obj, SN_MEM_READ_MEMORY) : Obj;
                Vec_IntPush(vDescriptor, Vec_IntEntry(vOwners, Owner));
                Vec_IntPush(vDescriptor, Types[t] == SN_MEM_READ ? (int)k : Vec_IntEntry(vPorts, Obj));
            }
        }
        Vec_IntFree(vOwners);
        Vec_IntFree(vPorts);
    }
    // Describe cuts in actual interface order, including boxes with no output bits.
    pCutOrder = ABC_ALLOC(Sn_CutOrder_t, Boundary.primitives.size);
    for (size_t i = 0; i < Boundary.primitives.size; ++i)
    {
        const sn_blast_primitive_t * pBox = &sn_vec_at(sn_blast_primitive_t, &Boundary.primitives, i);
        pCutOrder[i].Index = (uint32_t)i;
        pCutOrder[i].Ci = pBox->ci_begin;
        pCutOrder[i].Co = pBox->co_begin;
    }
    if (Boundary.primitives.size > 1)
        qsort(pCutOrder, Boundary.primitives.size, sizeof(*pCutOrder), Sn_GiaCompareCutOrder);
    for (size_t i = 0; i < Boundary.primitives.size; ++i)
    {
        const sn_blast_primitive_t * pBox = &sn_vec_at(sn_blast_primitive_t, &Boundary.primitives, pCutOrder[i].Index);
        const sn_module_t * pModule = sn_design_get_module_const(pDesign,
            sn_vec_at(sn_blast_occurrence_t, &Boundary.occurrences, pBox->occurrence).module);
        if (sn_obj_type(pModule, pBox->inst) == SN_MUL && pOptions->fMultiply)
        {
            Sn_GiaDescribeObject(vDescriptor, pModule, pBox->inst);
            continue;
        }
        // A reachable opaque boundary must have been explicitly requested.
        if ( !pBox->explicit_cut || pBox->module == SN_INVALID_ID ) { Good = 0; continue; }
        Sn_GiaDescribeObject(vDescriptor, pModule, pBox->inst);
        const sn_module_t * pChild = sn_design_get_module_const(pDesign, pBox->module);
        Vec_IntPush(vDescriptor, pChild->type_objects[SN_PO].size);
        for ( size_t k = 0; k < pChild->type_objects[SN_PO].size; ++k )
            Vec_IntPush(vDescriptor, sn_obj_width(pChild, sn_vec_at(sn_obj_id_t, &pChild->type_objects[SN_PO], k)));
    }
    if ( !Good )
    {
        fprintf(pError, "SN extraction: unsupported or incompatible state/abstraction boundary; comparison not performed.\n");
        Gia_ManStop(pGia); pGia = NULL;
        Vec_IntClear(vDescriptor);
    }
    else Sn_GiaSetNames(pGia, pDesign, Top, &Boundary, Boundary.loops.size != 0, NULL, NULL);
done:
    sn_blast_boundary_destroy(&Boundary);
    ABC_FREE(pModules);
    ABC_FREE(pCutOrder);
    ABC_FREE(Context.pModules);
    ABC_FREE(Context.pInstances);
    return pGia;
}
ABC_NAMESPACE_IMPL_END
