/**CFile****************************************************************

  FileName    [snAigCost.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Shared-master AIG area and local logic-depth characterization.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snAigCost.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#include "snAigCost.h"
#include "snBlast.h"
#include "snCheck.h"
#include "aig/gia/gia.h"
#include <math.h>
#include <stdarg.h>

ABC_NAMESPACE_IMPL_START

extern Gia_Man_t * Gia_ManFromMiniAig( Mini_Aig_t *, Vec_Int_t **, int );

typedef struct Snac_Output_t_
{
    unsigned Object;
    int Node;
} Snac_Output_t;

typedef struct Snac_Observer_t_
{
    const sn_module_t * pModule;
    unsigned * pOwners;
    int * pStack;
    size_t Capacity;
    Snac_Output_t * pOutputs;
    size_t nOutputs, nOutputCapacity;
    int Failed;
} Snac_Observer_t;

typedef struct Snac_Frame_t_
{
    unsigned Module, Next;
} Snac_Frame_t;

/**Function*************************************************************

  Synopsis    [Formats a characterization diagnostic.]

***********************************************************************/
static int Snac_Error( char * pError, unsigned nError, const char * pFormat, ... )
{
    va_list Args;
    va_start(Args,pFormat);
    if ( pError && nError ) vsnprintf(pError,nError,pFormat,Args);
    va_end(Args);
    return 0;
}

/**Function*************************************************************

  Synopsis    [Allocates a checked zero-initialized array.]

***********************************************************************/
static void * Snac_Alloc( size_t Count, size_t Size )
{
    if ( Count > SIZE_MAX/Size ) return NULL;
    return calloc(Count ? Count : 1,Size);
}

/**Function*************************************************************

  Synopsis    [Adds a checked nonnegative count.]

***********************************************************************/
static int Snac_Add( uint64_t * pValue, uint64_t Value )
{
    if ( *pValue > UINT64_MAX-Value ) return 0;
    *pValue += Value;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Adds a checked occurrence-weighted count.]

***********************************************************************/
static int Snac_MultiplyAdd( uint64_t * pValue, uint64_t Count, uint64_t Value )
{
    if ( Count && Value > UINT64_MAX/Count ) return 0;
    return Snac_Add(pValue,Count*Value);
}

/**Function*************************************************************

  Synopsis    [Grows MiniAIG ownership and traversal storage together.]

***********************************************************************/
static int Snac_Reserve( Snac_Observer_t * p, size_t Count )
{
    size_t Capacity = p->Capacity ? p->Capacity : 256, i;
    unsigned * pOwners;
    int * pStack;
    if ( Count <= p->Capacity ) return 1;
    while ( Capacity < Count )
    {
        if ( Capacity > SIZE_MAX/2 ) { Capacity = Count; break; }
        Capacity *= 2;
    }
    if ( Capacity > SIZE_MAX/sizeof(*pOwners) || Capacity > SIZE_MAX/sizeof(*pStack) ) return 0;
    pOwners = (unsigned *)malloc(Capacity*sizeof(*pOwners));
    pStack = (int *)malloc(Capacity*sizeof(*pStack));
    if ( !pOwners || !pStack ) { free(pOwners); free(pStack); return 0; }
    if ( p->Capacity ) memcpy(pOwners,p->pOwners,p->Capacity*sizeof(*pOwners));
    for ( i = p->Capacity; i < Capacity; ++i ) pOwners[i] = SN_INVALID_ID;
    free(p->pOwners); free(p->pStack);
    p->pOwners = pOwners; p->pStack = pStack; p->Capacity = Capacity;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Remembers output literals without keeping dead AIG logic alive.]

***********************************************************************/
static int Snac_Outputs( Snac_Observer_t * p, unsigned Object, const int * pBits, unsigned Width )
{
    Snac_Output_t * pOutputs;
    size_t Count, Capacity;
    unsigned i;
    if ( (size_t)Width > SIZE_MAX-p->nOutputs ) return 0;
    Count = p->nOutputs+(size_t)Width;
    if ( Count > p->nOutputCapacity )
    {
        Capacity = p->nOutputCapacity ? p->nOutputCapacity : 256;
        while ( Capacity < Count )
        {
            if ( Capacity > SIZE_MAX/2 ) { Capacity = Count; break; }
            Capacity *= 2;
        }
        if ( Capacity > SIZE_MAX/sizeof(*pOutputs) ) return 0;
        pOutputs = (Snac_Output_t *)realloc(p->pOutputs,Capacity*sizeof(*pOutputs));
        if ( !pOutputs ) return 0;
        p->pOutputs = pOutputs; p->nOutputCapacity = Capacity;
    }
    for ( i = 0; i < Width; ++i )
    {
        p->pOutputs[p->nOutputs].Object = Object;
        p->pOutputs[p->nOutputs++].Node = Mini_AigLit2Var(pBits[i]);
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Records outputs and assigns exposed logic to its first SN owner.]

***********************************************************************/
static void Snac_Observe( void * pUser, const sn_module_t * pModule, sn_obj_id_t Object,
    Mini_Aig_t * pAig, const int * pBits, uint32_t Width )
{
    Snac_Observer_t * p = (Snac_Observer_t *)pUser;
    unsigned i, nStack = 0;
    int Node, Fanin, k;
    if ( p->Failed ) return;
    if ( pModule != p->pModule || Object >= pModule->obj_types.size ||
         !Snac_Reserve(p,(size_t)Mini_AigNodeNum(pAig)) || !Snac_Outputs(p,Object,pBits,Width) )
    { p->Failed = 1; return; }
    for ( i = 0; i < Width; ++i )
    {
        Node = Mini_AigLit2Var(pBits[i]);
        if ( !Mini_AigNodeIsAnd(pAig,Node) || p->pOwners[Node] != SN_INVALID_ID ) continue;
        p->pOwners[Node] = Object;
        p->pStack[nStack++] = Node;
        while ( nStack )
        {
            Node = p->pStack[--nStack];
            for ( k = 0; k < 2; ++k )
            {
                Fanin = Mini_AigLit2Var(k ? Mini_AigNodeFanin1(pAig,Node) : Mini_AigNodeFanin0(pAig,Node));
                if ( !Mini_AigNodeIsAnd(pAig,Fanin) || p->pOwners[Fanin] != SN_INVALID_ID ) continue;
                p->pOwners[Fanin] = Object;
                p->pStack[nStack++] = Fanin;
            }
        }
    }
}

/**Function*************************************************************

  Synopsis    [Collects surviving output levels through the cleanup mapping.]

***********************************************************************/
static void Snac_OutputLevels( Sn_AigCostModule_t * pResult, const Snac_Observer_t * pObserver,
    Gia_Man_t * pGia, Vec_Int_t * vCopies )
{
    size_t i;
    unsigned Object, Level;
    int Lit;
    pResult->Levels = (unsigned)Gia_ManLevelNum(pGia);
    for ( Object = 0; Object < pResult->nObjects; ++Object )
        pResult->pObjectLevels[Object] = SN_AIG_COST_LEVEL_NONE;
    for ( i = 0; i < pObserver->nOutputs; ++i )
    {
        Lit = Vec_IntEntry(vCopies,pObserver->pOutputs[i].Node);
        if ( Lit < 0 ) continue;
        Object = pObserver->pOutputs[i].Object;
        Level = (unsigned)Gia_ObjLevelId(pGia,Abc_Lit2Var(Lit));
        if ( pResult->pObjectLevels[Object] == SN_AIG_COST_LEVEL_NONE ||
             pResult->pObjectLevels[Object] < Level )
            pResult->pObjectLevels[Object] = Level;
        // Multi-output boundary owners are not evaluated: their separate FAN
        // objects are seeded directly. Keep the owner's aggregate level too.
        if ( sn_obj_type(pObserver->pModule,Object) != SN_FAN ) continue;
        Object = sn_fan_owner(pObserver->pModule,Object);
        if ( pResult->pObjectLevels[Object] == SN_AIG_COST_LEVEL_NONE ||
             pResult->pObjectLevels[Object] < Level )
            pResult->pObjectLevels[Object] = Level;
    }
}

/**Function*************************************************************

  Synopsis    [Collects distinct masters in children-before-parent order.]

***********************************************************************/
static int Snac_Order( const sn_design_t * pDesign, unsigned Root, uint8_t * pState,
    Snac_Frame_t * pStack, unsigned * pOrder, unsigned * pnOrder )
{
    unsigned nStack = 0;
    if ( pState[Root] == 2 ) return 1;
    pStack[nStack].Module = Root; pStack[nStack++].Next = 0; pState[Root] = 1;
    while ( nStack )
    {
        Snac_Frame_t * pFrame = pStack+nStack-1;
        const sn_module_t * pModule = sn_design_get_module_const(pDesign,pFrame->Module);
        if ( !sn_module_is_technology_primitive(pModule) && pFrame->Next < pModule->type_objects[SN_INST].size )
        {
            unsigned Instance = sn_vec_at(sn_obj_id_t,&pModule->type_objects[SN_INST],pFrame->Next++);
            unsigned Child = sn_inst_module_id(pModule,Instance);
            if ( Child >= pDesign->modules.size || pState[Child] == 1 ) return 0;
            if ( pState[Child] == 2 ) continue;
            pStack[nStack].Module = Child; pStack[nStack++].Next = 0; pState[Child] = 1;
            continue;
        }
        pOrder[(*pnOrder)++] = pFrame->Module;
        pState[pFrame->Module] = 2;
        --nStack;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns supported, unknown, or fatal before the shared blaster.]

***********************************************************************/
static int Snac_Preflight( const sn_module_t * pModule, Sn_AigCostModule_t * pResult,
    char * pError, unsigned nError )
{
    const sn_library_t * pLibrary = pModule->design->library;
    unsigned i;
    if ( !sn_module_is_topo(pModule) )
    {
        Snac_Error(pError,nError,"AIG characterization requires topological module %s",
            sn_name_get(&pModule->design->names,pModule->name));
        return -1;
    }
    for ( i = 0; i < pModule->type_objects[SN_LUT].size; ++i )
        if ( sn_obj_fanin_count(pModule,sn_vec_at(sn_obj_id_t,&pModule->type_objects[SN_LUT],i)) > 6 )
            return Snac_Error(pResult->UnknownReason,sizeof(pResult->UnknownReason),
                "object %u: LUT has more than six inputs",sn_vec_at(sn_obj_id_t,&pModule->type_objects[SN_LUT],i));
    for ( i = 0; i < pModule->type_objects[SN_GATE].size; ++i )
    {
        unsigned Object = sn_vec_at(sn_obj_id_t,&pModule->type_objects[SN_GATE],i);
        unsigned Cell = sn_obj_gate_id(pModule,Object);
        if ( !pLibrary || Cell >= pLibrary->cell_count || !pLibrary->functions )
            return Snac_Error(pResult->UnknownReason,sizeof(pResult->UnknownReason),
                "object %u: no bound Liberty function",Object);
        if ( sn_library_ff_boundary(pLibrary,Cell) || sn_library_latch_boundary(pLibrary,Cell) ) continue;
        if ( !sn_expr_check(pLibrary->functions+Cell) || pLibrary->functions[Cell].inputs != sn_obj_fanin_count(pModule,Object) )
            return Snac_Error(pResult->UnknownReason,sizeof(pResult->UnknownReason),"object %u cell %s: %s",Object,
                sn_library_cell_name(pLibrary,Cell),pLibrary->cells[Cell].unsupported_reason ?
                pLibrary->cells[Cell].unsupported_reason : "unsupported Liberty interface");
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Counts explicit storage once without lowering memory ports.]

***********************************************************************/
static int Snac_Storage( const sn_module_t * pModule, Sn_AigCostModule_t * pResult,
    double FlopArea, double SramArea )
{
    unsigned i;
    for ( i = 0; i < pModule->obj_types.size; ++i )
    {
        sn_obj_type_t Type = sn_obj_type(pModule,i);
        uint64_t Bits = 0;
        double Area = 0;
        if ( Type == SN_REG_OUT )
        {
            Bits = sn_obj_width(pModule,i);
            if ( !Snac_Add(&pResult->FlopBits,Bits) ) return 0;
            Area = FlopArea*(double)Bits;
        }
        else if ( Type == SN_MEM_OUT )
        {
            Bits = (uint64_t)sn_obj_width(pModule,i)*(uint64_t)sn_obj_data(pModule,i);
            if ( !Snac_Add(&pResult->SramBits,Bits) ) return 0;
            Area = SramArea*(double)Bits;
        }
        else if ( Type == SN_GATE )
        {
            const sn_library_t * pLibrary = pModule->design->library;
            unsigned Cell = sn_obj_gate_id(pModule,i), k;
            if ( sn_library_ff_boundary(pLibrary,Cell) || sn_library_latch_boundary(pLibrary,Cell) )
            {
                const sn_lib_t * pModel = pLibrary->cells[Cell].model;
                const sn_lib_cell_t * pCell = pModel->cells+pLibrary->cells[Cell].local_id;
                for ( k = pCell->state_first; k < pCell->state_first+pCell->state_count; ++k )
                    if ( !pModel->states[k].in_test_cell && !Snac_Add(&Bits,pModel->states[k].bits) ) return 0;
                if ( !Snac_Add(&pResult->FlopBits,Bits) ) return 0;
                Area = FlopArea*(double)Bits;
            }
        }
        if ( !isfinite(Area) || !isfinite(pResult->LocalArea+Area) ) return 0;
        pResult->pObjectAreas[i] += Area;
        pResult->LocalArea += Area;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Characterizes one shared definition and its object ownership.]

***********************************************************************/
static int Snac_Module( const sn_module_t * pModule, Sn_AigCostModule_t * pResult,
    double FlopArea, double SramArea, char * pError, unsigned nError )
{
    sn_blast_options_t Options = sn_blast_default_options();
    sn_blast_boundary_t Boundary;
    Snac_Observer_t Observer;
    Mini_Aig_t * pMini = NULL;
    Gia_Man_t * pGia = NULL;
    Vec_Int_t * vCopies = NULL;
    uint8_t * pAssigned = NULL;
    Gia_Obj_t * pObject;
    int i, Lit, Node, Supported, ok = 0;
    memset(&Observer,0,sizeof(Observer)); Observer.pModule = pModule;
    sn_blast_boundary_init(&Boundary);
    pResult->nObjects = (unsigned)pModule->obj_types.size;
    pResult->fSelected = 1;
    if ( sn_module_is_technology_primitive(pModule) )
    {
        Snac_Error(pResult->UnknownReason,sizeof(pResult->UnknownReason),"opaque technology primitive");
        ok = 1; goto done;
    }
    Supported = Snac_Preflight(pModule,pResult,pError,nError);
    if ( Supported < 0 ) goto done;
    if ( !Supported ) { ok = 1; goto done; }
    pResult->pObjectAreas = (double *)Snac_Alloc(pResult->nObjects,sizeof(double));
    pResult->pObjectLevels = (unsigned *)Snac_Alloc(pResult->nObjects,sizeof(unsigned));
    if ( !pResult->pObjectAreas || !pResult->pObjectLevels ) goto memory;
    Options.abstract_instances = true;
    Options.opaque_sequential_gates = true;
    Options.probe_all_register_controls = true;
    Options.observe_object = Snac_Observe; Options.observe_context = &Observer;
    pMini = sn_design_blast_hier_boundary_options(pModule->design,pModule->id,Options,NULL,&Boundary);
    if ( !pMini ) { Snac_Error(pError,nError,"AIG bit blasting failed for module %s",
        sn_name_get(&pModule->design->names,pModule->name)); goto done; }
    if ( Observer.Failed ) goto memory;
    pGia = Gia_ManFromMiniAig(pMini,&vCopies,0);
    if ( !pGia ) goto memory;
    pAssigned = (uint8_t *)Snac_Alloc((size_t)Gia_ManObjNum(pGia),1);
    if ( !pAssigned ) goto memory;
    Mini_AigForEachAnd(pMini,i)
    {
        unsigned Owner;
        if ( (size_t)i >= Observer.Capacity || Observer.pOwners[i] == SN_INVALID_ID ) continue;
        Lit = Vec_IntEntry(vCopies,i);
        if ( Lit < 0 ) continue;
        Node = Abc_Lit2Var(Lit);
        if ( !Gia_ObjIsAnd(Gia_ManObj(pGia,Node)) || pAssigned[Node] ) continue;
        Owner = Observer.pOwners[i];
        if ( Owner >= pResult->nObjects ) { Snac_Error(pError,nError,"invalid AIG ownership"); goto done; }
        pAssigned[Node] = 1;
        pResult->pObjectAreas[Owner] += 1;
        ++pResult->Ands;
    }
    Gia_ManForEachAnd(pGia,pObject,i)
        if ( !pAssigned[i] ) { Snac_Error(pError,nError,"unassigned AIG node in module %s",
            sn_name_get(&pModule->design->names,pModule->name)); goto done; }
    pResult->LocalArea = (double)pResult->Ands;
    if ( !Snac_Storage(pModule,pResult,FlopArea,SramArea) )
    { Snac_Error(pError,nError,"AIG storage area/count overflow"); goto done; }
    Snac_OutputLevels(pResult,&Observer,pGia,vCopies);
    pResult->Known = 1;
    ok = 1;
    goto done;
memory:
    Snac_Error(pError,nError,"AIG characterization allocation failed");
done:
    free(pAssigned); free(Observer.pOwners); free(Observer.pStack); free(Observer.pOutputs);
    if ( vCopies ) Vec_IntFree(vCopies);
    if ( pGia ) Gia_ManStop(pGia);
    if ( pMini ) Mini_AigStop(pMini);
    sn_blast_boundary_destroy(&Boundary);
    return ok;
}

/**Function*************************************************************

  Synopsis    [Releases every owned characterization array.]

***********************************************************************/
void Sn_AigCostFree( Sn_AigCost_t * p )
{
    unsigned i;
    if ( !p ) return;
    if ( p->pModules ) for ( i = 0; i < p->nModules; ++i )
    {
        free(p->pModules[i].pObjectAreas);
        free(p->pModules[i].pObjectLevels);
    }
    free(p->pModules); free(p);
}

/**Function*************************************************************

  Synopsis    [Releases an independently characterized master and its arrays.]

***********************************************************************/
void Sn_AigCostModuleFree( Sn_AigCostModule_t * p )
{
    if ( !p ) return;
    free(p->pObjectAreas); free(p->pObjectLevels); free(p);
}

/**Function*************************************************************

  Synopsis    [Characterizes one definition without revisiting its descendants.]

***********************************************************************/
static int Snac_ComputeModule( const sn_design_t * pDesign, int fLocal, unsigned Module,
    double FlopArea, double SramArea, Sn_AigCostModule_t ** ppResult, char * pError, unsigned nError )
{
    Sn_AigCostModule_t * p;
    if ( ppResult ) *ppResult = NULL;
    if ( pError && nError ) pError[0] = 0;
    if ( !ppResult || !pDesign || !pDesign->modules.size || pDesign->modules.size >= SN_INVALID_ID ||
         Module >= pDesign->modules.size || !(FlopArea > 0) || !(SramArea > 0) ||
         !isfinite(FlopArea) || !isfinite(SramArea) )
        return Snac_Error(pError,nError,"invalid single-master AIG characterization arguments");
    if ( fLocal ? !sn_module_check_local(sn_design_get_module_const(pDesign,Module),NULL) :
         !sn_design_check_output(pDesign,NULL,false) )
        return Snac_Error(pError,nError,"SN consistency check failed before AIG characterization");
    if ( pDesign->library && !sn_library_compile(pDesign->library) )
        return Snac_Error(pError,nError,"Liberty function compilation failed");
    p = (Sn_AigCostModule_t *)calloc(1,sizeof(*p));
    if ( !p ) return Snac_Error(pError,nError,"AIG characterization allocation failed");
    if ( !Snac_Module(sn_design_get_module_const(pDesign,Module),p,FlopArea,SramArea,pError,nError) )
    { Sn_AigCostModuleFree(p); return 0; }
    p->Occurrences = 1;
    *ppResult = p;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Characterizes one master after validating its complete design.]

***********************************************************************/
int Sn_AigCostComputeModule( const sn_design_t * pDesign, unsigned Module,
    double FlopArea, double SramArea, Sn_AigCostModule_t ** ppResult, char * pError, unsigned nError )
{
    return Snac_ComputeModule(pDesign,0,Module,FlopArea,SramArea,ppResult,pError,nError);
}

/**Function*************************************************************

  Synopsis    [Characterizes a locally checked master in an already validated design.]

***********************************************************************/
int Sn_AigCostComputeModuleLocal( const sn_design_t * pDesign, unsigned Module,
    double FlopArea, double SramArea, Sn_AigCostModule_t ** ppResult, char * pError, unsigned nError )
{
    return Snac_ComputeModule(pDesign,1,Module,FlopArea,SramArea,ppResult,pError,nError);
}

/**Function*************************************************************

  Synopsis    [Collects exact local costs and checked hierarchy totals.]

***********************************************************************/
int Sn_AigCostCompute( const sn_design_t * pDesign, unsigned Top, int fAll,
    double FlopArea, double SramArea, Sn_AigCost_t ** ppResult, char * pError, unsigned nError )
{
    Sn_AigCost_t * p = NULL;
    Snac_Frame_t * pStack = NULL;
    uint8_t * pState = NULL;
    unsigned * pOrder = NULL, nOrder = 0, i, k;
    int ok = 0;
    if ( ppResult ) *ppResult = NULL;
    if ( pError && nError ) pError[0] = 0;
    if ( !ppResult || !pDesign || !pDesign->modules.size || pDesign->modules.size >= SN_INVALID_ID ||
         !(FlopArea > 0) || !(SramArea > 0) || !isfinite(FlopArea) || !isfinite(SramArea) )
        return Snac_Error(pError,nError,"invalid AIG characterization arguments");
    if ( Top == SN_INVALID_ID ) Top = (unsigned)pDesign->modules.size-1;
    if ( Top >= pDesign->modules.size ) return Snac_Error(pError,nError,"invalid AIG characterization top");
    if ( !sn_design_check_output(pDesign,NULL,false) ) return Snac_Error(pError,nError,"SN consistency check failed before AIG characterization");
    if ( pDesign->library && !sn_library_compile(pDesign->library) )
        return Snac_Error(pError,nError,"Liberty function compilation failed");
    p = (Sn_AigCost_t *)calloc(1,sizeof(*p));
    if ( !p ) goto memory;
    p->nModules = (unsigned)pDesign->modules.size; p->Top = Top;
    p->pModules = (Sn_AigCostModule_t *)Snac_Alloc(p->nModules,sizeof(*p->pModules));
    pState = (uint8_t *)Snac_Alloc(p->nModules,1);
    pStack = (Snac_Frame_t *)Snac_Alloc(p->nModules,sizeof(*pStack));
    pOrder = (unsigned *)Snac_Alloc(p->nModules,sizeof(*pOrder));
    if ( !p->pModules || !pState || !pStack || !pOrder ) goto memory;
    if ( !Snac_Order(pDesign,Top,pState,pStack,pOrder,&nOrder) ) goto hierarchy;
    if ( fAll ) for ( i = 0; i < p->nModules; ++i )
        if ( !Snac_Order(pDesign,i,pState,pStack,pOrder,&nOrder) ) goto hierarchy;
    for ( i = 0; i < nOrder; ++i )
    {
        unsigned Id = pOrder[i];
        Sn_AigCostModule_t * pModule = p->pModules+Id;
        if ( !Snac_Module(sn_design_get_module_const(pDesign,Id),pModule,FlopArea,SramArea,pError,nError) ) goto done;
        if ( pModule->Known ) ++p->nCharacterized; else ++p->nOpaque;
        if ( p->MaxLevels < pModule->Levels ) p->MaxLevels = pModule->Levels;
        if ( !Snac_Add(&p->Ands,pModule->Ands) || !Snac_Add(&p->FlopBits,pModule->FlopBits) ||
             !Snac_Add(&p->SramBits,pModule->SramBits) || !isfinite(p->LocalArea+pModule->LocalArea) ) goto overflow;
        p->LocalArea += pModule->LocalArea;
    }
    p->pModules[Top].Occurrences = 1;
    for ( i = nOrder; i-- > 0; )
    {
        unsigned Id = pOrder[i];
        const sn_module_t * pSource = sn_design_get_module_const(pDesign,Id);
        Sn_AigCostModule_t * pModule = p->pModules+Id;
        uint64_t Count = pModule->Occurrences;
        double Area = (double)Count*pModule->LocalArea;
        if ( !Snac_Add(&p->Occurrences,Count) || !Snac_MultiplyAdd(&p->ExpandedAnds,Count,pModule->Ands) ||
             !Snac_MultiplyAdd(&p->ExpandedFlopBits,Count,pModule->FlopBits) ||
             !Snac_MultiplyAdd(&p->ExpandedSramBits,Count,pModule->SramBits) ||
             !isfinite(Area) || !isfinite(p->ExpandedArea+Area) ) goto overflow;
        p->ExpandedArea += Area;
        if ( sn_module_is_technology_primitive(pSource) ) continue;
        for ( k = 0; k < pSource->type_objects[SN_INST].size; ++k )
        {
            unsigned Instance = sn_vec_at(sn_obj_id_t,&pSource->type_objects[SN_INST],k);
            unsigned Child = sn_inst_module_id(pSource,Instance);
            if ( !Snac_Add(&p->pModules[Child].Occurrences,Count) ) goto overflow;
        }
    }
    *ppResult = p; p = NULL; ok = 1;
    goto done;
memory:
    Snac_Error(pError,nError,"AIG characterization allocation failed"); goto done;
hierarchy:
    Snac_Error(pError,nError,"invalid or recursive AIG characterization hierarchy"); goto done;
overflow:
    Snac_Error(pError,nError,"AIG characterization occurrence/area overflow");
done:
    free(pOrder); free(pStack); free(pState); Sn_AigCostFree(p);
    return ok;
}

ABC_NAMESPACE_IMPL_END
