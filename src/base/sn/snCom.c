/**CFile****************************************************************

  FileName    [snCom.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [ABC command handlers and manager ownership for the SN design interface.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snCom.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

// Expose POSIX declarations (notably readlink) in strict C99 builds. Feature-test
// macros must precede every system header; respect an explicitly selected level.
#if !defined(_MSC_VER) && !defined(__MINGW32__) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L
#endif

#include "sn.h"
#include "snMiniAig.h"
#include "snBlast.h"
#include "snCheck.h"
#include "snMiniGate.h"
#include "snMiniLut.h"
#include "snMapDff.h"
#include "snMapFf.h"
#include "snMapLut.h"
#include "snMapTech.h"
#include "snMux.h"
#include "base/main/mainInt.h"
#include "map/mio/mio.h"
#include "misc/util/utilNam.h"
#include "snMio.h"
#include "snNtk.h"
#include "snMapCell.h"
#include "snStitch.h"
#include "snClock.h"
#include "map/scl/sclLib.h"
#include "map/amap/amap.h"
#include "map/mapper/mapper.h"

#include <ctype.h>
#include <limits.h>

#if defined(_MSC_VER) || defined(__MINGW32__)
#include <io.h>
#include <process.h>
#include <windows.h>
#else
#include <fcntl.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#if defined(__APPLE__)
#include <mach-o/dyld.h>
#endif
#endif

ABC_NAMESPACE_IMPL_START

typedef struct Sn_Man_t_ Sn_Man_t;
typedef struct Sn_TargetIdentity_t_
{
    uint64_t Size, Hash;
} Sn_TargetIdentity_t;
struct Sn_Man_t_
{
    sn_design_t *      pDesign;
    sn_module_id_t     Top;
    sn_name_id_t       Name;
    unsigned long long Revision;
    int                Technology;
    sn_module_id_t     BlastModule;
    sn_name_id_t       BlastName;
    sn_blast_boundary_t Boundary;
    int                fBoundary;
    int                fBlasted;
    int                BlastMode;
    int                fLastBlast;
    const char *       pLastAnalysis; // diagnostic-only kind, static string
    sn_module_id_t     LastBlastModule;
    sn_name_id_t       LastBlastName;
    unsigned long long LastBlastRevision;
    ABC_UINT64_T       BlastBoundarySignature;
    ABC_UINT64_T       BlastInterfaceSignature;
    ABC_UINT64_T       BlastGenlibSignature;
    ABC_UINT64_T       BlastToken;
    sn_vec_t           TargetModels; // ordered source size/hash identities; independent of design-local model IDs
    ABC_UINT64_T       TargetGenlibSignature;
};

enum
{
    SN_COMMAND_TECH_GENERIC = 0,
    SN_COMMAND_TECH_XILINX_ULTRASCALE
};

static int Sn_CommandRead( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandReadLib( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandMapCell( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandSlang( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandCollapse( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandCheck( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandMapMem( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandMapDsp( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandMapAdd( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandMapDff( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandMapFf( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandMapSrl( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandOptMux( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandBlast( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandStitch( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandPut( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandMapLut( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandWrite( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandPs( Abc_Frame_t * pAbc, int argc, char ** argv );
static int Sn_CommandStatus( Abc_Frame_t * pAbc, int argc, char ** argv );
static const char * Sn_ManPutStatus( const Sn_Man_t * p, Gia_Man_t * pGia );
static const char * Sn_ManPutNtkStatus( const Sn_Man_t * p, Abc_Ntk_t * pNtk );

extern int tmpFile( const char * pPrefix, const char * pSuffix, char ** ppFileName );

static int Sn_TempPrefix( char * pBuffer, size_t nBuffer, const char * pStem )
{
    int Written;
#if defined(_MSC_VER) || defined(__MINGW32__)
    Written = snprintf( pBuffer, nBuffer, "%s\\%s", Abc_GetTmpDir(), pStem );
#else
    Written = snprintf( pBuffer, nBuffer, "%s/%s", Abc_GetTmpDir(), pStem );
#endif
    return Written >= 0 && (size_t)Written < nBuffer;
}

static inline Sn_Man_t * Sn_AbcGetMan( Abc_Frame_t * pAbc )
{
    return (Sn_Man_t *)pAbc->pAbcSn;
}

static void Sn_ManFree( Sn_Man_t * p )
{
    if ( p == NULL )
        return;
    if ( p->fBoundary )
        sn_blast_boundary_destroy( &p->Boundary );
    sn_design_destroy( p->pDesign );
    sn_vec_destroy( &p->TargetModels );
    ABC_FREE( p );
}

static void Sn_AbcUpdateMan( Abc_Frame_t * pAbc, Sn_Man_t * p )
{
    Sn_Man_t * pOld = Sn_AbcGetMan(pAbc);
    // Reading another design invalidates extraction, not the selected target
    // identities. Actual model membership is checked again before legalization.
    if ( p && pOld && !p->TargetModels.size )
    {
        sn_vec_dup(Sn_TargetIdentity_t, &p->TargetModels, &pOld->TargetModels);
        p->TargetGenlibSignature = pOld->TargetGenlibSignature;
    }
    Sn_ManFree( Sn_AbcGetMan(pAbc) );
    pAbc->pAbcSn = p;
}

static Sn_Man_t * Sn_ManAlloc( sn_design_t * pDesign, sn_module_id_t Top )
{
    Sn_Man_t * p;
    size_t i;
    assert( pDesign != NULL );
    assert( Top < pDesign->modules.size );
    p = ABC_CALLOC( Sn_Man_t, 1 );
    assert( p != NULL );
    p->pDesign = pDesign;
    p->Top = Top;
    p->Name = sn_design_get_module_const( pDesign, Top )->name;
    p->Revision = 1;
    for ( i = 0; i < pDesign->modules.size; i++ )
        if ( sn_module_is_technology_primitive(sn_design_get_module_const(pDesign, (sn_module_id_t)i)) )
        {
            p->Technology = SN_COMMAND_TECH_XILINX_ULTRASCALE;
            break;
        }
    p->BlastModule = SN_INVALID_ID;
    p->BlastName = SN_INVALID_ID;
    p->LastBlastModule = SN_INVALID_ID;
    p->LastBlastName = SN_INVALID_ID;
    sn_blast_boundary_init( &p->Boundary );
    p->fBoundary = 1;
    return p;
}

static void Sn_ManAdvanceRevision( Sn_Man_t * p )
{
    assert( p && p->Revision != ULLONG_MAX );
    p->Revision++;
    p->fBlasted = 0;
    p->pLastAnalysis = NULL;
    p->BlastModule = SN_INVALID_ID;
    p->BlastName = SN_INVALID_ID;
}

static int Sn_FileHasSuffix( const char * pFileName, const char * pSuffix )
{
    size_t nFileName = strlen( pFileName );
    size_t nSuffix = strlen( pSuffix );
    return nFileName >= nSuffix && strcmp( pFileName + nFileName - nSuffix, pSuffix ) == 0;
}

static int Sn_CommandCheckDesign( Abc_Frame_t * pAbc )
{
    if ( Sn_AbcGetMan(pAbc) != NULL )
        return 1;
    Abc_Print( -1, "There is no current SN design.\n" );
    return 0;
}

static Sn_Man_t * Sn_ManReadBinary( const char * pFileName, const char * pTopName, FILE * pError )
{
    sn_design_t * pDesign;
    sn_module_id_t Top;
    FILE * pFile = fopen( pFileName, "rb" );
    int c, Status;
    if ( pFile == NULL )
    {
        Abc_Print( -1, "Cannot open input file \"%s\".\n", pFileName );
        return NULL;
    }
    pDesign = sn_design_read_binary_checked( pFile, pError );
    if ( pDesign == NULL )
    {
        fclose( pFile );
        Abc_Print( -1, "Cannot read SN design from \"%s\".\n", pFileName );
        return NULL;
    }
    c = fgetc( pFile );
    Status = ferror( pFile );
    Status |= fclose( pFile ) != 0;
    if ( c != EOF || Status )
    {
        Abc_Print( -1, "Cannot finish reading input file \"%s\".\n", pFileName );
        sn_design_destroy( pDesign );
        return NULL;
    }
    if ( pDesign->modules.size == 0 )
    {
        Abc_Print( -1, "SN design \"%s\" contains no modules.\n", pFileName );
        sn_design_destroy( pDesign );
        return NULL;
    }
    Top = pTopName ? sn_design_find_module( pDesign, pTopName ) : (sn_module_id_t)(pDesign->modules.size - 1);
    if ( Top == SN_INVALID_ID )
    {
        Abc_Print( -1, "Cannot find top module \"%s\" in SN design \"%s\".\n", pTopName, pFileName );
        sn_design_destroy( pDesign );
        return NULL;
    }
    if ( !sn_design_is_topo(pDesign) )
    {
        Abc_Print( -1, "SN design \"%s\" is not topologically ordered.\n", pFileName );
        sn_design_destroy( pDesign );
        return NULL;
    }
    return Sn_ManAlloc( pDesign, Top );
}

static Sn_Man_t * Sn_ManDup( const Sn_Man_t * p )
{
    sn_design_t * pDesign;
    Sn_Man_t * pNew;
    if ( p == NULL )
        return NULL;
    pDesign = sn_design_dup( p->pDesign );
    assert( p->Top < pDesign->modules.size );
    pNew = Sn_ManAlloc( pDesign, p->Top );
    pNew->Name = p->Name;
    pNew->Revision = p->Revision;
    pNew->Technology = p->Technology;
    pNew->fLastBlast = p->fLastBlast;
    pNew->pLastAnalysis = p->pLastAnalysis;
    pNew->LastBlastModule = p->LastBlastModule;
    pNew->LastBlastName = p->LastBlastName;
    pNew->LastBlastRevision = p->LastBlastRevision;
    pNew->BlastMode = p->BlastMode;
    pNew->BlastBoundarySignature = p->BlastBoundarySignature;
    pNew->BlastInterfaceSignature = p->BlastInterfaceSignature;
    pNew->BlastToken = p->BlastToken;
    pNew->BlastGenlibSignature = p->BlastGenlibSignature;
    pNew->TargetGenlibSignature = p->TargetGenlibSignature;
    sn_vec_dup(Sn_TargetIdentity_t, &pNew->TargetModels, &p->TargetModels);
    return pNew;
}

// Installs a freshly reconstructed module at the stable ID selected by @blast -M. Parent insts therefore continue to
// reference the same module, and modules outside the selected hierarchy remain untouched. The temporary append-only
// module is removed from the design vector after its storage is moved into the selected slot.
static void Sn_ManReplaceModule( Sn_Man_t * p, sn_module_id_t Module, sn_name_id_t Name,
                                 sn_module_id_t Temporary )
{
    assert( p );
    sn_design_replace_appended_module( p->pDesign, Module, Name, Temporary );
}

static void Sn_ManReplaceBlastedModule( Sn_Man_t * p, sn_module_id_t Temporary )
{
    Sn_ManReplaceModule( p, p->BlastModule, p->BlastName, Temporary );
}

static char * Sn_SlangExecutable()
{
    char * pExecutable = Abc_FrameReadFlag( "snslang" );
    if ( pExecutable != NULL )
        return pExecutable;
#if defined(_MSC_VER) || defined(__MINGW32__)
    return "sn_slang.exe";
#else
    return "sn_slang";
#endif
}

static int Sn_RunProcess( char ** ppArgs )
{
#if defined(__wasm)
    (void)ppArgs;
    return -1;
#elif defined(_MSC_VER) || defined(__MINGW32__)
    return (int)_spawnvp( _P_WAIT, ppArgs[0], (const char * const *)ppArgs );
#else
    pid_t Child = fork();
    int Status;
    if ( Child < 0 )
        return -1;
    if ( Child == 0 )
    {
        execvp( ppArgs[0], ppArgs );
        // execvp() returns only on failure. Release the child copy so memory checkers do not report it as leaked;
        // the parent's copy is unaffected and is freed by the caller.
        ABC_FREE( ppArgs );
        _exit( 127 );
    }
    if ( waitpid(Child, &Status, 0) != Child )
        return -1;
    return WIFEXITED(Status) ? WEXITSTATUS(Status) : -1;
#endif
}

static int Sn_DesignHasType( const sn_design_t * pDesign, sn_obj_type_t Type )
{
    size_t i;
    for ( i = 0; i < pDesign->modules.size; i++ )
        if ( sn_design_get_module_const(pDesign, (sn_module_id_t)i)->type_objects[Type].size )
            return 1;
    return 0;
}

static int Sn_CommandRejectLatches( const sn_design_t * pDesign, sn_module_id_t Root, const char * pCommand )
{
    sn_module_id_t LatchModule = sn_design_find_reachable_latch( pDesign, Root, NULL );
    const sn_module_t * pModule;
    if ( LatchModule == SN_INVALID_ID )
        return 0;
    pModule = sn_design_get_module_const( pDesign, LatchModule );
    Abc_Print( -1, "Cannot %s: reachable module \"%s\" contains a level-sensitive latch; "
                   "latch blasting is not supported.\n",
               pCommand, sn_name_get(&pDesign->names, pModule->name) );
    return 1;
}

static void Sn_FormatMemory( size_t Bytes, char * pBuffer, size_t BufferSize )
{
    static const char * pUnits[] = { "", "K", "M", "G" };
    double Value = (double)Bytes;
    int Unit = 0;
    while ( Value >= 1000.0 && Unit < 3 )
    {
        Value /= 1000.0;
        Unit++;
    }
    if ( Unit == 0 )
        snprintf( pBuffer, BufferSize, "%zu", Bytes );
    else
        snprintf( pBuffer, BufferSize, "%.1f%s", Value, pUnits[Unit] );
}

static void Sn_ModulePrintStats( FILE * pOut, const sn_module_t * pModule, int fMem, int fLut, int fGate )
{
    uint64_t nRegBits = 0;
    uint64_t nMemBits = 0;
    size_t i;
    for ( i = 0; i < pModule->type_objects[SN_REG_OUT].size; i++ )
    {
        sn_obj_id_t Obj = sn_vec_at( sn_obj_id_t, &pModule->type_objects[SN_REG_OUT], i );
        nRegBits += sn_obj_width( pModule, Obj );
    }
    for ( i = 0; i < pModule->type_objects[SN_MEM_OUT].size; i++ )
    {
        sn_obj_id_t Obj = sn_vec_at( sn_obj_id_t, &pModule->type_objects[SN_MEM_OUT], i );
        nMemBits += (uint64_t)sn_obj_width( pModule, Obj ) * sn_obj_mem_depth( pModule, Obj );
    }
    fprintf( pOut, "%-24s : obj = %8zu  pi = %6zu  po = %6zu  reg = %6zu/%llu  inst = %6zu",
             sn_name_get( &pModule->design->names, pModule->name ), pModule->obj_types.size,
             pModule->type_objects[SN_PI].size, pModule->type_objects[SN_PO].size,
             pModule->type_objects[SN_REG_OUT].size, (unsigned long long)nRegBits,
             pModule->type_objects[SN_INST].size );
    if ( fMem )
        fprintf( pOut, "  mem = %5zu/%llu", pModule->type_objects[SN_MEM_OUT].size,
                 (unsigned long long)nMemBits );
    if ( fLut )
        fprintf( pOut, "  lut = %6zu", pModule->type_objects[SN_LUT].size );
    if ( fGate )
        fprintf( pOut, "  gate = %6zu", pModule->type_objects[SN_GATE].size );
    if ( pModule->type_objects[SN_LOOP_OUT].size )
        fprintf( pOut, "  loop = %6zu", pModule->type_objects[SN_LOOP_OUT].size );
    fprintf( pOut, "\n" );
}

typedef struct Sn_DistribEntry_t_ Sn_DistribEntry_t;
struct Sn_DistribEntry_t_
{
    uint32_t OutWidth;
    uint32_t In0Width;
    uint32_t In1Width;
    uint32_t FaninNum;
    uint64_t Occur;
    unsigned char Signs;
};

static const char * Sn_ObjTypeNames[SN_OBJ_TYPE_COUNT] = {
    "none", "pi", "po", "const0", "const1", "const", "buf", "fan", "inst",
    "reg_out", "reg_in", "mem_out", "mem_in", "mem_read", "mem_write", "loop_out", "loop_in",
    "+u", "-u", "~", "!", "&r", "~&r", "|r", "~|r", "^r", "~^r",
    "+", "-", "*", "/", "%", "**", "&", "|", "^", "~^", "&&", "||",
    "==", "!=", "===", "!==", "==?", "!=?", "<", "<=", ">", ">=", "<<", ">>", "<<<", ">>>",
    "mux", "bmux", "pmux", "{,}", "repeat", "slice", "cast", "lut", "gate"
};

static int Sn_DistribEntryCompare( const void * pLeft, const void * pRight )
{
    const Sn_DistribEntry_t * pL = (const Sn_DistribEntry_t *)pLeft;
    const Sn_DistribEntry_t * pR = (const Sn_DistribEntry_t *)pRight;
    if ( pL->Occur != pR->Occur )
        return pL->Occur < pR->Occur ? 1 : -1;
    if ( pL->OutWidth != pR->OutWidth )
        return pL->OutWidth < pR->OutWidth ? 1 : -1;
    if ( pL->In0Width != pR->In0Width )
        return pL->In0Width < pR->In0Width ? 1 : -1;
    if ( pL->In1Width != pR->In1Width )
        return pL->In1Width < pR->In1Width ? 1 : -1;
    if ( pL->FaninNum != pR->FaninNum )
        return pL->FaninNum < pR->FaninNum ? 1 : -1;
    return (int)pL->Signs - (int)pR->Signs;
}

static int Sn_DistribAdd( Sn_DistribEntry_t ** ppEntries, size_t * pnEntries, size_t * pnCap,
                          const sn_module_t * pModule, sn_obj_id_t Obj, uint64_t Mult )
{
    Sn_DistribEntry_t Entry;
    uint32_t nFanins = sn_obj_fanin_count( pModule, Obj );
    uint32_t i;
    memset( &Entry, 0, sizeof(Entry) );
    Entry.OutWidth = sn_obj_width( pModule, Obj );
    Entry.FaninNum = nFanins;
    Entry.Signs = (unsigned char)sn_obj_is_signed( pModule, Obj );
    for ( i = 0; i < nFanins && i < 2; i++ )
    {
        sn_obj_id_t Fanin = sn_obj_fanin( pModule, Obj, i );
        if ( Fanin == SN_INVALID_ID )
            continue;
        if ( i == 0 )
            Entry.In0Width = sn_obj_width( pModule, Fanin );
        else
            Entry.In1Width = sn_obj_width( pModule, Fanin );
        Entry.Signs |= (unsigned char)(sn_obj_is_signed( pModule, Fanin ) << (i + 1));
    }
    for ( i = 0; i < *pnEntries; i++ )
    {
        Sn_DistribEntry_t * pOld = *ppEntries + i;
        if ( pOld->OutWidth == Entry.OutWidth && pOld->In0Width == Entry.In0Width &&
             pOld->In1Width == Entry.In1Width && pOld->FaninNum == Entry.FaninNum && pOld->Signs == Entry.Signs )
        {
            if ( UINT64_MAX - pOld->Occur < Mult )
                return 0;
            pOld->Occur += Mult;
            return 1;
        }
    }
    if ( *pnEntries == *pnCap )
    {
        Sn_DistribEntry_t * pNew;
        if ( *pnCap > SIZE_MAX / 2 / sizeof(Sn_DistribEntry_t) )
            return 0;
        *pnCap = *pnCap ? 2 * *pnCap : 8;
        pNew = ABC_REALLOC( Sn_DistribEntry_t, *ppEntries, *pnCap );
        if ( pNew == NULL )
            return 0;
        *ppEntries = pNew;
    }
    Entry.Occur = Mult;
    (*ppEntries)[(*pnEntries)++] = Entry;
    return 1;
}

static int Sn_ModuleCollectDistrib( const sn_design_t * pDesign, sn_module_id_t ModuleId, uint64_t Mult,
                                    Sn_DistribEntry_t ** ppEntries, size_t * pnEntries, size_t * pnCaps,
                                    uint64_t * pTypeCounts )
{
    const sn_module_t * pModule = sn_design_get_module_const( pDesign, ModuleId );
    sn_obj_id_t Obj;
    for ( Obj = 0; Obj < pModule->obj_types.size; Obj++ )
    {
        sn_obj_type_t Type = sn_obj_type( pModule, Obj );
        if ( UINT64_MAX - pTypeCounts[Type] < Mult )
            return 0;
        pTypeCounts[Type] += Mult;
        if ( !Sn_DistribAdd(ppEntries + Type, pnEntries + Type, pnCaps + Type, pModule, Obj, Mult) )
            return 0;
    }
    return 1;
}

typedef struct Sn_DistribFrame_t_
{
    sn_module_id_t Module;
    size_t          NextInst;
} Sn_DistribFrame_t;

// Returns the number of reachable occurrences of each module definition under Top. The hierarchy is a DAG, so a
// reverse-postorder propagation accounts for repeated insts without expanding every hierarchical occurrence.
static uint64_t * Sn_DesignCountModuleOccurrences( const sn_design_t * pDesign, sn_module_id_t Top )
{
    unsigned char * pStates;
    uint64_t * pMults;
    sn_vec_t Stack, Postorder;
    Sn_DistribFrame_t * pFrame;
    size_t i;
    if ( pDesign == NULL || Top >= pDesign->modules.size )
        return NULL;
    pStates = ABC_CALLOC( unsigned char, pDesign->modules.size );
    pMults = ABC_CALLOC( uint64_t, pDesign->modules.size );
    if ( pStates == NULL || pMults == NULL )
    {
        ABC_FREE( pStates );
        ABC_FREE( pMults );
        return NULL;
    }
    sn_vec_init( &Stack );
    sn_vec_init( &Postorder );
    pStates[Top] = 1;
    pFrame = sn_vec_push( Sn_DistribFrame_t, &Stack );
    pFrame->Module = Top;
    pFrame->NextInst = 0;
    while ( Stack.size )
    {
        const sn_module_t * pModule;
        pFrame = &sn_vec_at( Sn_DistribFrame_t, &Stack, Stack.size - 1 );
        pModule = sn_design_get_module_const( pDesign, pFrame->Module );
        if ( pFrame->NextInst < pModule->type_objects[SN_INST].size )
        {
            sn_module_id_t Child = sn_inst_module_id(pModule, sn_vec_at(sn_obj_id_t, &pModule->type_objects[SN_INST], pFrame->NextInst++));
            if ( Child >= pDesign->modules.size || pStates[Child] == 1 )
                goto fail;
            if ( pStates[Child] == 0 )
            {
                pStates[Child] = 1;
                pFrame = sn_vec_push( Sn_DistribFrame_t, &Stack );
                pFrame->Module = Child;
                pFrame->NextInst = 0;
            }
            continue;
        }
        pStates[pFrame->Module] = 2;
        *sn_vec_push( sn_module_id_t, &Postorder ) = pFrame->Module;
        Stack.size--;
    }
    pMults[Top] = 1;
    for ( i = Postorder.size; i-- > 0; )
    {
        sn_module_id_t Module = sn_vec_at( sn_module_id_t, &Postorder, i );
        const sn_module_t * pModule = sn_design_get_module_const( pDesign, Module );
        uint64_t Mult = pMults[Module];
        if ( Mult == 0 )
            continue;
        for ( size_t k = 0; k < pModule->type_objects[SN_INST].size; k++ )
        {
            sn_module_id_t Child = sn_inst_module_id(pModule, sn_vec_at(sn_obj_id_t, &pModule->type_objects[SN_INST], k));
            if ( Child >= pDesign->modules.size || UINT64_MAX - pMults[Child] < Mult )
                goto fail;
            pMults[Child] += Mult;
        }
    }
    sn_vec_destroy( &Postorder );
    sn_vec_destroy( &Stack );
    ABC_FREE( pStates );
    return pMults;

fail:
    sn_vec_destroy( &Postorder );
    sn_vec_destroy( &Stack );
    ABC_FREE( pStates );
    ABC_FREE( pMults );
    return NULL;
}

static int Sn_ModulePortBits( const sn_module_t * pModule, sn_obj_type_t Type, uint64_t * pBits )
{
    uint64_t Bits = 0;
    size_t i;
    assert( Type == SN_PI || Type == SN_PO );
    for ( i = 0; i < pModule->type_objects[Type].size; i++ )
    {
        uint32_t Width = sn_obj_width( pModule, sn_vec_at(sn_obj_id_t, &pModule->type_objects[Type], i) );
        if ( UINT64_MAX - Bits < Width )
            return 0;
        Bits += Width;
    }
    *pBits = Bits;
    return 1;
}

static int Sn_DesignPrintCellArea( FILE * pOut, const sn_design_t * pDesign, sn_module_id_t Top )
{
    sn_library_t * pLibrary = pDesign->library;
    uint64_t * pMults = Sn_DesignCountModuleOccurrences(pDesign, Top);
    uint64_t * pCounts = pLibrary ? ABC_CALLOC(uint64_t, pLibrary->cell_count) : NULL;
    uint64_t Counts[4] = {0}, Missing = 0, External = 0, Legacy = 0, Operators = 0, RegBits = 0;
    uint64_t Constants = 0, Ties = 0, ClockGates = 0, ClockPins = 0, PowerPins = 0;
    double Areas[4] = {0}; // combinational, sequential, opaque scalar, macro
    const char * Kinds[4] = {"comb", "seq", "opaque", "macro"};
    if ( !pMults || (pLibrary && (!pCounts || !sn_library_compile(pLibrary))) )
        goto failed;
    for ( size_t i = 0; i < pDesign->modules.size; ++i )
    {
        const sn_module_t * pModule = sn_design_get_module_const(pDesign, (sn_module_id_t)i);
        uint64_t Mult = pMults[i];
        if ( !Mult ) continue;
        if ( sn_module_is_blackbox(pModule) )
        {
            uint32_t Cell = sn_module_is_library_interface(pModule) ?
                sn_library_find_cell(pLibrary, sn_name_get(&pDesign->names, pModule->name)) : SN_LIB_NONE;
            uint64_t * pCount = Cell == SN_LIB_NONE ? &External : &pCounts[Cell];
            if ( Cell == SN_LIB_NONE )
                fprintf(pOut, "external %s count=%llu area=unavailable\n",
                    sn_name_get(&pDesign->names, pModule->name), (unsigned long long)Mult);
            if ( UINT64_MAX - *pCount < Mult ) goto failed;
            *pCount += Mult;
            continue;
        }
        for ( sn_obj_id_t Obj = 0; Obj < pModule->obj_types.size; ++Obj )
        {
            sn_obj_type_t Type = sn_obj_type(pModule, Obj);
            uint64_t * pCount = NULL, Weight = Mult;
            if ( Type == SN_GATE )
                pCount = pLibrary ? &pCounts[sn_obj_gate_id(pModule, Obj)] : &Legacy;
            else if ( Type == SN_REG_OUT )
            {
                if ( Mult > UINT64_MAX / sn_obj_width(pModule, Obj) ) goto failed;
                Weight *= sn_obj_width(pModule, Obj);
                pCount = &RegBits;
            }
            else if ( Type >= SN_POS && Type <= SN_PMUX )
                pCount = &Operators;
            else if ( Type == SN_LUT )
                pCount = &Operators;
            else if ( Type == SN_CONST0 || Type == SN_CONST1 || Type == SN_CONST )
                pCount = &Constants;
            if ( pCount )
            {
                if ( UINT64_MAX - *pCount < Weight ) goto failed;
                *pCount += Weight;
            }
        }
    }
    fprintf(pOut, "Cell histogram (physical owners, hierarchy occurrences; native Liberty area units):\n");
    for ( uint32_t i = 0; pLibrary && i < pLibrary->cell_count; ++i )
    {
        const sn_library_cell_t * pEntry = &pLibrary->cells[i];
        const sn_lib_cell_t * pCell = &pEntry->model->cells[pEntry->local_id];
        int Kind = !pEntry->scalar || pCell->is_macro ? 3 :
            sn_lib_cell_is_sequential(pEntry->model, pEntry->local_id) ? 1 :
            sn_expr_check(&pLibrary->functions[i]) ? 0 : 2;
        double Area = pCell->area * (double)pCounts[i];
        if ( !pCounts[i] ) continue;
        // Annotation inventory, not clock-tree recognition or power analysis.
        const sn_expr_t * pFunction = &pLibrary->functions[i];
        if ( !pEntry->input_count && pEntry->output_count == 1 &&
             sn_expr_check(pFunction) && pFunction->roots[0] <= 1 )
        {
            if ( UINT64_MAX - Ties < pCounts[i] ) goto failed;
            Ties += pCounts[i];
        }
        if ( pCell->clock_gating_integrated )
        {
            if ( UINT64_MAX - ClockGates < pCounts[i] ) goto failed;
            ClockGates += pCounts[i];
        }
        for ( uint32_t k = 0; k < pCell->pin_count; ++k )
        {
            const sn_lib_pin_t * pPin = &pEntry->model->pins[pCell->pin_first + k];
            if ( pPin->clock )
            {
                if ( UINT64_MAX - ClockPins < pCounts[i] ) goto failed;
                ClockPins += pCounts[i];
            }
            if ( pPin->kind == SN_LIB_PIN_PG )
            {
                if ( UINT64_MAX - PowerPins < pCounts[i] ) goto failed;
                PowerPins += pCounts[i];
            }
        }
        if ( UINT64_MAX - Counts[Kind] < pCounts[i] ) goto failed;
        Counts[Kind] += pCounts[i];
        fprintf(pOut, "cell %u %s %s count=%llu area=", i, sn_library_cell_name(pLibrary, i), Kinds[Kind],
            (unsigned long long)pCounts[i]);
        if ( !isfinite(pCell->area) || pCell->area < 0 )
        {
            if ( UINT64_MAX - Missing < pCounts[i] ) goto failed;
            Missing += pCounts[i];
            fprintf(pOut, "unavailable\n");
        }
        else
        {
            if ( !isfinite(Area) || !isfinite(Areas[Kind] + Area) ) goto failed;
            Areas[Kind] += Area;
            fprintf(pOut, "%.12g\n", Area);
        }
    }
    {
        uint64_t Total = 0;
        double Area = 0;
        for ( int i = 0; i < 4; ++i )
        {
            if ( UINT64_MAX - Total < Counts[i] || !isfinite(Area + Areas[i]) ) goto failed;
            Total += Counts[i];
            Area += Areas[i];
        }
        fprintf(pOut, "SN cell count: total=%llu comb=%llu seq=%llu opaque=%llu macro=%llu\n",
            (unsigned long long)Total, (unsigned long long)Counts[0], (unsigned long long)Counts[1],
            (unsigned long long)Counts[2], (unsigned long long)Counts[3]);
        fprintf(pOut, "SN cell area: total=%.12g comb=%.12g seq=%.12g opaque=%.12g macro=%.12g missing=%llu\n",
            Area, Areas[0], Areas[1], Areas[2], Areas[3], (unsigned long long)Missing);
        fprintf(pOut, "SN unmapped: operators=%llu register_bits=%llu legacy_gates=%llu external_boxes=%llu\n",
            (unsigned long long)Operators, (unsigned long long)RegBits, (unsigned long long)Legacy,
            (unsigned long long)External);
        fprintf(pOut, "SN inventory: constant_objects=%llu physical_ties=%llu clock_gating_cells=%llu clock_pin_annotations=%llu pg_pins=%llu\n",
            (unsigned long long)Constants, (unsigned long long)Ties, (unsigned long long)ClockGates,
            (unsigned long long)ClockPins, (unsigned long long)PowerPins);
        fprintf(pOut, "Power is nominal/on; PG connectivity, clock-tree classification and dynamic/leakage power are not analyzed.\n");
        if ( Missing || External )
            fprintf(pOut, "Area totals exclude unavailable areas and external boxes; not a complete design area.\n");
    }
    ABC_FREE(pCounts);
    ABC_FREE(pMults);
    return 1;
failed:
    ABC_FREE(pCounts);
    ABC_FREE(pMults);
    fprintf(pOut, "Cannot report cell area: invalid hierarchy, allocation failure or overflow.\n");
    return 0;
}

static void Sn_DesignPrintBlackboxes( FILE * pOut, const sn_design_t * pDesign, sn_module_id_t Top )
{
    const sn_module_t * pTop = sn_design_get_module_const( pDesign, Top );
    uint64_t * pMults = Sn_DesignCountModuleOccurrences( pDesign, Top );
    uint64_t nOccurrences = 0, nAigInputs = 0, nAigOutputs = 0;
    size_t nTypes = 0, i;
    if ( pMults == NULL )
    {
        fprintf( pOut, "Cannot count black-box occurrences: hierarchy is invalid or the count overflows.\n" );
        return;
    }
    fprintf( pOut, "Black boxes reachable from \"%s\":\n", sn_name_get(&pDesign->names, pTop->name) );
    fprintf( pOut, "Module                          occurrences   PI ports/bits   PO ports/bits   "
                   "AIG inputs   AIG outputs\n" );
    for ( i = 0; i < pDesign->modules.size; i++ )
    {
        const sn_module_t * pModule = sn_design_get_module_const( pDesign, (sn_module_id_t)i );
        uint64_t Mult = pMults[i], PiBits, PoBits, AigInputs, AigOutputs;
        if ( Mult == 0 || !sn_module_is_blackbox(pModule) )
            continue;
        if ( !Sn_ModulePortBits(pModule, SN_PI, &PiBits) || !Sn_ModulePortBits(pModule, SN_PO, &PoBits) ||
             (PoBits != 0 && Mult > UINT64_MAX / PoBits) ||
             (PiBits != 0 && Mult > UINT64_MAX / PiBits) )
            goto overflow;
        AigInputs = Mult * PoBits;
        AigOutputs = Mult * PiBits;
        if ( UINT64_MAX - nOccurrences < Mult || UINT64_MAX - nAigInputs < AigInputs ||
             UINT64_MAX - nAigOutputs < AigOutputs )
            goto overflow;
        nTypes++;
        nOccurrences += Mult;
        nAigInputs += AigInputs;
        nAigOutputs += AigOutputs;
        fprintf( pOut, "%-32s %10llu   %6zu/%-6llu   %6zu/%-6llu   %10llu   %11llu\n",
                 sn_name_get(&pDesign->names, pModule->name), (unsigned long long)Mult,
                 pModule->type_objects[SN_PI].size, (unsigned long long)PiBits,
                 pModule->type_objects[SN_PO].size, (unsigned long long)PoBits,
                 (unsigned long long)AigInputs, (unsigned long long)AigOutputs );
    }
    fprintf( pOut, "Black-box totals: types = %zu  occurrences = %llu  AIG inputs = %llu  AIG outputs = %llu\n",
             nTypes, (unsigned long long)nOccurrences, (unsigned long long)nAigInputs,
             (unsigned long long)nAigOutputs );
    ABC_FREE( pMults );
    return;

overflow:
    fprintf( pOut, "Cannot print black-box statistics: a bit or occurrence total overflows 64 bits.\n" );
    ABC_FREE( pMults );
}

static void Sn_DesignPrintDistrib( FILE * pOut, const sn_design_t * pDesign, sn_module_id_t Top )
{
    Sn_DistribEntry_t * pEntries[SN_OBJ_TYPE_COUNT] = { NULL };
    size_t nEntries[SN_OBJ_TYPE_COUNT] = { 0 };
    size_t nCaps[SN_OBJ_TYPE_COUNT] = { 0 };
    uint64_t TypeCounts[SN_OBJ_TYPE_COUNT] = { 0 };
    uint64_t * pMults = Sn_DesignCountModuleOccurrences( pDesign, Top );
    size_t i;
    int Type;
    if ( pMults == NULL )
    {
        fprintf( pOut, "Cannot print object distribution: hierarchy is invalid or the occurrence count overflows.\n" );
        return;
    }
    for ( i = 0; i < pDesign->modules.size; i++ )
        if ( pMults[i] && !Sn_ModuleCollectDistrib(pDesign, (sn_module_id_t)i, pMults[i], pEntries,
                                                   nEntries, nCaps, TypeCounts) )
        {
            fprintf( pOut, "Cannot print object distribution: a count overflows or allocation failed.\n" );
            for ( Type = 0; Type < SN_OBJ_TYPE_COUNT; Type++ )
                ABC_FREE( pEntries[Type] );
            ABC_FREE( pMults );
            return;
        }
    fprintf( pOut, "ID  :  name       occurrence  (occurrence)<output_width>=<input0_width>.<input1_width> ...\n" );
    for ( Type = 0; Type < SN_OBJ_TYPE_COUNT; Type++ )
    {
        size_t k;
        if ( TypeCounts[Type] == 0 )
            continue;
        qsort( pEntries[Type], nEntries[Type], sizeof(Sn_DistribEntry_t), Sn_DistribEntryCompare );
        fprintf( pOut, "%2d  :  %-10s %10llu  ", Type, Sn_ObjTypeNames[Type],
                 (unsigned long long)TypeCounts[Type] );
        for ( k = 0; k < nEntries[Type]; k++ )
        {
            const Sn_DistribEntry_t * pEntry = pEntries[Type] + k;
            if ( k && k % 6 == 0 )
                fprintf( pOut, "\n                              " );
            fprintf( pOut, "(%llu)%s%u", (unsigned long long)pEntry->Occur,
                     (pEntry->Signs & 1) ? "-" : "", pEntry->OutWidth );
            if ( pEntry->FaninNum )
                fprintf( pOut, "=%s%u", (pEntry->Signs & 2) ? "-" : "", pEntry->In0Width );
            if ( pEntry->FaninNum > 1 )
                fprintf( pOut, ".%s%u", (pEntry->Signs & 4) ? "-" : "", pEntry->In1Width );
            if ( pEntry->FaninNum > 2 )
                fprintf( pOut, "[%u]", pEntry->FaninNum );
            fprintf( pOut, " " );
        }
        fprintf( pOut, "\n" );
        ABC_FREE( pEntries[Type] );
    }
    ABC_FREE( pMults );
}

void Sn_Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "New word level", "@slang", Sn_CommandSlang, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@read",  Sn_CommandRead,  0 );
    Cmd_CommandAdd( pAbc, "New word level", "@check", Sn_CommandCheck, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@collapse", Sn_CommandCollapse, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@map_mem", Sn_CommandMapMem, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@map_dsp", Sn_CommandMapDsp, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@map_add", Sn_CommandMapAdd, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@map_dff", Sn_CommandMapDff, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@map_ff", Sn_CommandMapFf, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@map_srl", Sn_CommandMapSrl, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@opt_mux", Sn_CommandOptMux, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@blast", Sn_CommandBlast, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@stitch", Sn_CommandStitch, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@put", Sn_CommandPut, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@read_lib", Sn_CommandReadLib, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@map_cell", Sn_CommandMapCell, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@map_lut", Sn_CommandMapLut, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@write", Sn_CommandWrite, 0 );
    Cmd_CommandAdd( pAbc, "New word level", "@ps",    Sn_CommandPs,    0 );
    Cmd_CommandAdd( pAbc, "New word level", "@status", Sn_CommandStatus, 0 );
}

void Sn_End( Abc_Frame_t * pAbc )
{
    Sn_AbcUpdateMan( pAbc, NULL );
}

static int Sn_CommandRead( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char * pTopName = NULL;
    char * pFileName;
    Sn_Man_t * p;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "Mvh")) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a module name.\n" );
                goto usage;
            }
            pTopName = argv[globalUtilOptind++];
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( argc - globalUtilOptind != 1 )
        goto usage;
    pFileName = argv[globalUtilOptind];
    p = Sn_ManReadBinary( pFileName, pTopName, Abc_FrameReadErr(pAbc) );
    if ( p == NULL )
        return 1;
    Sn_AbcUpdateMan( pAbc, p );
    if ( fVerbose )
        Abc_Print( 1, "Read SN design \"%s\" with %zu modules. Top module is \"%s\".\n", pFileName,
                   p->pDesign->modules.size,
                   sn_name_get(&p->pDesign->names, sn_design_get_module_const(p->pDesign, p->Top)->name) );
    return 0;

usage:
    Abc_Print( -2, "usage: @read [-Mvh] <file.sn>\n" );
    Abc_Print( -2, "\t         reads a binary SN design\n" );
    Abc_Print( -2, "\t-M name : select the top module [default = last module]\n" );
    Abc_Print( -2, "\t-v      : print verbose output\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static int Sn_CommandSlang( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char TempPrefix[512];
    char * pTopName = NULL;
    char * pExtraFile = NULL;
    char * pDefine;
    char * pTempName = NULL;
    char ** ppArgs;
    Vec_Ptr_t * vDefines = Vec_PtrAlloc( 4 );
    Sn_Man_t * p;
    int c, fVerbose = 0, nFiles, nArgs, i, k, File;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "MFDBIvh")) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-%c\" should be followed by a module name.\n", c );
                goto usage;
            }
            pTopName = argv[globalUtilOptind++];
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by a file name.\n" );
                goto usage;
            }
            pExtraFile = argv[globalUtilOptind++];
            break;
        case 'D':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-D\" should be followed by definitions.\n" );
                goto usage;
            }
            Vec_PtrPush( vDefines, argv[globalUtilOptind++] );
            break;
        case 'B':
        case 'I':
            Abc_Print( -1, "Command line switch \"-%c\" is not supported by the external SN frontend yet.\n", c );
            Vec_PtrFree( vDefines );
            return 1;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    nFiles = argc - globalUtilOptind + (pExtraFile != NULL);
    if ( nFiles == 0 )
        goto usage;
    for ( i = globalUtilOptind; i < argc; i++ )
    {
        FILE * pFile = fopen( argv[i], "r" );
        if ( pFile == NULL )
        {
            Abc_Print( -1, "Cannot open input file \"%s\".\n", argv[i] );
            Vec_PtrFree( vDefines );
            return 1;
        }
        fclose( pFile );
    }
    if ( pExtraFile != NULL )
    {
        FILE * pFile = fopen( pExtraFile, "r" );
        if ( pFile == NULL )
        {
            Abc_Print( -1, "Cannot open input file \"%s\".\n", pExtraFile );
            Vec_PtrFree( vDefines );
            return 1;
        }
        fclose( pFile );
    }
    if ( !Sn_TempPrefix(TempPrefix, sizeof(TempPrefix), "sn_slang_") )
    {
        Abc_Print( -1, "Temporary-file path is too long.\n" );
        Vec_PtrFree( vDefines );
        return 1;
    }
    File = tmpFile( TempPrefix, ".sn", &pTempName );
    if ( File < 0 )
    {
        Abc_Print( -1, "Cannot create a temporary SN file.\n" );
        Vec_PtrFree( vDefines );
        return 1;
    }
#if defined(_MSC_VER) || defined(__MINGW32__)
    _close( File );
#else
    close( File );
#endif
    nArgs = 1 + (pTopName ? 2 : 0) + 2 * Vec_PtrSize(vDefines) + (fVerbose ? 1 : 0) + 2 + nFiles + 1;
    ppArgs = ABC_ALLOC( char *, nArgs );
    k = 0;
    ppArgs[k++] = Sn_SlangExecutable();
    if ( pTopName )
    {
        ppArgs[k++] = "-M";
        ppArgs[k++] = pTopName;
    }
    Vec_PtrForEachEntry( char *, vDefines, pDefine, i )
    {
        ppArgs[k++] = "-D";
        ppArgs[k++] = pDefine;
    }
    if ( fVerbose )
        ppArgs[k++] = "-t";
    ppArgs[k++] = "-o";
    ppArgs[k++] = pTempName;
    for ( i = globalUtilOptind; i < argc; i++ )
        ppArgs[k++] = argv[i];
    if ( pExtraFile )
        ppArgs[k++] = pExtraFile;
    ppArgs[k] = NULL;
    assert( k + 1 == nArgs );
    if ( fVerbose )
    {
        Abc_Print( 1, "Running:" );
        for ( i = 0; i < k; i++ )
            Abc_Print( 1, " %s", ppArgs[i] );
        Abc_Print( 1, "\n" );
        fflush( pAbc->Out );
    }
    c = Sn_RunProcess( ppArgs );
    ABC_FREE( ppArgs );
    Vec_PtrFree( vDefines );
    if ( c != 0 )
    {
        Abc_Print( -1, "External SN frontend failed with status %d.\n", c );
        remove( pTempName );
        ABC_FREE( pTempName );
        return 1;
    }
    p = Sn_ManReadBinary( pTempName, pTopName, Abc_FrameReadErr(pAbc) );
    remove( pTempName );
    ABC_FREE( pTempName );
    if ( p == NULL )
        return 1;
    Sn_AbcUpdateMan( pAbc, p );
    if ( fVerbose )
        Abc_Print( 1, "Loaded SN design with %zu modules.\n", p->pDesign->modules.size );
    return 0;

usage:
    Vec_PtrFree( vDefines );
    Abc_Print( -2, "usage: @slang [-M <module>] [-D <definition>] [-F <file>] [-vh] <file_name>...\n" );
    Abc_Print( -2, "\t         reads Verilog or SystemVerilog using the external sn_slang frontend\n" );
    Abc_Print( -2, "\t         based on Mike Popoloski's slang: https://github.com/MikePopoloski/slang\n" );
    Abc_Print( -2, "\t-M name : select the top module\n" );
    Abc_Print( -2, "\t-D def  : define one macro as NAME or NAME=value; may be repeated\n" );
    Abc_Print( -2, "\t-F file : add another Verilog/SystemVerilog input file\n" );
    Abc_Print( -2, "\t-v      : print the external command and frontend timing\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static int Sn_CommandCollapse( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Sn_Man_t * p;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF )
    {
        switch ( c )
        {
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( argc != globalUtilOptind )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    p = Sn_ManDup( Sn_AbcGetMan(pAbc) );
    if ( p == NULL )
    {
        Abc_Print( -1, "Cannot duplicate the current SN design.\n" );
        return 1;
    }
    p->Top = sn_design_collapse_module_tech( p->pDesign, p->Top );
    assert( sn_design_is_topo(p->pDesign) );
    Sn_ManAdvanceRevision( p );
    Sn_AbcUpdateMan( pAbc, p );
    if ( fVerbose )
        Abc_Print( 1, "Collapsed SN design into module \"%s\".\n",
                   sn_name_get(&p->pDesign->names, sn_design_get_module_const(p->pDesign, p->Top)->name) );
    return 0;

usage:
    Abc_Print( -2, "usage: @collapse [-vh]\n" );
    Abc_Print( -2, "\t         flattens user hierarchy while preserving mapped technology primitives\n" );
    Abc_Print( -2, "\t-v      : print the resulting flat module name\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static int Sn_CommandMapTech( Abc_Frame_t * pAbc, int fMapMem, int fMapDsp, int fMapAdd, int fMapSrl,
                              int MinAddWidth, int fVerbose )
{
    Sn_Man_t * p = Sn_ManDup( Sn_AbcGetMan(pAbc) );
    sn_tech_t Tech = sn_tech_xilinx_ultrascale();
    sn_tech_map_options_t Options = sn_tech_map_default_options();
    sn_tech_map_stats_t Stats = {0};
    Options.map_memories = fMapMem != 0;
    Options.map_multipliers = fMapDsp != 0;
    Options.map_adders = fMapAdd != 0;
    Options.map_shift_registers = fMapSrl != 0;
    Options.add.min_width = MinAddWidth > 0 ? (uint32_t)MinAddWidth : Options.add.min_width;
    if ( p == NULL )
    {
        Abc_Print( -1, "Cannot duplicate the current SN design.\n" );
        return 1;
    }
    if ( !sn_design_check(p->pDesign, Abc_FrameReadErr(pAbc), false) )
    {
        Sn_ManFree( p );
        return 1;
    }
    p->Top = sn_design_map_tech_hierarchy( p->pDesign, p->Top, &Tech, &Options, &Stats );
    if ( p->Top == SN_INVALID_ID )
    {
        Abc_Print( -1, "Technology mapping cannot honor the requested hard-block constraints.\n" );
        Sn_ManFree( p );
        return 1;
    }
    if ( !sn_design_check(p->pDesign, Abc_FrameReadErr(pAbc), false) )
    {
        Sn_ManFree( p );
        return 1;
    }
    p->Technology = SN_COMMAND_TECH_XILINX_ULTRASCALE;
    Sn_ManAdvanceRevision( p );
    Sn_AbcUpdateMan( pAbc, p );
    if ( fVerbose )
        Abc_Print( 1, "Mapped SN design: memory instances = %zu  DSP instances = %zu  CARRY4 instances = %zu  "
                   "SRL instances = %zu.\n",
                   Stats.mem_insts, Stats.dsp_insts, Stats.carry_insts, Stats.srl_insts );
    return 0;
}

static int Sn_CommandCheck( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF )
    {
        if ( c == 'v' )
            fVerbose ^= 1;
        else
            goto usage;
    }
    if ( argc != globalUtilOptind )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    if ( !sn_design_check(Sn_AbcGetMan(pAbc)->pDesign, Abc_FrameReadErr(pAbc), fVerbose != 0) )
        return 1;
    if ( !fVerbose )
        Abc_Print( 1, "SN design is consistent.\n" );
    return 0;

usage:
    Abc_Print( -2, "usage: @check [-vh]\n" );
    Abc_Print( -2, "\t         checks the complete SN design for structural consistency\n" );
    Abc_Print( -2, "\t-v      : print per-module and design summaries\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static int Sn_CommandMapMem( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF )
    {
        if ( c == 'v' )
            fVerbose ^= 1;
        else
            goto usage;
    }
    if ( argc != globalUtilOptind )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    return Sn_CommandMapTech( pAbc, 1, 0, 0, 0, 0, fVerbose );

usage:
    Abc_Print( -2, "usage: @map_mem [-vh]\n" );
    Abc_Print( -2, "\t         maps memories into AMD/Xilinx UltraScale+ primitives\n" );
    Abc_Print( -2, "\t-v      : print mapping statistics\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static int Sn_CommandMapDsp( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF )
    {
        if ( c == 'v' )
            fVerbose ^= 1;
        else
            goto usage;
    }
    if ( argc != globalUtilOptind )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    return Sn_CommandMapTech( pAbc, 0, 1, 0, 0, 0, fVerbose );

usage:
    Abc_Print( -2, "usage: @map_dsp [-vh]\n" );
    Abc_Print( -2, "\t         maps multipliers into AMD/Xilinx UltraScale+ DSP primitives\n" );
    Abc_Print( -2, "\t-v      : print mapping statistics\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static int Sn_CommandMapAdd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, MinWidth = 0, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "Wvh")) != EOF )
    {
        if ( c == 'W' )
        {
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-W\" should be followed by an integer.\n" );
                goto usage;
            }
            MinWidth = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( MinWidth < 1 )
                goto usage;
        }
        else if ( c == 'v' )
            fVerbose ^= 1;
        else
            goto usage;
    }
    if ( argc != globalUtilOptind )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    return Sn_CommandMapTech( pAbc, 0, 0, 1, 0, MinWidth, fVerbose );

usage:
    Abc_Print( -2, "usage: @map_add [-W num] [-vh]\n" );
    Abc_Print( -2, "\t         maps adders and subtractors into AMD/Xilinx UltraScale+ CARRY4 primitives\n" );
    Abc_Print( -2, "\t-W num  : the minimum adder width mapped into carry chains [default = 3]\n" );
    Abc_Print( -2, "\t-v      : print mapping statistics\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static int Sn_CommandMapFf( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Sn_Man_t * p, * pWork;
    sn_library_t * pLibrary;
    uint8_t * pTargets;
    sn_ff_map_stats_t Stats;
    int c, fInfo = 0, Success;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "ih")) != EOF )
        if ( c == 'i' ) fInfo ^= 1;
        else goto usage;
    if ( argc != globalUtilOptind ) goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) ) return 1;
    p = Sn_AbcGetMan(pAbc);
    pLibrary = p->pDesign->library;
    if ( !pLibrary || !p->TargetModels.size )
    {
        Abc_Print(-1, "Load the selected target models with @read_lib before @map_ff.\n");
        return 1;
    }
    pTargets = ABC_CALLOC(uint8_t, pLibrary->cell_count);
    if ( !pTargets ) return 1;
    for ( size_t Target = 0; Target < p->TargetModels.size; ++Target )
    {
        Sn_TargetIdentity_t Identity = sn_vec_at(Sn_TargetIdentity_t, &p->TargetModels, Target);
        int Found = 0;
        for ( uint32_t Model = 0; Model < pLibrary->model_count; ++Model )
            if ( pLibrary->models[Model]->source_size == Identity.Size &&
                 pLibrary->models[Model]->source_hash == Identity.Hash )
            {
                Found = 1;
                for ( uint32_t Cell = 0; Cell < pLibrary->cell_count; ++Cell )
                    pTargets[Cell] |= pLibrary->cells[Cell].model == pLibrary->models[Model];
            }
        if ( !Found )
        {
            Abc_Print(-1, "Selected target is absent from this design; attach it with @read_lib.\n");
            ABC_FREE(pTargets);
            return 1;
        }
    }
    if ( fInfo )
    {
        unsigned Eligible = 0;
        for ( uint32_t Cell = 0; Cell < pLibrary->cell_count; ++Cell )
        {
            sn_seq_info_t Info;
            if ( !pTargets[Cell] ) continue;
            if ( !sn_library_seq_info(pLibrary, Cell, &Info) )
            {
                sn_seq_info_destroy(&Info);
                ABC_FREE(pTargets);
                return 1;
            }
            if ( Info.state )
            {
                const sn_library_cell_t * pCell = &pLibrary->cells[Cell];
                const sn_lib_cell_t * pRecord = &pCell->model->cells[pCell->local_id];
                fprintf(pAbc->Out, "%s: %s, area %.9g, mapping %s\n", sn_lib_name(pCell->model, pRecord->name),
                        Info.latch ? "latch" : "FF", pRecord->area, Info.map_reason ? Info.map_reason : "eligible");
                Eligible += Info.map_reason == NULL;
            }
            sn_seq_info_destroy(&Info);
        }
        fprintf(pAbc->Out, "Sequential target survey: %u eligible cells; no design mutation.\n", Eligible);
        ABC_FREE(pTargets);
        return 0;
    }
    pWork = Sn_ManDup(p);
    if ( !pWork ) { ABC_FREE(pTargets); return 1; }
    Success = sn_design_map_ff(pWork->pDesign, pWork->Top, pTargets, &Stats, pAbc->Err) &&
              sn_design_check(pWork->pDesign, pAbc->Err, false);
    ABC_FREE(pTargets);
    if ( !Success )
    {
        Sn_ManFree(pWork);
        return 1;
    }
    Sn_ManAdvanceRevision(pWork);
    Sn_AbcUpdateMan(pAbc, pWork);
    Abc_Print(1, "Sequential cell mapping: %zu modules, %zu registers, %zu bits (%zu latch bits); "
                "%zu clock/gate pin inversions, %zu verified inactive async ties.\n",
                Stats.modules, Stats.registers, Stats.bits, Stats.latches, Stats.clock_inversions, Stats.inactive_ties);
    return 0;
usage:
    Abc_Print(-2, "usage: @map_ff [-i]\n  -i : survey selected sequential cells without mutation\n"
                 "Maps native FF/latch bits exactly or refuses transactionally. Explicit initialization, "
                 "joint async controls, and unproved scan ties are not approximated.\n");
    return 1;
}

static int Sn_CommandMapDff( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Sn_Man_t * p;
    sn_dff_map_options_t Options = sn_dff_map_default_options();
    sn_dff_map_stats_t Stats = {0};
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "cmlvh")) != EOF )
    {
        if ( c == 'c' )
            Options.fold_constants = !Options.fold_constants;
        else if ( c == 'm' )
            Options.merge_registers = !Options.merge_registers;
        else if ( c == 'l' )
            Options.merge_logic = !Options.merge_logic;
        else if ( c == 'v' )
            fVerbose ^= 1;
        else
            goto usage;
    }
    if ( argc != globalUtilOptind )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    p = Sn_ManDup( Sn_AbcGetMan(pAbc) );
    if ( p == NULL )
    {
        Abc_Print( -1, "Cannot duplicate the current SN design.\n" );
        return 1;
    }
    if ( !sn_design_check(p->pDesign, Abc_FrameReadErr(pAbc), false) )
    {
        Sn_ManFree( p );
        return 1;
    }
    p->Top = sn_design_opt_dff_hierarchy( p->pDesign, p->Top, &Options, &Stats );
    if ( !sn_design_check(p->pDesign, Abc_FrameReadErr(pAbc), false) )
    {
        Sn_ManFree( p );
        return 1;
    }
    Sn_ManAdvanceRevision( p );
    Sn_AbcUpdateMan( pAbc, p );
    if ( fVerbose )
        Abc_Print( 1, "Register optimization: modules changed = %zu  constant regs = %zu  merged regs = %zu  "
                   "shared objects = %zu  regs %zu (%zu bits) -> %zu (%zu bits).\n",
                   Stats.modules_changed, Stats.const_regs, Stats.merged_regs, Stats.merged_objects,
                   Stats.regs_before, Stats.reg_bits_before, Stats.regs_after, Stats.reg_bits_after );
    return 0;

usage:
    Abc_Print( -2, "usage: @map_dff [-cmlvh]\n" );
    Abc_Print( -2, "\t         optimizes registers before flip-flop technology mapping:\n" );
    Abc_Print( -2, "\t         folds provably constant registers, merges identical registers,\n" );
    Abc_Print( -2, "\t         shares identical logic, and sweeps unobservable cones\n" );
    Abc_Print( -2, "\t-c      : toggle folding constant registers [default = yes]\n" );
    Abc_Print( -2, "\t-m      : toggle merging identical registers [default = yes]\n" );
    Abc_Print( -2, "\t-l      : toggle sharing identical logic [default = yes]\n" );
    Abc_Print( -2, "\t-v      : print optimization statistics\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static int Sn_CommandMapSrl( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF )
    {
        if ( c == 'v' )
            fVerbose ^= 1;
        else
            goto usage;
    }
    if ( argc != globalUtilOptind )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    return Sn_CommandMapTech( pAbc, 0, 0, 0, 1, 0, fVerbose );

usage:
    Abc_Print( -2, "usage: @map_srl [-vh]\n" );
    Abc_Print( -2, "\t         extracts shift-register memories into behavioral SRL primitives\n" );
    Abc_Print( -2, "\t-v      : print mapping statistics\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static int Sn_CommandOptMux( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Sn_Man_t * p, * pCurrent;
    sn_share_options_t Options = sn_share_default_options();
    sn_share_stats_t Stats;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF )
    {
        if ( c == 'v' )
            fVerbose ^= 1;
        else
            goto usage;
    }
    if ( argc != globalUtilOptind )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    pCurrent = Sn_AbcGetMan( pAbc );
    if ( !sn_design_check(pCurrent->pDesign, Abc_FrameReadErr(pAbc), 0) )
    {
        Abc_Print( -1, "Cannot @opt_mux: the current SN design is inconsistent.\n" );
        return 1;
    }
    p = Sn_ManDup( pCurrent );
    if ( p == NULL )
    {
        Abc_Print( -1, "Cannot duplicate the current SN design.\n" );
        return 1;
    }
    Stats = sn_design_share( p->pDesign, Options );
    if ( !sn_design_check(p->pDesign, Abc_FrameReadErr(pAbc), 0) )
    {
        Abc_Print( -1, "Cannot @opt_mux: the transformed SN design is inconsistent.\n" );
        Sn_ManFree( p );
        return 1;
    }
    if ( Stats.modules == 0 )
    {
        Sn_ManFree( p );
        if ( fVerbose )
            Abc_Print( 1, "Optimized SN mux paths: no profitable rewrites.\n" );
        return 0;
    }
    Sn_ManAdvanceRevision( p );
    Sn_AbcUpdateMan( pAbc, p );
    if ( fVerbose )
        Abc_Print( 1, "Optimized SN mux paths: modules = %llu  registers = %llu  muxes = %llu  paths = %llu -> %llu.\n",
                   (unsigned long long)Stats.modules, (unsigned long long)Stats.registers,
                   (unsigned long long)Stats.muxes, (unsigned long long)Stats.paths_before,
                   (unsigned long long)Stats.paths_after );
    return 0;

usage:
    Abc_Print( -2, "usage: @opt_mux [-vh]\n" );
    Abc_Print( -2, "\t         shares repeated alternatives in register mux cones\n" );
    Abc_Print( -2, "\t-v      : print transformation statistics\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static ABC_UINT64_T Sn_SignatureWord( ABC_UINT64_T Signature, ABC_UINT64_T Word )
{
    int i;
    for ( i = 0; i < 8; i++ )
    {
        Signature ^= (unsigned char)(Word >> (8 * i));
        Signature *= ABC_CONST(1099511628211);
    }
    return Signature;
}

static ABC_UINT64_T Sn_SignatureString( ABC_UINT64_T Signature, const char * pString )
{
    if ( pString == NULL )
        return Sn_SignatureWord( Signature, ~(ABC_UINT64_T)0 );
    while ( *pString )
    {
        Signature ^= (unsigned char)*pString++;
        Signature *= ABC_CONST(1099511628211);
    }
    return Sn_SignatureWord( Signature, 0 );
}

// Snapshot the library vocabulary, functions, pin order and ranking costs.
// Mio's root collector legitimately renumbers Cell during &nf, so Cell itself
// is not a generation marker. Reconstruction uses that same root collector.
static ABC_UINT64_T Sn_GenlibSignature( Mio_Library_t * pLibrary )
{
    ABC_UINT64_T Signature = ABC_CONST(0xcbf29ce484222325);
    Mio_Gate_t * pGate;
    if ( !pLibrary )
        return 0;
    Mio_LibraryForEachGate( pLibrary, pGate )
    {
        Mio_Pin_t * pPin;
        int Inputs = Mio_GateReadPinNum(pGate);
        uint64_t Truth[SN_MIO_TRUTH_MAX_WORDS];
        int HasTruth = sn_mio_copy_truth(pGate, Truth);
        union { double Real; ABC_UINT64_T Bits; } Area, Delay;
        Area.Real = Mio_GateReadArea(pGate);
        Delay.Real = Mio_GateReadDelayMax(pGate);
        Signature = Sn_SignatureWord( Signature, Area.Bits );
        Signature = Sn_SignatureWord( Signature, Delay.Bits );
        Signature = Sn_SignatureString( Signature, Mio_GateReadName(pGate) );
        Signature = Sn_SignatureString( Signature, Mio_GateReadOutName(pGate) );
        Signature = Sn_SignatureWord( Signature, Inputs );
        Mio_GateForEachPin( pGate, pPin )
            Signature = Sn_SignatureString( Signature, Mio_PinReadName(pPin) );
        Signature = Sn_SignatureWord(Signature, HasTruth);
        if ( HasTruth )
            for ( unsigned i = 0; i < (Inputs <= 6 ? 1u : 1u << (Inputs - 6)); ++i )
                Signature = Sn_SignatureWord( Signature, Truth[i] );
        else
            Signature = Sn_SignatureString(Signature, Mio_GateReadForm(pGate));
    }
    return Signature;
}

static ABC_UINT64_T Sn_BoundaryBitSignature( ABC_UINT64_T Signature,
                                             const sn_blast_boundary_bit_t * pBit )
{
    Signature = Sn_SignatureWord( Signature, (uint32_t)pBit->kind );
    Signature = Sn_SignatureWord( Signature, pBit->signal.occurrence );
    Signature = Sn_SignatureWord( Signature, pBit->signal.object );
    Signature = Sn_SignatureWord( Signature, pBit->signal.bit );
    Signature = Sn_SignatureWord( Signature, pBit->owner );
    return Sn_SignatureWord( Signature, pBit->port );
}

// This signature covers the selected module and every table that gives meaning to a boundary owner. Endpoint order,
// kind, hierarchical signal reference, owner, port, and bit are included explicitly to avoid hashing struct padding.
static ABC_UINT64_T Sn_BoundarySignature( const Sn_Man_t * p )
{
    ABC_UINT64_T Signature = ABC_CONST(0xcbf29ce484222325);
    size_t i;
    int Slot;
    Signature = Sn_SignatureWord( Signature, p->BlastModule );
    Signature = Sn_SignatureString( Signature, sn_name_get(&p->pDesign->names, p->BlastName) );
    Signature = Sn_SignatureWord( Signature, (uint32_t)p->BlastMode );
    Signature = Sn_SignatureWord( Signature, p->Boundary.register_bits );
    Signature = Sn_SignatureWord( Signature, p->Boundary.occurrences.size );
    for ( i = 0; i < p->Boundary.occurrences.size; i++ )
    {
        const sn_blast_occurrence_t * pEntry = &sn_vec_at(sn_blast_occurrence_t, &p->Boundary.occurrences, i);
        Signature = Sn_SignatureWord( Signature, pEntry->module );
        Signature = Sn_SignatureWord( Signature, pEntry->parent_occurrence );
        Signature = Sn_SignatureWord( Signature, pEntry->parent_inst );
    }
    Signature = Sn_SignatureWord( Signature, p->Boundary.primitives.size );
    for ( i = 0; i < p->Boundary.primitives.size; i++ )
    {
        const sn_blast_primitive_t * pEntry = &sn_vec_at(sn_blast_primitive_t, &p->Boundary.primitives, i);
        Signature = Sn_SignatureWord( Signature, pEntry->occurrence );
        Signature = Sn_SignatureWord( Signature, pEntry->inst );
        Signature = Sn_SignatureWord( Signature, pEntry->module );
        Signature = Sn_SignatureWord( Signature, pEntry->ci_begin );
        Signature = Sn_SignatureWord( Signature, pEntry->output_count );
        Signature = Sn_SignatureWord( Signature, pEntry->ci_count );
        Signature = Sn_SignatureWord( Signature, pEntry->co_begin );
        Signature = Sn_SignatureWord( Signature, pEntry->co_count );
    }
    Signature = Sn_SignatureWord( Signature, p->Boundary.registers.size );
    for ( i = 0; i < p->Boundary.registers.size; i++ )
    {
        const sn_blast_register_t * pEntry = &sn_vec_at(sn_blast_register_t, &p->Boundary.registers, i);
        Signature = Sn_SignatureWord( Signature, pEntry->occurrence );
        Signature = Sn_SignatureWord( Signature, pEntry->reg_out );
        Signature = Sn_SignatureWord( Signature, pEntry->ci_begin );
        Signature = Sn_SignatureWord( Signature, pEntry->co_begin );
        Signature = Sn_SignatureWord( Signature, pEntry->width );
        for ( Slot = 0; Slot < SN_REG_FANIN_COUNT; Slot++ )
            Signature = Sn_SignatureWord( Signature, pEntry->control_co_begin[Slot] );
    }
    Signature = Sn_SignatureWord( Signature, p->Boundary.loops.size );
    for ( i = 0; i < p->Boundary.loops.size; i++ )
    {
        const sn_blast_loop_t * pEntry = &sn_vec_at(sn_blast_loop_t, &p->Boundary.loops, i);
        Signature = Sn_SignatureWord( Signature, pEntry->occurrence );
        Signature = Sn_SignatureWord( Signature, pEntry->loop_out );
        Signature = Sn_SignatureWord( Signature, pEntry->co_begin );
        Signature = Sn_SignatureWord( Signature, pEntry->width );
    }
    Signature = Sn_SignatureWord( Signature, p->Boundary.cis.size );
    for ( i = 0; i < p->Boundary.cis.size; i++ )
        Signature = Sn_BoundaryBitSignature(
            Signature, &sn_vec_at(sn_blast_boundary_bit_t, &p->Boundary.cis, i) );
    Signature = Sn_SignatureWord( Signature, p->Boundary.cos.size );
    for ( i = 0; i < p->Boundary.cos.size; i++ )
        Signature = Sn_BoundaryBitSignature(
            Signature, &sn_vec_at(sn_blast_boundary_bit_t, &p->Boundary.cos, i) );
    return Signature;
}

// Boundary names contain the retained signal name, bit index, and a unique interface index. ABC's normal GIA
// synthesis commands preserve these names. Hashing their ordered vectors detects interface permutations and also
// rejects a command that discarded the identity needed to prove that the boundary order is unchanged.
static ABC_UINT64_T Sn_GiaInterfaceSignature( Gia_Man_t * pGia )
{
    ABC_UINT64_T Signature = ABC_CONST(0xcbf29ce484222325);
    char * pName;
    int i;
    Signature = Sn_SignatureWord( Signature, Gia_ManCiNum(pGia) );
    Signature = Sn_SignatureWord( Signature, Gia_ManCoNum(pGia) );
    Signature = Sn_SignatureWord( Signature, pGia->vNamesIn ? (ABC_UINT64_T)Vec_PtrSize(pGia->vNamesIn) : ~(ABC_UINT64_T)0 );
    if ( pGia->vNamesIn )
        Vec_PtrForEachEntry( char *, pGia->vNamesIn, pName, i )
            Signature = Sn_SignatureString( Signature, pName );
    Signature = Sn_SignatureWord( Signature, pGia->vNamesOut ? (ABC_UINT64_T)Vec_PtrSize(pGia->vNamesOut) : ~(ABC_UINT64_T)0 );
    if ( pGia->vNamesOut )
        Vec_PtrForEachEntry( char *, pGia->vNamesOut, pName, i )
            Signature = Sn_SignatureString( Signature, pName );
    return Signature;
}

static ABC_UINT64_T Sn_NtkInterfaceSignature( Abc_Ntk_t * pNtk )
{
    ABC_UINT64_T Signature = ABC_CONST(0xcbf29ce484222325);
    Abc_Obj_t * pObj;
    int i;
    Signature = Sn_SignatureWord(Signature, Abc_NtkCiNum(pNtk));
    Signature = Sn_SignatureWord(Signature, Abc_NtkCoNum(pNtk));
    Signature = Sn_SignatureWord(Signature, Abc_NtkCiNum(pNtk));
    Abc_NtkForEachCi(pNtk, pObj, i)
        Signature = Sn_SignatureString(Signature, Abc_ObjName(pObj));
    Signature = Sn_SignatureWord(Signature, Abc_NtkCoNum(pNtk));
    Abc_NtkForEachCo(pNtk, pObj, i)
        Signature = Sn_SignatureString(Signature, Abc_ObjName(pObj));
    return Signature;
}

// ABC copies pSpec through &put and the main-space mappers. It is provenance
// for this generated network, not a file to read. The token distinguishes a
// stale network even when a later extraction has exactly the same port names.
static void Sn_StampExtraction( Sn_Man_t * p, Gia_Man_t * pGia )
{
    static ABC_UINT64_T NextToken = 0;
    char Token[80];
    p->BlastToken = ++NextToken;
    snprintf(Token, sizeof(Token), "sn-extraction-%llu", (unsigned long long)p->BlastToken);
    ABC_FREE(pGia->pSpec);
    pGia->pSpec = Abc_UtilStrsav(Token);
}

// Canonical boundary names (see sn_blast_boundary_bit_name). Duplicate names receive a "#<n>" suffix so that every
// CI/CO name is unique; the counts of non-canonical and suffixed names are returned for reporting.
static void Sn_GiaSetNames( Gia_Man_t * pGia, const Sn_Man_t * p, int fOmitLoops,
                            int * pNonCanonical, int * pDuplicates )
{
    Abc_Nam_t * pNam = Abc_NamStart( (int)(p->Boundary.cis.size + p->Boundary.cos.size) + 16, 32 );
    int nNonCanonical = 0, nDuplicates = 0;
    size_t i;
    assert( pGia && (fOmitLoops || (size_t)Gia_ManCiNum(pGia) == p->Boundary.cis.size) );
    assert( fOmitLoops || (size_t)Gia_ManCoNum(pGia) == p->Boundary.cos.size );
    if ( pGia->vNamesIn )
        Vec_PtrFreeFree( pGia->vNamesIn );
    if ( pGia->vNamesOut )
        Vec_PtrFreeFree( pGia->vNamesOut );
    pGia->vNamesIn = Vec_PtrAlloc( Gia_ManCiNum(pGia) );
    pGia->vNamesOut = Vec_PtrAlloc( Gia_ManCoNum(pGia) );
    for ( i = 0; i < p->Boundary.cis.size + p->Boundary.cos.size; i++ )
    {
        int fCi = i < p->Boundary.cis.size;
        const sn_blast_boundary_bit_t * pBit = fCi
            ? &sn_vec_at(sn_blast_boundary_bit_t, &p->Boundary.cis, i)
            : &sn_vec_at(sn_blast_boundary_bit_t, &p->Boundary.cos, i - p->Boundary.cis.size);
        if ( fOmitLoops && (pBit->kind == SN_BLAST_BOUNDARY_LOOP_INPUT || pBit->kind == SN_BLAST_BOUNDARY_LOOP_OUTPUT) )
            continue;
        bool fCanonical = true;
        char * pName = sn_blast_boundary_bit_name( p->pDesign, &p->Boundary, pBit, &fCanonical );
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
        (char *)sn_name_get(&p->pDesign->names, sn_design_get_module_const(p->pDesign, p->BlastModule)->name) );
    if ( pNonCanonical )
        *pNonCanonical = nNonCanonical;
    if ( pDuplicates )
        *pDuplicates = nDuplicates;
}

static int Sn_CommandClockBlast( Abc_Frame_t * pAbc, Sn_Man_t * p, sn_module_id_t Top,
                                 int fTransition, int fZero, int fMacros, int fNamedStates,
                                 int fStateActions, int fVerbose, const char * pConstraints )
{
    const sn_module_t * pTop = sn_design_get_module_const(p->pDesign, Top);
    sn_clock_options_t Options = {0};
    Vec_Int_t * pValues = Vec_IntAlloc(100);
    Gia_Man_t * pResult;
    const char * pReason;
    char * pText = pConstraints ? Abc_UtilStrsav((char *)pConstraints) : NULL, * pEntry = pText;
    for ( size_t i = 0; i < pTop->type_objects[SN_PI].size; ++i )
    {
        sn_obj_id_t Obj = sn_vec_at(sn_obj_id_t, &pTop->type_objects[SN_PI], i);
        for ( uint32_t b = 0; b < sn_obj_width(pTop, Obj); ++b ) Vec_IntPush(pValues, -1);
    }
    while ( pEntry )
    {
        char * pNext = strchr(pEntry, ','), * pEqual;
        int Bit = 0, Found = 0;
        if ( pNext ) *pNext++ = 0;
        pEqual = strrchr(pEntry, '=');
        if ( !pEqual || (strcmp(pEqual + 1, "0") && strcmp(pEqual + 1, "1")) )
            goto bad_constraint;
        *pEqual++ = 0;
        for ( size_t i = 0; i < pTop->type_objects[SN_PI].size; ++i )
        {
            sn_obj_id_t Obj = sn_vec_at(sn_obj_id_t, &pTop->type_objects[SN_PI], i);
            if ( sn_obj_width(pTop, Obj) == 1 && sn_obj_name_id(pTop, Obj) != SN_INVALID_ID &&
                 !strcmp(sn_obj_name(pTop, Obj), pEntry) )
            {
                if ( Vec_IntEntry(pValues, Bit) >= 0 ) goto bad_constraint;
                Vec_IntWriteEntry(pValues, Bit, *pEqual - '0');
                Found = 1;
            }
            Bit += sn_obj_width(pTop, Obj);
        }
        if ( !Found ) goto bad_constraint;
        pEntry = pNext;
    }
    Options.transition = fTransition;
    Options.assume_zero = fZero;
    Options.allow_macros = fMacros;
    Options.named_states = fNamedStates || fStateActions;
    Options.state_actions = fStateActions;
    Options.verbose = fVerbose;
    Options.pi_values = Vec_IntArray(pValues);
    Options.pi_count = Vec_IntSize(pValues);
    pResult = sn_design_clock_abstract(p->pDesign, Top, Options, pAbc->Out, &pReason);
    ABC_FREE(pText);
    Vec_IntFree(pValues);
    if ( !pResult ) return 1;
    pResult->pName = Abc_UtilStrsav((char *)sn_name_get(&p->pDesign->names, pTop->name));
    Abc_FrameUpdateGia(pAbc, pResult);
    p->fBlasted = 0; // analysis is never a combinational reinsertion boundary
    p->fLastBlast = 0;
    p->pLastAnalysis = fStateActions ? "state-action signature" : "clock abstraction";
    return 0;
bad_constraint:
    Abc_Print(-1, "Invalid -R constraint: use distinct scalar top inputs, name=0,name=1; vector ports and bit selections are not supported.\n");
    ABC_FREE(pText);
    Vec_IntFree(pValues);
    return 1;
}

static int Sn_CommandBlast( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Sn_Man_t * p;
    Mini_Aig_t * pAig;
    abctime clkBlast, clkImport, clkNames;
    int nMiniAnds;
    sn_blast_options_t Options = sn_blast_default_options();
    sn_blast_hier_stats_t Stats = {0};
    char * pModuleName = NULL, * pConstraints = NULL;
    sn_module_id_t BlastModule;
    int c, fVerbose = 0, nNonCanonical = 0, nDuplicates = 0, fAbstract = 0, fStateActions = 0, fZero = 0, fMacros = 0, fNamedStates = 0, fOrdinaryOptions = 0;
    // Header-level blast diagnostics go to stderr. Finish buffered @ps output
    // before any such diagnostic so redirected logs do not interleave mid-line.
    fflush( pAbc->Out );
    if ( pAbc->Out != stdout )
        fflush( stdout );
    Options.mode = SN_BLAST_SEQ;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "MRNaqzuctdbrpfvh")) != EOF )
    {
        if ( strchr("cdbrpf", c) ) fOrdinaryOptions = 1;
        switch ( c )
        {
        case 'a': fAbstract = 1; break;
        case 'q': fStateActions = 1; break;
        case 'z': fZero = 1; break;
        case 'u': fMacros = 1; break;
        case 'N': fNamedStates = 1; break;
        case 'R':
            if ( globalUtilOptind >= argc || pConstraints ) goto usage;
            pConstraints = argv[globalUtilOptind++];
            break;
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a module name.\n" );
                goto usage;
            }
            pModuleName = argv[globalUtilOptind++];
            break;
        case 'c':
            Options.mode = SN_BLAST_COMB;
            break;
        case 't':
            Options.mode = SN_BLAST_TRANSITION;
            break;
        case 'b':
            Options.mul_mode = Options.mul_mode == SN_BLAST_MUL_BOOTH ? SN_BLAST_MUL_BAUGH_WOOLEY :
                                                                       SN_BLAST_MUL_BOOTH;
            break;
        case 'd':
            Options.delay_comparators ^= 1;
            break;
        case 'r':
            Options.ripple_adders ^= 1;
            break;
        case 'p':
            Options.abstract_memory_primitives = false;
            Options.abstract_multipliers = false;
            Options.abstract_carries = false;
            break;
        case 'f':
            Options.opaque_sequential_gates = true;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( argc != globalUtilOptind )
        goto usage;
    if ( ((fAbstract || fStateActions) && fOrdinaryOptions) || (fAbstract && fStateActions) ||
         (fStateActions && (fZero || Options.mode == SN_BLAST_TRANSITION)) ||
         (!(fAbstract || fStateActions) && (fZero || fMacros || fNamedStates || pConstraints)) )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    p = Sn_AbcGetMan( pAbc );
    BlastModule = pModuleName ? sn_design_find_module( p->pDesign, pModuleName ) : p->Top;
    if ( BlastModule == SN_INVALID_ID )
    {
        Abc_Print( -1, "Cannot find module \"%s\" in the current SN design.\n", pModuleName );
        return 1;
    }
    if ( sn_module_is_blackbox(sn_design_get_module_const(p->pDesign, BlastModule)) )
    {
        Abc_Print( -1, "Cannot @blast: selected module \"%s\" is an opaque black box; "
                       "blast its enclosing design to expose the black-box boundary.\n",
                   sn_name_get(&p->pDesign->names,
                               sn_design_get_module_const(p->pDesign, BlastModule)->name) );
        return 1;
    }
    if ( fAbstract || fStateActions )
        return Sn_CommandClockBlast(pAbc, p, BlastModule, fStateActions || Options.mode == SN_BLAST_TRANSITION,
                                   fZero, fMacros, fNamedStates, fStateActions, fVerbose, pConstraints);
    sn_blast_boundary_destroy( &p->Boundary );
    sn_blast_boundary_init( &p->Boundary );
    clkBlast = Abc_Clock();
    pAig = sn_design_blast_hier_boundary_options( p->pDesign, BlastModule, Options, &Stats, &p->Boundary );
    if ( pAig == NULL )
        return 1;
    clkBlast = Abc_Clock() - clkBlast;
    nMiniAnds = Mini_AigAndNum( pAig );
    clkImport = Abc_Clock();
    Abc_FrameGiaInputMiniAig( pAbc, pAig );
    clkImport = Abc_Clock() - clkImport;
    Mini_AigStop( pAig );
    p->BlastModule = BlastModule;
    p->BlastName = sn_design_get_module_const( p->pDesign, BlastModule )->name;
    p->fBlasted = 1;
    p->BlastMode = Options.mode;
    p->fLastBlast = 1;
    p->pLastAnalysis = NULL;
    p->LastBlastModule = p->BlastModule;
    p->LastBlastName = p->BlastName;
    p->LastBlastRevision = p->Revision;
    p->BlastBoundarySignature = Sn_BoundarySignature( p );
    clkNames = Abc_Clock();
    Sn_GiaSetNames( Abc_FrameReadGia(pAbc), p, 0, &nNonCanonical, &nDuplicates );
    p->BlastInterfaceSignature = Sn_GiaInterfaceSignature( Abc_FrameReadGia(pAbc) );
    p->BlastGenlibSignature = Sn_GenlibSignature( (Mio_Library_t *)Abc_FrameReadLibGen() );
    Sn_StampExtraction(p, Abc_FrameReadGia(pAbc));
    clkNames = Abc_Clock() - clkNames;
    if ( fVerbose )
    {
        Abc_Print( 1, "Blasted SN design: PI bits = %llu  PO bits = %llu  flop bits = %llu  "
                       "memories = %llu  multipliers = %llu.\n",
                   (unsigned long long)Stats.primary_input_bits, (unsigned long long)Stats.primary_output_bits,
                   (unsigned long long)Stats.flop_bits, (unsigned long long)Stats.memory_count,
                   (unsigned long long)Stats.multiplier_count );
        Abc_Print( 1, "@blast phases: MiniAIG = %.2f s (%d ANDs)  GIA import = %.2f s (%d ANDs)  names = %.2f s.\n",
                   (double)clkBlast / CLOCKS_PER_SEC, nMiniAnds, (double)clkImport / CLOCKS_PER_SEC,
                   Gia_ManAndNum(Abc_FrameReadGia(pAbc)), (double)clkNames / CLOCKS_PER_SEC );
        if ( nNonCanonical || nDuplicates )
            Abc_Print( 1, "@blast names: %d boundary bit(s) have non-canonical names and %d received a #n suffix; "
                          "name-based matching of these bits across @put is unreliable.\n",
                       nNonCanonical, nDuplicates );
    }
    return 0;

usage:
    Abc_Print( -2, "usage: @blast [-M module] [-ctdbrpfaqNuzvh] [-R pin=0,pin=1]\n" );
    Abc_Print( -2, "       ordinary extraction: @blast [-M module] [-ctdbrpfv]\n" );
    Abc_Print( -2, "       @blast -a [-M module] [-t | -z] [-uNv] [-R pin=0,pin=1]\n" );
    Abc_Print( -2, "       @blast -q [-M module] [-uv] [-R pin=0,pin=1]\n" );
    Abc_Print( -2, "\t-q      : named state-action/trigger proof signature, including plain latches;\n" );
    Abc_Print( -2, "\t          combinational only, not a time-step model; never eligible for @put\n" );
    Abc_Print( -2, "\t-N      : pair states by instance/register identity, not index (with -a)\n" );
    Abc_Print( -2, "\t-u      : allow named opaque macro cuts (with -a or -q); model is explicitly conditional\n" );
    Abc_Print( -2, "\t-a      : checked closed single-clock analysis; refuses unsupported cuts/domains\n" );
    Abc_Print( -2, "\t-z      : explicitly assume zero for unspecified state (analysis only, with -a)\n" );
    Abc_Print( -2, "\t-R list : constrain scalar inputs constantly (with -a or -q); async controls must prove inactive\n" );
    Abc_Print( -2, "\t          vector ports and bit selections are not supported\n" );
    Abc_Print( -2, "\t         derives a flat AIG directly from the hierarchical SN design\n" );
    Abc_Print( -2, "\t-M name : select the module replaced by a later @put [default = current top]\n" );
    Abc_Print( -2, "\t-c      : use combinational AIG mode\n" );
    Abc_Print( -2, "\t-t      : ordinary mode: sampled transition relation; with -a: checked free-state relation\n" );
    Abc_Print( -2, "\t-b      : toggle Booth multiplier blasting [default = Baugh-Wooley]\n" );
    Abc_Print( -2, "\t-d      : toggle delay-oriented comparator blasting [default = enabled]\n" );
    Abc_Print( -2, "\t-r      : toggle ripple-carry adders [default = Brent-Kung]\n" );
    Abc_Print( -2, "\t-p      : expand mapped memory, DSP, and carry primitives for verification\n" );
    Abc_Print( -2, "\t-f      : keep Liberty flip-flop cells as opaque boundaries (enables @put after mapping)\n" );
    Abc_Print( -2, "\t-v      : print bit-blasting statistics; analysis modes also print per-bit identity/phase\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

typedef struct Sn_MioBindings_t_
{
    sn_mio_binding_t * pEntries;
    unsigned Count;
} Sn_MioBindings_t;

static void Sn_MioBindingsFree( Sn_MioBindings_t * p )
{
    if ( !p )
        return;
    for ( unsigned i = 0; i < p->Count; ++i )
        sn_mio_binding_destroy( &p->pEntries[i] );
    ABC_FREE( p->pEntries );
    ABC_FREE( p );
}

static Sn_MioBindings_t * Sn_MioBindingsStart( sn_library_t * pLibrary, Mio_Library_t * pMio )
{
    Sn_MioBindings_t * p = ABC_CALLOC( Sn_MioBindings_t, 1 );
    Mio_Gate_t * pGate;
    if ( !p || !pMio || !sn_library_compile(pLibrary) )
    {
        ABC_FREE( p );
        return NULL;
    }
    p->Count = (unsigned)Mio_LibraryReadGateNum(pMio);
    p->pEntries = ABC_CALLOC( sn_mio_binding_t, p->Count );
    if ( !p->pEntries )
    {
        ABC_FREE( p );
        return NULL;
    }
    Mio_LibraryForEachGate( pMio, pGate )
    {
        int Id = Mio_GateReadCell(pGate);
        if ( Id < 0 || (unsigned)Id >= p->Count || p->pEntries[Id].kind != SN_MIO_UNBOUND ||
             !sn_mio_bind_gate(pLibrary, pGate, &p->pEntries[Id]) )
        {
            Abc_Print( -1, "Cannot bind cell %s: %s.\n", Mio_GateReadName(pGate),
                       Id >= 0 && (unsigned)Id < p->Count && p->pEntries[Id].reason ?
                       p->pEntries[Id].reason : "invalid or duplicate Mio cell ID" );
            Sn_MioBindingsFree( p );
            return NULL;
        }
    }
    return p;
}

static int Sn_CommandReadLib( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Vec_Str_t * Abc_SclProduceGenlibStrSimple( SC_Lib * p );
    Sn_Man_t * p;
    sn_lib_t * pModel = NULL;
    sn_library_t * pBundle = NULL, * pAddition = NULL;
    SC_Lib * pScl = NULL;
    Mio_Library_t * pMio = NULL;
    Amap_Lib_t * pAmap = NULL;
    Sn_MioBindings_t * pBindings = NULL;
    uint32_t * pTargets = NULL;
    char ** pTextPaths = NULL;
    SC_DontUse DontUse = {0, NULL};
    int c, fMulti = 0, fMixedCorner = 0;
    const sn_lib_t * pFirstTarget = NULL;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "mh")) != EOF )
        if ( c == 'm' ) fMulti ^= 1;
        else goto usage;
    if ( argc - globalUtilOptind < 1 )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    p = Sn_AbcGetMan(pAbc);
    if ( !p->pDesign->library )
        for ( size_t i = 0; i < p->pDesign->modules.size; ++i )
            if ( sn_design_get_module_const(p->pDesign, i)->type_objects[SN_GATE].size )
            {
                Abc_Print( -1, "Cannot @read_lib: regenerate legacy Mio-ID SN gates from their source.\n" );
                return 1;
            }
    if ( Abc_FrameReadNtk(pAbc) && Abc_NtkHasMapping(Abc_FrameReadNtk(pAbc)) )
    {
        Abc_Print( -1, "Cannot @read_lib: clear the mapped main network before replacing its library.\n" );
        return 1;
    }
    if ( p->pDesign->library )
    {
        pBundle = sn_library_clone_models(p->pDesign->library);
        if ( !pBundle )
            goto failed;
    }
    pTargets = ABC_ALLOC(uint32_t, argc - globalUtilOptind);
    pTextPaths = ABC_CALLOC(char *, argc - globalUtilOptind);
    if ( !pTargets || !pTextPaths ) goto failed;
    for ( int Arg = globalUtilOptind; Arg < argc; ++Arg )
    {
        uint32_t Reuse = SN_LIB_NONE;
        int Binary = sn_lib_is_binary_file(argv[Arg]);
        pModel = sn_lib_load_any(argv[Arg]);
        if ( !sn_lib_ok(pModel) ) goto failed;
        // Binary SN models contain functions, not an ABC SCL representation.
        // Reuse the recorded source only after checking its entire byte identity;
        // a same-named corner or a changed file is never a timing substitute.
        const char * pTextPath = Binary ? pModel->path : argv[Arg];
        uint64_t TextSize = 0, TextHash = 0;
        if ( Binary && (!pTextPath || !sn_lib_source_identity(pTextPath, &TextSize, &TextHash) ||
                        TextSize != pModel->source_size || TextHash != pModel->source_hash) )
        {
            Abc_Print(-1, "Binary target %s needs its byte-identical Liberty source (%s); "
                          "recorded size/hash did not match an available file.\n",
                      argv[Arg], pTextPath ? pTextPath : "no recorded path");
            goto failed;
        }
        pTextPaths[Arg - globalUtilOptind] = sn_lib_copy_string(pTextPath);
        if ( !pTextPaths[Arg - globalUtilOptind] ) goto failed;
        if ( Binary )
            Abc_Print(1, "Binary target %s: verified source size/hash for SCL timing reuse from %s.\n",
                      argv[Arg], pTextPath);
        for ( uint32_t i = 0; pBundle && i < pBundle->model_count; ++i )
            if ( pBundle->models[i]->source_hash == pModel->source_hash &&
                 pBundle->models[i]->source_size == pModel->source_size )
                Reuse = i;
        if ( Reuse != SN_LIB_NONE )
        {
            sn_lib_destroy(pModel);
            pModel = NULL;
        }
        else
        {
            Reuse = pBundle ? pBundle->model_count : 0;
            pAddition = sn_library_create(pModel);
            pModel = NULL; // create consumes the model on success or failure
            if ( !pAddition ) goto failed;
            if ( !pBundle ) pBundle = pAddition;
            else if ( !sn_library_append(pBundle, pAddition) ) goto failed;
            pAddition = NULL;
        }
        pTargets[Arg - globalUtilOptind] = Reuse;
    }
    // Prepare all three ABC representations before changing any global handle.
    // This is the preparation part of Abc_SclInstallGenlib, split from its
    // non-transactional global installation so a failure cannot corrupt SN.
    if ( !sn_library_compile(pBundle) ) goto failed;
    // Keep unsupported cells in SN for preservation, but do not let the SCL
    // converter offer them as targets which the checked binder cannot consume.
    DontUse.dont_use_list = ABC_ALLOC(char *, pBundle->cell_count);
    if ( !DontUse.dont_use_list ) goto failed;
    for ( uint32_t Cell = 0; Cell < pBundle->cell_count; ++Cell )
        if ( pBundle->cells[Cell].output_count > 2 || pBundle->cells[Cell].input_count > 16 )
        {
            DontUse.dont_use_list[DontUse.size++] = (char *)sn_library_cell_name(pBundle, Cell);
            Abc_Print(1, "Excluded mapping target %s (%u inputs, %u outputs): checked binding supports at most 16 inputs and 2 outputs.\n",
                      sn_library_cell_name(pBundle, Cell), pBundle->cells[Cell].input_count, pBundle->cells[Cell].output_count);
        }
    for ( int Arg = globalUtilOptind; Arg < argc; ++Arg )
    {
        uint32_t ModelId = pTargets[Arg - globalUtilOptind];
        const sn_lib_t * pTarget = pBundle->models[ModelId];
        int Duplicate = 0, Eligible = 0;
        for ( int Prior = globalUtilOptind; Prior < Arg; ++Prior )
            Duplicate |= pTargets[Prior - globalUtilOptind] == ModelId;
        if ( Duplicate ) continue;
        for ( uint32_t Cell = 0; Cell < pBundle->cell_count; ++Cell )
            if ( pBundle->cells[Cell].model == pTarget &&
                 sn_expr_check(&pBundle->functions[Cell]) && !sn_expr_check(&pBundle->transitions[Cell]) &&
                 !pTarget->cells[pBundle->cells[Cell].local_id].dont_use &&
                 pBundle->cells[Cell].input_count <= 16 &&
                 pBundle->cells[Cell].output_count <= (fMulti ? 2u : 1u) )
                ++Eligible;
        if ( !Eligible )
        {
            Abc_Print(1, "Target %s contributes interfaces only (no eligible combinational cells).\n", argv[Arg]);
            continue;
        }
        if ( pFirstTarget &&
             ((isfinite(pFirstTarget->nom_temperature) && isfinite(pTarget->nom_temperature) &&
               pFirstTarget->nom_temperature != pTarget->nom_temperature) ||
              (isfinite(pFirstTarget->nom_process) && isfinite(pTarget->nom_process) &&
               pFirstTarget->nom_process != pTarget->nom_process)) )
        {
            fMixedCorner = 1;
            Abc_Print(0, "Nominal corners differ: %s (temperature=%g, process=%g) and %s (temperature=%g, process=%g).\n",
                      pFirstTarget->path, pFirstTarget->nom_temperature, pFirstTarget->nom_process,
                      pTarget->path, pTarget->nom_temperature, pTarget->nom_process);
        }
        if ( !pFirstTarget ) pFirstTarget = pTarget;
        // SCL normalizes supported time/load units to ps/ff. Reject unknown
        // explicit declarations instead of allowing its fallback defaults.
        const char * pTimeUnit = sn_lib_name(pTarget, pTarget->time_unit);
        const char * pCapUnit = sn_lib_name(pTarget, pTarget->capacitive_load_unit_name);
        if ( (pTarget->time_unit != SN_LIB_NONE && strcmp(pTimeUnit, "1ns") && strcmp(pTimeUnit, "100ps") &&
              strcmp(pTimeUnit, "10ps") && strcmp(pTimeUnit, "1ps")) ||
             (pTarget->capacitive_load_unit_name != SN_LIB_NONE &&
              ((strcmp(pCapUnit, "pf") && strcmp(pCapUnit, "ff")) ||
               !isfinite(pTarget->capacitive_load_unit) || pTarget->capacitive_load_unit <= 0)) )
        {
            Abc_Print(-1, "Unsupported explicit Liberty time/load units in %s.\n", argv[Arg]);
            goto failed;
        }
        SC_Lib * pNext = Abc_SclReadLiberty(pTextPaths[Arg - globalUtilOptind], 0, 0, DontUse, !fMulti);
        if ( !pNext ) goto failed;
        if ( !pScl ) pScl = pNext;
        else
        {
            SC_Lib * pMerged;
            if ( pScl->unit_time != pNext->unit_time || pScl->unit_cap_fst != pNext->unit_cap_fst ||
                 pScl->unit_cap_snd != pNext->unit_cap_snd )
            {
                Abc_Print(-1, "Target library units differ; explicit normalization is required.\n");
                Abc_SclLibFree(pNext);
                goto failed;
            }
            if ( pScl->nom_voltage != pNext->nom_voltage )
            {
                fMixedCorner = 1;
                Abc_Print(0, "Nominal voltages differ: %s (%g V) and %s (%g V).\n",
                          pFirstTarget->path, pScl->nom_voltage, pTarget->path, pNext->nom_voltage);
            }
            pMerged = Abc_SclMergeLibraries(pScl, pNext, 0);
            Abc_SclLibFree(pNext);
            if ( !pMerged ) goto failed;
            Abc_SclLibFree(pScl);
            pScl = pMerged;
        }
    }
    if ( !pScl || Abc_SclLibClassNum(pScl) < 3 )
        goto failed;
    // The stock genlib text adapter uses 200-byte formatting buffers. Refuse
    // unrepresentable targets before entering it (including Release builds).
    {
        SC_Cell * pCell;
        SC_Pin * pPin;
        int i, k;
        SC_LibForEachCell(pScl, pCell, i)
        {
            if ( strlen(pCell->pName) >= 200 || !isfinite(pCell->area) ||
                 pCell->area < 0 || pCell->area > 1e100 )
                goto failed;
            SC_CellForEachPinIn(pCell, pPin, k)
                if ( strlen(pPin->pName) >= 200 )
                    goto failed;
        }
    }
    {
        Vec_Str_t * pText = Abc_SclProduceGenlibStrSimple(pScl);
        Vec_Str_t * pText2 = Vec_StrDup(pText);
        pMio = Mio_LibraryRead(argv[globalUtilOptind], Vec_StrArray(pText), NULL, 0, 0);
        pAmap = Amap_LibReadAndPrepare(argv[globalUtilOptind], Vec_StrArray(pText2), 0, 0);
        Vec_StrFree(pText);
        Vec_StrFree(pText2);
    }
    if ( !pMio || !pAmap || !(pBindings = Sn_MioBindingsStart(pBundle, pMio)) )
        goto failed;
    Sn_MioBindingsFree(pBindings);
    if ( Abc_FrameReadLibSuper() )
        Map_SuperLibFree((Map_SuperLib_t *)Abc_FrameReadLibSuper());
    Abc_FrameSetLibSuper(NULL);
    Mio_LibraryDelete((Mio_Library_t *)Abc_FrameReadLibGen());
    Amap_LibFree((Amap_Lib_t *)Abc_FrameReadLibGen2());
    Abc_FrameSetLibGen(pMio);
    Abc_FrameSetLibGen2(pAmap);
    if ( pAbc->pLibScl )
        Abc_SclLibFree((SC_Lib *)pAbc->pLibScl);
    pAbc->pLibScl = fMixedCorner ? NULL : pScl;
    if ( fMixedCorner )
    {
        Abc_SclLibFree(pScl);
        Abc_Print(0, "Mixed nominal corners: functional/area mapping only; SCL timing and sizing disabled.\n");
    }
    sn_library_release(p->pDesign->library);
    p->pDesign->library = pBundle;
    sn_vec_resize(Sn_TargetIdentity_t, &p->TargetModels, argc - globalUtilOptind);
    for ( int Arg = globalUtilOptind; Arg < argc; ++Arg )
    {
        const sn_lib_t * pTarget = pBundle->models[pTargets[Arg - globalUtilOptind]];
        Sn_TargetIdentity_t * pIdentity = &sn_vec_at(Sn_TargetIdentity_t, &p->TargetModels, Arg - globalUtilOptind);
        pIdentity->Size = pTarget->source_size;
        pIdentity->Hash = pTarget->source_hash;
    }
    Sn_ManAdvanceRevision(p);
    p->TargetGenlibSignature = Sn_GenlibSignature(pMio);
    ABC_FREE(DontUse.dont_use_list);
    ABC_FREE(pTargets);
    for ( int i = 0; i < argc - globalUtilOptind; ++i ) ABC_FREE(pTextPaths[i]);
    ABC_FREE(pTextPaths);
    Abc_Print( 1, "Bound SN library: %u cells; target uses %d genlib outputs (%s).\n",
               pBundle->cell_count, Mio_LibraryReadGateNum(pMio), fMulti ? "twins enabled" : "single-output" );
    return 0;
failed:
    ABC_FREE(DontUse.dont_use_list);
    ABC_FREE(pTargets);
    if ( pTextPaths )
        for ( int i = 0; i < argc - globalUtilOptind; ++i ) ABC_FREE(pTextPaths[i]);
    ABC_FREE(pTextPaths);
    Sn_MioBindingsFree(pBindings);
    sn_lib_destroy(pModel);
    sn_library_release(pAddition);
    sn_library_release(pBundle);
    if ( pScl ) Abc_SclLibFree(pScl);
    if ( pMio ) Mio_LibraryDelete(pMio);
    if ( pAmap ) Amap_LibFree(pAmap);
    Abc_Print( -1, "Cannot @read_lib: library preparation or checked binding failed; existing state is unchanged.\n" );
    return 1;
usage:
    Abc_Print( -2, "usage: @read_lib [-m] <file.lib|file.snlib> [file.lib|file.snlib ...]\n" );
    Abc_Print( -2, "\tloads and checks a single-output mapping target, retaining parser-order SN cell IDs\n" );
    Abc_Print( -2, "\t-m enables two-output mapping cells with checked physical pin correspondence\n" );
    Abc_Print( -2, "\tbinary targets require their recorded text source with matching byte size and hash\n" );
    return 1;
}

static Abc_Ntk_t * Sn_MapCellPartition( void * pContext, sn_module_id_t Module, const char * pName, Mini_Aig_t * pMini )
{
    extern Gia_Man_t * Gia_ManFromMiniAig( Mini_Aig_t *, Vec_Int_t **, int );
    extern void Nf_ManSetDefaultPars( Jf_Par_t * );
    extern Gia_Man_t * Nf_ManPerformMapping( Gia_Man_t *, Jf_Par_t * );
    extern Abc_Ntk_t * Abc_NtkFromCellMappedGia( Gia_Man_t *, int );
    Gia_Man_t * pGia = Gia_ManFromMiniAig(pMini, NULL, 0), * pMapped;
    Abc_Ntk_t * pNtk = NULL;
    Jf_Par_t Pars;
    char Name[64];
    FILE * pProgress = (FILE *)pContext;
    abctime Started = Abc_Clock();
    if ( pProgress )
    {
        fprintf(pProgress, "@map_cell module %u %s: %d ANDs, %d inputs, %d outputs\n",
                Module, pName, Mini_AigAndNum(pMini), Mini_AigPiNum(pMini), Mini_AigPoNum(pMini));
        fflush(pProgress);
    }
    if ( !pGia ) return NULL;
    pGia->vNamesIn = Vec_PtrAlloc(Gia_ManCiNum(pGia));
    pGia->vNamesOut = Vec_PtrAlloc(Gia_ManCoNum(pGia));
    for ( int i = 0; i < Gia_ManCiNum(pGia); ++i )
    {
        sn_map_cell_port_name(Name, sizeof(Name), false, i);
        Vec_PtrPush(pGia->vNamesIn, Abc_UtilStrsav(Name));
    }
    for ( int i = 0; i < Gia_ManCoNum(pGia); ++i )
    {
        sn_map_cell_port_name(Name, sizeof(Name), true, i);
        Vec_PtrPush(pGia->vNamesOut, Abc_UtilStrsav(Name));
    }
    Nf_ManSetDefaultPars(&Pars);
    pMapped = Nf_ManPerformMapping(pGia, &Pars);
    if ( pMapped && Gia_ManHasCellMapping(pMapped) )
    {
        pNtk = Abc_NtkFromCellMappedGia(pMapped, 0);
        // The raw GIA-to-network adapter creates dummy names; &put normally
        // performs this transfer. Check the mapper's retained interface first.
        if ( pNtk && pMapped->vNamesIn && pMapped->vNamesOut &&
             Vec_PtrSize(pMapped->vNamesIn) == Abc_NtkCiNum(pNtk) &&
             Vec_PtrSize(pMapped->vNamesOut) == Abc_NtkCoNum(pNtk) )
        {
            Abc_Obj_t * pPort;
            int i;
            Abc_NtkForEachCi(pNtk, pPort, i)
            {
                Nm_ManDeleteIdName(pNtk->pManName, Abc_ObjId(pPort));
                Abc_ObjAssignName(pPort, (char *)Vec_PtrEntry(pMapped->vNamesIn, i), NULL);
            }
            Abc_NtkForEachCo(pNtk, pPort, i)
            {
                Nm_ManDeleteIdName(pNtk->pManName, Abc_ObjId(pPort));
                Abc_ObjAssignName(pPort, (char *)Vec_PtrEntry(pMapped->vNamesOut, i), NULL);
            }
        }
    }
    if ( pMapped && pMapped != pGia ) Gia_ManStop(pMapped);
    Gia_ManStop(pGia);
    if ( pProgress )
    {
        fprintf(pProgress, "@map_cell module %u mapper %s in %.2f s\n", Module, pNtk ? "finished" : "failed",
                (double)(Abc_Clock() - Started) / CLOCKS_PER_SEC);
        fflush(pProgress);
    }
    return pNtk;
}

static int Sn_CommandMapCell( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Sn_Man_t * p, * pWork;
    Sn_MioBindings_t * pBindings;
    sn_map_cell_stats_t Stats;
    const char * pReason = NULL;
    int c, fVerbose = 0;
    abctime Started;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "vh")) != EOF )
        if (c == 'v') fVerbose ^= 1;
        else goto usage;
    if ( argc != globalUtilOptind ) goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) ) return 1;
    p = Sn_AbcGetMan(pAbc);
    if ( !p->pDesign->library || !p->TargetModels.size || !p->TargetGenlibSignature ||
         p->TargetGenlibSignature != Sn_GenlibSignature((Mio_Library_t *)Abc_FrameReadLibGen()) )
    {
        Abc_Print(-1, "@map_cell requires a checked @read_lib mapping target.\n");
        return 1;
    }
    pBindings = Sn_MioBindingsStart(p->pDesign->library, (Mio_Library_t *)Abc_FrameReadLibGen());
    if ( !pBindings ) return 1;
    Sn_MioBindingsFree(pBindings);
    pWork = Sn_ManDup(p);
    if ( !pWork ) return 1;
    Started = Abc_Clock();
    if ( !sn_design_map_cell_hierarchy(pWork->pDesign, pWork->Top, (Mio_Library_t *)Abc_FrameReadLibGen(),
            Sn_MapCellPartition, fVerbose ? pAbc->Out : NULL, &Stats, &pReason) || !sn_design_check(pWork->pDesign, pAbc->Err, false) )
    {
        Abc_Print(-1, "@map_cell refused in module %u: %s; SN and ABC workspaces are unchanged.\n",
                  Stats.failed_module, pReason ? pReason : "invalid reconstruction");
        Sn_ManFree(pWork);
        return 1;
    }
    Sn_ManAdvanceRevision(pWork);
    Sn_AbcUpdateMan(pAbc, pWork);
    Abc_Print(1, "Cell hierarchy: %u mapped definitions, %u primitives, %u empty; %llu input ANDs, "
                "%llu cell owners. Time = %.2f s.\n", Stats.mapped_modules, Stats.primitive_modules,
                Stats.empty_modules, (unsigned long long)Stats.input_ands,
                (unsigned long long)Stats.output_cells, (double)(Abc_Clock() - Started) / CLOCKS_PER_SEC);
    return 0;
usage:
    Abc_Print(-2, "usage: @map_cell [-vh]\n"
                 "  Maps each reachable module definition with nf, preserving hierarchy and state/macro cuts.\n"
                 "  Serial in-process mapping; requires @read_lib; leaves ABC workspaces unchanged.\n"
                 "  -v prints progress and mapper runtime for each definition.\n");
    return 1;
}

static uint32_t Sn_GateIdResolver( void * pContext, const char * pGateName )
{
    Mio_Library_t * pLibrary = (Mio_Library_t *)pContext;
    Mio_Gate_t * pGate = Mio_LibraryReadGateByName( pLibrary, (char *)pGateName, NULL );
    int GateId;
    if ( pGate == NULL )
        return SN_INVALID_ID;
    GateId = Mio_GateReadCell( pGate );
    return GateId >= 0 ? (uint32_t)GateId : SN_INVALID_ID;
}

static int Sn_BoundaryHasGenericMemories( const sn_blast_boundary_t * pBoundary )
{
    size_t i;
    for ( i = 0; i < pBoundary->cis.size; i++ )
    {
        sn_blast_boundary_kind_t Kind = sn_vec_at(sn_blast_boundary_bit_t, &pBoundary->cis, i).kind;
        if ( Kind == SN_BLAST_BOUNDARY_MEMORY_OUTPUT )
            return 1;
    }
    for ( i = 0; i < pBoundary->cos.size; i++ )
    {
        sn_blast_boundary_kind_t Kind = sn_vec_at(sn_blast_boundary_bit_t, &pBoundary->cos, i).kind;
        if ( Kind == SN_BLAST_BOUNDARY_MEMORY_INPUT )
            return 1;
    }
    return 0;
}

static int Sn_CommandPut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern Abc_Ntk_t * Abc_NtkFromCellMappedGia( Gia_Man_t * pGia, int fUseBuffs );
    extern Vec_Int_t * Abc_NtkWriteMiniMapping( Abc_Ntk_t * pNtk );
    Sn_Man_t * p;
    Gia_Man_t * pGia;
    sn_module_id_t Top;
    const char * pPutStatus;
    int c, fVerbose = 0, fNtk = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "nvh")) != EOF )
    {
        switch ( c )
        {
        case 'n':
            fNtk ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( argc != globalUtilOptind )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    p = Sn_AbcGetMan( pAbc );
    pGia = Abc_FrameReadGia( pAbc );
    pPutStatus = fNtk ? Sn_ManPutNtkStatus(p, Abc_FrameReadNtk(pAbc)) : Sn_ManPutStatus(p, pGia);
    if ( strcmp(pPutStatus, "compatible") != 0 )
    {
        Abc_Print( -1, "Cannot @put: %s.\n", pPutStatus );
        return 1;
    }

    if ( fNtk )
    {
        sn_design_t * pWork = sn_design_dup(p->pDesign);
        const char * pReason = NULL;
        char Name[64];
        unsigned Suffix = (unsigned)pWork->modules.size;
        do { snprintf(Name, sizeof(Name), "sn_network_mapped_%u", Suffix++); }
        while ( sn_design_find_module(pWork, Name) != SN_INVALID_ID );
        Top = sn_design_add_mapped_network(pWork, p->BlastModule, Abc_FrameReadNtk(pAbc),
            (Mio_Library_t *)Abc_FrameReadLibGen(), &p->Boundary, Name, &pReason);
        if ( Top == SN_INVALID_ID || !sn_design_check(pWork, pAbc->Err, false) )
        {
            Abc_Print(-1, "Cannot @put -n: %s.\n", pReason ? pReason : "reconstructed design is invalid");
            sn_design_destroy(pWork);
            return 1;
        }
        sn_design_destroy(p->pDesign);
        p->pDesign = pWork;
        if ( fVerbose )
            Abc_Print(1, "Inserted mapped main network: physical cells = %u.\n",
                (unsigned)sn_design_get_module(pWork, Top)->type_objects[SN_GATE].size);
    }
    else if ( Gia_ManHasCellMapping(pGia) )
    {
        Mio_Library_t * pLibrary = (Mio_Library_t *)Abc_FrameReadLibGen();
        Abc_Ntk_t * pNtk;
        Vec_Int_t * vMapping = NULL;
        if ( pLibrary == NULL )
        {
            Abc_Print( -1, "The cell-mapped GIA has no current genlib library.\n" );
            return 1;
        }
        pNtk = Abc_NtkFromCellMappedGia( pGia, 0 );
        if ( !pNtk )
            return 1;
        if ( p->pDesign->library )
        {
            sn_design_t * pWork = sn_design_dup(p->pDesign);
            char TemporaryName[64];
            uint32_t Suffix = (uint32_t)pWork->modules.size;
            do { snprintf(TemporaryName, sizeof(TemporaryName), "sn_gate_mapped_%u", Suffix++); }
            while ( sn_design_find_module(pWork, TemporaryName) != SN_INVALID_ID );
            const char * pReason = NULL;
            Top = sn_design_add_mapped_network(pWork, p->BlastModule, pNtk, pLibrary,
                &p->Boundary, TemporaryName, &pReason);
            if ( Top == SN_INVALID_ID )
                Abc_Print(-1, "Cannot reconstruct mapped cells: %s.\n", pReason);
            if ( Top == SN_INVALID_ID || !sn_design_check(pWork, pAbc->Err, false) )
            {
                sn_design_destroy(pWork);
                Top = SN_INVALID_ID;
            }
            else
            {
                sn_design_destroy(p->pDesign);
                p->pDesign = pWork;
            }
        }
        else
        {
            vMapping = Abc_NtkWriteMiniMapping(pNtk);
            if ( !vMapping )
            {
                Abc_NtkDelete(pNtk);
                return 1;
            }
            Top = sn_design_add_gate_module( p->pDesign, p->BlastModule, Vec_IntArray(vMapping),
                                             (size_t)Vec_IntSize(vMapping), &p->Boundary, Sn_GateIdResolver,
                                             pLibrary, "__sn_gate_mapped" );
        }
        if ( Top == SN_INVALID_ID )
        {
            Abc_Print( -1, "Cannot @put: the current genlib does not contain every gate used by the mapped GIA.\n" );
            if ( vMapping ) Vec_IntFree( vMapping );
            Abc_NtkDelete( pNtk );
            return 1;
        }
        if ( fVerbose )
            Abc_Print( 1, "Inserted cell-mapped logic: gates = %u.\n",
                (unsigned)sn_design_get_module(p->pDesign, Top)->type_objects[SN_GATE].size );
        if ( vMapping ) Vec_IntFree( vMapping );
        Abc_NtkDelete( pNtk );
    }
    else if ( Gia_ManHasMapping(pGia) )
    {
        Mini_Lut_t * pLut = (Mini_Lut_t *)Abc_FrameGiaOutputMiniLut( pAbc );
        sn_lut_stats_t Stats;
        if ( pLut == NULL )
        {
            Abc_Print( -1, "Cannot extract the mapped MiniLUT network.\n" );
            return 1;
        }
        Stats = sn_lut_analyze( pLut, &p->Boundary );
        Top = sn_design_add_lut_module( p->pDesign, p->BlastModule, pLut, &p->Boundary, "__sn_lut_mapped" );
        Mini_LutStop( pLut );
        if ( fVerbose )
            Abc_Print( 1, "Inserted LUT-mapped logic: LUTs = %u  LUT size = %u  levels = %u.\n",
                       Stats.lut_count, Stats.lut_size, Stats.lut_levels );
    }
    else
    {
        Mini_Aig_t * pAig = (Mini_Aig_t *)Abc_FrameGiaOutputMiniAig( pAbc );
        assert( pAig != NULL );
        Top = sn_design_add_aig_module( p->pDesign, p->BlastModule, pAig, &p->Boundary, "__sn_aig_inserted" );
        if ( fVerbose )
            Abc_Print( 1, "Inserted unmapped logic: ANDs = %d.\n", Mini_AigAndNum(pAig) );
        Mini_AigStop( pAig );
    }
    Sn_ManReplaceBlastedModule( p, Top );
    Sn_ManAdvanceRevision( p );
    assert( sn_design_is_topo(p->pDesign) );
    return 0;

usage:
    Abc_Print( -2, "usage: @put [-nvh]\n" );
    Abc_Print( -2, "\t         inserts the current &-space GIA into the SN design after @blast\n" );
    Abc_Print( -2, "\t-v      : print reconstruction statistics\n" );
    Abc_Print( -2, "\t-n      : select the checked mapped main network instead of the &-space GIA\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static char * Sn_SourceCommand( const char * pFileName )
{
    Vec_Str_t * vCommand;
    FILE * pFile = fopen( pFileName, "r" );
    if ( pFile == NULL )
        return NULL;
    if ( fclose(pFile) != 0 )
        return NULL;
    vCommand = Vec_StrAlloc( (int)strlen(pFileName) + 16 );
    Vec_StrPrintStr( vCommand, "source -s " );
    Vec_StrPrintStr( vCommand, pFileName );
    Vec_StrPush( vCommand, '\0' );
    return Vec_StrReleaseArray( vCommand );
}

typedef struct Sn_MapLutContext_t_
{
    Abc_Frame_t * pAbc;
    const char *  pScript;
    const char *  pExecutable;
    const char *  pExtractPrefix;
    unsigned      nProcesses;
    int           fVerbose;
} Sn_MapLutContext_t;

static int Sn_MapLutExtractName( char * pFileName, size_t nFileName, const char * pPrefix,
                                 unsigned Module, const char * pName, const char * pSuffix )
{
    size_t Pos, NameLength, SuffixLength;
    int Written = snprintf( pFileName, nFileName, "%s_%04u_", pPrefix, Module );
    if ( Written < 0 || (size_t)Written >= nFileName )
        return 0;
    Pos = (size_t)Written;
    NameLength = strlen( pName );
    SuffixLength = strlen( pSuffix );
    if ( NameLength > nFileName - Pos - 1 || SuffixLength > nFileName - Pos - NameLength - 1 )
        return 0;
    while ( *pName )
    {
        unsigned char Char = (unsigned char)*pName++;
        pFileName[Pos++] = (char)(isalnum(Char) || Char == '_' || Char == '-' ? Char : '_');
    }
    memcpy( pFileName + Pos, pSuffix, SuffixLength + 1 );
    return 1;
}

static int Sn_MapLutExecutable( char * pBuffer, size_t nBuffer )
{
    if ( pBuffer == NULL || nBuffer < 2 || nBuffer > UINT32_MAX )
        return 0;
#if defined(_MSC_VER) || defined(__MINGW32__)
    DWORD Length = GetModuleFileNameA( NULL, pBuffer, (DWORD)nBuffer );
    return Length > 0 && Length < nBuffer;
#elif defined(__APPLE__)
    uint32_t Size = (uint32_t)nBuffer;
    return _NSGetExecutablePath( pBuffer, &Size ) == 0;
#else
    // readlink does not terminate its result. Give it the full capacity so an
    // exact-capacity result is detected as truncation, not accepted as a path.
    ssize_t Length = readlink( "/proc/self/exe", pBuffer, nBuffer );
    if ( Length <= 0 || (size_t)Length >= nBuffer )
        return 0;
    pBuffer[Length] = '\0';
    return 1;
#endif
}

static int Sn_MapLutRunProcess( const char * pExecutable, const char * pCommand )
{
#if defined(_MSC_VER) || defined(__MINGW32__)
    const char * pArgs[] = {pExecutable, "-q", pCommand, NULL};
    return (int)_spawnv( _P_WAIT, pExecutable, pArgs );
#else
    pid_t Child = fork();
    int Status;
    if ( Child < 0 )
        return -1;
    if ( Child == 0 )
    {
        int Null = open( "/dev/null", O_WRONLY );
        if ( Null >= 0 )
        {
            dup2( Null, STDOUT_FILENO );
            dup2( Null, STDERR_FILENO );
            close( Null );
        }
        execl( pExecutable, pExecutable, "-q", pCommand, (char *)NULL );
        _exit( 127 );
    }
    if ( waitpid(Child, &Status, 0) != Child )
        return -1;
    return WIFEXITED(Status) ? WEXITSTATUS(Status) : -1;
#endif
}

// ABC-specific callback for the reusable snMapLut.h harness. The harness owns the input MiniAIG and returned MiniLUT.
static Mini_Lut_t * Sn_MapLutPartitionInt( void * pArg, sn_module_id_t Module, const char * pName,
                                           Mini_Aig_t * pAig, const sn_blast_boundary_t * pBoundary )
{
    Sn_MapLutContext_t * p = (Sn_MapLutContext_t *)pArg;
    Gia_Man_t * pGia;
    Mini_Lut_t * pLut;
    sn_lut_stats_t Stats;
    abctime clk = Abc_Clock();
    int nInputs = Mini_AigPiNum( pAig );
    int nOutputs = Mini_AigPoNum( pAig );
    int nAnds = Mini_AigAndNum( pAig );
    if ( p->pExtractPrefix )
    {
        char AigFile[1024], InfoFile[1024];
        FILE * pFile;
        if ( !Sn_MapLutExtractName(AigFile, sizeof(AigFile), p->pExtractPrefix, Module, pName, ".aig") ||
             !Sn_MapLutExtractName(InfoFile, sizeof(InfoFile), p->pExtractPrefix, Module, pName, ".txt") )
        {
            Abc_Print( -1, "Cannot extract module \"%s\": the -E output name is too long.\n", pName );
            return NULL;
        }
        pFile = fopen( AigFile, "wb" );
        if ( pFile == NULL )
            return NULL;
        fclose( pFile );
        Mini_AigerWrite( AigFile, pAig, 0 );
        pFile = fopen( InfoFile, "w" );
        if ( pFile == NULL )
            return NULL;
        fprintf( pFile, "module_id\t%u\nmodule_name\t%s\ninputs\t%d\noutputs\t%d\nands\t%d\n",
                 Module, pName, nInputs, nOutputs, nAnds );
        fprintf( pFile, "boundary_inputs\t%zu\nboundary_outputs\t%zu\n",
                 pBoundary->cis.size, pBoundary->cos.size );
        fclose( pFile );
        if ( p->fVerbose )
            Abc_Print( 1, "@map_lut: extracted %-24s %7d ANDs  %d inputs  %d outputs  time = %.2f s.\n",
                       pName, nAnds, nInputs, nOutputs, (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC );
        return Mini_LutStart( 2 );
    }
    if ( p->nProcesses > 1 )
    {
        char Prefix[512], Command[4096];
        char * pAigFile = NULL, * pLutFile = NULL;
        int AigFd = -1, LutFd = -1;
        if ( !Sn_TempPrefix(Prefix, sizeof(Prefix), "sn_map_lut_") ||
             (AigFd = tmpFile(Prefix, ".aig", &pAigFile)) < 0 ||
             (LutFd = tmpFile(Prefix, ".lut", &pLutFile)) < 0 )
        {
#if defined(_MSC_VER) || defined(__MINGW32__)
            if ( AigFd >= 0 )
                _close( AigFd );
#else
            if ( AigFd >= 0 )
                close( AigFd );
#endif
            if ( pAigFile )
            {
                remove( pAigFile );
                ABC_FREE( pAigFile );
            }
            return NULL;
        }
#if defined(_MSC_VER) || defined(__MINGW32__)
        _close( AigFd );
        _close( LutFd );
#else
        close( AigFd );
        close( LutFd );
#endif
        Mini_AigerWrite( pAigFile, pAig, 0 );
        if ( snprintf(Command, sizeof(Command), "&read \"%s\"; %s; &write -l \"%s\"", pAigFile, p->pScript,
                      pLutFile) >=
             (int)sizeof(Command) || Sn_MapLutRunProcess(p->pExecutable, Command) != 0 )
        {
            remove( pAigFile );
            remove( pLutFile );
            ABC_FREE( pAigFile );
            ABC_FREE( pLutFile );
            return NULL;
        }
        pLut = sn_lut_load( pLutFile );
        remove( pAigFile );
        remove( pLutFile );
        ABC_FREE( pAigFile );
        ABC_FREE( pLutFile );
        if ( pLut == NULL || !sn_lut_interface_matches(pLut, pBoundary) )
        {
            if ( pLut )
                Mini_LutStop( pLut );
            return NULL;
        }
        Stats = sn_lut_analyze( pLut, pBoundary );
        if ( p->fVerbose )
            Abc_Print( 1, "@map_lut: %-24s %7d ANDs -> %7u LUTs  level = %u  time = %.2f s.\n",
                       pName, nAnds, Stats.lut_count, Stats.lut_levels,
                       (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC );
        return pLut;
    }
    Abc_FrameGiaInputMiniAig( p->pAbc, pAig );
    if ( Cmd_CommandExecute(p->pAbc, p->pScript) )
    {
        Abc_Print( -1, "ABC script failed while mapping module \"%s\".\n", pName );
        return NULL;
    }
    pGia = Abc_FrameReadGia( p->pAbc );
    if ( pGia == NULL || Gia_ManCiNum(pGia) != nInputs || Gia_ManCoNum(pGia) != nOutputs )
    {
        Abc_Print( -1, "ABC script changed the interface of module \"%s\" (%d/%d inputs, %d/%d outputs).\n",
                   pName, pGia ? Gia_ManCiNum(pGia) : -1, nInputs, pGia ? Gia_ManCoNum(pGia) : -1, nOutputs );
        return NULL;
    }
    if ( !Gia_ManHasMapping(pGia) )
    {
        Abc_Print( -1, "ABC script did not leave a LUT-mapped GIA while mapping module \"%s\".\n", pName );
        return NULL;
    }
    pLut = (Mini_Lut_t *)Abc_FrameGiaOutputMiniLut( p->pAbc );
    if ( pLut == NULL )
    {
        Abc_Print( -1, "Cannot extract the LUT-mapped network for module \"%s\".\n", pName );
        return NULL;
    }
    Stats = sn_lut_analyze( pLut, pBoundary );
    if ( p->fVerbose )
        Abc_Print( 1, "@map_lut: %-24s %7d ANDs -> %7u LUTs  level = %u  time = %.2f s.\n",
                   pName, nAnds, Stats.lut_count, Stats.lut_levels, (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC );
    return pLut;
}

static Mini_Lut_t * Sn_MapLutPartition( void * pArg, sn_module_id_t Module, const char * pName,
                                        Mini_Aig_t * pAig, const sn_blast_boundary_t * pBoundary )
{
    Sn_MapLutContext_t * p = (Sn_MapLutContext_t *)pArg;
    Abc_Frame_t * pPrevious = Abc_FrameEnter( p->pAbc );
    Mini_Lut_t * pLut = Sn_MapLutPartitionInt( pArg, Module, pName, pAig, pBoundary );
    Abc_FrameLeave( pPrevious );
    return pLut;
}

// Like Yosys's ABC integration, @map_lut uses natural module boundaries rather than graph partitioning. Each reachable
// non-primitive module is combinationally extracted, processed independently by the requested ABC script, and inserted
// back at the same module ID. The command works on a duplicate and commits it only after every partition succeeds.
static int Sn_CommandMapLut( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    static const char * pDefaultScript = "&resyn3; &if -m -K 6";
    Sn_Man_t * p, * pWork;
    const char * pScriptArg = NULL;
    const char * pScriptFile = NULL;
    const char * pModuleName = NULL;
    const char * pExtractPrefix = NULL;
    char * pFileScript = NULL;
    const char * pScript;
    char Executable[1024];
    sn_module_id_t Root;
    sn_map_lut_stats_t Stats;
    Sn_MapLutContext_t Context;
    abctime clk;
    int c, fVerbose = 0, nProcesses = 1;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "MSFPEvh")) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
                goto usage;
            pModuleName = argv[globalUtilOptind++];
            break;
        case 'S':
            if ( globalUtilOptind >= argc )
                goto usage;
            pScriptArg = argv[globalUtilOptind++];
            break;
        case 'F':
            if ( globalUtilOptind >= argc )
                goto usage;
            pScriptFile = argv[globalUtilOptind++];
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
                goto usage;
            nProcesses = atoi( argv[globalUtilOptind++] );
            if ( nProcesses < 1 || nProcesses > 100 )
                goto usage;
            break;
        case 'E':
            if ( globalUtilOptind >= argc )
                goto usage;
            pExtractPrefix = argv[globalUtilOptind++];
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( argc != globalUtilOptind || (pScriptArg && pScriptFile) ||
         (pExtractPrefix && (pScriptArg || pScriptFile || nProcesses != 1)) )
        goto usage;
    if ( nProcesses > 1 && !sn_pth_parallel_available() )
    {
        Abc_Print( -1, "Cannot use @map_lut -P %d: parallel SN mapping is unavailable in this build; use -P 1.\n",
                   nProcesses );
        return 1;
    }
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    p = Sn_AbcGetMan( pAbc );
    Root = pModuleName ? sn_design_find_module( p->pDesign, pModuleName ) : p->Top;
    if ( Root == SN_INVALID_ID )
    {
        Abc_Print( -1, "Cannot find module \"%s\" in the current SN design.\n", pModuleName );
        return 1;
    }
    if ( Sn_CommandRejectLatches(p->pDesign, Root, "@map_lut") )
        return 1;
    if ( pScriptFile )
    {
        pFileScript = Sn_SourceCommand( pScriptFile );
        if ( pFileScript == NULL )
        {
            Abc_Print( -1, "Cannot read ABC script file \"%s\".\n", pScriptFile );
            return 1;
        }
    }
    pScript = pScriptArg ? pScriptArg : pFileScript ? pFileScript : pDefaultScript;
    pWork = Sn_ManDup( p );
    if ( pWork == NULL )
    {
        Abc_Print( -1, "Cannot duplicate the current SN design.\n" );
        ABC_FREE( pFileScript );
        return 1;
    }
    Context.pAbc = pAbc;
    Context.pScript = pScript;
    Context.pExecutable = NULL;
    Context.pExtractPrefix = pExtractPrefix;
    Context.nProcesses = (unsigned)nProcesses;
    Context.fVerbose = fVerbose;
    if ( nProcesses > 1 )
    {
        if ( !Sn_MapLutExecutable(Executable, sizeof(Executable)) )
        {
            Abc_Print( -1, "Cannot determine the current ABC executable path.\n" );
            ABC_FREE( pFileScript );
            Sn_ManFree( pWork );
            return 1;
        }
        Context.pExecutable = Executable;
    }
    clk = Abc_Clock();
    if ( !sn_design_map_lut_hierarchy(pWork->pDesign, Root, Sn_MapLutPartition, &Context,
                                       (unsigned)nProcesses, pExtractPrefix != NULL, &Stats) )
    {
        if ( Stats.failed_module != SN_INVALID_ID )
        {
            const sn_module_t * pFailed = sn_design_get_module_const( pWork->pDesign, Stats.failed_module );
            Abc_Print( -1, "LUT mapping failed for module \"%s\".\n",
                       sn_name_get(&pWork->pDesign->names, pFailed->name) );
        }
        ABC_FREE( pFileScript );
        Sn_ManFree( pWork );
        return 1;
    }
    ABC_FREE( pFileScript );
    if ( pExtractPrefix )
    {
        Sn_ManFree( pWork );
        Abc_Print( 1, "Extracted %u module partitions (%llu input ANDs); skipped %u trivial, %u primitive, and %u "
                       "generic-memory modules.  Time = %.2f s.\n", Stats.mapped_modules,
                   (unsigned long long)Stats.input_ands, Stats.trivial_modules, Stats.primitive_modules,
                   Stats.generic_memory_modules, (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC );
        return 0;
    }
    Sn_ManAdvanceRevision( pWork );
    Sn_AbcUpdateMan( pAbc, pWork );
    Abc_Print( 1, "Mapped %u module partitions into %llu LUTs; skipped %u trivial, %u primitive, and %u generic-memory "
                   "modules.  "
                   "Time = %.2f s.\n", Stats.mapped_modules, (unsigned long long)Stats.output_luts,
               Stats.trivial_modules, Stats.primitive_modules, Stats.generic_memory_modules,
               (double)(Abc_Clock() - clk) / CLOCKS_PER_SEC );
    return 0;

usage:
    Abc_Print( -2, "usage: @map_lut [-M module] [-S \"commands\" | -F script] [-P num] [-E prefix] [-vh]\n" );
    Abc_Print( -2, "\t         maps each natural hierarchy partition independently and preserves the hierarchy\n" );
    Abc_Print( -2, "\t-M name : map modules reachable from this root [default = current top]\n" );
    Abc_Print( -2, "\t-S cmds : ABC commands applied to each partition [default = &resyn3; &if -m -K 6]\n" );
    Abc_Print( -2, "\t-F file : read the per-partition ABC commands from a file\n" );
    Abc_Print( -2, "\t-P num  : use num processes; P>1 requires pthreads and a non-Windows build [default = 1]\n" );
    Abc_Print( -2, "\t          P=1 leaves the last processed partition in &-space\n" );
    Abc_Print( -2, "\t-E pref : extract partition AIGs as pref_<id>_<module>.aig and stop before synthesis\n" );
    Abc_Print( -2, "\t-v      : print per-module mapping statistics\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static int Sn_CommandWrite( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Sn_Man_t * p;
    char * pFileName;
    FILE * pFile;
    int c, Status = 0, fNames = 0;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "nh")) != EOF )
        if ( c == 'n' )
            fNames ^= 1;
        else
            goto usage;
    if ( argc - globalUtilOptind != 1 )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    p = Sn_AbcGetMan( pAbc );
    pFileName = argv[globalUtilOptind];
    if ( Sn_FileHasSuffix(pFileName, ".sn") )
    {
        if ( fNames )
            goto usage;
        pFile = fopen( pFileName, "wb" );
        if ( pFile == NULL )
        {
            Abc_Print( -1, "Cannot open output file \"%s\".\n", pFileName );
            return 1;
        }
        Status = sn_design_write_binary( pFile, p->pDesign ) ? 0 : 1;
    }
    else if ( Sn_FileHasSuffix(pFileName, ".v") || Sn_FileHasSuffix(pFileName, ".sv") )
    {
        pFile = fopen( pFileName, "w" );
        if ( pFile == NULL )
        {
            Abc_Print( -1, "Cannot open output file \"%s\".\n", pFileName );
            return 1;
        }
        sn_design_write_module_verilog_with_deps_named(
            pFile, p->pDesign, p->Top, sn_name_get(&p->pDesign->names, p->Name), fNames != 0 );
        Status = ferror( pFile ) != 0;
    }
    else
    {
        Abc_Print( -1, "Output file \"%s\" should have extension .sn, .v, or .sv.\n", pFileName );
        return 1;
    }
    if ( fclose(pFile) != 0 )
        Status = 1;
    if ( Status )
    {
        remove( pFileName );
        Abc_Print( -1, "Cannot finish writing output file \"%s\".\n", pFileName );
        return 1;
    }
    return 0;

usage:
    Abc_Print( -2, "usage: @write [-nh] <file.sn|file.v|file.sv>\n" );
    Abc_Print( -2, "\t         writes the current SN design according to the file extension\n" );
    Abc_Print( -2, "\t-n      : preserve unique signal and instance names in Verilog; escape or safely rename collisions\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static int Sn_CommandPs( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Sn_Man_t * p;
    const sn_module_t * pReport;
    sn_design_mem_usage_t Mem;
    char * pModuleName = NULL;
    sn_module_id_t Report;
    size_t nObjects = 0;
    size_t i;
    int c, fDistrib = 0, fVerbose = 0, fArea = 0, fMem, fLut, fGate;
    char UsedMemory[32], AllocatedMemory[32];
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "Madvh")) != EOF )
    {
        switch ( c )
        {
        case 'M':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-M\" should be followed by a module name.\n" );
                goto usage;
            }
            pModuleName = argv[globalUtilOptind++];
            break;
        case 'd':
            fDistrib ^= 1;
            break;
        case 'a':
            fArea ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
        default:
            goto usage;
        }
    }
    if ( argc != globalUtilOptind )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    p = Sn_AbcGetMan( pAbc );
    Report = pModuleName ? sn_design_find_module( p->pDesign, pModuleName ) : p->Top;
    if ( Report == SN_INVALID_ID )
    {
        Abc_Print( -1, "Cannot find module \"%s\" in the current SN design.\n", pModuleName );
        return 1;
    }
    pReport = sn_design_get_module_const( p->pDesign, Report );
    for ( i = 0; i < p->pDesign->modules.size; i++ )
        nObjects += sn_design_get_module_const( p->pDesign, (sn_module_id_t)i )->obj_types.size;
    sn_design_get_mem_usage( p->pDesign, &Mem );
    fMem = Sn_DesignHasType( p->pDesign, SN_MEM_OUT );
    fLut = Sn_DesignHasType( p->pDesign, SN_LUT );
    fGate = Sn_DesignHasType( p->pDesign, SN_GATE );
    Sn_FormatMemory( Mem.total.used_bytes, UsedMemory, sizeof(UsedMemory) );
    Sn_FormatMemory( Mem.total.allocated_bytes, AllocatedMemory, sizeof(AllocatedMemory) );
    fprintf( pAbc->Out, "SN design: top = %s  modules = %zu  objects = %zu  memory = %s/%s "
                        "(used/allocated)\n",
             sn_name_get(&p->pDesign->names, pReport->name), p->pDesign->modules.size, nObjects,
             UsedMemory, AllocatedMemory );
    if ( p->pDesign->library )
    {
        sn_library_t * pLibrary = p->pDesign->library;
        fprintf( pAbc->Out, "Library: %u files, %u cells, %llu parser warnings; shared parsed library and expression storage excluded from SN memory totals.\n",
                 pLibrary->model_count, pLibrary->cell_count, (unsigned long long)sn_library_warning_count(pLibrary) );
        if ( pLibrary->compiled )
            fprintf( pAbc->Out, "Library compilation: %u cells unsupported for blasting.\n", pLibrary->unsupported_count );
    }
    if ( pModuleName )
        Sn_ModulePrintStats( pAbc->Out, pReport, fMem, fLut, fGate );
    else
    {
        fprintf( pAbc->Out, "Modules:\n" );
        for ( i = 0; i < p->pDesign->modules.size; i++ )
            Sn_ModulePrintStats( pAbc->Out, sn_design_get_module_const(p->pDesign, (sn_module_id_t)i),
                                 fMem, fLut, fGate );
    }
    if ( fVerbose )
    {
        fprintf( pAbc->Out, "Hierarchy:\n" );
        sn_design_print_hierarchy( pAbc->Out, p->pDesign, Report );
    }
    if ( fDistrib )
    {
        Sn_DesignPrintBlackboxes( pAbc->Out, p->pDesign, Report );
        Sn_DesignPrintDistrib( pAbc->Out, p->pDesign, Report );
    }
    if ( fArea && !Sn_DesignPrintCellArea(pAbc->Out, p->pDesign, Report) )
        return 1;
    return 0;

usage:
    Abc_Print( -2, "usage: @ps [-M module] [-advh]\n" );
    Abc_Print( -2, "\t         prints statistics for the current SN design\n" );
    Abc_Print( -2, "\t-M name : select one module and its hierarchy [default = print all module definitions]\n" );
    Abc_Print( -2, "\t-d      : print object-type and width distribution for the elaborated hierarchy\n" );
    Abc_Print( -2, "\t-a      : print physical cell counts, histogram and Liberty area (no SCL required)\n" );
    Abc_Print( -2, "\t-v      : print the hierarchy rooted at the selected module\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

static const char * Sn_BlastModeName( int Mode )
{
    if ( Mode == SN_BLAST_COMB )
        return "combinational";
    if ( Mode == SN_BLAST_TRANSITION )
        return "transition";
    return "sequential";
}

static int Sn_ManHasUserHierarchy( const Sn_Man_t * p )
{
    const sn_module_t * pTop = sn_design_get_module_const( p->pDesign, p->Top );
    size_t i;
    for ( i = 0; i < pTop->type_objects[SN_INST].size; i++ )
    {
        sn_obj_id_t Inst = sn_vec_at( sn_obj_id_t, &pTop->type_objects[SN_INST], i );
        const sn_module_t * pChild = sn_design_get_module_const( p->pDesign, sn_inst_module_id(pTop, Inst) );
        if ( !sn_module_is_technology_primitive(pChild) )
            return 1;
    }
    return 0;
}

static const char * Sn_ManBoundaryStatus( const Sn_Man_t * p )
{
    const sn_module_t * pModule;
    if ( !p->fLastBlast )
        return "unavailable (run @blast -c)";
    if ( p->LastBlastRevision != p->Revision )
        return "incompatible (SN revision changed)";
    if ( p->BlastMode != SN_BLAST_COMB )
        return "unsupported (last extraction was not combinational)";
    if ( !p->fBlasted )
        return "incompatible (saved boundary is unavailable)";
    for ( size_t i = 0; i < p->Boundary.cis.size; i++ )
        if ( sn_vec_at(sn_blast_boundary_bit_t, &p->Boundary.cis, i).kind == SN_BLAST_BOUNDARY_GATE_STATE )
            return "unsupported (sampled Liberty FF reconstruction)";
    if ( p->BlastModule != p->LastBlastModule || p->BlastName != p->LastBlastName ||
         p->BlastModule >= p->pDesign->modules.size )
        return "incompatible (extracted module identity changed)";
    pModule = sn_design_get_module_const( p->pDesign, p->BlastModule );
    if ( pModule->name != p->BlastName )
        return "incompatible (extracted module name changed)";
    if ( Sn_BoundarySignature(p) != p->BlastBoundarySignature )
        return "incompatible (saved boundary changed)";
    if ( Sn_BoundaryHasGenericMemories(&p->Boundary) )
        return "unsupported (generic memory boundary)";
    return "compatible";
}

static const char * Sn_ManPutStatus( const Sn_Man_t * p, Gia_Man_t * pGia )
{
    const char * pStatus = Sn_ManBoundaryStatus(p);
    if ( strcmp(pStatus, "compatible") )
        return pStatus;
    if ( pGia == NULL )
        return "incompatible (&-space GIA is unavailable)";
    if ( Gia_ManRegNum(pGia) != 0 )
        return "incompatible (GIA contains registers)";
    if ( (size_t)Gia_ManCiNum(pGia) != p->Boundary.cis.size ||
         (size_t)Gia_ManCoNum(pGia) != p->Boundary.cos.size )
        return "incompatible (GIA interface changed)";
    if ( Sn_GiaInterfaceSignature(pGia) != p->BlastInterfaceSignature )
        return "incompatible (GIA interface reordered or renamed)";
    if ( p->pDesign->library && Gia_ManHasCellMapping(pGia) &&
         (!p->BlastGenlibSignature || p->BlastGenlibSignature !=
            Sn_GenlibSignature((Mio_Library_t *)Abc_FrameReadLibGen())) )
        return "incompatible (mapping library changed; load @read_lib before @blast and remap)";
    return "compatible";
}

static const char * Sn_ManPutNtkStatus( const Sn_Man_t * p, Abc_Ntk_t * pNtk )
{
    const char * pStatus = Sn_ManBoundaryStatus(p);
    char Token[80];
    if ( strcmp(pStatus, "compatible") )
        return pStatus;
    if ( !pNtk )
        return "incompatible (main network is unavailable; use &put then map/amap/emap -m)";
    if ( Abc_NtkLatchNum(pNtk) || Abc_NtkBoxNum(pNtk) )
        return "incompatible (main network contains state or boxes)";
    if ( !Abc_NtkIsLogic(pNtk) || !Abc_NtkHasMapping(pNtk) || !p->pDesign->library )
        return "unsupported (main-space insertion requires library-backed cell mapping)";
    snprintf(Token, sizeof(Token), "sn-extraction-%llu", (unsigned long long)p->BlastToken);
    if ( !p->BlastToken || !pNtk->pSpec || strcmp(Token, pNtk->pSpec) )
        return "incompatible (main network is not from the current extraction)";
    if ( (size_t)Abc_NtkCiNum(pNtk) != p->Boundary.cis.size ||
         (size_t)Abc_NtkCoNum(pNtk) != p->Boundary.cos.size ||
         Sn_NtkInterfaceSignature(pNtk) != p->BlastInterfaceSignature )
        return "incompatible (main network interface changed, reordered or renamed)";
    if ( pNtk->pManFunc != Abc_FrameReadLibGen() || !p->BlastGenlibSignature ||
         p->BlastGenlibSignature != Sn_GenlibSignature((Mio_Library_t *)Abc_FrameReadLibGen()) )
        return "incompatible (main network mapping library changed)";
    return "compatible";
}

static int Sn_CommandStitch( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Sn_Man_t * p;
    Gia_Man_t * pGia, * pResult;
    const char * pReason;
    int CycleCi, NonCanonical, Duplicates;
    (void)argv;
    if ( argc != 1 )
    {
        Abc_Print( -2, "usage: @stitch\njoins LOOP wires in the current @blast -c -f proof AIG; "
                      "refuses observable cycles; state/macro cuts remain. Run @blast again before @put.\n" );
        return 1;
    }
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    p = Sn_AbcGetMan(pAbc);
    pGia = Abc_FrameReadGia(pAbc);
    pReason = Sn_ManPutStatus(p, pGia);
    if ( strcmp(pReason, "compatible") )
    {
        Abc_Print( -1, "Cannot @stitch: %s.\n", pReason );
        return 1;
    }
    pResult = sn_gia_stitch_loops(pGia, &p->Boundary, &pReason, &CycleCi);
    if ( !pResult )
    {
        Abc_Print( -1, "Cannot @stitch: %s.\n", pReason );
        if ( CycleCi >= 0 && pGia->vNamesIn )
            Abc_Print( -1, "Cycle includes LOOP boundary %s.\n", (char *)Vec_PtrEntry(pGia->vNamesIn, CycleCi) );
        return 1;
    }
    // Recompute canonical names without the deleted endpoints: otherwise a
    // removed LOOP can leave a spurious '#2' suffix on a surviving PO.
    Sn_GiaSetNames(pResult, p, 1, &NonCanonical, &Duplicates);
    Abc_Print( 1, "Joined %d LOOP bits: proof boundary %d CIs / %d COs; "
                  "state and opaque cuts remain independent.\n",
               Gia_ManCiNum(pGia) - Gia_ManCiNum(pResult), Gia_ManCiNum(pResult), Gia_ManCoNum(pResult) );
    Abc_FrameUpdateGia(pAbc, pResult);
    p->fBlasted = 0; // The proof interface deliberately cannot be reinserted.
    p->fLastBlast = 0;
    p->pLastAnalysis = "LOOP-stitched proof relation";
    return 0;
}

static int Sn_CommandStatus( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Sn_Man_t * p;
    Gia_Man_t * pGia;
    const char * pTopName;
    int c;
    Extra_UtilGetoptReset();
    while ( (c = Extra_UtilGetopt(argc, argv, "h")) != EOF )
        goto usage;
    if ( argc != globalUtilOptind )
        goto usage;
    if ( !Sn_CommandCheckDesign(pAbc) )
        return 1;
    p = Sn_AbcGetMan( pAbc );
    pGia = Abc_FrameReadGia( pAbc );
    pTopName = sn_name_get( &p->pDesign->names, sn_design_get_module_const(p->pDesign, p->Top)->name );
    fprintf( pAbc->Out, "SN design       : %s\n", sn_name_get(&p->pDesign->names, p->Name) );
    fprintf( pAbc->Out, "SN revision     : %llu\n", p->Revision );
    fprintf( pAbc->Out, "Top module      : %s\n", pTopName );
    fprintf( pAbc->Out, "Technology      : %s\n", p->Technology == SN_COMMAND_TECH_XILINX_ULTRASCALE ?
             "xilinx-ultrascale+" : "generic" );
    fprintf( pAbc->Out, "Hierarchy       : %s\n", Sn_ManHasUserHierarchy(p) ? "hierarchical" : "flat" );
    if ( p->pDesign->library )
        fprintf( pAbc->Out, "Liberty warnings: %llu\n",
                 (unsigned long long)sn_library_warning_count(p->pDesign->library) );
    if ( p->fLastBlast )
    {
        fprintf( pAbc->Out, "Last extraction : %s, module %s, revision %llu\n",
                 Sn_BlastModeName(p->BlastMode), sn_name_get(&p->pDesign->names, p->LastBlastName),
                 p->LastBlastRevision );
        fprintf( pAbc->Out, "Boundary hash   : 0x%016llx\n",
                 (unsigned long long)p->BlastBoundarySignature );
    }
    else if ( p->pLastAnalysis )
        fprintf( pAbc->Out, "Last extraction : %s (analysis only; no reinsertion boundary)\n", p->pLastAnalysis );
    else
        fprintf( pAbc->Out, "Last extraction : none\n" );
    if ( pGia )
        fprintf( pAbc->Out, "&-space GIA     : %d inputs, %d outputs, %d flops, %d ANDs\n",
                 Gia_ManPiNum(pGia), Gia_ManPoNum(pGia), Gia_ManRegNum(pGia), Gia_ManAndNum(pGia) );
    else
        fprintf( pAbc->Out, "&-space GIA     : none\n" );
    fprintf( pAbc->Out, "@put status     : %s\n", Sn_ManPutStatus(p, pGia) );
    fprintf( pAbc->Out, "@put -n status  : %s\n", Sn_ManPutNtkStatus(p, Abc_FrameReadNtk(pAbc)) );
    return 0;

usage:
    Abc_Print( -2, "usage: @status [-h]\n" );
    Abc_Print( -2, "\t         prints SN, saved @blast boundary, and current &-space GIA state\n" );
    Abc_Print( -2, "\t-h      : print the command usage\n" );
    return 1;
}

ABC_NAMESPACE_IMPL_END
