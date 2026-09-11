/**CFile****************************************************************

  FileName    [snStitch.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Checked elimination of wire cut points for boundary proofs.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snStitch.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__sn__snStitch_h
#define ABC__base__sn__snStitch_h

#include "aig/gia/gia.h"
#include "snBlast.h"

ABC_NAMESPACE_HEADER_START

// Checked CI substitution used by wire stitching and clock abstraction.
// aliases has one literal (or -1 to retain the CI) per source CI. Output
// literals may refer forward through substituted CIs. Only dependencies
// observable from roots are traversed. All graph marks are external.
static inline Gia_Man_t* sn_gia_substitute_cis_tracked(Gia_Man_t* source, const int* aliases,
                                             const int* roots, int root_count,
                                             const char** reason, int* cycle_ci, Vec_Int_t* unused_cis)
{
    Gia_Man_t* result = NULL;
    int *alias = NULL, *copy = NULL, *stack = NULL;
    unsigned char *color = NULL;
    int count, i, depth;
    Gia_Obj_t* object;
    *reason = NULL;
    *cycle_ci = -1;
    if (unused_cis) Vec_IntClear(unused_cis);
    if (!source || Gia_ManRegNum(source) || Gia_ManHasMapping(source) ||
        Gia_ManHasMapping2(source) || Gia_ManHasCellMapping(source) || Gia_ManHasChoices(source))
    {
        *reason = "requires an unmapped combinational GIA with its saved boundary";
        return NULL;
    }
    Gia_ManForEachAnd(source, object, i)
        if (!Gia_ObjIsAndReal(source, object) && !Gia_ObjIsBuf(object))
        {
            *reason = "explicit XOR/MUX nodes are not supported; use a fresh @blast -c -f";
            return NULL;
        }
    count = Gia_ManObjNum(source);
    alias = ABC_ALLOC(int, count);
    copy = ABC_ALLOC(int, count);
    stack = ABC_ALLOC(int, count);
    color = ABC_CALLOC(unsigned char, count);
    if (!alias || !copy || !stack || !color)
    {
        *reason = "allocation failure while resolving loop wires";
        goto cleanup;
    }
    for (i = 0; i < count; ++i)
        alias[i] = copy[i] = -1;
    Gia_ManForEachCi(source, object, i)
    {
        if (aliases[i] < -1 || (aliases[i] >= 0 &&
            (Abc_Lit2Var(aliases[i]) >= count || Gia_ObjIsCo(Gia_ManObj(source, Abc_Lit2Var(aliases[i]))))))
        {
            *reason = "invalid CI substitution literal";
            goto cleanup;
        }
        alias[Gia_ObjId(source, object)] = aliases[i];
    }
    for (i = 0; i < root_count; ++i)
        if (roots[i] < 0 || Abc_Lit2Var(roots[i]) >= count ||
            Gia_ObjIsCo(Gia_ManObj(source, Abc_Lit2Var(roots[i]))))
        {
            *reason = "invalid substitution output literal";
            goto cleanup;
        }
    result = Gia_ManStart(count);
    result->pName = source->pName ? Abc_UtilStrsav(source->pName) : NULL;
    result->pSpec = source->pSpec ? Abc_UtilStrsav(source->pSpec) : NULL;
    Gia_ManHashAlloc(result);
    copy[0] = 0;
    color[0] = 2;
    Gia_ManForEachCi(source, object, i)
        if (alias[Gia_ObjId(source, object)] < 0)
        {
            copy[Gia_ObjId(source, object)] = Gia_ManAppendCi(result);
            color[Gia_ObjId(source, object)] = 2;
        }
    for (i = 0; i < root_count; ++i)
    {
        int root = roots[i];
        depth = 0;
        if (color[Abc_Lit2Var(root)] != 2)
            stack[depth++] = Abc_Lit2Var(root);
        while (depth)
        {
            int id = stack[depth - 1], inputs[2], ninputs = 1, pending = -1;
            Gia_Obj_t* node = Gia_ManObj(source, id);
            color[id] = 1;
            if (alias[id] >= 0)
                inputs[0] = alias[id];
            else if (Gia_ObjIsAnd(node))
            {
                inputs[0] = Gia_ObjFaninLit0p(source, node);
                inputs[1] = Gia_ObjFaninLit1p(source, node);
                ninputs = Gia_ObjIsBuf(node) ? 1 : 2;
            }
            else
            {
                *reason = "unexpected node in loop dependency graph";
                goto cleanup;
            }
            for (int pin = 0; pin < ninputs; ++pin)
            {
                int dependency = Abc_Lit2Var(inputs[pin]);
                if (color[dependency] == 1)
                {
                    // Report one wire on the cycle, not an arbitrary upstream
                    // cut. Every cycle here contains a substituted CI.
                    for (int entry = depth - 1; entry >= 0; --entry)
                    {
                        if (Gia_ObjIsCi(Gia_ManObj(source, stack[entry])))
                            *cycle_ci = Gia_ObjCioId(Gia_ManObj(source, stack[entry]));
                        if (stack[entry] == dependency)
                            break;
                    }
                    *reason = "observable combinational cycle remains after joining LOOP wires";
                    goto cleanup;
                }
                if (!color[dependency])
                    pending = dependency;
            }
            if (pending >= 0)
            {
                stack[depth++] = pending;
                continue;
            }
            copy[id] = Abc_LitNotCond(copy[Abc_Lit2Var(inputs[0])], Abc_LitIsCompl(inputs[0]));
            if (ninputs == 2)
                copy[id] = Gia_ManHashAnd(result, copy[id],
                    Abc_LitNotCond(copy[Abc_Lit2Var(inputs[1])], Abc_LitIsCompl(inputs[1])));
            color[id] = 2;
            --depth;
        }
        Gia_ManAppendCo(result, Abc_LitNotCond(copy[Abc_Lit2Var(root)], Abc_LitIsCompl(root)));
    }
    if (unused_cis)
        Gia_ManForEachCi(source, object, i)
            if (aliases[i] >= 0 && !color[Gia_ObjId(source, object)]) Vec_IntPush(unused_cis, i);
    Gia_ManHashStop(result);
    goto cleanup;
cleanup:
    ABC_FREE(alias);
    ABC_FREE(copy);
    ABC_FREE(stack);
    ABC_FREE(color);
    if (*reason && result)
    {
        Gia_ManStop(result);
        result = NULL;
    }
    return result;
}

static inline Gia_Man_t* sn_gia_substitute_cis(Gia_Man_t* source, const int* aliases,
                                             const int* roots, int root_count,
                                             const char** reason, int* cycle_ci)
{
    return sn_gia_substitute_cis_tracked(source, aliases, roots, root_count, reason, cycle_ci, NULL);
}

// LOOP-only wrapper retaining all other cuts and their original names.
static inline Gia_Man_t* sn_gia_stitch_loops(Gia_Man_t* source,
                                            const sn_blast_boundary_t* boundary,
                                            const char** reason, int* cycle_ci)
{
    Gia_Man_t* result = NULL;
    int *aliases = NULL, *roots = NULL, root_count = 0;
    unsigned char* paired = NULL;
    *reason = NULL;
    *cycle_ci = -1;
    if (!source || (size_t)Gia_ManCiNum(source) != boundary->cis.size ||
        (size_t)Gia_ManCoNum(source) != boundary->cos.size)
    {
        *reason = "requires a GIA with its saved boundary";
        return NULL;
    }
    aliases = ABC_ALLOC(int, Gia_ManCiNum(source) + 1);
    roots = ABC_ALLOC(int, Gia_ManCoNum(source) + 1);
    paired = ABC_CALLOC(unsigned char, Gia_ManCoNum(source) + 1);
    if (!aliases || !roots || !paired)
    {
        *reason = "allocation failure while pairing LOOP wires";
        goto cleanup;
    }
    for (size_t i = 0; i < boundary->cis.size; ++i)
    {
        const sn_blast_boundary_bit_t* bit = &sn_vec_at(sn_blast_boundary_bit_t, &boundary->cis, i);
        aliases[i] = -1;
        if (bit->kind != SN_BLAST_BOUNDARY_LOOP_OUTPUT)
            continue;
        if (bit->owner >= boundary->loops.size)
            goto invalid;
        const sn_blast_loop_t* loop = &sn_vec_at(sn_blast_loop_t, &boundary->loops, bit->owner);
        size_t co = (size_t)loop->co_begin + bit->port;
        if (bit->port >= loop->width || co >= boundary->cos.size || paired[co])
            goto invalid;
        const sn_blast_boundary_bit_t* output = &sn_vec_at(sn_blast_boundary_bit_t, &boundary->cos, co);
        if (output->kind != SN_BLAST_BOUNDARY_LOOP_INPUT || output->owner != bit->owner || output->port != bit->port)
            goto invalid;
        paired[co] = 1;
        aliases[i] = Gia_ObjFaninLit0p(source, Gia_ManCo(source, (int)co));
    }
    for (size_t i = 0; i < boundary->cos.size; ++i)
    {
        bool loop = sn_vec_at(sn_blast_boundary_bit_t, &boundary->cos, i).kind == SN_BLAST_BOUNDARY_LOOP_INPUT;
        if (loop != (paired[i] != 0))
            goto invalid;
        if (!loop)
            roots[root_count++] = Gia_ObjFaninLit0p(source, Gia_ManCo(source, (int)i));
    }
    result = sn_gia_substitute_cis(source, aliases, roots, root_count, reason, cycle_ci);
    if (result && source->vNamesIn)
    {
        result->vNamesIn = Vec_PtrAlloc(Gia_ManCiNum(result));
        for (int i = 0; i < Gia_ManCiNum(source); ++i)
            if (aliases[i] < 0)
                Vec_PtrPush(result->vNamesIn, Abc_UtilStrsav((char*)Vec_PtrEntry(source->vNamesIn, i)));
    }
    if (result && source->vNamesOut)
    {
        result->vNamesOut = Vec_PtrAlloc(root_count);
        for (int i = 0; i < Gia_ManCoNum(source); ++i)
            if (!paired[i])
                Vec_PtrPush(result->vNamesOut, Abc_UtilStrsav((char*)Vec_PtrEntry(source->vNamesOut, i)));
    }
    goto cleanup;
invalid:
    *reason = "invalid LOOP boundary pairing";
cleanup:
    ABC_FREE(aliases);
    ABC_FREE(roots);
    ABC_FREE(paired);
    return result;
}

ABC_NAMESPACE_HEADER_END
#endif
