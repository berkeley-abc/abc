/**CFile****************************************************************

  FileName    [snMio.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Checked binding of Mio gates to shared SN Liberty cells.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snMio.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef ABC__base__sn__snMio_h
#define ABC__base__sn__snMio_h

#include "snLibrary.h"
#include "misc/vec/vec.h"
#include "misc/st/st.h"
#include "map/mio/mio.h"

ABC_NAMESPACE_HEADER_START

typedef enum sn_mio_binding_kind_t
{
    SN_MIO_UNBOUND, SN_MIO_CELL, SN_MIO_CONST0, SN_MIO_CONST1
} sn_mio_binding_kind_t;

// Derived, borrowed-library binding. Destroy before either library is replaced.
// The input permutation maps each physical SN input to its Mio fanin position.
// Unsupported cells remain explicit records, so they may be preserved in SN
// without becoming mapping targets. No function is expanded into SN operators.
typedef struct sn_mio_binding_t
{
    sn_mio_binding_kind_t kind;
    uint32_t cell, output, input_count;
    uint32_t* inputs;
    const char* reason;
} sn_mio_binding_t;

static inline void sn_mio_binding_destroy(sn_mio_binding_t* binding)
{
    free(binding->inputs);
    memset(binding, 0, sizeof(*binding));
}

// Bound the exhaustive cross-check, not the SN representation. Ordinary
// standard cells are small; larger cells need a SAT-based binding extension.
#define SN_MIO_TRUTH_MAX_INPUTS 16
#define SN_MIO_TRUTH_MAX_WORDS (1u << (SN_MIO_TRUTH_MAX_INPUTS - 6))

// Mio caches truth only through eight inputs. Larger gates still have a
// parsed formula; derive its full truth in Mio's grammar instead of treating
// an absent cache as a function mismatch. This never parses Liberty syntax.
// The caller provides SN_MIO_TRUTH_MAX_WORDS words.
static inline bool sn_mio_copy_truth(Mio_Gate_t* gate, uint64_t* truth)
{
    int count = gate ? Mio_GateReadPinNum(gate) : -1;
    if (count < 0 || count > SN_MIO_TRUTH_MAX_INPUTS)
        return false;
    unsigned words = count <= 6 ? 1u : 1u << (count - 6);
    word* cached = Mio_GateReadTruthP(gate);
    if (cached)
    {
        memcpy(truth, cached, words * sizeof(*truth));
        return true;
    }
    char* names[SN_MIO_TRUTH_MAX_INPUTS];
    Mio_Pin_t* pin;
    int index = 0;
    Mio_GateForEachPin(gate, pin)
    {
        if (index == count) return false;
        names[index++] = Mio_PinReadName(pin);
    }
    if (index != count) return false;
    Vec_Wrd_t* derived = Mio_ParseFormulaTruth(Mio_GateReadForm(gate), names, count);
    bool valid = derived && (unsigned)Vec_WrdSize(derived) == words;
    if (valid) memcpy(truth, Vec_WrdArray(derived), words * sizeof(*truth));
    if (derived) Vec_WrdFree(derived);
    return valid;
}

// Initializes a fresh record on both success and failure. The caller must
// destroy it in either case, and must not pass an already-live record.
static inline bool sn_mio_bind_gate(const sn_library_t* library, Mio_Gate_t* gate,
                                   sn_mio_binding_t* binding)
{
    memset(binding, 0, sizeof(*binding));
    binding->cell = SN_LIB_NONE;
    binding->reason = "missing or uncompiled library";
    if (!library || !library->compiled || !gate)
        return false;
    binding->cell = sn_library_find_cell(library, Mio_GateReadName(gate));
    int count = Mio_GateReadPinNum(gate);
    if (binding->cell == SN_LIB_NONE)
    {
        // Only ABC's designated synthetic constants may lack a physical cell.
        // Never recognize a constant merely by spelling or Boolean function.
        Mio_Library_t* mio = Mio_GateReadLib(gate);
        if (count == 0 && gate == Mio_LibraryReadConst0(mio) && Mio_GateReadTruth(gate) == 0)
            binding->kind = SN_MIO_CONST0;
        else if (count == 0 && gate == Mio_LibraryReadConst1(mio) && Mio_GateReadTruth(gate) == UINT64_MAX)
            binding->kind = SN_MIO_CONST1;
        else
        {
            binding->reason = "cell name is absent from the SN library";
            return false;
        }
        binding->reason = NULL;
        return true;
    }
    const sn_library_cell_t* entry = &library->cells[binding->cell];
    const sn_lib_cell_t* cell = &entry->model->cells[entry->local_id];
    const sn_expr_t* function = &library->functions[binding->cell];
    binding->reason = "cell is not an eligible combinational scalar cell with one or two outputs";
    if (!entry->scalar || cell->invalid || !entry->output_count || entry->output_count > 2 || !sn_expr_check(function) ||
        sn_expr_check(&library->transitions[binding->cell]) || function->inputs != entry->input_count ||
        function->outputs != entry->output_count)
        return false;
    if (cell->dont_use)
    {
        binding->reason = "cell is marked dont_use";
        return false;
    }
    binding->reason = "physical input/output interface differs from Mio";
    binding->output = SN_LIB_NONE;
    for (uint32_t output = 0; output < entry->output_count; ++output)
        if (strcmp(Mio_GateReadOutName(gate), sn_library_pin_name(library, binding->cell, SN_LIB_OUTPUT, output)) == 0)
        {
            if (binding->output != SN_LIB_NONE)
                return false;
            binding->output = output;
        }
    if (count < 0 || (uint32_t)count != entry->input_count || binding->output == SN_LIB_NONE)
        return false;
    if (count > SN_MIO_TRUTH_MAX_INPUTS)
    {
        binding->reason = "cell exceeds the exhaustive binding limit (needs SAT binding)";
        return false;
    }
    binding->input_count = (uint32_t)count;
    binding->inputs = count ? (uint32_t*)malloc((size_t)count * sizeof(*binding->inputs)) : NULL;
    if (count && !binding->inputs)
    {
        binding->reason = "out of memory allocating pin binding";
        return false;
    }
    for (uint32_t input = 0; input < (uint32_t)count; ++input)
    {
        const char* name = sn_library_pin_name(library, binding->cell, SN_LIB_INPUT, input);
        Mio_Pin_t* pin;
        uint32_t index = 0, matches = 0;
        Mio_GateForEachPin(gate, pin)
        {
            if (strcmp(name, Mio_PinReadName(pin)) == 0)
            {
                binding->inputs[input] = index;
                ++matches;
            }
            ++index;
        }
        if (matches != 1 || index != (uint32_t)count)
            return false;
        for (uint32_t previous = 0; previous < input; ++previous)
            if (binding->inputs[previous] == binding->inputs[input])
                return false;
    }
    uint64_t inputs[SN_MIO_TRUTH_MAX_INPUTS];
    size_t scratch_count = (size_t)function->inputs + function->count + 1;
    uint64_t* scratch = (uint64_t*)malloc(scratch_count * sizeof(*scratch));
    if (!scratch)
    {
        binding->reason = "out of memory checking gate function";
        return false;
    }
    uint64_t truth[SN_MIO_TRUTH_MAX_WORDS];
    bool equal = sn_mio_copy_truth(gate, truth);
    uint32_t assignments = UINT32_C(1) << count;
    for (uint32_t base = 0; equal && base < assignments; base += 64)
    {
        for (uint32_t input = 0; input < (uint32_t)count; ++input)
        {
            inputs[input] = 0;
            for (uint32_t bit = 0; bit < 64; ++bit)
                if (((base + bit) >> binding->inputs[input]) & 1)
                    inputs[input] |= UINT64_C(1) << bit;
        }
        uint64_t outputs[2];
        equal = sn_expr_simulate(function, inputs, scratch, scratch_count, outputs) &&
            outputs[binding->output] == truth[base / 64];
    }
    free(scratch);
    if (!equal)
    {
        binding->reason = "Boolean function differs under the physical pin permutation";
        return false;
    }
    binding->kind = SN_MIO_CELL;
    binding->reason = NULL;
    return true;
}

ABC_NAMESPACE_HEADER_END
#endif
