/**CFile****************************************************************

  FileName    [snSlang.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Slang-to-SN RTL frontend.]

  Synopsis    [SystemVerilog elaboration and lowering from Slang AST into SN designs.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snSlang.cpp,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

// The frontend uses Mike Popoloski's Slang (https://github.com/MikePopoloski/slang), whose
// SystemVerilog parsing and elaboration provide the foundation for this work. We gratefully
// acknowledge Mike and the Slang contributors.
//
// Several semantic abstractions and improvement priorities in this implementation were inspired
// by Martin Povišer's sv-elab project, which provided valuable ideas for lvalue analysis,
// procedural state, timing-pattern recognition, memory eligibility, addressing, resolved nets,
// and diagnostics. Warm thanks to Martin for saving us from discovering many of SystemVerilog's
// sharp edges the hard way.
// Project: https://github.com/povik/sv-elab
//
// We also thank Yosys and its contributors for an exemplary synthesis flow. Their approaches to
// elaboration, technology mapping, and other synthesis problems have been valuable examples
// from which we have learned while developing SN.
// Project: https://github.com/YosysHQ/yosys

#include "snSlang.h"
#include "snLvalue.h"
#include "snCheck.h"
#include "snLiberty.h"
#include "snPorts.h"

#include <algorithm>
#include <bit>
#include <chrono>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <iterator>
#include <limits>
#include <optional>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "slang/ast/Compilation.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Bitstream.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/TimingControl.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/ast/expressions/ConversionExpression.h"
#include "slang/ast/expressions/LiteralExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/statements/ConditionalStatements.h"
#include "slang/ast/statements/LoopStatements.h"
#include "slang/ast/statements/MiscStatements.h"
#include "slang/ast/symbols/AttributeSymbol.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/ValueSymbol.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/ast/types/NetType.h"
#include "slang/driver/Driver.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/text/SourceManager.h"

namespace
{

using namespace slang;
using namespace slang::ast;
using sn_slang_detail::sn_lvalue_analyze;
using sn_slang_detail::sn_lvalue_context_t;
using sn_slang_detail::sn_lvalue_t;

// Some generated Verilog netlists spell a positional parameter override as
// `cell#7 inst (...)` instead of the required `cell #(7) inst (...)`. Repair
// only this unambiguous instance pattern, outside comments and strings, while
// keeping the original source path and line numbers for Slang diagnostics.
static unsigned normalize_bare_parameter_overrides(std::string_view source, std::string& normalized)
{
    auto identifier_start = [](char c) {
        return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' || c == '$';
    };
    auto identifier_char = [&](char c) {
        return identifier_start(c) || (c >= '0' && c <= '9');
    };
    auto whitespace = [](char c) { return c == ' ' || c == '\t' || c == '\r' || c == '\n'; };
    size_t copied = 0;
    unsigned count = 0;
    for (size_t i = 0; i < source.size();)
    {
        if (source[i] == '/' && i + 1 < source.size() && source[i + 1] == '/')
        {
            i += 2;
            while (i < source.size() && source[i] != '\n') i++;
        }
        else if (source[i] == '/' && i + 1 < source.size() && source[i + 1] == '*')
        {
            i += 2;
            while (i + 1 < source.size() && !(source[i] == '*' && source[i + 1] == '/')) i++;
            i = std::min(i + 2, source.size());
        }
        else if (source[i] == '"')
        {
            i++;
            while (i < source.size() && source[i] != '"')
            {
                if (source[i] == '\\' && i + 1 < source.size()) i++;
                i++;
            }
            if (i < source.size()) i++;
        }
        else if (source[i] == '\\')
        {
            // Escaped Verilog identifiers terminate at whitespace.
            while (i < source.size() && !whitespace(source[i])) i++;
        }
        else if (identifier_start(source[i]))
        {
            size_t end = i + 1;
            while (end < source.size() && identifier_char(source[end])) end++;
            if (end < source.size() && source[end] == '#')
            {
                size_t number = end + 1;
                while (number < source.size() && source[number] >= '0' && source[number] <= '9') number++;
                size_t instance = number;
                while (instance < source.size() && whitespace(source[instance])) instance++;
                if (number > end + 1 && instance > number && instance < source.size() &&
                    identifier_start(source[instance]))
                {
                    size_t after_instance = instance + 1;
                    while (after_instance < source.size() && identifier_char(source[after_instance]))
                        after_instance++;
                    while (after_instance < source.size() && whitespace(source[after_instance]))
                        after_instance++;
                    if (after_instance < source.size() && source[after_instance] == '(')
                    {
                        normalized.append(source.substr(copied, end - copied));
                        normalized.append(" #(");
                        normalized.append(source.substr(end + 1, number - end - 1));
                        normalized.push_back(')');
                        copied = number;
                        count++;
                    }
                }
            }
            i = end;
        }
        else i++;
    }
    if (count) normalized.append(source.substr(copied));
    return count;
}

static void add_source_with_legacy_parameter_compat(driver::Driver& driver, const char* path)
{
    std::ifstream input(path, std::ios::binary);
    if (!input)
    {
        driver.sourceLoader.addFiles(path);
        return;
    }
    std::string source(std::istreambuf_iterator<char>{input}, {});
    std::string normalized;
    unsigned count = normalize_bare_parameter_overrides(source, normalized);
    if (!count)
    {
        driver.sourceLoader.addFiles(path);
        return;
    }
    std::fprintf(stderr, "sn-slang: normalized %u legacy bare parameter override(s) in %s\n", count, path);
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText(path, normalized));
}

static const InstanceBodySymbol* canonical_body(const InstanceBodySymbol& body)
{
    const InstanceBodySymbol* canonical = body.parentInstance ? body.parentInstance->getCanonicalBody() : nullptr;
    return canonical ? canonical : &body;
}

static bool is_ignored_system_task(const CallExpression* call)
{
    if (!call || !call->isSystemCall())
        return false;
    std::string_view name = call->getSubroutineName();
    return name == "$display" || name == "$finish" || name == "$stop" || name == "$readmemh" ||
           name == "$readmemb" || name == "$fatal" || name == "$error" || name == "$warning" ||
           name == "$info";
}

struct EvalFrameGuard
{
    EvalContext& context;

    explicit EvalFrameGuard(EvalContext& context) : context(context) { context.pushEmptyFrame(); }
    ~EvalFrameGuard() { context.popFrame(); }
};

struct TranslateOffCache
{
    struct Directives
    {
        std::vector<size_t> off;
        std::vector<size_t> on;
    };

    const SourceManager* source_manager;
    std::unordered_map<BufferID, Directives> buffers;

    explicit TranslateOffCache(const SourceManager* source_manager) : source_manager(source_manager) {}

    bool contains(SourceLocation location)
    {
        location = source_manager->getFullyOriginalLoc(location);
        if (!location)
            return false;
        std::string_view source = source_manager->getSourceText(location.buffer());
        size_t start = location.offset();
        if (start > source.size())
            return false;
        auto [entry, inserted] = buffers.try_emplace(location.buffer());
        if (inserted)
        {
            auto collect = [&](std::string_view text, std::vector<size_t>& offsets) {
                for (size_t offset = source.find(text); offset != std::string_view::npos;
                     offset = source.find(text, offset + 1))
                    offsets.push_back(offset);
            };
            collect("translate_off", entry->second.off);
            collect("translate_on", entry->second.on);
        }
        auto last_before = [&](const std::vector<size_t>& offsets) -> std::optional<size_t> {
            auto position = std::upper_bound(offsets.begin(), offsets.end(), start);
            return position == offsets.begin() ? std::nullopt : std::optional<size_t>(*--position);
        };
        auto off = last_before(entry->second.off);
        auto on = last_before(entry->second.on);
        return off && (!on || *off > *on);
    }
};

struct LoopConstantGuard
{
    std::unordered_map<const ValueSymbol*, ConstantValue*>& values;
    std::vector<std::pair<const ValueSymbol*, ConstantValue*>> saved;

    explicit LoopConstantGuard(std::unordered_map<const ValueSymbol*, ConstantValue*>& values) : values(values) {}

    void bind(const ValueSymbol* symbol, ConstantValue* value)
    {
        auto it = values.find(symbol);
        saved.emplace_back(symbol, it == values.end() ? nullptr : it->second);
        values[symbol] = value;
    }

    ~LoopConstantGuard()
    {
        for (auto it = saved.rbegin(); it != saved.rend(); ++it)
        {
            if (it->second)
                values[it->first] = it->second;
            else
                values.erase(it->first);
        }
    }
};

struct ApproximationCounters
{
    size_t x_bits = 0;
    size_t z_bits = 0;

    void report() const
    {
        if (x_bits || z_bits)
            std::fprintf(stderr,
                         "sn-slang: warning: concretized %zu X bit(s) and %zu Z bit(s) at the final "
                         "two-state SN boundary\n",
                         x_bits, z_bits);
    }
};

struct FormalStatementCounters
{
    size_t immediate = 0;
    size_t concurrent = 0;

    void report(sn_slang_assertion_policy_t policy) const
    {
        size_t total = immediate + concurrent;
        if (total && policy == SN_SLANG_ASSERT_WARN)
            std::fprintf(stderr,
                         "sn-slang: warning: ignored %zu formal statement(s) (%zu immediate, %zu concurrent); "
                         "use -I to accept this policy quietly or -R to reject them\n",
                         total, immediate, concurrent);
    }
};

struct ModuleImporter
{
    struct PartialDriver
    {
        uint32_t offset;
        uint32_t width;
        sn_obj_id_t value;
    };

    struct SelectedValue
    {
        const ValueSymbol* symbol;
        int64_t index;
        int64_t bit = -1;

        bool operator==(const SelectedValue&) const = default;
    };

    struct SelectedValueHash
    {
        size_t operator()(const SelectedValue& value) const
        {
            return std::hash<const void*>{}(value.symbol) ^ (std::hash<int64_t>{}(value.index) << 1) ^
                   (std::hash<int64_t>{}(value.bit) << 2);
        }
    };

    struct ProceduralValues
    {
        struct MemoryWrite
        {
            const ValueSymbol* memory;
            sn_obj_id_t address;
            sn_obj_id_t data;
            sn_obj_id_t enable;
            sn_obj_id_t mask;

            bool operator==(const MemoryWrite&) const = default;
        };

        std::unordered_map<const ValueSymbol*, sn_obj_id_t> values;
        std::unordered_map<SelectedValue, sn_obj_id_t, SelectedValueHash> selected_values;
        std::unordered_map<const ValueSymbol*, std::vector<uint32_t>> assigned_masks;
        std::unordered_map<SelectedValue, std::vector<uint32_t>, SelectedValueHash> selected_assigned_masks;
        std::vector<MemoryWrite> memory_writes;
        sn_obj_id_t return_flag = SN_INVALID_ID;
        sn_obj_id_t break_flag = SN_INVALID_ID;
        sn_obj_id_t continue_flag = SN_INVALID_ID;
    };

    struct FunctionArgumentsHash
    {
        size_t operator()(const std::vector<sn_obj_id_t>& arguments) const
        {
            size_t hash = arguments.size();
            for (sn_obj_id_t argument : arguments)
                hash ^= size_t(argument) + 0x9e3779b9u + (hash << 6) + (hash >> 2);
            return hash;
        }
    };

    struct ProceduralLoopGuard
    {
        ProceduralValues& environment;
        uint32_t& depth;
        sn_obj_id_t outer_break;
        sn_obj_id_t outer_continue;

        ProceduralLoopGuard(ProceduralValues& environment, uint32_t& depth) :
            environment(environment), depth(depth), outer_break(environment.break_flag),
            outer_continue(environment.continue_flag)
        {
            environment.break_flag = SN_INVALID_ID;
            environment.continue_flag = SN_INVALID_ID;
            depth++;
        }

        ~ProceduralLoopGuard()
        {
            environment.break_flag = outer_break;
            environment.continue_flag = outer_continue;
            depth--;
        }

        void next_iteration() { environment.continue_flag = SN_INVALID_ID; }
    };

    struct ProceduralWriteGuard
    {
        ProceduralValues*& active;
        ProceduralValues* saved;

        ProceduralWriteGuard(ProceduralValues*& active, ProceduralValues& environment) :
            active(active), saved(active)
        {
            active = &environment;
        }

        ~ProceduralWriteGuard() { active = saved; }
    };

    struct Memory
    {
        sn_obj_pair_t pair;
        int64_t start_offset;
        uint32_t depth;
        int64_t load_start;
        int64_t load_step;
    };

    struct MemoryElement
    {
        const ValueSymbol* memory;
        const Expression* address;
    };

    struct PendingInstance
    {
        const InstanceSymbol* symbol;
        sn_obj_id_t object;
    };

    struct SequentialBlock
    {
        const ProceduralBlockSymbol* procedural;
        const Statement* synchronous_body;
        const Statement* asynchronous_body;
        std::vector<const Statement*> prologue;
        sn_obj_id_t clock;
        sn_obj_id_t reset;
        uint32_t flags;
        std::vector<const ValueSymbol*> targets;
        std::vector<SelectedValue> selected_targets;
    };

    sn_module_t* module;
    const InstanceBodySymbol* body;
    const std::unordered_map<const InstanceBodySymbol*, sn_module_id_t>* body_modules;
    const SourceManager* source_manager;
    TranslateOffCache* translate_off_cache;
    ApproximationCounters* approximation_counters;
    FormalStatementCounters* formal_statement_counters;
    std::unordered_map<const ValueSymbol*, sn_obj_id_t> values;
    std::unordered_set<const ValueSymbol*> undriven_values;
    std::unordered_map<const ValueSymbol*, const Expression*> assignments;
    std::unordered_map<const ValueSymbol*, std::vector<const Expression*>> additional_value_assignments;
    std::unordered_map<const ValueSymbol*, std::vector<sn_obj_id_t>> additional_value_drivers;
    std::unordered_set<const ValueSymbol*> inout_symbols;
    std::unordered_map<const ValueSymbol*, const Expression*> inout_assignments;
    std::unordered_set<const ValueSymbol*> resolving;
    std::unordered_map<const ValueSymbol*, sn_obj_pair_t> continuous_loops;
    std::vector<const ValueSymbol*> assignment_order;
    std::vector<const AssignmentExpression*> structured_assignments;
    std::unordered_map<const ValueSymbol*, std::vector<const AssignmentExpression*>> structured_drivers;
    std::unordered_map<const ValueSymbol*, std::vector<PartialDriver>> partial_value_drivers;
    std::unordered_map<SelectedValue, std::vector<PartialDriver>, SelectedValueHash> partial_selected_drivers;
    std::unordered_set<const AssignmentExpression*> lowering_structured;
    std::unordered_set<const AssignmentExpression*> lowered_structured;
    std::vector<std::pair<const ValueSymbol*, const Expression*>> variable_initializers;
    std::unordered_set<const ValueSymbol*> collected_declaration_initializers;
    std::unordered_map<SelectedValue, sn_obj_id_t, SelectedValueHash> selected_values;
    std::unordered_set<SelectedValue, SelectedValueHash> undriven_selected_values;
    std::unordered_map<SelectedValue, const Expression*, SelectedValueHash> selected_assignments;
    std::unordered_map<SelectedValue, std::vector<const Expression*>, SelectedValueHash>
        additional_selected_assignments;
    std::unordered_set<SelectedValue, SelectedValueHash> resolving_selected;
    std::unordered_map<SelectedValue, sn_obj_pair_t, SelectedValueHash> selected_continuous_loops;
    std::vector<SelectedValue> selected_assignment_order;
    std::vector<const ProceduralBlockSymbol*> procedural_blocks;
    struct PrimitiveDriver
    {
        const PrimitiveInstanceSymbol* inst;
        uint32_t output_index;
    };
    std::unordered_map<const ValueSymbol*, std::vector<PrimitiveDriver>> primitive_value_drivers;
    // A primitive output expression is a lazy driver token, not a read of its
    // lvalue. Reuse selected-assignment resolution (including cycles and net
    // resolution) without constructing synthetic Slang assignments.
    std::unordered_map<const Expression*, PrimitiveDriver> primitive_output_expressions;
    std::vector<const ValueSymbol*> memory_symbols;
    std::unordered_set<const ValueSymbol*> memory_candidates;
    std::unordered_map<const ValueSymbol*, std::string> memory_hints;
    std::unordered_map<const ValueSymbol*, Memory> memories;
    std::vector<SequentialBlock> sequential_blocks;
    std::unordered_map<const ValueSymbol*, sn_obj_pair_t> sequential_registers;
    std::unordered_map<SelectedValue, sn_obj_pair_t, SelectedValueHash> sequential_selected_registers;
    std::unordered_map<sn_obj_id_t, SelectedValue> latch_declarations;
    std::unordered_map<const ValueSymbol*, sn_obj_id_t> combinational_placeholders;
    std::unordered_map<SelectedValue, sn_obj_id_t, SelectedValueHash> combinational_selected_placeholders;
    std::vector<PendingInstance> pending_insts;
    bool preserve_state = false;
    std::unordered_set<std::string> warned_unknown_modules;
    const ProceduralValues* active_procedural_values = nullptr;
    const ProceduralValues* nonblocking_read_values = nullptr;
    ProceduralValues* active_procedural_writes = nullptr;
    const VariableSymbol* active_return_value = nullptr;
    uint32_t procedural_loop_depth = 0;
    const Expression* active_lvalue_expression = nullptr;
    EvalContext* active_constant_context = nullptr;
    std::unordered_map<const ValueSymbol*, ConstantValue*> active_loop_constants;
    std::unordered_set<const ValueSymbol*> constant_dead_values;
    std::unordered_set<SelectedValue, SelectedValueHash> constant_dead_selected_values;
    bool prune_procedural_constants = true;
    bool lowering_initial_block = false;
    std::unordered_set<const SubroutineSymbol*> active_subroutines;
    std::unordered_map<const SubroutineSymbol*, bool> function_cacheable;
    std::unordered_set<const SubroutineSymbol*> checking_function_cacheability;
    std::unordered_set<const Statement*> handled_formal_statements;
    std::unordered_map<const SubroutineSymbol*,
                       std::unordered_map<std::vector<sn_obj_id_t>, sn_obj_id_t, FunctionArgumentsHash>>
        function_results;
    std::unordered_map<sn_obj_id_t, sn_obj_id_t> constant_valid_masks;
    std::unordered_map<sn_obj_id_t, sn_obj_id_t> constant_z_masks;
    bool memories_from_attributes_only = false;
    bool preserve_metadata = false;
    sn_slang_assertion_policy_t assertion_policy = SN_SLANG_ASSERT_WARN;

    ModuleImporter(sn_module_t* module, const InstanceBodySymbol* body,
                   const std::unordered_map<const InstanceBodySymbol*, sn_module_id_t>* body_modules,
                   const SourceManager* source_manager, TranslateOffCache* translate_off_cache,
                   ApproximationCounters* approximation_counters,
                   FormalStatementCounters* formal_statement_counters,
                   bool memories_from_attributes_only = false, bool preserve_metadata = false,
                   sn_slang_assertion_policy_t assertion_policy = SN_SLANG_ASSERT_WARN) :
        module(module), body(body), body_modules(body_modules), source_manager(source_manager),
        translate_off_cache(translate_off_cache), approximation_counters(approximation_counters),
        formal_statement_counters(formal_statement_counters),
        memories_from_attributes_only(memories_from_attributes_only),
        preserve_metadata(preserve_metadata), assertion_policy(assertion_policy)
    {
    }

    void add_source_metadata(sn_obj_id_t object, SourceLocation location)
    {
        if (!preserve_metadata || !location)
            return;
        location = source_manager->getFullyOriginalLoc(location);
        if (!location)
            return;
        std::string path = source_manager->getFullPath(location.buffer()).string();
        if (path.empty())
            path = std::string(source_manager->getFileName(location));
        if (path.empty())
            path = "<unknown>";
        size_t line = source_manager->getLineNumber(location);
        size_t column = source_manager->getColumnNumber(location);
        sn_module_add_source_record(module, object, path.c_str(), uint32_t(std::min(line, size_t(UINT32_MAX))),
                                    uint32_t(std::min(column, size_t(UINT32_MAX))));
    }

    static bool preserve_attribute(std::string_view name)
    {
        static constexpr std::string_view names[] = {
            "keep",          "dont_touch",     "ram_block",       "rom_block",      "ram_style",
            "rom_style",     "ramstyle",       "romstyle",        "syn_ramstyle",   "syn_romstyle",
            "blackbox",      "black_box",      "syn_black_box",   "keep_hierarchy", "flatten",
            "use_dsp",       "multstyle",      "altera_attribute", "max_fanout"};
        return std::find(std::begin(names), std::end(names), name) != std::end(names);
    }

    static std::string attribute_value(const ConstantValue& constant)
    {
        if (constant.isInteger())
        {
            const SVInt& integer = constant.integer();
            uint32_t bits = uint32_t(integer.getBitWidth());
            if (bits && bits <= 4096 && (bits & 7u) == 0 && !integer.hasUnknown())
            {
                std::string text;
                text.reserve(bits / 8 + 2);
                text.push_back('"');
                bool printable = true;
                for (uint32_t byte = bits / 8; byte-- > 0;)
                {
                    unsigned char ch = 0;
                    for (uint32_t bit = 0; bit < 8; bit++)
                        ch |= unsigned(integer[int32_t(byte * 8 + bit)].value != 0) << bit;
                    printable &= ch >= 32 && ch < 127;
                    if (ch == '"' || ch == '\\')
                        text.push_back('\\');
                    text.push_back(char(ch));
                }
                text.push_back('"');
                if (printable)
                    return text;
            }
        }
        return constant.toString(4096, true, true);
    }

    void add_attribute_metadata(sn_obj_id_t object, const Symbol& symbol)
    {
        if (!preserve_metadata)
            return;
        for (const AttributeSymbol* attribute : body->getCompilation().getAttributes(symbol))
            if (preserve_attribute(attribute->name))
            {
                std::string name(attribute->name);
                std::string value = attribute_value(attribute->getValue());
                sn_module_add_attribute_record(module, object, name.c_str(), value.c_str());
            }
    }

    void add_metadata(sn_obj_id_t object, const Symbol& symbol)
    {
        add_source_metadata(object, symbol.location);
        add_attribute_metadata(object, symbol);
    }

    enum class SecPathPolicy { Register, General };

    // Use one relative-path and named-generate-scope check for SEC metadata.
    // Register keys retain their stricter simple-identifier rule; memory and
    // instance keys permit the printable indexed paths they used before.
    std::optional<std::string> sec_relative_path(const Symbol& symbol, SecPathPolicy policy) const
    {
        auto simple = [](std::string_view name) {
            if (name.empty() || !(std::isalpha((unsigned char)name[0]) || name[0] == '_')) return false;
            return std::all_of(name.begin(), name.end(), [](unsigned char c) {
                return std::isalnum(c) || c == '_' || c == '$';
            });
        };
        if (symbol.name.starts_with("_sn_") || symbol.name.starts_with("__sn_") ||
            (policy == SecPathPolicy::Register && !simple(symbol.name)))
            return std::nullopt;
        const Scope* scope = symbol.getParentScope();
        while (scope && &scope->asSymbol() != body)
        {
            const Symbol& parent = scope->asSymbol();
            // A named generate-for owns unnamed per-index block entries.
            // Their path comes from the named array and its declared index.
            if (parent.as_if<GenerateBlockSymbol>() && parent.getParentScope())
                if (const auto* array = parent.getParentScope()->asSymbol().as_if<GenerateBlockArraySymbol>();
                    array && !array->isUnnamed &&
                    (policy == SecPathPolicy::General || simple(array->name)))
                { scope = parent.getParentScope(); continue; }
            if (const auto* gen = parent.as_if<GenerateBlockSymbol>(); gen && gen->isUnnamed)
                return std::nullopt;
            if (const auto* array = parent.as_if<GenerateBlockArraySymbol>(); array && array->isUnnamed)
                return std::nullopt;
            if (policy == SecPathPolicy::Register && !simple(parent.name))
                return std::nullopt;
            scope = parent.getParentScope();
        }
        if (policy == SecPathPolicy::Register && !scope) return std::nullopt;
        std::string path = symbol.getHierarchicalPath();
        std::string prefix = body->getHierarchicalPath() + ".";
        if (!path.starts_with(prefix)) return std::nullopt;
        path.erase(0, prefix.size());
        if (policy == SecPathPolicy::General &&
            !std::all_of(path.begin(), path.end(), [](unsigned char c) {
                return std::isalnum(c) || c == '_' || c == '$' || c == '.' ||
                       c == '[' || c == ']' || c == '-';
            }))
            return std::nullopt;
        return path;
    }

    // SEC correspondence is an explicit source-level assumption. Do not infer
    // identities from generated SN object names or from flattened bit positions.
    bool add_sec_identity(sn_obj_id_t object, const ValueSymbol& symbol)
    {
        if (!preserve_state) return true;
        for (const AttributeSymbol* attribute : body->getCompilation().getAttributes(symbol))
            if (attribute->name == "sn_sec_identity")
            {
                std::string identity;
                if (!register_name(symbol, identity, "sn_sec_identity"))
                    return false;
                sn_module_add_attribute_record(module, object, "sn_sec_identity", identity.c_str());
                return true;
            }
        auto path = sec_relative_path(symbol, SecPathPolicy::Register);
        if (!path) return true;
        const Type& type = symbol.getType().getCanonicalType();
        // Initially support scalar/integral and one-dimensional packed words.
        // Packed structs, multidimensional and individually lowered array words
        // require a richer tuple identity and are deliberately not guessed.
        if (!type.isIntegral()) return true;
        if (const auto* array = type.as_if<PackedArrayType>(); array && array->elementType.getCanonicalType().isPackedArray()) return true;
        if (type.isStruct() || type.isUnion()) return true;
        ConstantRange range = type.getFixedRange();
        std::string identity = *path + "|" + std::to_string(range.left) + ":" +
            std::to_string(range.right) + ":" + std::to_string(width(type));
        sn_module_add_attribute_record(module, object, "sn_sec_identity", identity.c_str());
        return true;
    }

    void add_module_metadata(const InstanceBodySymbol& instance_body)
    {
        // Internal source identity survives parameter specialization and SN binary roundtrips.
        std::string definition(instance_body.getDefinition().name);
        sn_module_add_attribute_record(module, SN_INVALID_ID, "sn_source_module", definition.c_str());
        add_source_metadata(SN_INVALID_ID, instance_body.location);
        add_attribute_metadata(SN_INVALID_ID, instance_body.getDefinition());
    }

    void collect_declaration_order(const Scope& scope, std::unordered_map<const ValueSymbol*, size_t>& order)
    {
        for (const Symbol& symbol : scope.members())
        {
            if (symbol.as_if<InstanceSymbol>())
                continue;
            if (const auto* generate = symbol.as_if<GenerateBlockSymbol>(); generate && generate->isUninstantiated)
                continue;
            if (const auto* value = symbol.as_if<ValueSymbol>())
                order.emplace(value, order.size());
            if (const Scope* child = symbol.as_if<Scope>())
                collect_declaration_order(*child, order);
        }
    }

    // Boundary order must not depend on procedural assignment order or hash-table iteration.
    void order_state_declarations()
    {
        std::unordered_map<const ValueSymbol*, size_t> order;
        collect_declaration_order(*body, order);
        using Key = std::tuple<size_t, int64_t, int64_t>;
        std::unordered_map<sn_obj_id_t, Key> keys;
        auto rank = [&](const ValueSymbol* symbol) {
            auto it = order.find(symbol);
            return it == order.end() ? SIZE_MAX : it->second;
        };
        for (const auto& [symbol, pair] : sequential_registers)
            keys.emplace(pair.out, Key(rank(symbol), 0, -1));
        for (const auto& [selected, pair] : sequential_selected_registers)
            keys.emplace(pair.out, Key(rank(selected.symbol), selected.index, selected.bit));
        for (const auto& [object, selected] : latch_declarations)
            keys.emplace(object, Key(rank(selected.symbol), selected.index, selected.bit));
        for (const auto& [symbol, memory] : memories)
            keys.emplace(memory.pair.out, Key(rank(symbol), 0, -1));
        for (sn_obj_type_t type : {SN_REG_OUT, SN_MEM_OUT})
        {
            auto& objects = module->type_objects[type];
            if (objects.size < 2)
                continue;
            auto* first = &sn_vec_at(sn_obj_id_t, &objects, 0);
            std::stable_sort(first, first + objects.size, [&](sn_obj_id_t a, sn_obj_id_t b) {
                auto ia = keys.find(a), ib = keys.find(b);
                Key ka = ia == keys.end() ? Key(SIZE_MAX, 0, 0) : ia->second;
                Key kb = ib == keys.end() ? Key(SIZE_MAX, 0, 0) : ib->second;
                return ka < kb;
            });
        }
    }

    // The named writer can disambiguate a state variable from a buffered output.
    // Restore its boundary identity for both FFs and inferred latches. This
    // attribute supplies a name only, never behavior or initial state.
    bool register_name(const Symbol& target, std::string& name,
                       std::string_view attribute_name = "sn_register_name")
    {
        for (const AttributeSymbol* attribute : body->getCompilation().getAttributes(target))
            if (attribute->name == attribute_name)
            {
                const auto& value = attribute->getValue();
                if ((!value.isInteger() && !value.isString()) ||
                    (value.isInteger() && value.integer().hasUnknown()))
                {
                    std::fprintf(stderr, "sn-slang: invalid %.*s annotation\n",
                                 int(attribute_name.size()), attribute_name.data());
                    return false;
                }
                name = value.convertToStr().str();
                if (name.empty() || std::any_of(name.begin(), name.end(), [](unsigned char c) {
                        return c < 32 || c >= 127;
                    }))
                {
                    std::fprintf(stderr, "sn-slang: invalid %.*s annotation\n",
                                 int(attribute_name.size()), attribute_name.data());
                    return false;
                }
            }
        return true;
    }

    bool handle_formal_statement(const Statement& statement)
    {
        if (!handled_formal_statements.emplace(&statement).second)
            return true;
        if (statement.as_if<ImmediateAssertionStatement>())
            formal_statement_counters->immediate++;
        else if (statement.as_if<ConcurrentAssertionStatement>())
            formal_statement_counters->concurrent++;
        else
            return false;
        if (assertion_policy == SN_SLANG_ASSERT_ERROR)
        {
            report_timing_error(statement.sourceRange.start(),
                                "formal statements are disabled by -R; remove -R or use -I to ignore them");
            return false;
        }
        return true;
    }

    static uint32_t width(const Type& type)
    {
        uint64_t bits = type.getBitWidth() > 0 ? uint64_t(type.getBitWidth())
                                               : (type.isFixedSize() ? type.getBitstreamWidth() : 0);
        if (!bits || bits > std::numeric_limits<uint32_t>::max())
        {
            std::fprintf(stderr, "sn-slang: unsupported zero or oversized fixed-size type\n");
            return 0;
        }
        return uint32_t(bits);
    }

    static bool is_zero_width(const Type& type)
    {
        return type.isFixedSize() && type.getBitstreamWidth() == 0;
    }

    static const ValueSymbol* referenced_value(const Expression& expression)
    {
        if (const auto* hierarchical = expression.as_if<HierarchicalValueExpression>())
        {
            if (const auto* modport_port = hierarchical->ref.target
                                                   ? hierarchical->ref.target->as_if<ModportPortSymbol>()
                                                   : nullptr)
                for (auto it = hierarchical->ref.path.rbegin(); it != hierarchical->ref.path.rend(); ++it)
                {
                    if (const auto* inst = it->symbol->as_if<InstanceSymbol>())
                        for (const Symbol& member : inst->body.members())
                            if (member.name == hierarchical->ref.target->name)
                                if (const auto* value = member.as_if<ValueSymbol>())
                                    return value;
                    if (const auto* port = it->symbol->as_if<InterfacePortSymbol>())
                    {
                        auto [connection, unused_modport] = port->getConnection();
                        if (const auto* inst = connection ? connection->as_if<InstanceSymbol>() : nullptr)
                            for (const Symbol& member : inst->body.members())
                                if (member.name == modport_port->name)
                                    if (const auto* value = member.as_if<ValueSymbol>())
                                        return value;
                    }
                }
            if (const auto* target = hierarchical->ref.target
                                         ? hierarchical->ref.target->as_if<ValueSymbol>()
                                         : nullptr)
                return target;
        }
        if (const auto* value = expression.as_if<ValueExpressionBase>())
            return &value->symbol;
        return nullptr;
    }

    static bool crosses_retained_module_boundary(const HierarchicalValueExpression& expression)
    {
        for (const auto& element : expression.ref.path)
            if (const auto* inst = element.symbol->as_if<InstanceSymbol>(); inst && inst->isModule())
                return true;
        return false;
    }

    static const Expression* retained_boundary_port_connection(const HierarchicalValueExpression& expression)
    {
        const auto* target = expression.ref.target ? expression.ref.target->as_if<ValueSymbol>() : nullptr;
        const InstanceSymbol* module_inst = nullptr;
        for (const auto& element : expression.ref.path)
        {
            const auto* inst = element.symbol->as_if<InstanceSymbol>();
            if (!inst || !inst->isModule())
                continue;
            if (module_inst)
                return nullptr; // A multi-level reference needs hidden-port synthesis, not a local alias.
            module_inst = inst;
        }
        if (!target || !module_inst)
            return nullptr;
        for (const Symbol* symbol : module_inst->body.getPortList())
        {
            const auto* port = symbol->as_if<PortSymbol>();
            const auto* internal = port && port->internalSymbol
                                       ? port->internalSymbol->as_if<ValueSymbol>()
                                       : nullptr;
            if (!port || internal != target)
                continue;
            const PortConnection* connection = module_inst->getPortConnection(*port);
            return connection ? connection->getExpression() : nullptr;
        }
        return nullptr;
    }

    static sn_obj_type_t net_resolution_operator(const ValueSymbol& symbol)
    {
        const auto* net = symbol.as_if<NetSymbol>();
        if (!net)
            return SN_NONE;
        switch (net->netType.netKind)
        {
        case NetType::WAnd:
        case NetType::TriAnd:
            return SN_BIT_AND;
        case NetType::WOr:
        case NetType::TriOr:
            return SN_BIT_OR;
        default:
            return SN_NONE;
        }
    }

    sn_obj_id_t resolve_net_driver(const ValueSymbol& symbol, sn_obj_id_t first, sn_obj_id_t second)
    {
        if (sn_obj_same_typed_value(module, first, second))
            return first;
        sn_obj_type_t type = net_resolution_operator(symbol);
        if (sn_obj_width(module, first) != sn_obj_width(module, second))
            return SN_INVALID_ID;
        if (type != SN_NONE)
        {
            sn_obj_id_t fanins[2] = {first, second};
            return sn_module_add_operator(module, type, sn_obj_width(module, first), symbol.getType().isSigned(), 2,
                                          fanins, nullptr);
        }

        auto first_z_it = constant_z_masks.find(first);
        auto second_z_it = constant_z_masks.find(second);
        if (first_z_it == constant_z_masks.end() && second_z_it == constant_z_masks.end())
        {
            std::fprintf(stderr, "sn-slang: ordinary net '%.*s' has multiple active drivers; use wand/wor semantics "
                                 "or remove the conflict\n",
                         int(symbol.name.size()), symbol.name.data());
            return SN_INVALID_ID;
        }

        uint32_t bits = sn_obj_width(module, first);
        sn_obj_id_t all_valid = mask_constant(bits, true);
        sn_obj_id_t no_z = mask_constant(bits, false);
        auto first_valid_it = constant_valid_masks.find(first);
        auto second_valid_it = constant_valid_masks.find(second);
        sn_obj_id_t first_valid = first_valid_it == constant_valid_masks.end() ? all_valid : first_valid_it->second;
        sn_obj_id_t second_valid = second_valid_it == constant_valid_masks.end() ? all_valid
                                                                                  : second_valid_it->second;
        sn_obj_id_t first_z = first_z_it == constant_z_masks.end() ? no_z : first_z_it->second;
        sn_obj_id_t second_z = second_z_it == constant_z_masks.end() ? no_z : second_z_it->second;
        auto binary = [&](sn_obj_type_t op, sn_obj_id_t left, sn_obj_id_t right) {
            sn_obj_id_t fanins[2] = {left, right};
            return sn_module_add_operator(module, op, bits, false, 2, fanins, nullptr);
        };
        auto invert = [&](sn_obj_id_t value) {
            return sn_module_add_operator(module, SN_BIT_NOT, bits, false, 1, &value, nullptr);
        };
        sn_obj_id_t first_one = binary(SN_BIT_AND, first_valid, first);
        sn_obj_id_t second_one = binary(SN_BIT_AND, second_valid, second);
        sn_obj_id_t first_zero = binary(SN_BIT_AND, first_valid, invert(first));
        sn_obj_id_t second_zero = binary(SN_BIT_AND, second_valid, invert(second));
        sn_obj_id_t first_accepts_one = binary(SN_BIT_OR, first_z, first_one);
        sn_obj_id_t second_accepts_one = binary(SN_BIT_OR, second_z, second_one);
        sn_obj_id_t first_accepts_zero = binary(SN_BIT_OR, first_z, first_zero);
        sn_obj_id_t second_accepts_zero = binary(SN_BIT_OR, second_z, second_zero);
        sn_obj_id_t known_one = binary(SN_BIT_OR, binary(SN_BIT_AND, first_one, second_accepts_one),
                                      binary(SN_BIT_AND, second_one, first_accepts_one));
        sn_obj_id_t known_zero = binary(SN_BIT_OR, binary(SN_BIT_AND, first_zero, second_accepts_zero),
                                       binary(SN_BIT_AND, second_zero, first_accepts_zero));
        sn_obj_id_t result = known_one;
        if (symbol.getType().isSigned())
            result = sn_module_add_operator(module, SN_CAST, bits, true, 1, &known_one, nullptr);
        constant_valid_masks[result] = binary(SN_BIT_OR, known_one, known_zero);
        constant_z_masks[result] = binary(SN_BIT_AND, first_z, second_z);
        return result;
    }

    // Slang folds an equality whose operand carries X or Z bits to a known value in cases where the
    // LRM result is decided by the other bits (a definite mismatch makes != and !=? true). Those
    // expressions are lowered through lower_equality(), which implements the documented policy.
    bool equality_fold_is_unreliable(const Expression& expression, EvalContext& context) const
    {
        const auto* binary = expression.as_if<BinaryExpression>();
        if (!binary)
            return false;
        switch (binary->op)
        {
        case BinaryOperator::Equality:
        case BinaryOperator::Inequality:
        case BinaryOperator::CaseEquality:
        case BinaryOperator::CaseInequality:
        case BinaryOperator::WildcardEquality:
        case BinaryOperator::WildcardInequality:
            break;
        default:
            return false;
        }
        for (const Expression* operand : {&binary->left(), &binary->right()})
        {
            ConstantValue value = operand->eval(context);
            if (value && value.isInteger() && value.integer().hasUnknown())
                return true;
        }
        return false;
    }

    std::optional<int64_t> constant_integer(const Expression& expression) const
    {
        if (active_constant_context)
        {
            ConstantValue constant = expression.eval(*active_constant_context);
            if (constant && constant.isInteger() && !constant.integer().hasUnknown())
                return constant.integer().as<int64_t>();
        }
        else
        {
            EvalContext context(*body->parentInstance);
            ConstantValue constant = expression.eval(context);
            if (constant && constant.isInteger() && !constant.integer().hasUnknown())
                return constant.integer().as<int64_t>();
        }

        // Some elaborated procedural loop locals are not resolved by a fresh
        // expression evaluation even though their EvalContext frame is active.
        if (const auto* named = expression.as_if<NamedValueExpression>())
        {
            auto loop_constant = active_loop_constants.find(&named->symbol);
            if (loop_constant != active_loop_constants.end())
            {
                const ConstantValue& value = *loop_constant->second;
                if (value && value.isInteger() && !value.integer().hasUnknown())
                    return value.integer().as<int64_t>();
            }
            if (active_constant_context)
            {
                ConstantValue* local = active_constant_context->findLocal(&named->symbol);
                if (local && *local && local->isInteger() && !local->integer().hasUnknown())
                    return local->integer().as<int64_t>();
            }
            if (const auto* parameter = named->symbol.as_if<ParameterSymbol>())
            {
                const ConstantValue& value = parameter->getValue();
                if (value && value.isInteger() && !value.integer().hasUnknown())
                    return value.integer().as<int64_t>();
            }
        }
        if (const auto* conversion = expression.as_if<ConversionExpression>())
            return constant_integer(conversion->operand());
        if (const auto* unary = expression.as_if<UnaryExpression>())
        {
            auto operand = constant_integer(unary->operand());
            if (!operand)
                return std::nullopt;
            if (unary->op == UnaryOperator::Plus)
                return operand;
            if (unary->op == UnaryOperator::Minus && *operand != INT64_MIN)
                return -*operand;
        }
        if (const auto* binary = expression.as_if<BinaryExpression>())
        {
            auto left = constant_integer(binary->left());
            auto right = constant_integer(binary->right());
            if (!left || !right)
                return std::nullopt;
            __int128 result;
            if (binary->op == BinaryOperator::Add)
                result = __int128(*left) + *right;
            else if (binary->op == BinaryOperator::Subtract)
                result = __int128(*left) - *right;
            else if (binary->op == BinaryOperator::Multiply)
                result = __int128(*left) * *right;
            else if (binary->op == BinaryOperator::Equality || binary->op == BinaryOperator::CaseEquality)
                result = *left == *right;
            else if (binary->op == BinaryOperator::Inequality || binary->op == BinaryOperator::CaseInequality)
                result = *left != *right;
            else if (binary->op == BinaryOperator::LessThan)
                result = *left < *right;
            else if (binary->op == BinaryOperator::LessThanEqual)
                result = *left <= *right;
            else if (binary->op == BinaryOperator::GreaterThan)
                result = *left > *right;
            else if (binary->op == BinaryOperator::GreaterThanEqual)
                result = *left >= *right;
            else if (binary->op == BinaryOperator::LogicalAnd)
                result = *left != 0 && *right != 0;
            else if (binary->op == BinaryOperator::LogicalOr)
                result = *left != 0 || *right != 0;
            else
                return std::nullopt;
            if (result >= INT64_MIN && result <= INT64_MAX)
                return int64_t(result);
        }
        return std::nullopt;
    }

    std::optional<bool> constant_truth(const Expression& expression) const
    {
        EvalContext local_context(*body->parentInstance);
        EvalContext& context = active_constant_context ? *active_constant_context : local_context;
        ConstantValue constant = expression.eval(context);
        if (constant && constant.isInteger() && !constant.integer().hasUnknown() &&
            !equality_fold_is_unreliable(expression, context))
            return constant.isTrue();
        auto integer = constant_integer(expression);
        return integer ? std::optional<bool>(*integer != 0) : std::nullopt;
    }

    bool source_range_contains(SourceRange range, std::string_view text) const
    {
        range = source_manager->getFullyOriginalRange(range);
        if (!range.start() || !range.end() || range.start().buffer() != range.end().buffer())
            return false;
        std::string_view source = source_manager->getSourceText(range.start().buffer());
        size_t start = range.start().offset();
        size_t end = range.end().offset();
        return start <= end && end <= source.size() &&
               source.substr(start, end - start).find(text) != std::string_view::npos;
    }

    bool source_is_translate_off(SourceLocation location) const
    {
        return translate_off_cache->contains(location);
    }

    std::optional<SelectedValue> named_element(const Expression& expression) const
    {
        const auto* select = expression.as_if<ElementSelectExpression>();
        auto selected_base = [&](auto&& self, const Expression& value_expression) -> const ValueSymbol* {
            if (const auto* conversion = value_expression.as_if<ConversionExpression>())
                return self(self, conversion->operand());
            if (const auto* member = value_expression.as_if<MemberAccessExpression>())
                return member->member.as_if<ValueSymbol>();
            return referenced_value(value_expression);
        };
        const ValueSymbol* value = select ? selected_base(selected_base, select->value()) : nullptr;
        if (!value)
            return std::nullopt;
        auto index = constant_integer(select->selector());
        if (!index)
            return std::nullopt;
        return SelectedValue{value, *index};
    }

    std::optional<SelectedValue> named_element_bit(const Expression& expression) const
    {
        const auto* select = expression.as_if<ElementSelectExpression>();
        auto element = select ? named_element(select->value()) : std::nullopt;
        auto bit = select ? constant_integer(select->selector()) : std::nullopt;
        if (!element || !bit)
            return std::nullopt;
        element->bit = *bit;
        return element;
    }

    uint32_t selected_width(const SelectedValue& selected) const
    {
        if (selected.bit >= 0)
        {
            const Type* first = selected.symbol->getType().getArrayElementType();
            const Type* second = first ? first->getArrayElementType() : nullptr;
            return second ? width(*second) : 1;
        }
        const Type* element_type = selected.symbol->getType().getArrayElementType();
        // A direct selection of either a packed or unpacked array denotes one complete element. In particular,
        // packed arrays of structs and words must not be mistaken for arrays of individual bits.
        return element_type ? width(*element_type) : 1;
    }

    static bool is_automatic_value(const ValueSymbol& symbol)
    {
        const Scope* scope = symbol.getParentScope();
        if (!scope)
            return false;
        SymbolKind kind = scope->asSymbol().kind;
        return kind == SymbolKind::StatementBlock || kind == SymbolKind::Subroutine;
    }

    bool selected_is_signed(const SelectedValue& selected) const
    {
        if (selected.bit >= 0)
        {
            const Type* first = selected.symbol->getType().getArrayElementType();
            const Type* second = first ? first->getArrayElementType() : nullptr;
            return second && second->isSigned();
        }
        const Type* element_type = selected.symbol->getType().getArrayElementType();
        return element_type && element_type->isSigned();
    }

    static std::string selected_name(const SelectedValue& selected)
    {
        std::string name(selected.symbol->name);
        name += "_" + std::to_string(selected.index);
        if (selected.bit >= 0)
            name += "_" + std::to_string(selected.bit);
        return name;
    }

    bool has_selected_driver(const SelectedValue& selected) const
    {
        auto has_direct_driver = [&](const SelectedValue& value) {
            return selected_values.contains(value) || selected_assignments.contains(value) ||
                   (active_procedural_values && active_procedural_values->selected_values.contains(value));
        };
        if (has_direct_driver(selected))
            return true;
        if (selected.bit >= 0)
            return false;
        const Type* element_type = selected.symbol->getType().getArrayElementType();
        if (!element_type)
            return false;
        ConstantRange range = element_type->getFixedRange();
        uint32_t bits = width(*element_type);
        for (uint32_t offset = 0; offset < bits; offset++)
        {
            int64_t bit_index = range.isDescending() ? int64_t(range.right) + offset
                                                     : int64_t(range.right) - offset;
            if (!has_direct_driver(SelectedValue{selected.symbol, selected.index, bit_index}))
                return false;
        }
        return bits != 0;
    }

    std::optional<MemoryElement> memory_element(const Expression& expression) const
    {
        const auto* select = expression.as_if<ElementSelectExpression>();
        const auto* named = select ? select->value().as_if<NamedValueExpression>() : nullptr;
        if (!named || !memories.contains(&named->symbol))
            return std::nullopt;
        return MemoryElement{&named->symbol, &select->selector()};
    }

    sn_obj_id_t normalize_memory_address(const Memory& memory, sn_obj_id_t address)
    {
        if (memory.start_offset == 0)
            return address;
        uint32_t bits = sn_obj_width(module, address);
        if (!bits)
            return SN_INVALID_ID;
        uint64_t magnitude = memory.start_offset < 0 ? uint64_t(-(memory.start_offset + 1)) + 1
                                                     : uint64_t(memory.start_offset);
        std::vector<uint32_t> words(sn_const_word_count(bits));
        for (uint32_t word = 0; word < words.size() && word < 2; word++)
            words[word] = uint32_t(magnitude >> (32 * word));
        sn_obj_id_t offset = sn_module_add_const(module, bits, false, words.data(), nullptr);
        sn_obj_id_t fanins[2] = {address, offset};
        sn_obj_type_t operation = memory.start_offset < 0 ? SN_ADD : SN_SUB;
        return sn_module_add_operator(module, operation, bits, false, 2, fanins, nullptr);
    }

    sn_obj_id_t index_constant(uint32_t bits, int64_t value)
    {
        std::vector<uint32_t> words(sn_const_word_count(bits));
        uint64_t encoded = uint64_t(value);
        for (uint32_t word = 0; word < words.size(); word++)
            words[word] = word < 2 ? uint32_t(encoded >> (32 * word)) : value < 0 ? UINT32_MAX : 0;
        if (bits & 31)
            words.back() &= (uint32_t(1) << (bits & 31)) - 1;
        return sn_module_add_const(module, bits, value < 0, words.data(), nullptr);
    }

    sn_obj_id_t lower_sparse_selection(sn_obj_id_t selector,
                                       const std::vector<std::pair<int64_t, sn_obj_id_t>>& alternatives,
                                       sn_obj_id_t default_value)
    {
        if (alternatives.empty())
            return default_value;
        uint32_t selector_bits = sn_obj_width(module, selector);
        std::vector<sn_obj_id_t> conditions;
        std::vector<sn_obj_id_t> values;
        conditions.reserve(alternatives.size());
        values.reserve(alternatives.size());
        for (const auto& [index, value] : alternatives)
        {
            if (!index_is_representable(index, selector_bits, sn_obj_is_signed(module, selector)))
                continue;
            sn_obj_id_t constant = index_constant(selector_bits, index);
            sn_obj_id_t fanins[2] = {selector, constant};
            conditions.push_back(sn_module_add_operator(module, SN_EQ, 1, false, 2, fanins, nullptr));
            values.push_back(value);
        }
        if (conditions.empty())
            return default_value;
        sn_obj_id_t select = sn_module_add_concat(module, uint32_t(conditions.size()), conditions.data(), nullptr);
        sn_obj_id_t packed = sn_module_add_concat(module, uint32_t(values.size()), values.data(), nullptr);
        return sn_module_add_pmux(module, select, packed, default_value, nullptr);
    }

    static bool index_is_representable(int64_t index, uint32_t bits, bool is_signed)
    {
        if (bits >= 64)
            return true;
        if (!is_signed)
            return index >= 0 && uint64_t(index) < (uint64_t(1) << bits);
        int64_t limit = int64_t(1) << (bits - 1);
        return index >= -limit && index < limit;
    }

    sn_obj_id_t lower_sparse_indexed_part(sn_obj_id_t value, sn_obj_id_t base, ConstantRange value_range,
                                          uint32_t result_bits, RangeSelectionKind selection_kind,
                                          bool base_is_signed)
    {
        std::vector<uint32_t> zero_words(sn_const_word_count(result_bits));
        sn_obj_id_t zero = sn_module_add_const(module, result_bits, false, zero_words.data(), nullptr);
        int64_t padding = int64_t(result_bits) - 1;
        int64_t first = std::max<int64_t>(INT32_MIN, int64_t(value_range.lower()) - padding);
        int64_t last = std::min<int64_t>(INT32_MAX, int64_t(value_range.upper()) + padding);
        std::vector<std::pair<int64_t, sn_obj_id_t>> alternatives;
        for (int64_t base_index = first; base_index <= last; base_index++)
        {
            if (!index_is_representable(base_index, sn_obj_width(module, base), base_is_signed))
                continue;
            auto selected = ConstantRange::getIndexedRange(int32_t(base_index), int32_t(result_bits),
                                                           value_range.isDescending(),
                                                           selection_kind == RangeSelectionKind::IndexedUp);
            if (!selected)
                continue;
            bool overlaps = false;
            std::vector<sn_obj_id_t> bits;
            bits.reserve(result_bits);
            for (uint32_t offset = 0; offset < result_bits; offset++)
            {
                int64_t index = selected->left >= selected->right ? int64_t(selected->right) + offset
                                                                  : int64_t(selected->right) - offset;
                if (index >= INT32_MIN && index <= INT32_MAX && value_range.containsPoint(int32_t(index)))
                {
                    int32_t physical = value_range.translateIndex(int32_t(index));
                    bits.push_back(sn_module_add_slice(module, value, physical, physical, nullptr));
                    overlaps = true;
                }
                else
                {
                    const uint32_t zero_word = 0;
                    bits.push_back(sn_module_add_const(module, 1, false, &zero_word, nullptr));
                }
            }
            if (overlaps)
                alternatives.emplace_back(base_index,
                                          sn_module_add_concat(module, result_bits, bits.data(), nullptr));
        }
        return lower_sparse_selection(base, alternatives, zero);
    }

    sn_obj_id_t lower_integer(const SVInt& value, const Type& type)
    {
        // SN is a two-state synthesis IR. X and Z bits are synthesis
        // don't-cares and are deterministically concretized to zero.
        SVInt concrete = value;
        bool had_unknown = concrete.hasUnknown();
        if (had_unknown)
            concrete.flattenUnknowns();
        uint32_t bits = width(type);
        if (!bits || uint32_t(concrete.getBitWidth()) != bits)
        {
            std::fprintf(stderr, "sn-slang: integer constant has an unsupported width conversion\n");
            return SN_INVALID_ID;
        }
        std::vector<uint32_t> words(sn_const_word_count(bits));
        const uint64_t* raw = concrete.getRawPtr();
        for (uint32_t i = 0; i < words.size(); i++)
            words[i] = uint32_t(raw[i / 2] >> (32 * (i & 1u)));
        sn_obj_id_t data = sn_module_add_const(module, bits, type.isSigned(), words.data(), nullptr);
        if (had_unknown)
        {
            std::vector<uint32_t> mask_words(sn_const_word_count(bits));
            std::vector<uint32_t> z_words(sn_const_word_count(bits));
            for (uint32_t bit = 0; bit < bits; bit++)
            {
                if (!value[int32_t(bit)].isUnknown())
                    mask_words[bit / 32] |= uint32_t(1) << (bit % 32);
                else if (value[int32_t(bit)].value == logic_t::z.value)
                {
                    z_words[bit / 32] |= uint32_t(1) << (bit % 32);
                    approximation_counters->z_bits++;
                }
                else
                    approximation_counters->x_bits++;
            }
            sn_obj_id_t mask = sn_module_add_const(module, bits, false, mask_words.data(), nullptr);
            sn_obj_id_t z_mask = sn_module_add_const(module, bits, false, z_words.data(), nullptr);
            // Constants are interned by their concretized two-state value. Keep the per-lowering-site X/Z identity
            // on a unique buffer so an unknown literal can never attach masks to an equal-valued plain constant.
            sn_obj_id_t identity =
                sn_module_add_operator(module, SN_BUF, bits, type.isSigned(), 1, &data, nullptr);
            constant_valid_masks[identity] = mask;
            constant_z_masks[identity] = z_mask;
            data = identity;
        }
        return data;
    }

    // The declared index range that a constant range-select of value covers, honoring the
    // declaration direction for indexed (+:/-:) selections. The right bound of the result is
    // always the least-significant selected index.
    static std::optional<ConstantRange> selected_index_range(const RangeSelectExpression& range, int64_t left,
                                                             int64_t right)
    {
        if (left < INT32_MIN || left > INT32_MAX || right < INT32_MIN || right > INT32_MAX)
            return std::nullopt;
        if (range.getSelectionKind() == RangeSelectionKind::Simple)
            return ConstantRange{int32_t(left), int32_t(right)};
        if (right <= 0 || !range.value().type->hasFixedRange())
            return std::nullopt;
        return ConstantRange::getIndexedRange(int32_t(left), int32_t(right),
                                              range.value().type->getFixedRange().isDescending(),
                                              range.getSelectionKind() == RangeSelectionKind::IndexedUp);
    }

    // The declared index of result bit `offset` (LSB first) within a selected index range.
    static int64_t selected_bit_index(const ConstantRange& selected, uint32_t offset)
    {
        return selected.left >= selected.right ? int64_t(selected.right) + offset : int64_t(selected.right) - offset;
    }

    // True when every bit cleared in the validity mask is set in the Z mask, i.e. the constant has
    // no X bits. A missing Z mask means all unknown bits are X.
    bool constant_is_all_ones_where(sn_obj_id_t valid_mask,
                                    std::unordered_map<sn_obj_id_t, sn_obj_id_t>::const_iterator z)
    {
        if (z == constant_z_masks.end())
            return false;
        uint32_t bits = sn_obj_width(module, valid_mask);
        for (uint32_t bit = 0; bit < bits; bit++)
            if (!sn_const_bit(module, valid_mask, bit) && !sn_const_bit(module, z->second, bit))
                return false;
        return true;
    }

    sn_obj_id_t lower_zero(const Type& type)
    {
        uint32_t bits = width(type);
        if (!bits)
            return SN_INVALID_ID;
        std::vector<uint32_t> words(sn_const_word_count(bits));
        return sn_module_add_const(module, bits, type.isSigned(), words.data(), nullptr);
    }

    sn_obj_id_t materialize_constant_slice(sn_obj_id_t object)
    {
        sn_obj_type_t type = sn_obj_type(module, object);
        if (type == SN_CONST0 || type == SN_CONST1 || type == SN_CONST)
            return object;
        uint32_t bits = sn_obj_width(module, object);
        std::vector<uint32_t> words(sn_const_word_count(bits));
        std::unordered_set<sn_obj_id_t> active;
        struct ActiveGuard
        {
            std::unordered_set<sn_obj_id_t>& active;
            sn_obj_id_t object;
            ~ActiveGuard() { active.erase(object); }
        };
        auto constant_bit = [&](auto&& self, sn_obj_id_t value, uint32_t bit) -> std::optional<bool> {
            if (value == SN_INVALID_ID || value >= module->obj_types.size)
                return std::nullopt;
            if (!active.insert(value).second)
                return std::nullopt;
            ActiveGuard guard{active, value};
            sn_obj_type_t value_type = sn_obj_type(module, value);
            uint32_t value_width = sn_obj_width(module, value);
            if (bit >= value_width)
                return std::nullopt;
            if (value_type == SN_CONST0 || value_type == SN_CONST1 || value_type == SN_CONST)
                return sn_const_bit(module, value, bit);
            if (value_type == SN_BUF)
                return self(self, sn_obj_fanin(module, value, 0), bit);
            if (value_type == SN_CAST)
            {
                sn_obj_id_t source = sn_obj_fanin(module, value, 0);
                uint32_t source_width = sn_obj_width(module, source);
                if (bit < source_width)
                    return self(self, source, bit);
                return sn_obj_is_signed(module, source) ? self(self, source, source_width - 1)
                                                        : std::optional<bool>(false);
            }
            if (value_type == SN_SLICE)
            {
                sn_slice_info_t info = sn_obj_slice_info(module, value);
                int64_t source_bit = info.left_index >= info.right_index ? int64_t(info.right_index) + bit
                                                                         : int64_t(info.right_index) - bit;
                return source_bit < 0 ? std::nullopt
                                      : self(self, sn_obj_fanin(module, value, 0), uint32_t(source_bit));
            }
            if (value_type == SN_CONCAT)
            {
                uint32_t offset = 0;
                for (uint32_t i = 0; i < sn_obj_fanin_count(module, value); i++)
                {
                    sn_obj_id_t fanin = sn_obj_fanin(module, value, i);
                    uint32_t fanin_width = sn_obj_width(module, fanin);
                    if (bit < offset + fanin_width)
                        return self(self, fanin, bit - offset);
                    offset += fanin_width;
                }
                return std::nullopt;
            }
            if (value_type == SN_REPLICATE)
            {
                sn_obj_id_t fanin = sn_obj_fanin(module, value, 0);
                return self(self, fanin, bit % sn_obj_width(module, fanin));
            }
            if (value_type == SN_BIT_NOT)
            {
                auto input = self(self, sn_obj_fanin(module, value, 0), bit);
                return input ? std::optional<bool>(!*input) : std::nullopt;
            }
            if (value_type == SN_BIT_AND || value_type == SN_BIT_OR || value_type == SN_BIT_XOR ||
                value_type == SN_BIT_XNOR)
            {
                auto left = self(self, sn_obj_fanin(module, value, 0), bit);
                auto right = self(self, sn_obj_fanin(module, value, 1), bit);
                if (value_type == SN_BIT_AND)
                {
                    if ((left && !*left) || (right && !*right))
                        return false;
                    if (!left || !right)
                        return std::nullopt;
                    return *left && *right;
                }
                if (value_type == SN_BIT_OR)
                {
                    if ((left && *left) || (right && *right))
                        return true;
                    if (!left || !right)
                        return std::nullopt;
                    return *left || *right;
                }
                if (!left || !right)
                    return std::nullopt;
                return value_type == SN_BIT_XOR ? *left != *right : *left == *right;
            }
            if (value_type == SN_MUX)
            {
                auto select = self(self, sn_obj_fanin(module, value, SN_MUX_SELECT), 0);
                return !select ? std::nullopt
                               : self(self, sn_obj_fanin(module, value,
                                                         *select ? SN_MUX_SELECTED : SN_MUX_DEFAULT),
                                      bit);
            }
            return std::nullopt;
        };
        for (uint32_t result_bit = 0; result_bit < bits; result_bit++)
        {
            auto bit = constant_bit(constant_bit, object, result_bit);
            if (!bit)
                return object;
            if (*bit)
                words[result_bit / 32] |= 1u << (result_bit % 32);
        }
        return sn_module_add_const(module, bits, sn_obj_is_signed(module, object), words.data(), nullptr);
    }

    std::optional<int64_t> procedural_constant_integer(const Expression& expression,
                                                       const ProceduralValues& environment)
    {
        if (auto value = constant_integer(expression))
            return value;
        if (const auto* conversion = expression.as_if<ConversionExpression>())
            return procedural_constant_integer(conversion->operand(), environment);
        if (const auto* unary = expression.as_if<UnaryExpression>())
        {
            auto operand = procedural_constant_integer(unary->operand(), environment);
            if (!operand)
                return std::nullopt;
            if (unary->op == UnaryOperator::Plus)
                return operand;
            if (unary->op == UnaryOperator::Minus && *operand != INT64_MIN)
                return -*operand;
            if (unary->op == UnaryOperator::LogicalNot)
                return *operand == 0;
            return std::nullopt;
        }
        if (const auto* binary = expression.as_if<BinaryExpression>())
        {
            auto left = procedural_constant_integer(binary->left(), environment);
            auto right = procedural_constant_integer(binary->right(), environment);
            if (!left || !right)
                return std::nullopt;
            __int128 result;
            switch (binary->op)
            {
            case BinaryOperator::Add:              result = __int128(*left) + *right; break;
            case BinaryOperator::Subtract:         result = __int128(*left) - *right; break;
            case BinaryOperator::Multiply:         result = __int128(*left) * *right; break;
            case BinaryOperator::Equality:
            case BinaryOperator::CaseEquality:     result = *left == *right; break;
            case BinaryOperator::Inequality:
            case BinaryOperator::CaseInequality:   result = *left != *right; break;
            case BinaryOperator::LessThan:          result = *left < *right; break;
            case BinaryOperator::LessThanEqual:     result = *left <= *right; break;
            case BinaryOperator::GreaterThan:       result = *left > *right; break;
            case BinaryOperator::GreaterThanEqual:  result = *left >= *right; break;
            case BinaryOperator::LogicalAnd:        result = *left != 0 && *right != 0; break;
            case BinaryOperator::LogicalOr:         result = *left != 0 || *right != 0; break;
            default: return std::nullopt;
            }
            return result >= INT64_MIN && result <= INT64_MAX ? std::optional<int64_t>(int64_t(result))
                                                              : std::nullopt;
        }
        const ValueSymbol* symbol = referenced_value(expression);
        auto found = symbol ? environment.values.find(symbol) : environment.values.end();
        if (found == environment.values.end())
            return std::nullopt;
        sn_obj_id_t object = materialize_constant_slice(found->second);
        sn_obj_type_t type = sn_obj_type(module, object);
        uint32_t bits = sn_obj_width(module, object);
        if ((type != SN_CONST0 && type != SN_CONST1 && type != SN_CONST) || !bits || bits > 64)
            return std::nullopt;
        uint64_t value = 0;
        for (uint32_t bit = 0; bit < bits; bit++)
            if (sn_const_bit(module, object, bit))
                value |= uint64_t(1) << bit;
        if (sn_obj_is_signed(module, object) && bits < 64 && (value & (uint64_t(1) << (bits - 1))))
            value |= UINT64_MAX << bits;
        return int64_t(value);
    }

    sn_obj_id_t normalize_condition(sn_obj_id_t condition)
    {
        if (condition == SN_INVALID_ID || sn_obj_width(module, condition) == 1)
            return condition;
        return sn_module_add_operator(module, SN_REDUCE_OR, 1, false, 1, &condition, nullptr);
    }

    std::optional<sn_lvalue_t> analyze_lvalue(const Expression& expression, std::string& error,
                                              bool split_packed_elements = false) const
    {
        sn_lvalue_context_t context;
        context.constant_integer = [&](const Expression& value) { return constant_integer(value); };
        context.is_memory = [&](const ValueSymbol& symbol) { return memories.contains(&symbol); };
        context.split_packed_elements = split_packed_elements;
        return sn_lvalue_analyze(expression, context, error);
    }

    static bool analyzed_lvalue_has_memory(const sn_lvalue_t& lvalue)
    {
        if (std::holds_alternative<sn_lvalue_t::memory_element_t>(lvalue.descriptor))
            return true;
        if (const auto* select = std::get_if<sn_lvalue_t::select_t>(&lvalue.descriptor))
            return analyzed_lvalue_has_memory(*select->inner);
        if (const auto* member = std::get_if<sn_lvalue_t::member_t>(&lvalue.descriptor))
            return analyzed_lvalue_has_memory(*member->inner);
        if (const auto* stream = std::get_if<sn_lvalue_t::stream_t>(&lvalue.descriptor))
            return analyzed_lvalue_has_memory(*stream->inner);
        if (const auto* concat = std::get_if<sn_lvalue_t::concat_t>(&lvalue.descriptor))
            for (const sn_lvalue_t& element : concat->elements)
                if (analyzed_lvalue_has_memory(element))
                    return true;
        return false;
    }

    sn_obj_id_t reorder_stream_value(sn_obj_id_t value, uint32_t slice_size)
    {
        uint32_t bits = sn_obj_width(module, value);
        if (!bits || !slice_size || bits % slice_size)
            return SN_INVALID_ID;
        uint32_t count = bits / slice_size;
        if (count == 1)
            return value;
        std::vector<sn_obj_id_t> slices;
        slices.reserve(count);
        for (uint32_t slice = 0; slice < count; slice++)
        {
            uint32_t offset = bits - (slice + 1) * slice_size;
            slices.push_back(sn_module_add_slice(module, value, int32_t(offset + slice_size - 1),
                                                 int32_t(offset), nullptr));
        }
        return sn_module_add_concat(module, count, slices.data(), nullptr);
    }

    bool static_lvalue_span(const sn_lvalue_t& lvalue, const ValueSymbol*& symbol, uint32_t& offset,
                            uint64_t accumulated = 0) const
    {
        if (const auto* variable = std::get_if<sn_lvalue_t::variable_t>(&lvalue.descriptor))
        {
            if (accumulated > UINT32_MAX)
                return false;
            symbol = variable->symbol;
            offset = uint32_t(accumulated);
            return true;
        }
        if (const auto* element = std::get_if<sn_lvalue_t::array_element_t>(&lvalue.descriptor))
        {
            const Type& type = element->symbol->getType();
            if (!element->constant_index || !type.hasFixedRange() || *element->constant_index < INT32_MIN ||
                *element->constant_index > INT32_MAX)
                return false;
            ConstantRange range = type.getFixedRange();
            if (!range.containsPoint(int32_t(*element->constant_index)))
                return false;
            uint64_t result = accumulated +
                              uint64_t(range.translateIndex(int32_t(*element->constant_index))) * lvalue.width;
            if (result > UINT32_MAX)
                return false;
            symbol = element->symbol;
            offset = uint32_t(result);
            return true;
        }
        if (const auto* select = std::get_if<sn_lvalue_t::select_t>(&lvalue.descriptor))
        {
            auto selected_offset = static_select_offset(*select, lvalue.width);
            return selected_offset &&
                   static_lvalue_span(*select->inner, symbol, offset, accumulated + *selected_offset);
        }
        if (const auto* member = std::get_if<sn_lvalue_t::member_t>(&lvalue.descriptor))
            return static_lvalue_span(*member->inner, symbol, offset, accumulated + member->bit_offset);
        return false;
    }

    bool lower_structured_range(const ValueSymbol& symbol, uint32_t offset, uint32_t bits)
    {
        auto drivers = structured_drivers.find(&symbol);
        if (drivers == structured_drivers.end())
            return true;
        for (const AssignmentExpression* assignment : drivers->second)
        {
            std::string error;
            auto lvalue = analyze_lvalue(assignment->left(), error);
            const ValueSymbol* root = nullptr;
            uint32_t driver_offset = 0;
            if (!lvalue || !static_lvalue_span(*lvalue, root, driver_offset) || root != &symbol)
                continue;
            if (uint64_t(offset) < uint64_t(driver_offset) + lvalue->width &&
                uint64_t(driver_offset) < uint64_t(offset) + bits &&
                !lower_structured_assignment(*assignment))
                return false;
        }
        return true;
    }

    std::optional<uint32_t> static_select_offset(const sn_lvalue_t::select_t& select,
                                                 uint32_t element_width = 1) const
    {
        if (!select.constant_selector || !select.constant_right || !select.input_type ||
            !select.input_type->hasFixedRange())
            return std::nullopt;
        ConstantRange input_range = select.input_type->getFixedRange();
        if (select.element)
        {
            if (*select.constant_selector < INT32_MIN || *select.constant_selector > INT32_MAX ||
                !input_range.containsPoint(int32_t(*select.constant_selector)))
                return std::nullopt;
            int32_t offset = input_range.translateIndex(int32_t(*select.constant_selector));
            return offset < 0 || uint64_t(offset) * element_width > UINT32_MAX
                       ? std::nullopt
                       : std::optional<uint32_t>(uint32_t(offset) * element_width);
        }

        if (*select.constant_selector < INT32_MIN || *select.constant_selector > INT32_MAX ||
            *select.constant_right < INT32_MIN || *select.constant_right > INT32_MAX)
            return std::nullopt;
        ConstantRange selected{int32_t(*select.constant_selector), int32_t(*select.constant_right)};
        if (select.selection_kind != RangeSelectionKind::Simple)
        {
            if (*select.constant_selector < INT32_MIN || *select.constant_selector > INT32_MAX ||
                *select.constant_right <= 0 || *select.constant_right > INT32_MAX)
                return std::nullopt;
            auto range = ConstantRange::getIndexedRange(int32_t(*select.constant_selector),
                                                        int32_t(*select.constant_right), input_range.isDescending(),
                                                        select.selection_kind == RangeSelectionKind::IndexedUp);
            if (!range)
                return std::nullopt;
            selected = *range;
        }
        if (!input_range.containsPoint(selected.left) || !input_range.containsPoint(selected.right))
            return std::nullopt;
        int32_t ordinal = input_range.translateIndex(selected.right);
        const Type* input_element = select.input_type->getArrayElementType();
        uint32_t stride = input_element ? width(*input_element) : 1;
        return ordinal < 0 || !stride || uint64_t(ordinal) * stride > UINT32_MAX
                   ? std::nullopt
                   : std::optional<uint32_t>(uint32_t(ordinal) * stride);
    }

    static bool add_partial_driver(std::vector<PartialDriver>& drivers, uint32_t total_width, uint32_t offset,
                                   uint32_t part_width, sn_obj_id_t value)
    {
        if (!part_width || uint64_t(offset) + part_width > total_width)
            return false;
        for (const PartialDriver& driver : drivers)
            if (uint64_t(offset) < uint64_t(driver.offset) + driver.width &&
                uint64_t(driver.offset) < uint64_t(offset) + part_width)
                return false;
        drivers.push_back({offset, part_width, value});
        return true;
    }

    sn_obj_id_t materialize_partial_drivers(uint32_t total_width, bool is_signed,
                                            const std::vector<PartialDriver>& drivers)
    {
        // Drivers are disjoint. Concatenation expresses wiring without introducing
        // a word-wide Boolean dependency on every neighboring driver.
        auto ordered = drivers;
        std::sort(ordered.begin(), ordered.end(), [](const auto& a, const auto& b) {
            return a.offset < b.offset;
        });
        std::vector<sn_obj_id_t> parts;
        uint32_t cursor = 0;
        auto pad = [&](uint32_t bits) {
            if (bits)
            {
                std::vector<uint32_t> words(sn_const_word_count(bits));
                parts.push_back(sn_module_add_const(module, bits, false, words.data(), nullptr));
            }
        };
        for (const PartialDriver& driver : ordered)
        {
            assert(driver.offset >= cursor && uint64_t(driver.offset) + driver.width <= total_width);
            pad(driver.offset - cursor);
            parts.push_back(driver.value);
            cursor = driver.offset + driver.width;
        }
        pad(total_width - cursor);
        sn_obj_id_t result = parts.size() == 1 ? parts[0]
            : sn_module_add_concat(module, uint32_t(parts.size()), parts.data(), nullptr);
        // Preserve the interpretation without changing a shared driver's attributes.
        return sn_obj_is_signed(module, result) == is_signed ? result
            : sn_module_add_operator(module, SN_POS, total_width, is_signed, 1, &result, nullptr);
    }

    static const ValueSymbol* interface_member_value(const Symbol* connection,
                                                     const ModportPortSymbol& member)
    {
        if (const auto* inst = connection ? connection->as_if<InstanceSymbol>() : nullptr)
            for (const Symbol& symbol : inst->body.members())
                if (symbol.name == member.name)
                    if (const auto* value = symbol.as_if<ValueSymbol>())
                        return value;
        return member.internalSymbol ? member.internalSymbol->as_if<ValueSymbol>() : nullptr;
    }

    template<typename Callback>
    bool for_each_interface_member(const InterfacePortSymbol& port, const Symbol* connection,
                                   const ModportSymbol* modport, Callback&& callback) const
    {
        if (!connection || !modport)
        {
            std::fprintf(stderr, "sn-slang: interface port '%.*s' has no concrete modport connection\n",
                         int(port.name.size()), port.name.data());
            return false;
        }
        std::vector<const InstanceSymbol*> instances;
        auto collect_instances = [&](auto&& self, const Symbol& symbol) -> void {
            if (const auto* inst = symbol.as_if<InstanceSymbol>())
            {
                instances.push_back(inst);
                return;
            }
            if (const auto* array = symbol.as_if<InstanceArraySymbol>())
                for (const Symbol* element : array->elements)
                    if (element)
                        self(self, *element);
        };
        collect_instances(collect_instances, *connection);
        if (instances.empty())
        {
            std::fprintf(stderr, "sn-slang: interface port '%.*s' does not connect to an interface instance\n",
                         int(port.name.size()), port.name.data());
            return false;
        }
        for (uint32_t index = 0; index < instances.size(); index++)
        {
            for (const Symbol& symbol : modport->members())
            {
                const auto* member = symbol.as_if<ModportPortSymbol>();
                if (!member)
                    continue;
                const ValueSymbol* value = interface_member_value(instances[index], *member);
                if (!value || is_zero_width(member->getType()))
                    continue;
                if (!callback(*member, *value, index, uint32_t(instances.size())))
                    return false;
            }
        }
        return true;
    }

    bool add_inputs(const InstanceBodySymbol& body)
    {
        for (const Symbol* symbol : body.getPortList())
        {
            const auto* port = symbol->as_if<PortSymbol>();
            if (!port)
            {
                if (const auto* interface_port = symbol->as_if<InterfacePortSymbol>())
                {
                    auto [connection, modport] = interface_port->getConnection();
                    if (!for_each_interface_member(
                            *interface_port, connection, modport, [&](const ModportPortSymbol& member,
                                                                     const ValueSymbol& value, uint32_t index,
                                                                     uint32_t count) {
                            if (member.direction != ArgumentDirection::In &&
                                member.direction != ArgumentDirection::InOut)
                                return true;
                            std::string name(interface_port->name);
                            if (count > 1)
                                name += "[" + std::to_string(index) + "]";
                            name += ".";
                            name += member.name;
                            sn_obj_id_t input = sn_module_add_pi(module, width(member.getType()),
                                                                 member.getType().isSigned(), name.c_str());
                            add_metadata(input, value);
                            values.emplace(&value, input);
                            if (member.direction == ArgumentDirection::InOut)
                            {
                                inout_symbols.emplace(&member);
                                inout_symbols.emplace(&value);
                            }
                            return true;
                        }))
                        return false;
                    continue;
                }
                std::fprintf(stderr, "sn-slang: only simple data ports are currently supported\n");
                return false;
            }
            // Parameterized cache and bus wrappers sometimes retain zero-width ports in inactive configurations.
            // They carry no bits and therefore have no SN interface object.
            if (is_zero_width(port->getType()))
                continue;
            if (port->direction != ArgumentDirection::In && port->direction != ArgumentDirection::InOut)
                continue;
            const auto* value = port->internalSymbol ? port->internalSymbol->as_if<ValueSymbol>() : nullptr;
            uint32_t bits = width(port->getType());
            if (!value || !bits)
            {
                std::fprintf(stderr, "sn-slang: input port '%.*s' has an unsupported connection or type\n",
                             int(port->name.size()), port->name.data());
                return false;
            }
            std::string name(port->name);
            sn_obj_id_t input = sn_module_add_pi(module, bits, port->getType().isSigned(), name.c_str());
            add_metadata(input, *value);
            values.emplace(value, input);
            if (port->direction == ArgumentDirection::InOut)
                inout_symbols.emplace(value);
        }
        return true;
    }

    bool collect_port_initializers(const InstanceBodySymbol& body)
    {
        for (const Symbol* symbol : body.getPortList())
        {
            const auto* port = symbol->as_if<PortSymbol>();
            if (!port || port->direction == ArgumentDirection::In)
                continue;
            if (is_zero_width(port->getType()))
                continue;
            const auto* value = port->internalSymbol ? port->internalSymbol->as_if<ValueSymbol>() : nullptr;
            const Expression* initializer = port->getInitializer();
            if (!initializer)
                continue;
            if (!value)
            {
                std::fprintf(stderr, "sn-slang: initialized output port '%.*s' has no internal value\n",
                             int(port->name.size()), port->name.data());
                return false;
            }
            if (!collected_declaration_initializers.emplace(value).second)
                continue;
            if (!value->as_if<VariableSymbol>())
            {
                if (values.contains(value) || !assignments.emplace(value, initializer).second)
                {
                    std::fprintf(stderr, "sn-slang: signal '%.*s' has multiple drivers\n",
                                 int(value->name.size()), value->name.data());
                    return false;
                }
                assignment_order.push_back(value);
                continue;
            }
            if (value->getType().isUnpackedArray() && value->getType().hasFixedRange())
            {
                std::fprintf(stderr, "sn-slang: initialized memories are not yet supported\n");
                return false;
            }
            variable_initializers.emplace_back(value, initializer);
        }
        return true;
    }

    static bool increment_or_decrement(UnaryOperator op, bool& decrement)
    {
        switch (op)
        {
        case UnaryOperator::Preincrement:
        case UnaryOperator::Postincrement:
            decrement = false;
            return true;
        case UnaryOperator::Predecrement:
        case UnaryOperator::Postdecrement:
            decrement = true;
            return true;
        default:
            return false;
        }
    }

    sn_obj_id_t mask_constant(uint32_t bits, bool ones)
    {
        std::vector<uint32_t> words(sn_const_word_count(bits), ones ? UINT32_MAX : 0);
        if (ones && (bits & 31))
            words.back() &= (uint32_t(1) << (bits & 31)) - 1;
        return sn_module_add_const(module, bits, false, words.data(), nullptr);
    }

    void propagate_concat_unknowns(sn_obj_id_t result, const std::vector<sn_obj_id_t>& fanins)
    {
        bool has_unknown = false;
        for (sn_obj_id_t fanin : fanins)
            has_unknown = has_unknown || constant_valid_masks.contains(fanin);
        if (!has_unknown)
            return;

        std::vector<sn_obj_id_t> valid_fanins;
        std::vector<sn_obj_id_t> z_fanins;
        valid_fanins.reserve(fanins.size());
        z_fanins.reserve(fanins.size());
        for (sn_obj_id_t fanin : fanins)
        {
            uint32_t bits = sn_obj_width(module, fanin);
            auto valid = constant_valid_masks.find(fanin);
            auto z = constant_z_masks.find(fanin);
            valid_fanins.push_back(valid == constant_valid_masks.end() ? mask_constant(bits, true)
                                                                       : valid->second);
            z_fanins.push_back(z == constant_z_masks.end() ? mask_constant(bits, false) : z->second);
        }
        constant_valid_masks[result] =
            sn_module_add_concat(module, uint32_t(valid_fanins.size()), valid_fanins.data(), nullptr);
        constant_z_masks[result] =
            sn_module_add_concat(module, uint32_t(z_fanins.size()), z_fanins.data(), nullptr);
    }

    void propagate_repeat_unknowns(sn_obj_id_t result, sn_obj_id_t value, uint32_t count)
    {
        auto valid = constant_valid_masks.find(value);
        if (valid == constant_valid_masks.end())
            return;
        constant_valid_masks[result] = sn_module_add_repeat(module, valid->second, count, nullptr);
        auto z = constant_z_masks.find(value);
        sn_obj_id_t z_mask = z == constant_z_masks.end() ? mask_constant(sn_obj_width(module, value), false)
                                                         : z->second;
        constant_z_masks[result] = sn_module_add_repeat(module, z_mask, count, nullptr);
    }

    void propagate_mux_unknowns(sn_obj_id_t result, sn_obj_id_t select, sn_obj_id_t selected,
                                sn_obj_id_t default_value)
    {
        auto selected_valid_it = constant_valid_masks.find(selected);
        auto default_valid_it = constant_valid_masks.find(default_value);
        if (selected_valid_it == constant_valid_masks.end() &&
            default_valid_it == constant_valid_masks.end())
            return;
        uint32_t bits = sn_obj_width(module, result);
        sn_obj_id_t all_valid = mask_constant(bits, true);
        sn_obj_id_t no_z = mask_constant(bits, false);
        sn_obj_id_t selected_valid = selected_valid_it == constant_valid_masks.end() ? all_valid
                                                                                      : selected_valid_it->second;
        sn_obj_id_t default_valid = default_valid_it == constant_valid_masks.end() ? all_valid
                                                                                    : default_valid_it->second;
        auto selected_z_it = constant_z_masks.find(selected);
        auto default_z_it = constant_z_masks.find(default_value);
        sn_obj_id_t selected_z = selected_z_it == constant_z_masks.end() ? no_z : selected_z_it->second;
        sn_obj_id_t default_z = default_z_it == constant_z_masks.end() ? no_z : default_z_it->second;
        constant_valid_masks[result] = sn_module_add_mux(module, select, selected_valid, default_valid, nullptr);
        constant_z_masks[result] = sn_module_add_mux(module, select, selected_z, default_z, nullptr);
    }

    sn_obj_id_t lower_equality(BinaryOperator op, sn_obj_id_t left, sn_obj_id_t right)
    {
        uint32_t bits = sn_obj_width(module, left);
        if (!bits || sn_obj_width(module, right) != bits)
            return SN_INVALID_ID;

        bool inequality = op == BinaryOperator::Inequality || op == BinaryOperator::CaseInequality ||
                          op == BinaryOperator::WildcardInequality;
        auto left_valid_it = constant_valid_masks.find(left);
        auto right_valid_it = constant_valid_masks.find(right);
        if (left_valid_it == constant_valid_masks.end() && right_valid_it == constant_valid_masks.end())
        {
            sn_obj_id_t fanins[2] = {left, right};
            return sn_module_add_operator(module, inequality ? SN_NE : SN_EQ, 1, false, 2, fanins, nullptr);
        }

        sn_obj_id_t all_valid = mask_constant(bits, true);
        sn_obj_id_t no_z = mask_constant(bits, false);
        sn_obj_id_t left_valid = left_valid_it == constant_valid_masks.end() ? all_valid : left_valid_it->second;
        sn_obj_id_t right_valid = right_valid_it == constant_valid_masks.end() ? all_valid : right_valid_it->second;
        auto left_z_it = constant_z_masks.find(left);
        auto right_z_it = constant_z_masks.find(right);
        sn_obj_id_t left_z = left_z_it == constant_z_masks.end() ? no_z : left_z_it->second;
        sn_obj_id_t right_z = right_z_it == constant_z_masks.end() ? no_z : right_z_it->second;

        auto binary = [&](sn_obj_type_t type, uint32_t width, sn_obj_id_t a, sn_obj_id_t b) {
            sn_obj_id_t fanins[2] = {a, b};
            return sn_module_add_operator(module, type, width, false, 2, fanins, nullptr);
        };
        auto unary = [&](sn_obj_type_t type, uint32_t width, sn_obj_id_t value) {
            return sn_module_add_operator(module, type, width, false, 1, &value, nullptr);
        };
        auto reduce_and = [&](sn_obj_id_t value) { return unary(SN_REDUCE_AND, 1, value); };
        auto reduce_or = [&](sn_obj_id_t value) { return unary(SN_REDUCE_OR, 1, value); };

        if (op == BinaryOperator::Equality || op == BinaryOperator::Inequality)
        {
            sn_obj_id_t both_valid = binary(SN_BIT_AND, bits, left_valid, right_valid);
            sn_obj_id_t difference = binary(SN_BIT_XOR, bits, left, right);
            sn_obj_id_t known_difference = binary(SN_BIT_AND, bits, difference, both_valid);
            sn_obj_id_t mismatch = reduce_or(known_difference);
            if (inequality)
                return mismatch;
            sn_obj_id_t known = reduce_and(both_valid);
            sn_obj_id_t matches = unary(SN_LOG_NOT, 1, mismatch);
            return binary(SN_LOG_AND, 1, known, matches);
        }

        if (op == BinaryOperator::WildcardEquality || op == BinaryOperator::WildcardInequality)
        {
            sn_obj_id_t right_invalid = unary(SN_BIT_NOT, bits, right_valid);
            sn_obj_id_t left_known_or_wild = binary(SN_BIT_OR, bits, left_valid, right_invalid);
            sn_obj_id_t difference = binary(SN_BIT_XOR, bits, left, right);
            difference = binary(SN_BIT_AND, bits, difference, right_valid);
            difference = binary(SN_BIT_AND, bits, difference, left_valid);
            sn_obj_id_t mismatch = reduce_or(difference);
            if (inequality)
                return mismatch;
            sn_obj_id_t known = reduce_and(left_known_or_wild);
            sn_obj_id_t matches = unary(SN_LOG_NOT, 1, mismatch);
            return binary(SN_LOG_AND, 1, known, matches);
        }

        assert(op == BinaryOperator::CaseEquality || op == BinaryOperator::CaseInequality);
        sn_obj_id_t data_difference = binary(SN_BIT_XOR, bits, left, right);
        sn_obj_id_t both_valid = binary(SN_BIT_AND, bits, left_valid, right_valid);
        sn_obj_id_t known_difference = binary(SN_BIT_AND, bits, data_difference, both_valid);
        sn_obj_id_t validity_difference = binary(SN_BIT_XOR, bits, left_valid, right_valid);
        sn_obj_id_t either_valid = binary(SN_BIT_OR, bits, left_valid, right_valid);
        sn_obj_id_t both_unknown = unary(SN_BIT_NOT, bits, either_valid);
        sn_obj_id_t z_difference = binary(SN_BIT_XOR, bits, left_z, right_z);
        z_difference = binary(SN_BIT_AND, bits, z_difference, both_unknown);
        sn_obj_id_t mismatch = binary(SN_BIT_OR, bits, known_difference, validity_difference);
        mismatch = binary(SN_BIT_OR, bits, mismatch, z_difference);
        mismatch = reduce_or(mismatch);
        return inequality ? mismatch : unary(SN_LOG_NOT, 1, mismatch);
    }

    bool function_call_is_cacheable(const SubroutineSymbol& subroutine)
    {
        auto known = function_cacheable.find(&subroutine);
        if (known != function_cacheable.end())
            return known->second;
        if (!checking_function_cacheability.emplace(&subroutine).second)
            return false;

        struct Cacheability : ASTVisitor<Cacheability,
                                         VisitFlags::Statements | VisitFlags::Expressions>
        {
            ModuleImporter& importer;
            const SubroutineSymbol& subroutine;
            bool cacheable = true;

            Cacheability(ModuleImporter& importer, const SubroutineSymbol& subroutine) :
                importer(importer), subroutine(subroutine)
            {
            }

            bool is_local(const Symbol& symbol) const
            {
                const Scope* scope = symbol.getParentScope();
                while (scope)
                {
                    const Symbol& parent = scope->asSymbol();
                    if (&parent == &subroutine)
                        return true;
                    scope = parent.getParentScope();
                }
                return false;
            }

            void handle(const ValueExpressionBase& expression)
            {
                const Symbol& symbol = expression.symbol;
                if (const auto* variable = symbol.as_if<VariableSymbol>())
                    if (!is_local(symbol) || variable->lifetime != VariableLifetime::Automatic)
                        cacheable = false;
                if (symbol.kind == SymbolKind::Net || symbol.kind == SymbolKind::Port ||
                    symbol.kind == SymbolKind::ClockVar)
                    cacheable = false;
            }

            void handle(const CallExpression& call)
            {
                for (const Expression* argument : call.arguments())
                    argument->visit(*this);
                if (call.isSystemCall())
                    return;
                const SubroutineSymbol* called = std::get<0>(call.subroutine);
                if (!called || !importer.function_call_is_cacheable(*called))
                    cacheable = false;
            }
        };

        bool cacheable = subroutine.subroutineKind == SubroutineKind::Function && subroutine.returnValVar;
        for (const FormalArgumentSymbol* argument : subroutine.getArguments())
            cacheable = cacheable && argument->direction == ArgumentDirection::In &&
                        argument->lifetime == VariableLifetime::Automatic;
        if (cacheable)
        {
            Cacheability analysis(*this, subroutine);
            subroutine.getBody().visit(analysis);
            cacheable = analysis.cacheable;
        }
        checking_function_cacheability.erase(&subroutine);
        function_cacheable.emplace(&subroutine, cacheable);
        return cacheable;
    }

    sn_obj_id_t lower_expression(const Expression& expression)
    {
        if (auto primitive = primitive_output_expressions.find(&expression);
            primitive != primitive_output_expressions.end())
            return lower_primitive_output(primitive->second);
        // Mapped instance outputs are bound before inputs are connected. Resolve
        // static selections from those drivers, never from the aggregate vector.
        // Procedural / structured assignments have their own ordering rules.
        if (!active_procedural_values &&
            (expression.as_if<ElementSelectExpression>() || expression.as_if<RangeSelectExpression>()))
        {
            std::string error;
            auto lvalue = analyze_lvalue(expression, error);
            const ValueSymbol* root = nullptr;
            uint32_t offset = 0;
            if (lvalue && static_lvalue_span(*lvalue, root, offset) && root &&
                !assignments.contains(root) &&
                !primitive_value_drivers.contains(root))
            {
                if (!lower_structured_range(*root, offset, width(*expression.type)))
                    return SN_INVALID_ID;
                auto it = partial_value_drivers.find(root);
                if (it != partial_value_drivers.end())
                {
                    uint32_t bits = width(*expression.type);
                    std::vector<PartialDriver> pieces;
                    uint32_t covered = 0;
                    for (const auto& driver : it->second)
                    {
                        uint64_t first = std::max(uint64_t(offset), uint64_t(driver.offset));
                        uint64_t end = std::min(uint64_t(offset) + bits,
                                                uint64_t(driver.offset) + driver.width);
                        if (first < end)
                        {
                            uint32_t part = uint32_t(end - first);
                            uint32_t start = uint32_t(first - driver.offset);
                            sn_obj_id_t value = start == 0 && part == driver.width ? driver.value
                                : sn_module_add_slice(module, driver.value, int32_t(start + part - 1),
                                                      int32_t(start), nullptr);
                            pieces.push_back({uint32_t(first - offset), part, value});
                            covered += part;
                        }
                    }
                    if (bits && covered == bits)
                        return materialize_partial_drivers(bits, expression.type->isSigned(), pieces);
                }
            }
        }
        if (const auto* hierarchical = expression.as_if<HierarchicalValueExpression>();
            hierarchical && crosses_retained_module_boundary(*hierarchical))
        {
            if (const Expression* connection = retained_boundary_port_connection(*hierarchical))
                return lower_expression(*connection);
            report_timing_error(expression.sourceRange.start(),
                                "hierarchical reference crosses a retained module boundary");
            return SN_INVALID_ID;
        }
        EvalContext local_constant_context(*body->parentInstance);
        EvalContext& constant_context = active_constant_context ? *active_constant_context : local_constant_context;
        ConstantValue constant = expression.eval(constant_context);
        if (constant && constant.isInteger() && !equality_fold_is_unreliable(expression, constant_context))
            return lower_integer(constant.integer(), *expression.type);
        if (constant && expression.type->isFixedSize() && !constant.isInteger())
        {
            ConstantValue packed = Bitstream::convertToBitVector(std::move(constant), expression.sourceRange,
                                                                  constant_context);
            if (packed && packed.isInteger())
                return lower_integer(packed.integer(), *expression.type);
        }

        if (const ValueSymbol* value = referenced_value(expression))
            return lower_value(*value);

        if (const auto* assignment = expression.as_if<AssignmentExpression>())
        {
            if (assignment->isLValueArg())
                return lower_expression(assignment->left());
            const Expression* previous_lvalue = active_lvalue_expression;
            active_lvalue_expression = &assignment->left();
            sn_obj_id_t result = lower_expression(assignment->right());
            active_lvalue_expression = previous_lvalue;
            return result;
        }

        if (expression.as_if<LValueReferenceExpression>())
        {
            if (!active_lvalue_expression)
            {
                std::fprintf(stderr, "sn-slang: lvalue reference appears outside an assignment expression\n");
                return SN_INVALID_ID;
            }
            return lower_expression(*active_lvalue_expression);
        }

        if (const auto* conversion = expression.as_if<ConversionExpression>())
        {
            sn_obj_id_t operand = lower_expression(conversion->operand());
            uint32_t bits = width(*conversion->type);
            if (operand == SN_INVALID_ID || !bits)
                return SN_INVALID_ID;
            uint32_t operand_bits = sn_obj_width(module, operand);
            bool operand_signed = sn_obj_is_signed(module, operand);
            bool target_signed = conversion->type->isSigned();
            if (operand_bits == bits && operand_signed == target_signed)
                return operand;
            sn_obj_id_t fanin = operand;
            // An explicit cast or an assignment-style conversion extends by the operand's own
            // signedness, and the target signedness only applies to the widened value, so
            // int'(unsigned_5) zero-extends. A conversion propagated from a mixed-signedness
            // expression context changes the signedness first and then extends, so a signed
            // operand widened to an unsigned context zero-extends as well.
            if (bits > operand_bits && operand_signed != target_signed &&
                conversion->conversionKind != ConversionKind::Propagated)
                fanin = sn_module_add_operator(module, SN_CAST, bits, operand_signed, 1, &fanin, nullptr);
            sn_obj_id_t result = sn_module_add_operator(module, SN_CAST, bits, target_signed, 1, &fanin, nullptr);
            if (sn_obj_width(module, operand) == bits)
            {
                auto valid = constant_valid_masks.find(operand);
                auto z = constant_z_masks.find(operand);
                if (valid != constant_valid_masks.end())
                    constant_valid_masks[result] = valid->second;
                if (z != constant_z_masks.end())
                    constant_z_masks[result] = z->second;
            }
            return result;
        }

        if (const auto* call = expression.as_if<CallExpression>())
        {
            std::string_view name = call->getSubroutineName();
            if (call->isSystemCall() && call->arguments().size() == 1 &&
                (name == "$signed" || name == "$unsigned"))
            {
                sn_obj_id_t operand = lower_expression(*call->arguments()[0]);
                uint32_t bits = width(*call->type);
                if (operand == SN_INVALID_ID || !bits)
                    return SN_INVALID_ID;
                if (sn_obj_width(module, operand) == bits &&
                    sn_obj_is_signed(module, operand) == call->type->isSigned())
                    return operand;
                return sn_module_add_operator(module, SN_CAST, bits, call->type->isSigned(), 1, &operand, nullptr);
            }
            if (!call->isSystemCall())
            {
                const SubroutineSymbol* subroutine = std::get<0>(call->subroutine);
                auto formals = subroutine->getArguments();
                if (subroutine->subroutineKind != SubroutineKind::Function || !subroutine->returnValVar ||
                    formals.size() != call->arguments().size() || active_subroutines.contains(subroutine))
                {
                    std::fprintf(stderr,
                                 "sn-slang: unsupported or recursive call '%.*s' (kind=%u, return=%u, "
                                 "formals=%zu, actuals=%zu, active=%u)\n",
                                 int(name.size()), name.data(), unsigned(subroutine->subroutineKind),
                                 subroutine->returnValVar != nullptr, formals.size(), call->arguments().size(),
                                 active_subroutines.contains(subroutine));
                    return SN_INVALID_ID;
                }
                ProceduralValues function_values;
                uint32_t result_bits = width(subroutine->returnValVar->getType());
                std::vector<uint32_t> result_words(sn_const_word_count(result_bits));
                function_values.values.emplace(
                    subroutine->returnValVar,
                    sn_module_add_const(module, result_bits, subroutine->returnValVar->getType().isSigned(),
                                        result_words.data(), nullptr));
                std::vector<sn_obj_id_t> argument_values;
                argument_values.reserve(formals.size());
                for (size_t i = 0; i < formals.size(); i++)
                {
                    ArgumentDirection direction = formals[i]->direction;
                    sn_obj_id_t argument = SN_INVALID_ID;
                    if (direction == ArgumentDirection::In || direction == ArgumentDirection::InOut ||
                        direction == ArgumentDirection::Ref)
                        argument = lower_expression(*call->arguments()[i]);
                    else if (direction == ArgumentDirection::Out)
                    {
                        uint32_t bits = width(formals[i]->getType());
                        std::vector<uint32_t> words(sn_const_word_count(bits));
                        argument = sn_module_add_const(module, bits, formals[i]->getType().isSigned(), words.data(),
                                                       nullptr);
                    }
                    if (argument == SN_INVALID_ID)
                        return SN_INVALID_ID;
                    function_values.values.emplace(formals[i], argument);
                    argument_values.push_back(argument);
                }
                bool cacheable = function_call_is_cacheable(*subroutine);
                if (cacheable)
                {
                    auto function = function_results.find(subroutine);
                    if (function != function_results.end())
                    {
                        auto cached = function->second.find(argument_values);
                        if (cached != function->second.end())
                            return cached->second;
                    }
                }
                active_subroutines.emplace(subroutine);
                const ProceduralValues* saved_values = active_procedural_values;
                const ProceduralValues* saved_nonblocking = nonblocking_read_values;
                const VariableSymbol* saved_return_value = active_return_value;
                nonblocking_read_values = nullptr;
                active_return_value = subroutine->returnValVar;
                bool lowered = lower_statement(subroutine->getBody(), function_values);
                active_procedural_values = saved_values;
                nonblocking_read_values = saved_nonblocking;
                active_return_value = saved_return_value;
                active_subroutines.erase(subroutine);
                if (lowered)
                {
                    for (size_t i = 0; i < formals.size(); i++)
                    {
                        ArgumentDirection direction = formals[i]->direction;
                        if (direction != ArgumentDirection::Out && direction != ArgumentDirection::InOut &&
                            direction != ArgumentDirection::Ref)
                            continue;
                        auto value = function_values.values.find(formals[i]);
                        const auto* assignment = call->arguments()[i]->as_if<AssignmentExpression>();
                        const Expression* lvalue = assignment && assignment->isLValueArg()
                                                       ? &assignment->left()
                                                       : call->arguments()[i];
                        if (!active_procedural_writes || value == function_values.values.end() ||
                            !assign_procedural_lvalue(*lvalue, value->second, *active_procedural_writes))
                        {
                            std::fprintf(stderr,
                                         "sn-slang: function '%.*s' output argument has an unsupported lvalue\n",
                                         int(name.size()), name.data());
                            return SN_INVALID_ID;
                        }
                    }
                }
                auto result = function_values.values.find(subroutine->returnValVar);
                if (result == function_values.values.end())
                {
                    ConstantRange result_range = subroutine->returnValVar->getType().getFixedRange();
                    std::vector<sn_obj_id_t> bits;
                    bits.reserve(result_bits);
                    for (uint32_t offset = 0; offset < result_bits; offset++)
                    {
                        int64_t bit_index = result_range.isDescending() ? int64_t(result_range.right) + offset
                                                                        : int64_t(result_range.right) - offset;
                        auto bit = function_values.selected_values.find({subroutine->returnValVar, bit_index});
                        if (bit == function_values.selected_values.end())
                            break;
                        bits.push_back(bit->second);
                    }
                    if (bits.size() == result_bits && result_bits)
                    {
                        function_values.values.emplace(
                            subroutine->returnValVar,
                            sn_module_add_concat(module, result_bits, bits.data(), nullptr));
                        result = function_values.values.find(subroutine->returnValVar);
                    }
                }
                if (!lowered || !function_values.memory_writes.empty() || result == function_values.values.end())
                {
                    std::fprintf(stderr, "sn-slang: function '%.*s' did not produce a supported return value\n",
                                 int(name.size()), name.data());
                    return SN_INVALID_ID;
                }
                if (cacheable)
                    function_results[subroutine].emplace(std::move(argument_values), result->second);
                return result->second;
            }
            std::string message = "unsupported call '" + std::string(name) + "'";
            report_timing_error(call->sourceRange.start(), message.c_str());
            return SN_INVALID_ID;
        }

        if (const auto* literal = expression.as_if<IntegerLiteral>())
            return lower_integer(literal->getValue(), *literal->type);

        if (const auto* unary = expression.as_if<UnaryExpression>())
        {
            sn_obj_type_t type = SN_NONE;
            switch (unary->op)
            {
            case UnaryOperator::Plus:
                type = SN_POS;
                break;
            case UnaryOperator::Minus:
                type = SN_NEG;
                break;
            case UnaryOperator::BitwiseNot:
                type = SN_BIT_NOT;
                break;
            case UnaryOperator::BitwiseAnd:
                type = SN_REDUCE_AND;
                break;
            case UnaryOperator::BitwiseOr:
                type = SN_REDUCE_OR;
                break;
            case UnaryOperator::BitwiseXor:
                type = SN_REDUCE_XOR;
                break;
            case UnaryOperator::BitwiseNand:
                type = SN_REDUCE_NAND;
                break;
            case UnaryOperator::BitwiseNor:
                type = SN_REDUCE_NOR;
                break;
            case UnaryOperator::BitwiseXnor:
                type = SN_REDUCE_XNOR;
                break;
            case UnaryOperator::LogicalNot:
                type = SN_LOG_NOT;
                break;
            default:
                std::fprintf(stderr, "sn-slang: unsupported unary operator %u\n", unsigned(unary->op));
                return SN_INVALID_ID;
            }
            sn_obj_id_t operand = lower_expression(unary->operand());
            uint32_t bits = width(*unary->type);
            if (operand == SN_INVALID_ID || !bits)
                return SN_INVALID_ID;
            return sn_module_add_operator(module, type, bits, unary->type->isSigned(), 1, &operand, nullptr);
        }

        if (const auto* binary = expression.as_if<BinaryExpression>())
        {
            if (binary->op == BinaryOperator::Divide || binary->op == BinaryOperator::Mod)
            {
                const Expression* divisor_expression = &binary->right();
                while (const auto* conversion = divisor_expression->as_if<ConversionExpression>())
                    divisor_expression = &conversion->operand();
                auto divisor = constant_integer(binary->right());
                uint32_t bits = width(*binary->type);
                if (divisor_expression->as_if<IntegerLiteral>() && divisor && *divisor == 0 && bits)
                {
                    std::vector<uint32_t> words(sn_const_word_count(bits));
                    return sn_module_add_const(module, bits, binary->type->isSigned(), words.data(), nullptr);
                }
            }

            // A vector assembled from individually assigned bits can have an
            // acyclic prefix dependency that looks cyclic at whole-vector
            // granularity. Preserve the constant mask and lower only the bits
            // that can actually influence this AND expression.
            if (binary->op == BinaryOperator::BinaryAnd)
            {
                auto lower_masked_selected = [&](const Expression& data_expression,
                                                 const Expression& mask_expression) -> sn_obj_id_t {
                    const Expression* data = &data_expression;
                    while (const auto* conversion = data->as_if<ConversionExpression>())
                        data = &conversion->operand();
                    const auto* named = data->as_if<NamedValueExpression>();
                    auto mask = constant_integer(mask_expression);
                    uint32_t bits = width(*binary->type);
                    if (!named || !mask || !bits || bits > 64 || width(named->symbol.getType()) != bits)
                        return SN_INVALID_ID;

                    ConstantRange range = named->symbol.getType().getFixedRange();
                    std::vector<SelectedValue> selected_bits;
                    selected_bits.reserve(bits);
                    for (uint32_t bit = 0; bit < bits; bit++)
                    {
                        int64_t index = range.isDescending() ? int64_t(range.right) + bit
                                                             : int64_t(range.right) - bit;
                        SelectedValue selected{&named->symbol, index};
                        if ((uint64_t(*mask) & (uint64_t(1) << bit)) &&
                            !selected_values.contains(selected) && !selected_assignments.contains(selected))
                            return SN_INVALID_ID;
                        selected_bits.push_back(selected);
                    }

                    uint32_t zero_word = 0;
                    sn_obj_id_t zero = sn_module_add_const(module, 1, false, &zero_word, nullptr);
                    std::vector<sn_obj_id_t> result_bits;
                    result_bits.reserve(bits);
                    for (uint32_t bit = 0; bit < bits; bit++)
                    {
                        if (uint64_t(*mask) & (uint64_t(1) << bit))
                        {
                            sn_obj_id_t selected = lower_selected(selected_bits[bit]);
                            if (selected == SN_INVALID_ID)
                                return SN_INVALID_ID;
                            result_bits.push_back(selected);
                        }
                        else
                            result_bits.push_back(zero);
                    }
                    return sn_module_add_concat(module, bits, result_bits.data(), nullptr);
                };

                sn_obj_id_t masked = lower_masked_selected(binary->left(), binary->right());
                if (masked == SN_INVALID_ID)
                    masked = lower_masked_selected(binary->right(), binary->left());
                if (masked != SN_INVALID_ID)
                    return masked;
            }

            sn_obj_type_t type = SN_NONE;
            switch (binary->op)
            {
            case BinaryOperator::Add:
                type = SN_ADD;
                break;
            case BinaryOperator::Subtract:
                type = SN_SUB;
                break;
            case BinaryOperator::Multiply:
                type = SN_MUL;
                break;
            case BinaryOperator::Divide:
                type = SN_DIV;
                break;
            case BinaryOperator::Mod:
                type = SN_MOD;
                break;
            case BinaryOperator::Power:
                type = SN_POW;
                break;
            case BinaryOperator::BinaryAnd:
                type = SN_BIT_AND;
                break;
            case BinaryOperator::BinaryOr:
                type = SN_BIT_OR;
                break;
            case BinaryOperator::BinaryXor:
                type = SN_BIT_XOR;
                break;
            case BinaryOperator::BinaryXnor:
                type = SN_BIT_XNOR;
                break;
            case BinaryOperator::Equality:
            case BinaryOperator::CaseEquality:
            case BinaryOperator::Inequality:
            case BinaryOperator::CaseInequality:
            case BinaryOperator::WildcardEquality:
            case BinaryOperator::WildcardInequality:
                break;
            case BinaryOperator::LogicalAnd:
                type = SN_LOG_AND;
                break;
            case BinaryOperator::LogicalOr:
                type = SN_LOG_OR;
                break;
            case BinaryOperator::LogicalShiftLeft:
                type = SN_SHL;
                break;
            case BinaryOperator::LogicalShiftRight:
                type = SN_SHR;
                break;
            case BinaryOperator::ArithmeticShiftLeft:
                type = SN_ASHL;
                break;
            case BinaryOperator::ArithmeticShiftRight:
                type = SN_ASHR;
                break;
            case BinaryOperator::GreaterThanEqual:
                type = SN_GE;
                break;
            case BinaryOperator::GreaterThan:
                type = SN_GT;
                break;
            case BinaryOperator::LessThanEqual:
                type = SN_LE;
                break;
            case BinaryOperator::LessThan:
                type = SN_LT;
                break;
            default:
                std::fprintf(stderr, "sn-slang: unsupported binary operator '%.*s'\n",
                             int(OpInfo::getText(binary->op).size()), OpInfo::getText(binary->op).data());
                return SN_INVALID_ID;
            }
            auto lower_mul_operand = [this](const Expression& expression) {
                // Slang propagates an assignment context through multiplication and represents the resulting
                // operand widening as implicit conversions.  SN_MUL keeps independently sized operands; its
                // output width records where the product is truncated or extended.  Remove only pure implicit
                // resizes that preserve signedness.  Explicit and mixed-signedness conversions remain semantic.
                const Expression* operand = &expression;
                while (const auto* conversion = operand->as_if<ConversionExpression>())
                {
                    if (!conversion->isImplicit() || !conversion->type->isIntegral() ||
                        !conversion->operand().type->isIntegral() ||
                        conversion->type->isSigned() != conversion->operand().type->isSigned())
                        break;
                    operand = &conversion->operand();
                }
                return lower_expression(*operand);
            };
            sn_obj_id_t fanins[2];
            if (binary->op == BinaryOperator::Multiply)
            {
                fanins[0] = lower_mul_operand(binary->left());
                fanins[1] = lower_mul_operand(binary->right());
            }
            else
            {
                fanins[0] = lower_expression(binary->left());
                fanins[1] = lower_expression(binary->right());
            }
            uint32_t bits = width(*binary->type);
            if (fanins[0] == SN_INVALID_ID || fanins[1] == SN_INVALID_ID || !bits)
                return SN_INVALID_ID;
            if (binary->op == BinaryOperator::Equality || binary->op == BinaryOperator::Inequality ||
                binary->op == BinaryOperator::CaseEquality || binary->op == BinaryOperator::CaseInequality ||
                binary->op == BinaryOperator::WildcardEquality || binary->op == BinaryOperator::WildcardInequality)
                return lower_equality(binary->op, fanins[0], fanins[1]);
            return sn_module_add_operator(module, type, bits, binary->type->isSigned(), 2, fanins, nullptr);
        }

        if (const auto* inside = expression.as_if<InsideExpression>())
        {
            sn_obj_id_t value = lower_expression(inside->left());
            if (value == SN_INVALID_ID || !inside->left().type->isIntegral())
                return SN_INVALID_ID;
            sn_obj_id_t result = SN_INVALID_ID;
            for (const Expression* item : inside->rangeList())
            {
                sn_obj_id_t hit = SN_INVALID_ID;
                if (const auto* range = item->as_if<ValueRangeExpression>())
                {
                    if (range->rangeKind != ValueRangeKind::Simple)
                    {
                        std::fprintf(stderr, "sn-slang: tolerance ranges in inside expressions are unsupported\n");
                        return SN_INVALID_ID;
                    }
                    sn_obj_id_t lower = lower_expression(range->left());
                    sn_obj_id_t upper = lower_expression(range->right());
                    if (lower == SN_INVALID_ID || upper == SN_INVALID_ID)
                        return SN_INVALID_ID;
                    sn_obj_id_t lower_fanins[2] = {value, lower};
                    sn_obj_id_t upper_fanins[2] = {value, upper};
                    sn_obj_id_t at_least = sn_module_add_operator(module, SN_GE, 1,
                                                                   range->left().type->isSigned(), 2,
                                                                   lower_fanins, nullptr);
                    sn_obj_id_t at_most = sn_module_add_operator(module, SN_LE, 1,
                                                                  range->right().type->isSigned(), 2,
                                                                  upper_fanins, nullptr);
                    sn_obj_id_t range_fanins[2] = {at_least, at_most};
                    hit = sn_module_add_operator(module, SN_LOG_AND, 1, false, 2, range_fanins, nullptr);
                }
                else
                {
                    sn_obj_id_t candidate = lower_expression(*item);
                    if (candidate == SN_INVALID_ID)
                        return SN_INVALID_ID;
                    hit = lower_equality(BinaryOperator::WildcardEquality, value, candidate);
                }
                if (result == SN_INVALID_ID)
                    result = hit;
                else
                {
                    sn_obj_id_t fanins[2] = {result, hit};
                    result = sn_module_add_operator(module, SN_LOG_OR, 1, false, 2, fanins, nullptr);
                }
            }
            if (result != SN_INVALID_ID)
                return result;
            uint32_t zero = 0;
            return sn_module_add_const(module, 1, false, &zero, nullptr);
        }

        if (const auto* streaming = expression.as_if<StreamingConcatenationExpression>())
        {
            std::vector<sn_obj_id_t> fanins;
            auto streams = streaming->streams();
            fanins.reserve(streams.size());
            for (auto it = streams.rbegin(); it != streams.rend(); ++it)
            {
                if (it->withExpr)
                {
                    std::fprintf(stderr, "sn-slang: streaming concatenation with a with-clause is unsupported\n");
                    return SN_INVALID_ID;
                }
                sn_obj_id_t operand = lower_expression(*it->operand);
                if (operand == SN_INVALID_ID)
                    return SN_INVALID_ID;
                fanins.push_back(operand);
            }
            if (fanins.empty())
                return SN_INVALID_ID;
            sn_obj_id_t packed = fanins.size() == 1
                                     ? fanins[0]
                                     : sn_module_add_concat(module, uint32_t(fanins.size()), fanins.data(), nullptr);
            uint64_t slice_size = streaming->getSliceSize();
            if (!slice_size)
                return packed;
            uint32_t bits = sn_obj_width(module, packed);
            if (slice_size > UINT32_MAX || !slice_size || bits % uint32_t(slice_size))
            {
                std::fprintf(stderr, "sn-slang: irregular streaming concatenation is unsupported\n");
                return SN_INVALID_ID;
            }
            uint32_t chunk_width = uint32_t(slice_size);
            uint32_t chunk_count = bits / chunk_width;
            std::vector<sn_obj_id_t> chunks;
            chunks.reserve(chunk_count);
            for (uint32_t chunk = 0; chunk < chunk_count; chunk++)
            {
                uint32_t offset = bits - (chunk + 1) * chunk_width;
                chunks.push_back(sn_module_add_slice(module, packed, int32_t(offset + chunk_width - 1),
                                                     int32_t(offset), nullptr));
            }
            return chunk_count == 1 ? chunks[0]
                                    : sn_module_add_concat(module, chunk_count, chunks.data(), nullptr);
        }

        if (const auto* concat = expression.as_if<ConcatenationExpression>())
        {
            std::vector<sn_obj_id_t> fanins;
            fanins.reserve(concat->operands().size());
            for (auto it = concat->operands().rbegin(); it != concat->operands().rend(); ++it)
            {
                if (const auto* repeated = (*it)->as_if<ReplicationExpression>(); repeated)
                {
                    auto count = constant_integer(repeated->count());
                    if (count && *count == 0)
                        continue;
                }
                sn_obj_id_t operand = lower_expression(**it);
                if (operand == SN_INVALID_ID)
                    return SN_INVALID_ID;
                fanins.push_back(operand);
            }
            if (fanins.empty())
            {
                std::fprintf(stderr, "sn-slang: empty concatenations are unsupported\n");
                return SN_INVALID_ID;
            }
            sn_obj_id_t result = sn_module_add_concat(module, uint32_t(fanins.size()), fanins.data(), nullptr);
            propagate_concat_unknowns(result, fanins);
            return result;
        }

        if (const auto* replication = expression.as_if<ReplicationExpression>())
        {
            auto count = constant_integer(replication->count());
            sn_obj_id_t value = lower_expression(replication->concat());
            if (!count || *count <= 0 || uint64_t(*count) > UINT32_MAX || value == SN_INVALID_ID)
            {
                std::fprintf(stderr,
                             "sn-slang: module '%s': replication count must be a positive 32-bit constant\n",
                             sn_name_get(&module->design->names, module->name));
                return SN_INVALID_ID;
            }
            sn_obj_id_t result = sn_module_add_repeat(module, value, uint32_t(*count), nullptr);
            propagate_repeat_unknowns(result, value, uint32_t(*count));
            return result;
        }

        if (SimpleAssignmentPatternExpression::isKind(expression.kind) ||
            StructuredAssignmentPatternExpression::isKind(expression.kind) ||
            ReplicatedAssignmentPatternExpression::isKind(expression.kind))
        {
            const auto& pattern = static_cast<const AssignmentPatternExpressionBase&>(expression);
            std::vector<sn_obj_id_t> elements;
            elements.reserve(pattern.elements().size());
            for (auto it = pattern.elements().rbegin(); it != pattern.elements().rend(); ++it)
            {
                sn_obj_id_t element = lower_expression(**it);
                if (element == SN_INVALID_ID)
                    return SN_INVALID_ID;
                elements.push_back(element);
            }
            if (elements.empty())
            {
                std::fprintf(stderr, "sn-slang: empty assignment pattern is unsupported\n");
                return SN_INVALID_ID;
            }
            sn_obj_id_t value = elements.size() == 1
                                    ? elements[0]
                                    : sn_module_add_concat(module, uint32_t(elements.size()), elements.data(),
                                                           nullptr);
            if (elements.size() > 1)
                propagate_concat_unknowns(value, elements);
            if (const auto* replicated = expression.as_if<ReplicatedAssignmentPatternExpression>())
            {
                auto count = constant_integer(replicated->count());
                if (!count || *count <= 0 || uint64_t(*count) > UINT32_MAX)
                {
                    std::fprintf(stderr, "sn-slang: assignment-pattern replication count is invalid\n");
                    return SN_INVALID_ID;
                }
                sn_obj_id_t repeated = sn_module_add_repeat(module, value, uint32_t(*count), nullptr);
                propagate_repeat_unknowns(repeated, value, uint32_t(*count));
                value = repeated;
            }
            if (sn_obj_width(module, value) != width(*expression.type))
            {
                std::fprintf(stderr, "sn-slang: assignment-pattern bitstream width mismatch\n");
                return SN_INVALID_ID;
            }
            return value;
        }

        if (const auto* select = expression.as_if<ElementSelectExpression>())
        {
            if (auto selected_bit = named_element_bit(expression);
                selected_bit && (selected_values.contains(*selected_bit) ||
                                 selected_assignments.contains(*selected_bit)))
                return lower_selected(*selected_bit);
            if (auto element = memory_element(expression))
            {
                const Memory& memory = memories.at(element->memory);
                sn_obj_id_t address = lower_expression(*element->address);
                if (address == SN_INVALID_ID)
                    return SN_INVALID_ID;
                address = normalize_memory_address(memory, address);
                return sn_module_add_mem_read(module, memory.pair.out, SN_INVALID_ID, SN_INVALID_ID, address,
                                              nullptr);
            }
            if (auto element = named_element(expression); element && !memories.contains(element->symbol))
            {
                bool has_procedural_value = active_procedural_values &&
                                            active_procedural_values->selected_values.contains(*element);
                if (element->symbol->getType().isUnpackedArray() || has_procedural_value ||
                    selected_values.contains(*element) || selected_assignments.contains(*element))
                    return lower_selected(*element);
            }
            const auto* array_named = select->value().as_if<NamedValueExpression>();
            if (array_named && array_named->symbol.getType().isUnpackedArray() &&
                array_named->symbol.getType().hasFixedRange())
            {
                const Type& array_type = array_named->symbol.getType();
                const Type* element_type = array_type.getArrayElementType();
                ConstantRange range = array_type.getFixedRange();
                uint32_t element_bits = element_type ? width(*element_type) : 0;
                sn_obj_id_t selector = lower_expression(select->selector());
                uint32_t selector_bits = selector == SN_INVALID_ID ? 0 : sn_obj_width(module, selector);
                if (!element_type || !element_bits || range.width() <= 0 || !selector_bits)
                {
                    std::fprintf(stderr,
                                 "sn-slang: module '%s': unsupported dynamic unpacked-array selection '%.*s' "
                                 "(element width %u, range %lld:%lld, selector width %u)\n",
                                 sn_name_get(&module->design->names, module->name),
                                 int(array_named->symbol.name.size()), array_named->symbol.name.data(), element_bits,
                                 (long long)range.left, (long long)range.right, selector_bits);
                    return SN_INVALID_ID;
                }
                std::vector<uint32_t> zero_words(sn_const_word_count(element_bits));
                sn_obj_id_t zero = sn_module_add_const(module, element_bits, element_type->isSigned(),
                                                       zero_words.data(), nullptr);
                // A BMUX has 2^selector_bits alternatives. Use it only when the declared range naturally
                // occupies that selector width. A wider selector must take the sparse path: sizing the packed
                // table from an unrelated 16- or 30-bit index can otherwise allocate gigabytes, and signed
                // selectors must preserve negative out-of-range values instead of being interpreted as unsigned.
                uint32_t dense_bits = 0;
                while (dense_bits < 31 && (uint64_t(1) << dense_bits) <= uint64_t(range.upper()))
                    dense_bits++;
                bool dense_unsigned = !select->selector().type->isSigned() && range.lower() >= 0 &&
                                      selector_bits == dense_bits && dense_bits < 20;
                if (!dense_unsigned)
                {
                    std::vector<std::pair<int64_t, sn_obj_id_t>> alternatives;
                    for (int64_t index = range.lower(); index <= range.upper(); index++)
                    {
                        SelectedValue selected{&array_named->symbol, index};
                        if (!has_selected_driver(selected))
                            continue;
                        sn_obj_id_t element = lower_selected(selected);
                        if (element == SN_INVALID_ID)
                            return SN_INVALID_ID;
                        alternatives.emplace_back(index, element);
                    }
                    return lower_sparse_selection(selector, alternatives, zero);
                }
                uint32_t alternative_count = 1u << selector_bits;
                std::vector<sn_obj_id_t> alternatives(alternative_count, zero);
                for (int64_t index = range.lower(); index <= range.upper(); index++)
                {
                    SelectedValue selected{&array_named->symbol, index};
                    if (!has_selected_driver(selected))
                        continue;
                    sn_obj_id_t element = lower_selected(selected);
                    if (element == SN_INVALID_ID)
                        return SN_INVALID_ID;
                    alternatives[size_t(index)] = element;
                }
                sn_obj_id_t packed = sn_module_add_concat(module, alternative_count, alternatives.data(), nullptr);
                return sn_module_add_bmux(module, selector, packed, element_bits, element_type->isSigned(), nullptr);
            }
            auto index = constant_integer(select->selector());
            sn_obj_id_t value = lower_expression(select->value());
            if (value == SN_INVALID_ID)
                return SN_INVALID_ID;
            ConstantRange value_range = select->value().type->getFixedRange();
            if (!index)
            {
                uint32_t element_bits = width(*select->type);
                if (element_bits > 1)
                {
                    sn_obj_id_t selector = lower_expression(select->selector());
                    if (selector == SN_INVALID_ID)
                        return SN_INVALID_ID;
                    sn_obj_id_t zero = lower_zero(*select->type);
                    uint32_t selector_bits = sn_obj_width(module, selector);
                    uint32_t dense_bits = 0;
                    while (dense_bits < 31 && (uint64_t(1) << dense_bits) <= uint64_t(value_range.upper()))
                        dense_bits++;
                    bool dense_unsigned = !select->selector().type->isSigned() && value_range.lower() >= 0 &&
                                          selector_bits == dense_bits && dense_bits < 20;
                    if (dense_unsigned)
                    {
                        uint32_t count = 1u << selector_bits;
                        std::vector<sn_obj_id_t> alternatives(count, zero);
                        for (int64_t legal = value_range.lower(); legal <= value_range.upper(); legal++)
                        {
                            int32_t physical = value_range.translateIndex(int32_t(legal)) * int32_t(element_bits);
                            alternatives[size_t(legal)] = sn_module_add_slice(
                                module, value, physical + int32_t(element_bits) - 1, physical, nullptr);
                        }
                        sn_obj_id_t packed =
                            sn_module_add_concat(module, uint32_t(alternatives.size()), alternatives.data(), nullptr);
                        return sn_module_add_bmux(module, selector, packed, element_bits,
                                                  select->type->isSigned(), nullptr);
                    }
                    std::vector<std::pair<int64_t, sn_obj_id_t>> alternatives;
                    alternatives.reserve(size_t(value_range.width()));
                    for (int64_t legal = value_range.lower(); legal <= value_range.upper(); legal++)
                    {
                        int32_t physical = value_range.translateIndex(int32_t(legal)) * int32_t(element_bits);
                        alternatives.emplace_back(
                            legal, sn_module_add_slice(module, value, physical + int32_t(element_bits) - 1,
                                                       physical, nullptr));
                    }
                    return lower_sparse_selection(selector, alternatives, zero);
                }
                sn_obj_id_t selector = lower_expression(select->selector());
                if (selector == SN_INVALID_ID)
                    return SN_INVALID_ID;
                int64_t adjustment = int64_t(value_range.right);
                if (adjustment < 0 || uint64_t(adjustment) > UINT32_MAX)
                {
                    std::fprintf(stderr, "sn-slang: dynamic packed bit-select has unsupported array bounds\n");
                    return SN_INVALID_ID;
                }
                bool constant_minus_selector = !value_range.isDescending();
                uint32_t selector_bits = sn_obj_width(module, selector);
                if (value_range.lower() < 0 || select->selector().type->isSigned() ||
                    !index_is_representable(adjustment, selector_bits, false))
                {
                    sn_obj_id_t zero = lower_zero(*select->type);
                    std::vector<std::pair<int64_t, sn_obj_id_t>> alternatives;
                    alternatives.reserve(size_t(value_range.width()));
                    for (int64_t legal_index = value_range.lower(); legal_index <= value_range.upper(); legal_index++)
                    {
                        int32_t offset = value_range.translateIndex(int32_t(legal_index));
                        alternatives.emplace_back(legal_index,
                                                  sn_module_add_slice(module, value, offset, offset, nullptr));
                    }
                    return lower_sparse_selection(selector, alternatives, zero);
                }
                std::vector<uint32_t> words(sn_const_word_count(selector_bits));
                words[0] = uint32_t(adjustment);
                sn_obj_id_t constant_offset =
                    sn_module_add_const(module, selector_bits, false, words.data(), nullptr);
                sn_obj_id_t compare_fanins[2] = {constant_minus_selector ? constant_offset : selector,
                                                  constant_minus_selector ? selector : constant_offset};
                sn_obj_id_t nonnegative =
                    sn_module_add_operator(module, SN_GE, 1, false, 2, compare_fanins, nullptr);
                sn_obj_id_t right_offset = sn_module_add_operator(module, SN_SUB, selector_bits, false, 2,
                                                                   compare_fanins, nullptr);
                sn_obj_id_t left_fanins[2] = {compare_fanins[1], compare_fanins[0]};
                sn_obj_id_t left_offset =
                    sn_module_add_operator(module, SN_SUB, selector_bits, false, 2, left_fanins, nullptr);
                sn_obj_id_t right_fanins[2] = {value, right_offset};
                sn_obj_id_t shifted_right = sn_module_add_operator(module, SN_SHR, sn_obj_width(module, value),
                                                                    false, 2, right_fanins, nullptr);
                sn_obj_id_t left_shift_fanins[2] = {value, left_offset};
                sn_obj_id_t shifted_left = sn_module_add_operator(module, SN_SHL, sn_obj_width(module, value), false,
                                                                   2, left_shift_fanins, nullptr);
                sn_obj_id_t mux_fanins[SN_MUX_FANIN_COUNT] = {nonnegative, shifted_right, shifted_left};
                sn_obj_id_t shifted = sn_module_add_operator(module, SN_MUX, sn_obj_width(module, value), false,
                                                              SN_MUX_FANIN_COUNT, mux_fanins, nullptr);
                return sn_module_add_slice(module, shifted, 0, 0, nullptr);
            }
            // An unsigned elaborated expression such as 0 - 1 can arrive as 32'hffffffff. It is simply an
            // out-of-range select (and therefore X in SystemVerilog, concretized to zero by SN), not an oversized
            // legal index. Check against the declared range before narrowing to Slang's 32-bit range API.
            if (*index < value_range.lower() || *index > value_range.upper())
                return lower_zero(*select->type);
            if (*index < INT32_MIN || *index > INT32_MAX)
            {
                SourceLocation location = source_manager->getFullyOriginalLoc(select->sourceRange.start());
                std::string path = location ? source_manager->getFullPath(location.buffer()).string() : "<unknown>";
                size_t line = location ? source_manager->getLineNumber(location) : 0;
                std::fprintf(stderr,
                             "sn-slang: %s:%zu: packed bit-selection index %lld exceeds 32 bits\n",
                             path.c_str(), line, static_cast<long long>(*index));
                return SN_INVALID_ID;
            }
            uint32_t element_bits = width(*select->type);
            int32_t translated = value_range.translateIndex(int32_t(*index)) * int32_t(element_bits);
            return sn_module_add_slice(module, value, translated + int32_t(element_bits) - 1, translated, nullptr);
        }

        if (const auto* select = expression.as_if<RangeSelectExpression>())
        {
            auto left = constant_integer(select->left());
            auto right = constant_integer(select->right());
            if (select->getSelectionKind() != RangeSelectionKind::Simple && !left && right && *right > 0 &&
                uint64_t(*right) <= UINT32_MAX)
            {
                sn_obj_id_t value = lower_expression(select->value());
                sn_obj_id_t base = lower_expression(select->left());
                uint32_t result_bits = width(*select->type);
                uint32_t selected_bits = uint32_t(*right);
                if (value == SN_INVALID_ID || base == SN_INVALID_ID || !result_bits)
                {
                    SourceLocation location = source_manager->getFullyOriginalLoc(select->sourceRange.start());
                    std::string path =
                        location ? source_manager->getFullPath(location.buffer()).string() : "<unknown>";
                    size_t line = location ? source_manager->getLineNumber(location) : 0;
                    std::fprintf(stderr,
                                 "sn-slang: %s:%zu: cannot lower dynamic indexed part-select "
                                 "(value=%s, base=%s, width=%u, declared=%lld)\n",
                                 path.c_str(), line, value == SN_INVALID_ID ? "invalid" : "ok",
                                 base == SN_INVALID_ID ? "invalid" : "ok", result_bits,
                                 static_cast<long long>(*right));
                    return SN_INVALID_ID;
                }
                auto extend_result = [&](sn_obj_id_t selected) {
                    if (selected == SN_INVALID_ID || selected_bits == result_bits)
                        return selected;
                    return sn_module_add_operator(module, SN_CAST, result_bits, false, 1, &selected, nullptr);
                };

                ConstantRange value_range = select->value().type->getFixedRange();
                int64_t adjustment;
                bool constant_minus_base = !value_range.isDescending();
                if (value_range.isDescending())
                    adjustment = int64_t(value_range.right) +
                                 (select->getSelectionKind() == RangeSelectionKind::IndexedDown ? selected_bits - 1
                                                                                                : 0);
                else
                    adjustment = int64_t(value_range.right) -
                                 (select->getSelectionKind() == RangeSelectionKind::IndexedUp ? selected_bits - 1
                                                                                              : 0);
                if (value_range.lower() < 0 || select->left().type->isSigned() ||
                    !index_is_representable(adjustment, sn_obj_width(module, base), false))
                    return extend_result(lower_sparse_indexed_part(value, base, value_range, selected_bits,
                                                                   select->getSelectionKind(),
                                                                   select->left().type->isSigned()));
                if (adjustment < 0 || uint64_t(adjustment) > UINT32_MAX)
                {
                    std::fprintf(stderr, "sn-slang: dynamic indexed part-select has unsupported array bounds\n");
                    return SN_INVALID_ID;
                }

                uint32_t selector_bits = sn_obj_width(module, base);
                std::vector<uint32_t> words(sn_const_word_count(selector_bits));
                words[0] = uint32_t(adjustment);
                sn_obj_id_t constant_offset =
                    sn_module_add_const(module, selector_bits, false, words.data(), nullptr);
                sn_obj_id_t compare_fanins[2] = {constant_minus_base ? constant_offset : base,
                                                  constant_minus_base ? base : constant_offset};
                sn_obj_id_t nonnegative =
                    sn_module_add_operator(module, SN_GE, 1, false, 2, compare_fanins, nullptr);
                sn_obj_id_t right_offset = sn_module_add_operator(module, SN_SUB, selector_bits, false, 2,
                                                                   compare_fanins, nullptr);
                sn_obj_id_t left_fanins[2] = {compare_fanins[1], compare_fanins[0]};
                sn_obj_id_t left_offset =
                    sn_module_add_operator(module, SN_SUB, selector_bits, false, 2, left_fanins, nullptr);
                sn_obj_id_t right_shift_fanins[2] = {value, right_offset};
                sn_obj_id_t shifted_right = sn_module_add_operator(module, SN_SHR, sn_obj_width(module, value),
                                                                    false, 2, right_shift_fanins, nullptr);
                sn_obj_id_t left_shift_fanins[2] = {value, left_offset};
                sn_obj_id_t shifted_left = sn_module_add_operator(module, SN_SHL, sn_obj_width(module, value), false,
                                                                   2, left_shift_fanins, nullptr);
                sn_obj_id_t mux_fanins[SN_MUX_FANIN_COUNT] = {nonnegative, shifted_right, shifted_left};
                sn_obj_id_t shifted = sn_module_add_operator(module, SN_MUX, sn_obj_width(module, value), false,
                                                              SN_MUX_FANIN_COUNT, mux_fanins, nullptr);
                return extend_result(sn_module_add_slice(module, shifted, int32_t(selected_bits - 1), 0, nullptr));
            }
            if (!left || !right || *left < INT32_MIN || *left > INT32_MAX || *right < INT32_MIN ||
                *right > INT32_MAX)
            {
                std::fprintf(stderr,
                             "sn-slang: module '%s': part-select bounds must be 32-bit constants "
                             "(left kind %u, right kind %u, loop context %s)\n",
                             sn_name_get(&module->design->names, module->name), unsigned(select->left().kind),
                             unsigned(select->right().kind), active_constant_context ? "active" : "inactive");
                return SN_INVALID_ID;
            }

            ConstantRange selected_range{int32_t(*left), int32_t(*right)};
            if (select->getSelectionKind() != RangeSelectionKind::Simple)
            {
                bool indexed_up = select->getSelectionKind() == RangeSelectionKind::IndexedUp;
                auto range = ConstantRange::getIndexedRange(int32_t(*left), int32_t(*right),
                                                            select->value().type->getFixedRange().isDescending(),
                                                            indexed_up);
                if (!range)
                {
                    std::fprintf(stderr, "sn-slang: indexed part-select range is invalid\n");
                    return SN_INVALID_ID;
                }
                selected_range = *range;
            }

            if (auto element = named_element(select->value()))
            {
                uint32_t bits = width(*select->type);
                std::vector<SelectedValue> selected_bits;
                selected_bits.reserve(bits);
                bool all_bits_available = true;
                for (uint32_t offset = 0; offset < bits; offset++)
                {
                    int64_t bit = selected_range.left >= selected_range.right
                                      ? int64_t(selected_range.right) + offset
                                      : int64_t(selected_range.right) - offset;
                    SelectedValue selected_bit{element->symbol, element->index, bit};
                    if (!has_selected_driver(selected_bit))
                        all_bits_available = false;
                    selected_bits.push_back(selected_bit);
                }
                if (all_bits_available)
                {
                    std::vector<sn_obj_id_t> result_bits;
                    result_bits.reserve(bits);
                    for (const SelectedValue& selected_bit : selected_bits)
                    {
                        sn_obj_id_t bit = lower_selected(selected_bit);
                        if (bit == SN_INVALID_ID)
                            return SN_INVALID_ID;
                        result_bits.push_back(bit);
                    }
                    return sn_module_add_concat(module, bits, result_bits.data(), nullptr);
                }
            }

            sn_obj_id_t value = lower_expression(select->value());
            if (value == SN_INVALID_ID)
                return SN_INVALID_ID;
            ConstantRange value_range = select->value().type->getFixedRange();
            const Type* element_type = select->value().type->getArrayElementType();
            uint32_t element_width = element_type ? width(*element_type) : 1;
            if (!element_width)
                return SN_INVALID_ID;
            // Elements outside the declared range read as X, which SN concretizes to zero. Keep the
            // in-range part of the selection and pad the result with zero elements on either side.
            int64_t selected_low = std::min(selected_range.left, selected_range.right);
            int64_t selected_high = std::max(selected_range.left, selected_range.right);
            int64_t in_low = std::max<int64_t>(selected_low, value_range.lower());
            int64_t in_high = std::min<int64_t>(selected_high, value_range.upper());
            if (in_low > in_high)
                return lower_zero(*select->type);
            if (in_low != selected_low || in_high != selected_high)
            {
                bool descending_select = selected_range.left >= selected_range.right;
                ConstantRange inner = descending_select ? ConstantRange{int32_t(in_high), int32_t(in_low)}
                                                        : ConstantRange{int32_t(in_low), int32_t(in_high)};
                // Elements below the LSB end of the selection precede the kept part; those beyond it follow.
                int64_t lsb_pad = descending_select ? in_low - selected_low : selected_high - in_high;
                int64_t msb_pad = descending_select ? selected_high - in_high : in_low - selected_low;
                int32_t inner_left = value_range.translateIndex(inner.left);
                int32_t inner_right = value_range.translateIndex(inner.right);
                int64_t inner_msb = int64_t(std::max(inner_left, inner_right)) * element_width + element_width - 1;
                int64_t inner_lsb = int64_t(std::min(inner_left, inner_right)) * element_width;
                if (inner_msb > INT32_MAX)
                    return SN_INVALID_ID;
                sn_obj_id_t kept = sn_module_add_slice(module, value, int32_t(inner_msb), int32_t(inner_lsb), nullptr);
                std::vector<sn_obj_id_t> parts;
                if (lsb_pad)
                {
                    std::vector<uint32_t> zero_words(sn_const_word_count(uint32_t(lsb_pad * element_width)));
                    parts.push_back(sn_module_add_const(module, uint32_t(lsb_pad * element_width), false,
                                                        zero_words.data(), nullptr));
                }
                parts.push_back(kept);
                if (msb_pad)
                {
                    std::vector<uint32_t> zero_words(sn_const_word_count(uint32_t(msb_pad * element_width)));
                    parts.push_back(sn_module_add_const(module, uint32_t(msb_pad * element_width), false,
                                                        zero_words.data(), nullptr));
                }
                return parts.size() == 1 ? parts[0]
                                         : sn_module_add_concat(module, uint32_t(parts.size()), parts.data(), nullptr);
            }
            int32_t left_ordinal = value_range.translateIndex(selected_range.left);
            int32_t right_ordinal = value_range.translateIndex(selected_range.right);
            if (left_ordinal < 0 || right_ordinal < 0)
                return SN_INVALID_ID;
            int64_t left_index = int64_t(left_ordinal) * element_width;
            int64_t right_index = int64_t(right_ordinal) * element_width;
            if (left_ordinal >= right_ordinal)
                left_index += element_width - 1;
            else
                right_index += element_width - 1;
            if (left_index > INT32_MAX || right_index > INT32_MAX)
                return SN_INVALID_ID;
            return sn_module_add_slice(module, value, int32_t(left_index), int32_t(right_index), nullptr);
        }

        if (const auto* member = expression.as_if<MemberAccessExpression>())
        {
            if (member->member.kind != SymbolKind::Field)
            {
                std::fprintf(stderr, "sn-slang: unsupported non-field member access\n");
                return SN_INVALID_ID;
            }
            uint64_t offset = sn_slang_detail::sn_lvalue_member_offset(member->member.as<FieldSymbol>());
            uint32_t bits = width(*member->type);
            std::string lvalue_error;
            auto lvalue = analyze_lvalue(expression, lvalue_error);
            const ValueSymbol* root = nullptr;
            uint32_t root_offset = 0;
            if (lvalue && static_lvalue_span(*lvalue, root, root_offset) && root && bits &&
                structured_drivers.contains(root))
            {
                if (!lower_structured_range(*root, root_offset, bits))
                    return SN_INVALID_ID;
                auto cached = values.find(root);
                if (cached != values.end() && uint64_t(root_offset) + bits <= sn_obj_width(module, cached->second))
                    return sn_module_add_slice(module, cached->second, int32_t(root_offset + bits - 1),
                                               int32_t(root_offset), nullptr);
                auto partial = partial_value_drivers.find(root);
                if (partial != partial_value_drivers.end())
                {
                    sn_obj_id_t packed = materialize_partial_drivers(width(root->getType()),
                                                                     root->getType().isSigned(),
                                                                     partial->second);
                    // Cache the packed view. A later partial driver invalidates this entry in
                    // bind_analyzed_lvalue(), so repeated field reads share the aggregate without hiding a
                    // subsequently discovered field assignment.
                    values.insert_or_assign(root, packed);
                    if (uint64_t(root_offset) + bits <= sn_obj_width(module, packed))
                        return sn_module_add_slice(module, packed, int32_t(root_offset + bits - 1),
                                                   int32_t(root_offset), nullptr);
                }
            }
            sn_obj_id_t value = lower_expression(member->value());
            if (offset == UINT64_MAX || !bits || value == SN_INVALID_ID ||
                offset + bits > sn_obj_width(module, value) || offset + bits > uint64_t(INT32_MAX) + 1)
                return SN_INVALID_ID;
            return sn_module_add_slice(module, value, int32_t(offset + bits - 1), int32_t(offset), nullptr);
        }

        if (const auto* conditional = expression.as_if<ConditionalExpression>())
        {
            if (conditional->conditions.size() != 1 || conditional->conditions[0].pattern)
            {
                std::fprintf(stderr, "sn-slang: only simple conditional expressions are supported\n");
                return SN_INVALID_ID;
            }
            sn_obj_id_t select = lower_expression(*conditional->conditions[0].expr);
            sn_obj_id_t selected = lower_expression(conditional->left());
            sn_obj_id_t default_value = lower_expression(conditional->right());
            if (select == SN_INVALID_ID || selected == SN_INVALID_ID || default_value == SN_INVALID_ID)
                return SN_INVALID_ID;
            select = normalize_condition(select);
            sn_obj_id_t result = sn_module_add_mux(module, select, selected, default_value, nullptr);
            propagate_mux_unknowns(result, select, selected, default_value);
            return result;
        }

        std::fprintf(stderr, "sn-slang: unsupported expression kind %u\n", unsigned(expression.kind));
        return SN_INVALID_ID;
    }

    sn_obj_id_t lower_primitive_output(const PrimitiveDriver& driver)
    {
        const PrimitiveInstanceSymbol& inst = *driver.inst;
        std::span<const Expression* const> ports = inst.getPortConnections();
        std::string_view name = inst.primitiveType.name;
        if (driver.output_index >= ports.size())
            return SN_INVALID_ID;

        auto lower_port = [&](uint32_t index) {
            return index < ports.size() && ports[index] ? lower_expression(*ports[index]) : SN_INVALID_ID;
        };
        auto invert = [&](sn_obj_id_t value) {
            return value == SN_INVALID_ID ? value
                                          : sn_module_add_operator(module, SN_BIT_NOT, 1, false, 1, &value,
                                                                   nullptr);
        };
        auto combine = [&](sn_obj_type_t type, sn_obj_id_t left, sn_obj_id_t right) {
            if (left == SN_INVALID_ID || right == SN_INVALID_ID)
                return SN_INVALID_ID;
            sn_obj_id_t fanins[2] = {left, right};
            return sn_module_add_operator(module, type, 1, false, 2, fanins, nullptr);
        };
        auto reduce = [&](sn_obj_type_t type, uint32_t first) {
            sn_obj_id_t result = lower_port(first);
            for (uint32_t index = first + 1; result != SN_INVALID_ID && index < ports.size(); index++)
                result = combine(type, result, lower_port(index));
            return result;
        };
        auto tristate = [&](sn_obj_id_t data, sn_obj_id_t enable) {
            if (data == SN_INVALID_ID || enable == SN_INVALID_ID)
                return SN_INVALID_ID;
            const uint32_t zero_word = 0;
            sn_obj_id_t zero = sn_module_add_const(module, 1, false, &zero_word, nullptr);
            sn_obj_id_t result = sn_module_add_mux(module, enable, data, zero, nullptr);
            constant_valid_masks[result] = enable;
            constant_z_masks[result] = invert(enable);
            return result;
        };

        if (name == "pullup")
        {
            const uint32_t one_word = 1;
            return sn_module_add_const(module, 1, false, &one_word, nullptr);
        }
        if (name == "pulldown")
        {
            const uint32_t zero_word = 0;
            return sn_module_add_const(module, 1, false, &zero_word, nullptr);
        }
        if (name == "buf" || name == "not")
        {
            sn_obj_id_t result = lower_port(uint32_t(ports.size() - 1));
            return name == "not" ? invert(result) : result;
        }
        if (name == "and" || name == "nand" || name == "or" || name == "nor" || name == "xor" ||
            name == "xnor")
        {
            sn_obj_type_t type = name == "and" || name == "nand" ? SN_BIT_AND
                                 : name == "or" || name == "nor" ? SN_BIT_OR
                                                                   : SN_BIT_XOR;
            sn_obj_id_t result = reduce(type, 1);
            return name == "nand" || name == "nor" || name == "xnor" ? invert(result) : result;
        }
        if (name == "bufif0" || name == "bufif1" || name == "notif0" || name == "notif1")
        {
            sn_obj_id_t data = lower_port(1);
            if (name == "notif0" || name == "notif1")
                data = invert(data);
            sn_obj_id_t enable = lower_port(2);
            if (name == "bufif0" || name == "notif0")
                enable = invert(enable);
            return tristate(data, enable);
        }
        if (name == "nmos" || name == "rnmos" || name == "pmos" || name == "rpmos")
        {
            sn_obj_id_t enable = lower_port(2);
            if (name == "pmos" || name == "rpmos")
                enable = invert(enable);
            return tristate(lower_port(1), enable);
        }
        if (name == "cmos" || name == "rcmos")
        {
            sn_obj_id_t ncontrol = lower_port(2);
            sn_obj_id_t pcontrol = invert(lower_port(3));
            return tristate(lower_port(1), combine(SN_BIT_AND, ncontrol, pcontrol));
        }

        std::string message = "unsupported primitive '" + std::string(name) + "'";
        report_timing_error(inst.location, message.c_str());
        return SN_INVALID_ID;
    }

    sn_obj_id_t merge_primitive_drivers(const ValueSymbol& symbol, sn_obj_id_t result)
    {
        auto found = primitive_value_drivers.find(&symbol);
        if (found == primitive_value_drivers.end())
            return result;
        std::vector<PrimitiveDriver> drivers = std::move(found->second);
        primitive_value_drivers.erase(found);
        for (const PrimitiveDriver& driver : drivers)
        {
            sn_obj_id_t primitive = lower_primitive_output(driver);
            if (primitive == SN_INVALID_ID)
                return SN_INVALID_ID;
            if (result == SN_INVALID_ID)
                result = primitive;
            else
                result = resolve_net_driver(symbol, result, primitive);
            if (result == SN_INVALID_ID)
                return SN_INVALID_ID;
        }
        return result;
    }

    sn_obj_id_t lower_value(const ValueSymbol& symbol)
    {
        auto loop_constant = active_loop_constants.find(&symbol);
        if (loop_constant != active_loop_constants.end())
        {
            const ConstantValue& value = *loop_constant->second;
            if (value && value.isInteger() && !value.integer().hasUnknown())
                return lower_integer(value.integer(), symbol.getType());
        }
        if (active_constant_context)
        {
            ConstantValue* local = active_constant_context->findLocal(&symbol);
            if (local && *local && local->isInteger() && !local->integer().hasUnknown())
                return lower_integer(local->integer(), symbol.getType());
        }
        if (active_procedural_values)
        {
            auto procedural_it = active_procedural_values->values.find(&symbol);
            if (procedural_it != active_procedural_values->values.end())
                return procedural_it->second;
        }
        auto value_it = values.find(&symbol);
        if (value_it != values.end())
        {
            sn_obj_id_t primitive_result = merge_primitive_drivers(symbol, value_it->second);
            if (primitive_result == SN_INVALID_ID)
                return SN_INVALID_ID;
            value_it->second = primitive_result;
            auto additional = additional_value_drivers.find(&symbol);
            if (additional != additional_value_drivers.end())
            {
                sn_obj_id_t result = value_it->second;
                for (sn_obj_id_t driver : additional->second)
                {
                    result = resolve_net_driver(symbol, result, driver);
                    if (result == SN_INVALID_ID)
                        return SN_INVALID_ID;
                }
                value_it->second = result;
                additional_value_drivers.erase(additional);
            }
            return value_it->second;
        }
        if (auto structured_it = structured_drivers.find(&symbol); structured_it != structured_drivers.end())
        {
            for (const AssignmentExpression* assignment : structured_it->second)
            {
                if (lowering_structured.contains(assignment))
                {
                    auto loop = continuous_loops.find(&symbol);
                    if (loop == continuous_loops.end())
                    {
                        uint32_t bits = width(symbol.getType());
                        if (!bits)
                            return SN_INVALID_ID;
                        std::string name(symbol.name);
                        sn_obj_pair_t pair = sn_module_add_loop_pair(module, bits, symbol.getType().isSigned(),
                                                                      name.c_str(), nullptr);
                        loop = continuous_loops.emplace(&symbol, pair).first;
                        values.emplace(&symbol, pair.out);
                    }
                    return loop->second.out;
                }
                if (!lower_structured_assignment(*assignment))
                    return SN_INVALID_ID;
            }
            value_it = values.find(&symbol);
            if (value_it != values.end())
            {
                sn_obj_id_t result = merge_primitive_drivers(symbol, value_it->second);
                if (result != SN_INVALID_ID)
                    value_it->second = result;
                return result;
            }
        }
        auto assignment_it = assignments.find(&symbol);
        auto partial_it = partial_value_drivers.find(&symbol);
        if (assignment_it == assignments.end() && partial_it != partial_value_drivers.end())
        {
            uint32_t bits = width(symbol.getType());
            // Instance outputs use partial drivers, while simple continuous element assignments are collected
            // separately. Include both before caching the aggregate, or neighboring assigned bits disappear.
            auto drivers = partial_it->second;
            const Type& type = symbol.getType();
            if (type.isIntegral() && type.hasFixedRange())
            {
                const Type* element_type = type.getArrayElementType();
                uint32_t element_bits = element_type ? width(*element_type) : 1;
                ConstantRange range = type.getFixedRange();
                for (const SelectedValue& selected : selected_assignment_order)
                {
                    if (selected.symbol != &symbol || selected.bit >= 0 || selected.index < INT32_MIN ||
                        selected.index > INT32_MAX || !range.containsPoint(int32_t(selected.index)))
                        continue;
                    uint32_t offset = uint32_t(range.translateIndex(int32_t(selected.index))) * element_bits;
                    sn_obj_id_t driver = lower_selected(selected);
                    if (driver == SN_INVALID_ID || !add_partial_driver(drivers, bits, offset, element_bits, driver))
                    {
                        std::fprintf(stderr, "sn-slang: overlapping or invalid selected driver for '%.*s'\n",
                                     int(symbol.name.size()), symbol.name.data());
                        return SN_INVALID_ID;
                    }
                }
            }
            sn_obj_id_t result = materialize_partial_drivers(bits, symbol.getType().isSigned(), drivers);
            result = merge_primitive_drivers(symbol, result);
            if (result == SN_INVALID_ID)
                return SN_INVALID_ID;
            values.emplace(&symbol, result);
            return result;
        }
        if (assignment_it == assignments.end() && primitive_value_drivers.contains(&symbol))
        {
            sn_obj_id_t result = merge_primitive_drivers(symbol, SN_INVALID_ID);
            if (result != SN_INVALID_ID)
                values.emplace(&symbol, result);
            return result;
        }
        if (assignment_it == assignments.end())
        {
            if (const auto* parameter = symbol.as_if<ParameterSymbol>())
            {
                const ConstantValue& constant = parameter->getValue();
                if (constant && constant.isInteger())
                    return lower_integer(constant.integer(), parameter->getType());
            }
            if (constant_dead_values.contains(&symbol))
            {
                sn_obj_id_t result = lower_zero(symbol.getType());
                if (result != SN_INVALID_ID)
                    values.emplace(&symbol, result);
                return result;
            }
            uint32_t bits = width(symbol.getType());
            std::vector<sn_obj_id_t> elements;
            if (!symbol.getType().isIntegral() && symbol.getType().isFixedSize() && bits)
            {
                elements.reserve(bits);
                for (uint32_t physical = 0; physical < bits; physical++)
                {
                    SelectedValue selected{&symbol, physical};
                    bool has_procedural_value = active_procedural_values &&
                                                active_procedural_values->selected_values.contains(selected);
                    if (!has_procedural_value && !selected_values.contains(selected) &&
                        !selected_assignments.contains(selected))
                        break;
                    sn_obj_id_t bit = lower_selected(selected);
                    if (bit == SN_INVALID_ID)
                        return SN_INVALID_ID;
                    elements.push_back(bit);
                }
                if (elements.size() == bits)
                {
                    sn_obj_id_t result = bits == 1 ? elements[0]
                                                   : sn_module_add_concat(module, bits, elements.data(), nullptr);
                    values.emplace(&symbol, result);
                    return result;
                }
                elements.clear();
            }
            if (symbol.getType().isIntegral() && bits)
            {
                ConstantRange range = symbol.getType().getFixedRange();
                const Type* element_type = symbol.getType().getArrayElementType();
                uint32_t element_bits = element_type ? width(*element_type) : 1;
                uint32_t element_count = element_bits && bits % element_bits == 0 ? bits / element_bits : 0;
                elements.reserve(element_count);
                for (uint32_t i = 0; i < element_count; i++)
                {
                    int64_t element_index = range.isDescending() ? int64_t(range.right) + i
                                                                  : int64_t(range.right) - i;
                    SelectedValue selected{&symbol, element_index};
                    bool has_procedural_value = active_procedural_values &&
                                                active_procedural_values->selected_values.contains(selected);
                    if (!has_procedural_value && !selected_values.contains(selected) &&
                        !selected_assignments.contains(selected))
                        break;
                    sn_obj_id_t element = lower_selected(selected);
                    if (element == SN_INVALID_ID)
                        return SN_INVALID_ID;
                    elements.push_back(element);
                }
                if (elements.size() == element_count && element_count)
                {
                    sn_obj_id_t result =
                        element_count == 1 ? elements[0]
                                           : sn_module_add_concat(module, element_count, elements.data(), nullptr);
                    values.emplace(&symbol, result);
                    return result;
                }
            }
            // A variable with a constant declaration initializer and no updates
            // retains that value; it is not an uninitialized/undriven zero.
            // Keep the placeholder bookkeeping in case a later collected driver
            // replaces it, just as for the undriven fallback below. Do not turn
            // a nonconstant time-zero initializer into a continuous assignment.
            if (const auto* variable = symbol.as_if<VariableSymbol>())
                if (const Expression* initializer = variable->getInitializer())
                {
                    EvalContext context(*body->parentInstance);
                    ConstantValue initial = initializer->eval(context);
                    if (initial && initial.isInteger())
                    {
                        sn_obj_id_t result = lower_integer(initial.integer(), symbol.getType());
                        if (result != SN_INVALID_ID)
                        {
                            values.emplace(&symbol, result);
                            undriven_values.emplace(&symbol);
                            return result;
                        }
                    }
                }
            // SN is a two-state synthesis IR, so an undriven data object (Z for a net and X for a variable) is
            // deterministically concretized to zero. This also covers state hidden behind an inactive generate
            // condition and explicit synthesis black-box outputs; a future black-box abstraction can replace the
            // latter with independent boundary inputs without changing ordinary elaboration.
            if (symbol.as_if<NetSymbol>() || symbol.as_if<VariableSymbol>())
            {
                sn_obj_id_t result = lower_zero(symbol.getType());
                if (result != SN_INVALID_ID)
                {
                    values.emplace(&symbol, result);
                    undriven_values.emplace(&symbol);
                    return result;
                }
            }
            std::fprintf(stderr, "sn-slang: module '%s': signal '%.*s' has no SN driver (loop context %s)\n",
                         sn_name_get(&module->design->names, module->name), int(symbol.name.size()),
                         symbol.name.data(), active_constant_context ? "active" : "inactive");
            return SN_INVALID_ID;
        }
        if (!resolving.emplace(&symbol).second)
        {
            auto loop = continuous_loops.find(&symbol);
            if (loop == continuous_loops.end())
            {
                uint32_t bits = width(symbol.getType());
                if (!bits)
                    return SN_INVALID_ID;
                std::string name(symbol.name);
                sn_obj_pair_t pair = sn_module_add_loop_pair(module, bits, symbol.getType().isSigned(),
                                                              name.c_str(), nullptr);
                loop = continuous_loops.emplace(&symbol, pair).first;
                values.emplace(&symbol, pair.out);
            }
            return loop->second.out;
        }
        sn_obj_id_t result = lower_expression(*assignment_it->second);
        if (result != SN_INVALID_ID)
        {
            auto extra_assignments = additional_value_assignments.find(&symbol);
            if (extra_assignments != additional_value_assignments.end())
                for (const Expression* expression : extra_assignments->second)
                {
                    sn_obj_id_t driver = lower_expression(*expression);
                    if (driver == SN_INVALID_ID)
                        return SN_INVALID_ID;
                    result = resolve_net_driver(symbol, result, driver);
                    if (result == SN_INVALID_ID)
                        return SN_INVALID_ID;
                }
            result = merge_primitive_drivers(symbol, result);
            if (result == SN_INVALID_ID)
                return SN_INVALID_ID;
            auto additional = additional_value_drivers.find(&symbol);
            if (additional != additional_value_drivers.end())
            {
                for (sn_obj_id_t driver : additional->second)
                {
                    result = resolve_net_driver(symbol, result, driver);
                    if (result == SN_INVALID_ID)
                        return SN_INVALID_ID;
                }
                additional_value_drivers.erase(additional);
            }
        }
        resolving.erase(&symbol);
        auto loop = continuous_loops.find(&symbol);
        if (result != SN_INVALID_ID && loop != continuous_loops.end())
        {
            sn_obj_connect(module, loop->second.in, 0, result);
            result = loop->second.out;
        }
        else if (result != SN_INVALID_ID)
            values.emplace(&symbol, result);
        return result;
    }

    sn_obj_id_t lower_selected(const SelectedValue& selected)
    {
        auto slice_whole = [&](sn_obj_id_t whole) -> sn_obj_id_t {
            const Type& outer_type = selected.symbol->getType();
            const Type* first_type = outer_type.getArrayElementType();
            if (!first_type || !outer_type.hasFixedRange() || selected.index < INT32_MIN ||
                selected.index > INT32_MAX)
                return SN_INVALID_ID;
            ConstantRange outer_range = outer_type.getFixedRange();
            if (!outer_range.containsPoint(int32_t(selected.index)))
                return SN_INVALID_ID;
            uint32_t first_width = width(*first_type);
            uint64_t offset = uint64_t(outer_range.translateIndex(int32_t(selected.index))) * first_width;
            uint32_t bits = first_width;
            if (selected.bit >= 0)
            {
                const Type* second_type = first_type->isUnpackedArray() ? first_type->getArrayElementType() : nullptr;
                if (!first_type->hasFixedRange() || selected.bit < INT32_MIN || selected.bit > INT32_MAX)
                    return SN_INVALID_ID;
                ConstantRange first_range = first_type->getFixedRange();
                if (!first_range.containsPoint(int32_t(selected.bit)))
                    return SN_INVALID_ID;
                bits = second_type ? width(*second_type) : 1;
                offset += uint64_t(first_range.translateIndex(int32_t(selected.bit))) * bits;
            }
            if (!bits || offset + bits > sn_obj_width(module, whole) || offset + bits > uint64_t(INT32_MAX) + 1)
                return SN_INVALID_ID;
            return sn_module_add_slice(module, whole, int32_t(offset + bits - 1), int32_t(offset), nullptr);
        };
        if (active_procedural_values)
        {
            auto whole_it = active_procedural_values->values.find(selected.symbol);
            if (whole_it != active_procedural_values->values.end())
                return slice_whole(whole_it->second);
            auto procedural_it = active_procedural_values->selected_values.find(selected);
            if (procedural_it != active_procedural_values->selected_values.end())
                return procedural_it->second;
        }
        auto value_it = selected_values.find(selected);
        if (value_it != selected_values.end())
            return value_it->second;
        if (auto whole_it = values.find(selected.symbol); whole_it != values.end())
            return slice_whole(whole_it->second);
        auto assignment_it = selected_assignments.find(selected);
        auto partial_it = partial_selected_drivers.find(selected);
        if (assignment_it == selected_assignments.end() && partial_it != partial_selected_drivers.end())
        {
            uint32_t bits = selected_width(selected);
            sn_obj_id_t result = materialize_partial_drivers(bits, selected_is_signed(selected), partial_it->second);
            selected_values.emplace(selected, result);
            return result;
        }
        if (assignment_it == selected_assignments.end())
        {
            if (constant_dead_selected_values.contains(selected))
            {
                uint32_t bits = selected_width(selected);
                std::vector<uint32_t> words(sn_const_word_count(bits));
                sn_obj_id_t result =
                    sn_module_add_const(module, bits, selected_is_signed(selected), words.data(), nullptr);
                selected_values.emplace(selected, result);
                return result;
            }
            const Type* element_type =
                selected.bit < 0 ? selected.symbol->getType().getArrayElementType() : nullptr;
            uint32_t bits = element_type ? width(*element_type) : 0;
            if (element_type && bits && element_type->hasFixedRange())
            {
                ConstantRange range = element_type->getFixedRange();
                uint32_t element_count = element_type->isUnpackedArray() ? uint32_t(range.width()) : bits;
                std::vector<sn_obj_id_t> elements;
                elements.reserve(element_count);
                for (uint32_t offset = 0; offset < element_count; offset++)
                {
                    int64_t bit_index = range.isDescending() ? int64_t(range.right) + offset
                                                              : int64_t(range.right) - offset;
                    SelectedValue selected_bit{selected.symbol, selected.index, bit_index};
                    if (!selected_values.contains(selected_bit) && !selected_assignments.contains(selected_bit))
                        break;
                    sn_obj_id_t bit = lower_selected(selected_bit);
                    if (bit == SN_INVALID_ID)
                        return SN_INVALID_ID;
                    elements.push_back(bit);
                }
                if (elements.size() == element_count)
                {
                    sn_obj_id_t result = element_count == 1
                                             ? elements[0]
                                             : sn_module_add_concat(module, element_count, elements.data(), nullptr);
                    selected_values.emplace(selected, result);
                    return result;
                }
            }
            // SN is a two-state representation. Match whole undriven signals by concretizing an undriven array
            // element (or an inactive generated element) to zero as well.
            uint32_t undriven_bits = selected_width(selected);
            if (undriven_bits)
            {
                std::vector<uint32_t> words(sn_const_word_count(undriven_bits));
                sn_obj_id_t result =
                    sn_module_add_const(module, undriven_bits, selected_is_signed(selected), words.data(), nullptr);
                selected_values.emplace(selected, result);
                undriven_selected_values.emplace(selected);
                return result;
            }
            std::fprintf(stderr, "sn-slang: selected value '%.*s[%lld][%lld]' has no SN driver\n",
                         int(selected.symbol->name.size()), selected.symbol->name.data(),
                         static_cast<long long>(selected.index), static_cast<long long>(selected.bit));
            return SN_INVALID_ID;
        }
        if (!resolving_selected.emplace(selected).second)
        {
            auto loop = selected_continuous_loops.find(selected);
            if (loop == selected_continuous_loops.end())
            {
                uint32_t bits = selected_width(selected);
                if (!bits)
                    return SN_INVALID_ID;
                std::string name = selected_name(selected);
                sn_obj_pair_t pair =
                    sn_module_add_loop_pair(module, bits, selected_is_signed(selected), name.c_str(), nullptr);
                loop = selected_continuous_loops.emplace(selected, pair).first;
                selected_values.emplace(selected, pair.out);
            }
            return loop->second.out;
        }
        sn_obj_id_t result = lower_expression(*assignment_it->second);
        if (result != SN_INVALID_ID)
        {
            auto additional = additional_selected_assignments.find(selected);
            if (additional != additional_selected_assignments.end())
                for (const Expression* expression : additional->second)
                {
                    sn_obj_id_t driver = lower_expression(*expression);
                    if (driver == SN_INVALID_ID)
                        return SN_INVALID_ID;
                    result = resolve_net_driver(*selected.symbol, result, driver);
                    if (result == SN_INVALID_ID)
                        return SN_INVALID_ID;
                }
        }
        resolving_selected.erase(selected);
        auto loop = selected_continuous_loops.find(selected);
        if (result != SN_INVALID_ID && loop != selected_continuous_loops.end())
        {
            sn_obj_connect(module, loop->second.in, 0, result);
            result = loop->second.out;
        }
        else if (result != SN_INVALID_ID)
            selected_values.emplace(selected, result);
        return result;
    }

    bool bind_analyzed_lvalue(const sn_lvalue_t& lvalue, sn_obj_id_t value, uint32_t target_offset = 0)
    {
        uint32_t value_width = sn_obj_width(module, value);
        if (!value_width || value_width > lvalue.width || uint64_t(target_offset) + value_width > lvalue.width)
        {
            std::fprintf(stderr, "sn-slang: assignment-target width mismatch (%u into %u at %u)\n", value_width,
                         lvalue.width, target_offset);
            return false;
        }

        if (const auto* variable = std::get_if<sn_lvalue_t::variable_t>(&lvalue.descriptor))
        {
            uint32_t total_width = width(variable->symbol->getType());
            if (undriven_values.erase(variable->symbol))
                values.erase(variable->symbol);
            if (!target_offset && value_width == total_width)
            {
                if (values.contains(variable->symbol) || assignments.contains(variable->symbol) ||
                    partial_value_drivers.contains(variable->symbol))
                {
                    auto loop = continuous_loops.find(variable->symbol);
                    if (loop != continuous_loops.end() && values.at(variable->symbol) == loop->second.out &&
                        sn_obj_fanin(module, loop->second.in, 0) == SN_INVALID_ID)
                    {
                        sn_obj_connect(module, loop->second.in, 0, value);
                        return true;
                    }
                    if (variable->symbol->as_if<NetSymbol>())
                    {
                        auto existing = values.find(variable->symbol);
                        if (existing == values.end() || net_resolution_operator(*variable->symbol) == SN_NONE)
                            additional_value_drivers[variable->symbol].push_back(value);
                        else
                        {
                            existing->second = resolve_net_driver(*variable->symbol, existing->second, value);
                            if (existing->second == SN_INVALID_ID)
                                return false;
                        }
                        return true;
                    }
                    std::fprintf(stderr, "sn-slang: signal '%.*s' has multiple drivers\n",
                                 int(variable->symbol->name.size()), variable->symbol->name.data());
                    return false;
                }
                values.emplace(variable->symbol, value);
                return true;
            }
            bool has_comb_placeholder = false;
            if (auto placeholder = combinational_placeholders.find(variable->symbol);
                placeholder != combinational_placeholders.end())
            {
                auto existing = values.find(variable->symbol);
                has_comb_placeholder = existing != values.end() && existing->second == placeholder->second &&
                                       sn_obj_fanin(module, placeholder->second, 0) == SN_INVALID_ID;
            }
            if (assignments.contains(variable->symbol))
            {
                std::fprintf(stderr, "sn-slang: whole and partial drivers overlap for '%.*s'\n",
                             int(variable->symbol->name.size()), variable->symbol->name.data());
                return false;
            }
            // lower_value() can materialize a packed aggregate from its fields before another field driver is
            // encountered (for example `assign out.valid = out.ex.valid`). Such a cached aggregate is a read view,
            // not an independent whole-object driver. Invalidate it when the first or a later partial arrives.
            if (!has_comb_placeholder)
                values.erase(variable->symbol);
            auto& drivers = partial_value_drivers[variable->symbol];
            if (!add_partial_driver(drivers, total_width, target_offset, value_width, value))
            {
                std::fprintf(stderr,
                             "sn-slang: overlapping or invalid partial driver for '%.*s' "
                             "(offset=%u, width=%u, object_width=%u)\n",
                             int(variable->symbol->name.size()), variable->symbol->name.data(), target_offset,
                             value_width, total_width);
                return false;
            }
            return true;
        }

        if (const auto* element = std::get_if<sn_lvalue_t::array_element_t>(&lvalue.descriptor))
        {
            if (!element->constant_index)
            {
                std::fprintf(stderr, "sn-slang: dynamic continuous array-element assignment is unsupported\n");
                return false;
            }
            SelectedValue selected{element->symbol, *element->constant_index};
            if (undriven_selected_values.erase(selected))
                selected_values.erase(selected);
            uint32_t total_width = selected_width(selected);
            if (!target_offset && value_width == total_width)
            {
                if (selected_values.contains(selected) || selected_assignments.contains(selected) ||
                    partial_selected_drivers.contains(selected))
                {
                    std::fprintf(stderr, "sn-slang: selected value has multiple drivers\n");
                    return false;
                }
                selected_values.emplace(selected, value);
                return true;
            }
            if (selected_assignments.contains(selected) ||
                (selected_values.contains(selected) && !partial_selected_drivers.contains(selected)))
            {
                std::fprintf(stderr, "sn-slang: whole and partial array-element drivers overlap for '%.*s[%lld]'\n",
                             int(selected.symbol->name.size()), selected.symbol->name.data(),
                             static_cast<long long>(selected.index));
                return false;
            }
            if (partial_selected_drivers.contains(selected))
                selected_values.erase(selected); // Invalidate an aggregate materialized from earlier partials.
            auto& drivers = partial_selected_drivers[selected];
            if (!add_partial_driver(drivers, total_width, target_offset, value_width, value))
            {
                std::fprintf(stderr, "sn-slang: overlapping or invalid partial array-element drivers\n");
                return false;
            }
            return true;
        }

        if (std::holds_alternative<sn_lvalue_t::memory_element_t>(lvalue.descriptor))
        {
            std::fprintf(stderr, "sn-slang: continuous memory writes are unsupported\n");
            return false;
        }

        if (const auto* stream = std::get_if<sn_lvalue_t::stream_t>(&lvalue.descriptor))
        {
            if (target_offset || value_width != lvalue.width)
                return false;
            sn_obj_id_t reordered = reorder_stream_value(value, stream->slice_size);
            return reordered != SN_INVALID_ID && bind_analyzed_lvalue(*stream->inner, reordered);
        }

        if (const auto* concat = std::get_if<sn_lvalue_t::concat_t>(&lvalue.descriptor))
        {
            uint32_t source_offset = 0;
            for (auto it = concat->elements.rbegin(); it != concat->elements.rend(); ++it)
            {
                sn_obj_id_t slice = sn_module_add_slice(module, value, int32_t(source_offset + it->width - 1),
                                                        int32_t(source_offset), nullptr);
                if (!bind_analyzed_lvalue(*it, slice))
                    return false;
                source_offset += it->width;
            }
            return source_offset == lvalue.width;
        }

        if (const auto* member = std::get_if<sn_lvalue_t::member_t>(&lvalue.descriptor))
        {
            if (member->bit_offset > UINT32_MAX - target_offset)
                return false;
            return bind_analyzed_lvalue(*member->inner, value, target_offset + uint32_t(member->bit_offset));
        }

        if (const auto* select = std::get_if<sn_lvalue_t::select_t>(&lvalue.descriptor))
        {
            auto offset = static_select_offset(*select, lvalue.width);
            if (!offset)
            {
                std::fprintf(stderr, "sn-slang: dynamic or out-of-range continuous selection is unsupported\n");
                return false;
            }
            return bind_analyzed_lvalue(*select->inner, value, target_offset + *offset);
        }
        return false;
    }

    bool bind_value_symbol(const ValueSymbol& target, sn_obj_id_t value)
    {
        if (undriven_values.erase(&target))
            values.erase(&target);
        if (values.contains(&target) || assignments.contains(&target))
        {
            auto loop = continuous_loops.find(&target);
            if (loop != continuous_loops.end() && values.at(&target) == loop->second.out &&
                sn_obj_fanin(module, loop->second.in, 0) == SN_INVALID_ID)
            {
                sn_obj_connect(module, loop->second.in, 0, value);
                return true;
            }
            auto existing = values.find(&target);
            if (existing != values.end() && existing->second == value)
                return true;
            if (target.as_if<NetSymbol>())
            {
                if (existing == values.end() || net_resolution_operator(target) == SN_NONE)
                    additional_value_drivers[&target].push_back(value);
                else
                {
                    existing->second = resolve_net_driver(target, existing->second, value);
                    if (existing->second == SN_INVALID_ID)
                        return false;
                }
                return true;
            }
            std::fprintf(stderr, "sn-slang: module '%s': signal '%.*s' has multiple drivers\n",
                         sn_name_get(&module->design->names, module->name), int(target.name.size()),
                         target.name.data());
            return false;
        }
        values.emplace(&target, value);
        return true;
    }

    bool bind_lvalue_legacy(const Expression& expression, sn_obj_id_t value)
    {
        if (const auto* member = expression.as_if<MemberAccessExpression>())
            if (const auto* target = member->member.as_if<ValueSymbol>())
                return bind_value_symbol(*target, value);
        if (auto selected_bit = named_element_bit(expression))
        {
            if (undriven_selected_values.erase(*selected_bit))
                selected_values.erase(*selected_bit);
            if (selected_values.contains(*selected_bit) || selected_assignments.contains(*selected_bit))
            {
                std::fprintf(stderr, "sn-slang: unpacked array bit has multiple drivers\n");
                return false;
            }
            selected_values.emplace(*selected_bit, value);
            return true;
        }
        if (auto selected = named_element(expression))
        {
            if (undriven_selected_values.erase(*selected))
                selected_values.erase(*selected);
            if (selected_values.contains(*selected) || selected_assignments.contains(*selected))
            {
                std::fprintf(stderr, "sn-slang: module '%s': unpacked array element '%.*s[%lld]' has multiple "
                                     "drivers\n",
                             sn_name_get(&module->design->names, module->name),
                             int(selected->symbol->name.size()), selected->symbol->name.data(),
                             static_cast<long long>(selected->index));
                return false;
            }
            selected_values.emplace(*selected, value);
            return true;
        }
        if (const ValueSymbol* target = referenced_value(expression))
            return bind_value_symbol(*target, value);
        if (const auto* range = expression.as_if<RangeSelectExpression>())
        {
            const auto* named = range->value().as_if<NamedValueExpression>();
            auto array_element = named_element(range->value());
            auto left = constant_integer(range->left());
            auto right = constant_integer(range->right());
            uint32_t bits = width(*range->type);
            if ((!named && !array_element) || !left || !right || !bits || bits != sn_obj_width(module, value))
            {
                std::fprintf(stderr, "sn-slang: unsupported range-selection lvalue\n");
                return false;
            }
            auto selected_range = selected_index_range(*range, *left, *right);
            if (!selected_range)
                return false;
            int64_t least_index = selected_range->right;
            for (uint32_t offset = 0; offset < bits; offset++)
            {
                int64_t index = selected_bit_index(*selected_range, offset);
                SelectedValue selected = array_element ? SelectedValue{array_element->symbol, array_element->index,
                                                                        index}
                                                       : SelectedValue{&named->symbol, index};
                if (selected_values.contains(selected) || selected_assignments.contains(selected))
                {
                    std::fprintf(stderr, "sn-slang: selected signal has multiple drivers\n");
                    return false;
                }
                sn_obj_id_t bit = sn_module_add_slice(module, value, int32_t(offset), int32_t(offset), nullptr);
                selected_values.emplace(selected, bit);
            }
            return true;
        }
        if (const auto* concat = expression.as_if<ConcatenationExpression>())
        {
            uint32_t offset = 0;
            for (auto it = concat->operands().rbegin(); it != concat->operands().rend(); ++it)
            {
                uint32_t bits = width(*(*it)->type);
                if (!bits || uint64_t(offset) + bits > sn_obj_width(module, value))
                {
                    std::fprintf(stderr, "sn-slang: invalid concatenated assignment width\n");
                    return false;
                }
                sn_obj_id_t slice = sn_module_add_slice(module, value, int32_t(offset + bits - 1), int32_t(offset),
                                                        nullptr);
                if (!bind_lvalue(**it, slice))
                    return false;
                offset += bits;
            }
            return offset == sn_obj_width(module, value);
        }
        if (const auto* streaming = expression.as_if<StreamingConcatenationExpression>();
            streaming && streaming->getSliceSize() == 0)
        {
            auto streams = streaming->streams();
            uint32_t offset = 0;
            for (auto it = streams.rbegin(); it != streams.rend(); ++it)
            {
                if (it->withExpr)
                    return false;
                uint32_t bits = width(*it->operand->type);
                if (!bits || uint64_t(offset) + bits > sn_obj_width(module, value))
                    return false;
                sn_obj_id_t slice = sn_module_add_slice(module, value, int32_t(offset + bits - 1), int32_t(offset),
                                                        nullptr);
                if (!bind_lvalue(*it->operand, slice))
                    return false;
                offset += bits;
            }
            return offset == sn_obj_width(module, value);
        }
        std::fprintf(stderr, "sn-slang: unsupported continuous-assignment lvalue kind %u\n",
                     unsigned(expression.kind));
        return false;
    }

    bool bind_lvalue(const Expression& expression, sn_obj_id_t value)
    {
        // Slang exposes unpacked-structure members as ValueSymbols and expression lowering uses those member
        // symbols directly. Keep the assignment side on the same representation instead of packing the containing
        // unpacked structure into an artificial bit vector.
        std::string error;
        auto lvalue = analyze_lvalue(expression, error);
        if (lvalue)
            return bind_analyzed_lvalue(*lvalue, value);
        // Preserve the established diagnostics and behavior for constructs not yet represented by the common
        // descriptor. This fallback is temporary and shrinks as the descriptor gains coverage.
        return bind_lvalue_legacy(expression, value);
    }

    void register_structured_driver(const Expression& expression, const AssignmentExpression* assignment)
    {
        if (const auto* nested = expression.as_if<AssignmentExpression>();
            nested && nested->right().as_if<EmptyArgumentExpression>())
        {
            register_structured_driver(nested->left(), assignment);
            return;
        }
        if (const auto* conversion = expression.as_if<ConversionExpression>())
        {
            register_structured_driver(conversion->operand(), assignment);
            return;
        }
        if (const ValueSymbol* value = referenced_value(expression))
        {
            structured_drivers[value].push_back(assignment);
            return;
        }
        if (const auto* concat = expression.as_if<ConcatenationExpression>())
        {
            for (const Expression* operand : concat->operands())
                register_structured_driver(*operand, assignment);
            return;
        }
        if (const auto* pattern = expression.as_if<SimpleAssignmentPatternExpression>(); pattern && pattern->isLValue)
        {
            for (const Expression* element : pattern->elements())
                register_structured_driver(*element, assignment);
            return;
        }
        if (const auto* streaming = expression.as_if<StreamingConcatenationExpression>())
        {
            for (const auto& stream : streaming->streams())
                register_structured_driver(*stream.operand, assignment);
            return;
        }
        if (const auto* range = expression.as_if<RangeSelectExpression>())
        {
            register_structured_driver(range->value(), assignment);
            return;
        }
        if (const auto* element = expression.as_if<ElementSelectExpression>())
        {
            register_structured_driver(element->value(), assignment);
            return;
        }
        if (const auto* member = expression.as_if<MemberAccessExpression>())
            register_structured_driver(member->value(), assignment);
    }

    bool lower_structured_assignment(const AssignmentExpression& assignment)
    {
        if (lowered_structured.contains(&assignment))
            return true;
        if (!lowering_structured.insert(&assignment).second)
        {
            SourceLocation location = source_manager->getFullyOriginalLoc(assignment.sourceRange.start());
            std::string path = location ? source_manager->getFullPath(location.buffer()).string() : "<unknown>";
            size_t line = location ? source_manager->getLineNumber(location) : 0;
            std::fprintf(stderr,
                         "sn-slang: %s:%zu: combinational structured-assignment cycle is unsupported\n",
                         path.c_str(), line);
            return false;
        }
        sn_obj_id_t rhs = lower_expression(assignment.right());
        bool success = rhs != SN_INVALID_ID && bind_lvalue(assignment.left(), rhs);
        lowering_structured.erase(&assignment);
        if (success)
            lowered_structured.insert(&assignment);
        return success;
    }

    bool collect_primitive_driver(const PrimitiveInstanceSymbol& inst)
    {
        std::span<const Expression* const> ports = inst.getPortConnections();
        std::string_view name = inst.primitiveType.name;
        if (inst.primitiveType.primitiveKind == PrimitiveSymbol::BiDiSwitch || name == "tran" ||
            name == "rtran" || name == "tranif0" || name == "tranif1" || name == "rtranif0" ||
            name == "rtranif1")
        {
            std::string message = "bidirectional switch primitive '" + std::string(name) +
                                  "' is not representable in SN";
            report_timing_error(inst.location, message.c_str());
            return false;
        }
        if (inst.primitiveType.primitiveKind == PrimitiveSymbol::UserDefined)
        {
            std::string message = "user-defined primitive '" + std::string(name) +
                                  "' requires explicit black-box support";
            report_timing_error(inst.location, message.c_str());
            return false;
        }

        std::vector<uint32_t> outputs;
        if (name == "pullup" || name == "pulldown")
        {
            for (uint32_t index = 0; index < ports.size(); index++)
                outputs.push_back(index);
        }
        else if (inst.primitiveType.primitiveKind == PrimitiveSymbol::NOutput)
        {
            for (uint32_t index = 0; index + 1 < ports.size(); index++)
                outputs.push_back(index);
        }
        else if (inst.primitiveType.primitiveKind == PrimitiveSymbol::NInput)
            outputs.push_back(0);
        else
        {
            for (uint32_t index = 0; index < inst.primitiveType.ports.size() && index < ports.size(); index++)
            {
                PrimitivePortDirection direction = inst.primitiveType.ports[index]->direction;
                if (direction == PrimitivePortDirection::Out || direction == PrimitivePortDirection::OutReg)
                    outputs.push_back(index);
            }
            if (outputs.empty() && !ports.empty())
                outputs.push_back(0);
        }

        for (uint32_t output : outputs)
        {
            const Expression* expression = ports[output];
            if (!expression)
                continue;
            if (const auto* assignment = expression->as_if<AssignmentExpression>();
                assignment && assignment->isLValueArg())
                expression = &assignment->left();
            const ValueSymbol* value = referenced_value(*expression);
            if (!value)
            {
                auto selected = named_element_bit(*expression);
                if (!selected) selected = named_element(*expression);
                if (selected && width(*expression->type) == 1)
                {
                    primitive_output_expressions.emplace(expression, PrimitiveDriver{&inst, output});
                    auto [existing, inserted] = selected_assignments.emplace(*selected, expression);
                    if (inserted)
                        selected_assignment_order.push_back(*selected);
                    else if (selected->symbol->as_if<NetSymbol>())
                        additional_selected_assignments[*selected].push_back(expression);
                    else
                    {
                        report_timing_error(expression->sourceRange.start(), "primitive output has multiple variable drivers");
                        return false;
                    }
                    continue;
                }
                std::string message = "primitive '" + std::string(name) +
                                      "' has a selected or structured output target that is not yet supported";
                report_timing_error(expression->sourceRange.start(), message.c_str());
                return false;
            }
            primitive_value_drivers[value].push_back({&inst, output});
            assignment_order.push_back(value);
        }
        return true;
    }

    std::optional<std::string_view> memory_hint(const ValueSymbol& symbol) const
    {
        static constexpr std::string_view names[] = {
            "ram_block", "rom_block", "ram_style", "rom_style", "ramstyle",
            "romstyle", "syn_ramstyle", "syn_romstyle"};
        for (const AttributeSymbol* attribute : body->getCompilation().getAttributes(symbol))
            for (std::string_view name : names)
                if (attribute->name == name && !attribute->getValue().isFalse())
                    return attribute->name;
        return std::nullopt;
    }

    void report_memory_disqualification(const ValueSymbol& symbol, SourceLocation use_location) const
    {
        auto hint = memory_hints.find(&symbol);
        if (hint == memory_hints.end())
            return;
        use_location = source_manager->getFullyOriginalLoc(use_location);
        std::string path = use_location ? source_manager->getFullPath(use_location.buffer()).string() : "<unknown>";
        size_t line = use_location ? source_manager->getLineNumber(use_location) : 0;
        std::fprintf(stderr,
                     "sn-slang: %s:%zu: warning: memory '%.*s' requested by attribute '%s' was not inferred "
                     "because of this use\n",
                     path.c_str(), line, int(symbol.name.size()), symbol.name.data(), hint->second.c_str());
    }

    bool collect_assignments(const Scope& scope)
    {
        for (const Symbol& symbol : scope.members())
        {
            if (const auto* primitive = symbol.as_if<PrimitiveInstanceSymbol>())
            {
                if (!collect_primitive_driver(*primitive))
                    return false;
                continue;
            }
            if (const auto* procedural = symbol.as_if<ProceduralBlockSymbol>())
            {
                if (!source_is_translate_off(procedural->location))
                    procedural_blocks.push_back(procedural);
                continue;
            }
            const ValueSymbol* declared_value = nullptr;
            bool declared_variable = false;
            if (const auto* net = symbol.as_if<NetSymbol>())
                declared_value = net;
            else if (const auto* variable = symbol.as_if<VariableSymbol>())
            {
                declared_value = variable;
                declared_variable = true;
            }
            // Unpacked variable arrays represent storage candidates. Unpacked
            // net arrays are structural bundles whose element assignments must
            // remain combinational; treating them as memories drops their
            // continuous drivers (common in generated AXI channel routing).
            if (declared_variable && declared_value->getType().isUnpackedArray() &&
                declared_value->getType().hasFixedRange())
            {
                if (declared_value->getInitializer())
                {
                    std::fprintf(stderr, "sn-slang: initialized memories are not yet supported\n");
                    return false;
                }
                memory_symbols.push_back(declared_value);
                auto hint = memory_hint(*declared_value);
                if (hint)
                    memory_hints.emplace(declared_value, std::string(*hint));
                if (!memories_from_attributes_only || hint)
                    memory_candidates.insert(declared_value);
                continue;
            }
            if (declared_value && declared_value->getInitializer())
            {
                if (!collected_declaration_initializers.emplace(declared_value).second)
                    continue;
                if (declared_variable)
                {
                    variable_initializers.emplace_back(declared_value, declared_value->getInitializer());
                    continue;
                }
                if (values.contains(declared_value) ||
                    !assignments.emplace(declared_value, declared_value->getInitializer()).second)
                {
                    std::fprintf(stderr, "sn-slang: signal '%.*s' has multiple drivers\n",
                                 int(declared_value->name.size()), declared_value->name.data());
                    return false;
                }
                assignment_order.push_back(declared_value);
            }

            const auto* continuous = symbol.as_if<ContinuousAssignSymbol>();
            if (!continuous)
                continue;
            const auto* assignment = continuous->getAssignment().as_if<AssignmentExpression>();
            const ValueSymbol* lhs = assignment ? referenced_value(assignment->left()) : nullptr;
            if (!assignment || assignment->isCompound())
            {
                std::fprintf(stderr, "sn-slang: compound continuous assignments are unsupported\n");
                return false;
            }
            if (!lhs)
            {
                if (auto selected_bit = named_element_bit(assignment->left()))
                {
                    if (selected_values.contains(*selected_bit))
                    {
                        std::fprintf(stderr, "sn-slang: module '%s': selected bit '%.*s[%lld][%lld]' has multiple "
                                             "drivers\n",
                                     sn_name_get(&module->design->names, module->name),
                                     int(selected_bit->symbol->name.size()), selected_bit->symbol->name.data(),
                                     static_cast<long long>(selected_bit->index),
                                     static_cast<long long>(selected_bit->bit));
                        return false;
                    }
                    auto [existing, inserted] =
                        selected_assignments.emplace(*selected_bit, &assignment->right());
                    if (inserted)
                        selected_assignment_order.push_back(*selected_bit);
                    else if (selected_bit->symbol->as_if<NetSymbol>())
                        additional_selected_assignments[*selected_bit].push_back(&assignment->right());
                    else
                    {
                        std::fprintf(stderr, "sn-slang: ordinary net bit '%.*s[%lld][%lld]' has multiple drivers\n",
                                     int(selected_bit->symbol->name.size()), selected_bit->symbol->name.data(),
                                     static_cast<long long>(selected_bit->index),
                                     static_cast<long long>(selected_bit->bit));
                        return false;
                    }
                    continue;
                }
                if (auto selected = named_element(assignment->left()))
                {
                    if (selected_values.contains(*selected))
                    {
                        std::fprintf(stderr, "sn-slang: module '%s': selected value '%.*s[%lld]' has multiple "
                                             "drivers\n",
                                     sn_name_get(&module->design->names, module->name),
                                     int(selected->symbol->name.size()), selected->symbol->name.data(),
                                     static_cast<long long>(selected->index));
                        return false;
                    }
                    auto [existing, inserted] = selected_assignments.emplace(*selected, &assignment->right());
                    if (inserted)
                        selected_assignment_order.push_back(*selected);
                    else if (selected->symbol->as_if<NetSymbol>())
                        additional_selected_assignments[*selected].push_back(&assignment->right());
                    else
                    {
                        std::fprintf(stderr, "sn-slang: ordinary net element '%.*s[%lld]' has multiple drivers\n",
                                     int(selected->symbol->name.size()), selected->symbol->name.data(),
                                     static_cast<long long>(selected->index));
                        return false;
                    }
                    continue;
                }
                if (!assignment->left().as_if<ConcatenationExpression>() &&
                    !assignment->left().as_if<RangeSelectExpression>() &&
                    !assignment->left().as_if<ElementSelectExpression>() &&
                    !assignment->left().as_if<MemberAccessExpression>() &&
                    !assignment->left().as_if<SimpleAssignmentPatternExpression>() &&
                    !assignment->left().as_if<StreamingConcatenationExpression>())
                {
                    std::fprintf(stderr, "sn-slang: module '%s': unsupported continuous-assignment lvalue kind %u\n",
                                 sn_name_get(&module->design->names, module->name),
                                 unsigned(assignment->left().kind));
                    return false;
                }
                structured_assignments.push_back(assignment);
                register_structured_driver(assignment->left(), assignment);
                continue;
            }
            if (values.contains(lhs) || !assignments.emplace(lhs, &assignment->right()).second)
            {
                if (inout_symbols.contains(lhs) && inout_assignments.emplace(lhs, &assignment->right()).second)
                    continue;
                if (!values.contains(lhs))
                {
                    additional_value_assignments[lhs].push_back(&assignment->right());
                    continue;
                }
                std::fprintf(stderr, "sn-slang: signal '%.*s' has multiple drivers\n", int(lhs->name.size()),
                             lhs->name.data());
                return false;
            }
            assignment_order.push_back(lhs);

            continue;
        }
        for (const Symbol& symbol : scope.members())
        {
            if (symbol.as_if<InstanceSymbol>())
                continue;
            if (const auto* generate = symbol.as_if<GenerateBlockSymbol>(); generate && generate->isUninstantiated)
                continue;
            if (const Scope* child_scope = symbol.as_if<Scope>())
                if (!collect_assignments(*child_scope))
                    return false;
        }
        return true;
    }

    struct MemoryEligibility : ASTVisitor<MemoryEligibility,
                                   VisitFlags::Statements | VisitFlags::Expressions>
    {
        // An unpacked static variable remains a memory only while every reference addresses an element. Whole-
        // array use and writes outside a single-edge nonblocking process disqualify it and leave it as a register
        // bank. Select expressions still visit their address logic, so arrays used as addresses are classified too.
        struct LhsVisitor : ASTVisitor<LhsVisitor, VisitFlags::Expressions>
        {
            MemoryEligibility& analysis;

            explicit LhsVisitor(MemoryEligibility& analysis) : analysis(analysis) {}

            void handle(const ElementSelectExpression& expression)
            {
                expression.value().visit(*this);
                expression.selector().visit(analysis);
            }

            void handle(const RangeSelectExpression& expression)
            {
                expression.value().visit(*this);
                expression.left().visit(analysis);
                expression.right().visit(analysis);
            }

            void handle(const ValueExpressionBase& expression)
            {
                analysis.disqualify(expression.symbol, expression.sourceRange.start());
            }
        };

        ModuleImporter& importer;
        std::unordered_set<const ValueSymbol*> candidates;
        bool write_allowed = false;

        explicit MemoryEligibility(ModuleImporter& importer) :
            importer(importer), candidates(importer.memory_candidates)
        {
        }

        // Each ModuleImporter analyzes exactly one module body. Child instances are analyzed separately from
        // their canonical bodies; descending here repeats the complete child hierarchy once per instance and can
        // turn a shallow wrapper with many identical instances into an enormous memory-eligibility traversal.
        void handle(const InstanceSymbol& symbol) { symbol.visitExprs(*this); }

        void disqualify(const ValueSymbol& symbol, SourceLocation location)
        {
            if (candidates.contains(&symbol))
                importer.report_memory_disqualification(symbol, location);
            candidates.erase(&symbol);
        }

        void handle(const ValueExpressionBase& expression)
        {
            disqualify(expression.symbol, expression.sourceRange.start());
        }

        void handle(const ElementSelectExpression& expression)
        {
            if (!ValueExpressionBase::isKind(expression.value().kind))
                expression.value().visit(*this);
            expression.selector().visit(*this);
        }

        void handle(const AssignmentExpression& assignment)
        {
            LhsVisitor lhs(*this);
            assignment.left().visit(lhs);
            assignment.right().visit(*this);
        }

        void handle(const ExpressionStatement& statement)
        {
            const auto* assignment = statement.expr.as_if<AssignmentExpression>();
            if (!assignment || !assignment->isNonBlocking() || !write_allowed)
            {
                statement.expr.visit(*this);
                return;
            }

            assignment->right().visit(*this);
            const Expression* lvalue = &assignment->left();
            LhsVisitor fallback(*this);
            bool selected_element = false;
            while (true)
            {
                if (const auto* range = lvalue->as_if<RangeSelectExpression>())
                {
                    range->left().visit(*this);
                    range->right().visit(*this);
                    lvalue = &range->value();
                    continue;
                }
                if (const auto* element = lvalue->as_if<ElementSelectExpression>())
                {
                    element->selector().visit(*this);
                    lvalue = &element->value();
                    selected_element = true;
                    if (selected_element && ValueExpressionBase::isKind(lvalue->kind))
                        return;
                    continue;
                }
                if (const auto* member = lvalue->as_if<MemberAccessExpression>())
                {
                    lvalue = &member->value();
                    continue;
                }
                lvalue->visit(fallback);
                return;
            }
        }

        void handle(const ProceduralBlockSymbol& procedural)
        {
            if (procedural.procedureKind == ProceduralBlockKind::Initial)
                return;
            bool saved = write_allowed;
            write_allowed = false;
            if (const TimedStatement* timed = timed_body(procedural))
            {
                std::vector<const SignalEventControl*> events;
                write_allowed = collect_event_controls(timed->timing, events) && events.size() == 1 &&
                                (events[0]->edge == EdgeKind::PosEdge || events[0]->edge == EdgeKind::NegEdge);
            }
            procedural.getBody().visit(*this);
            write_allowed = saved;
        }
    };

    struct FixedLoopIndexBound : ASTVisitor<FixedLoopIndexBound,
                                            VisitFlags::Statements | VisitFlags::Expressions>
    {
        struct UsesVariable : ASTVisitor<UsesVariable, VisitFlags::Expressions>
        {
            const ValueSymbol* variable;
            bool found = false;

            explicit UsesVariable(const ValueSymbol* variable) : variable(variable) {}
            void handle(const ValueExpressionBase& expression) { found = found || &expression.symbol == variable; }
        };

        const ValueSymbol* variable;
        uint32_t limit = 0;

        explicit FixedLoopIndexBound(const ValueSymbol* variable) : variable(variable) {}

        void handle(const ElementSelectExpression& expression)
        {
            const Expression* selector = &expression.selector();
            while (const auto* conversion = selector->as_if<ConversionExpression>())
                selector = &conversion->operand();
            const auto* named = selector->as_if<NamedValueExpression>();
            if (named && &named->symbol == variable && expression.value().type->hasFixedRange())
            {
                uint64_t width = uint64_t(expression.value().type->getFixedRange().width());
                if (width && width <= UINT32_MAX)
                    limit = !limit ? uint32_t(width) : std::min(limit, uint32_t(width));
            }
            expression.value().visit(*this);
        }

        void handle(const RangeSelectExpression& expression)
        {
            UsesVariable uses(variable);
            expression.left().visit(uses);
            uint64_t value_width = expression.value().type->isFixedSize()
                                       ? expression.value().type->getBitstreamWidth()
                                       : 0;
            if (uses.found && expression.getSelectionKind() != RangeSelectionKind::Simple && value_width &&
                value_width <= UINT32_MAX)
                limit = !limit ? uint32_t(value_width) : std::min(limit, uint32_t(value_width));
            expression.value().visit(*this);
            expression.right().visit(*this);
        }
    };

    std::optional<uint32_t> countdown_loop_limit(const ForLoopStatement& loop) const
    {
        if (loop.steps.size() != 1)
            return std::nullopt;
        const ValueSymbol* loop_variable = nullptr;
        const Expression* initializer = nullptr;
        if (loop.loopVars.size() == 1)
        {
            loop_variable = loop.loopVars[0];
            initializer = loop_variable->getInitializer();
        }
        else if (loop.loopVars.empty() && loop.initializers.size() == 1)
        {
            const auto* assignment = loop.initializers[0]->as_if<AssignmentExpression>();
            const auto* named = assignment ? assignment->left().as_if<NamedValueExpression>() : nullptr;
            loop_variable = named ? &named->symbol : nullptr;
            initializer = assignment ? &assignment->right() : nullptr;
        }
        if (!loop_variable || !initializer)
            return std::nullopt;
        auto initial = constant_integer(*initializer);
        if (!initial || *initial < 0 || *initial >= 1000000)
            return std::nullopt;
        auto strip = [](const Expression* expression) {
            while (const auto* conversion = expression->as_if<ConversionExpression>())
                expression = &conversion->operand();
            return expression;
        };
        const Expression* step = strip(loop.steps[0]);
        bool decrements = false;
        if (const auto* unary = step->as_if<UnaryExpression>())
        {
            const auto* value = strip(&unary->operand())->as_if<NamedValueExpression>();
            decrements = (unary->op == UnaryOperator::Predecrement ||
                          unary->op == UnaryOperator::Postdecrement) &&
                         value && &value->symbol == loop_variable;
        }
        if (const auto* assignment = step->as_if<AssignmentExpression>())
        {
            const auto* lhs = strip(&assignment->left())->as_if<NamedValueExpression>();
            const auto* sub = strip(&assignment->right())->as_if<BinaryExpression>();
            const auto* sub_lhs = sub ? strip(&sub->left())->as_if<NamedValueExpression>() : nullptr;
            decrements = lhs && &lhs->symbol == loop_variable && sub &&
                         sub->op == BinaryOperator::Subtract && sub_lhs &&
                         &sub_lhs->symbol == loop_variable && constant_integer(sub->right()) == 1;
        }
        return decrements ? std::optional<uint32_t>(uint32_t(*initial) + 1) : std::nullopt;
    }

    bool prepare_memories()
    {
        MemoryEligibility eligibility(*this);
        body->visit(eligibility);
        for (const ValueSymbol* symbol : memory_symbols)
        {
            if (!eligibility.candidates.contains(symbol))
                continue;
            const Type& array_type = symbol->getType();
            const Type* element_type = array_type.getArrayElementType();
            ConstantRange range = array_type.getFixedRange();
            uint32_t bits = element_type ? width(*element_type) : 0;
            if (!element_type || !bits || range.width() <= 0 || uint64_t(range.width()) > UINT32_MAX)
            {
                std::fprintf(stderr, "sn-slang: memory '%.*s' has an unsupported type or depth\n",
                             int(symbol->name.size()), symbol->name.data());
                return false;
            }
            std::string name(symbol->name);
            sn_obj_pair_t pair = sn_module_add_mem_pair(module, bits, element_type->isSigned(), uint32_t(range.width()),
                                                        name.c_str(), nullptr);
            add_metadata(pair.out, *symbol);
            if (preserve_state)
            {
                auto path = sec_relative_path(*symbol, SecPathPolicy::General);
                if (path && !path->empty())
                {
                    const Type& word = element_type->getCanonicalType();
                    const auto* packed_array = word.as_if<PackedArrayType>();
                    if (word.isIntegral() && !word.isStruct() && !word.isUnion() &&
                        (!packed_array || !packed_array->elementType.getCanonicalType().isPackedArray()))
                    {
                        ConstantRange packed = word.getFixedRange();
                        std::string identity = *path + "|" + std::to_string(range.lower()) + ":" +
                            std::to_string(range.width()) + ":" + std::to_string(packed.left) + ":" +
                            std::to_string(packed.right) + ":" + std::to_string(bits);
                        sn_module_add_attribute_record(module, pair.out, "sn_sec_memory", identity.c_str());
                    }
                }
            }
            memories.emplace(symbol,
                             Memory{pair, range.lower(), uint32_t(range.width()), range.left,
                                    range.left <= range.right ? int64_t(1) : int64_t(-1)});
        }
        return true;
    }

    struct MemoryInit
    {
        std::vector<uint32_t> data;
        std::vector<uint32_t> mask;
        bool loaded = false;
    };

    static void set_packed_bit(std::vector<uint32_t>& words, uint64_t bit)
    {
        words[size_t(bit >> 5)] |= uint32_t(1) << (bit & 31);
    }

    static bool tokenize_memory_file(const std::filesystem::path& path, std::vector<std::string>& tokens)
    {
        std::ifstream input(path);
        if (!input)
        {
            std::fprintf(stderr, "sn-slang: cannot open memory initialization file '%s'\n", path.c_str());
            return false;
        }
        std::string text((std::istreambuf_iterator<char>(input)), std::istreambuf_iterator<char>());
        std::string token;
        bool line_comment = false;
        bool block_comment = false;
        for (size_t i = 0; i < text.size(); i++)
        {
            char ch = text[i];
            char next = i + 1 < text.size() ? text[i + 1] : '\0';
            if (line_comment)
            {
                if (ch == '\n')
                    line_comment = false;
                continue;
            }
            if (block_comment)
            {
                if (ch == '*' && next == '/')
                {
                    block_comment = false;
                    i++;
                }
                continue;
            }
            if (ch == '/' && next == '/')
            {
                if (!token.empty())
                {
                    tokens.push_back(std::move(token));
                    token.clear();
                }
                line_comment = true;
                i++;
                continue;
            }
            if (ch == '/' && next == '*')
            {
                if (!token.empty())
                {
                    tokens.push_back(std::move(token));
                    token.clear();
                }
                block_comment = true;
                i++;
                continue;
            }
            if (std::isspace(static_cast<unsigned char>(ch)))
            {
                if (!token.empty())
                {
                    tokens.push_back(std::move(token));
                    token.clear();
                }
            }
            else
                token.push_back(ch);
        }
        if (block_comment)
        {
            std::fprintf(stderr, "sn-slang: unterminated comment in memory initialization file '%s'\n",
                         path.c_str());
            return false;
        }
        if (!token.empty())
            tokens.push_back(std::move(token));
        return true;
    }

    static std::optional<uint64_t> parse_memory_address(std::string_view token)
    {
        uint64_t value = 0;
        bool has_digit = false;
        if (token.size() < 2 || token[0] != '@')
            return std::nullopt;
        for (char ch : token.substr(1))
        {
            if (ch == '_')
                continue;
            has_digit = true;
            unsigned digit;
            if (ch >= '0' && ch <= '9')
                digit = unsigned(ch - '0');
            else if (ch >= 'a' && ch <= 'f')
                digit = unsigned(ch - 'a' + 10);
            else if (ch >= 'A' && ch <= 'F')
                digit = unsigned(ch - 'A' + 10);
            else
                return std::nullopt;
            if (value > (UINT64_MAX - digit) / 16)
                return std::nullopt;
            value = value * 16 + digit;
        }
        return has_digit ? std::optional<uint64_t>(value) : std::nullopt;
    }

    static bool store_memory_value(std::string_view token, unsigned radix, uint32_t width, uint64_t bit_offset,
                                   MemoryInit& init)
    {
        uint32_t bit = 0;
        bool has_digit = false;
        for (auto it = token.rbegin(); it != token.rend() && bit < width; ++it)
        {
            char ch = *it;
            if (ch == '_')
                continue;
            has_digit = true;
            unsigned digit;
            bool known = true;
            if (ch >= '0' && ch <= '9')
                digit = unsigned(ch - '0');
            else if (ch >= 'a' && ch <= 'f')
                digit = unsigned(ch - 'a' + 10);
            else if (ch >= 'A' && ch <= 'F')
                digit = unsigned(ch - 'A' + 10);
            else if (ch == 'x' || ch == 'X' || ch == 'z' || ch == 'Z' || ch == '?')
            {
                digit = 0; // Unknown data is concretized to zero and marked invalid below.
                known = false;
            }
            else
                return false;
            if (digit >= radix)
                return false;
            unsigned digit_bits = radix == 16 ? 4 : 1;
            for (unsigned i = 0; i < digit_bits && bit < width; i++, bit++)
            {
                if ((digit >> i) & 1)
                    set_packed_bit(init.data, bit_offset + bit);
                if (known)
                    set_packed_bit(init.mask, bit_offset + bit);
            }
        }
        if (!has_digit)
            return false;
        // A short word is zero-extended, so bits above the most-significant file digit are known zeros.
        for (; bit < width; bit++)
            set_packed_bit(init.mask, bit_offset + bit);
        init.loaded = true;
        return true;
    }

    bool load_memory_call(const CallExpression& call,
                          std::unordered_map<const ValueSymbol*, MemoryInit>& initializers)
    {
        std::string_view task = call.getSubroutineName();
        if (!call.isSystemCall() || (task != "$readmemh" && task != "$readmemb"))
            return true;
        auto arguments = call.arguments();
        auto unwrap_conversion = [](const Expression* expression) {
            while (const auto* conversion = expression ? expression->as_if<ConversionExpression>() : nullptr)
                expression = &conversion->operand();
            return expression;
        };
        const Expression* filename = arguments.size() >= 1 ? unwrap_conversion(arguments[0]) : nullptr;
        const Expression* target = arguments.size() >= 2 ? unwrap_conversion(arguments[1]) : nullptr;
        if (const auto* assignment = target ? target->as_if<AssignmentExpression>() : nullptr)
            target = unwrap_conversion(&assignment->left());
        const auto* literal = filename ? filename->as_if<StringLiteral>() : nullptr;
        const auto* named = target ? target->as_if<NamedValueExpression>() : nullptr;
        if (!literal || !named || arguments.size() > 4)
        {
            std::fprintf(stderr, "sn-slang: unsupported %.*s argument list (%zu arguments, kinds %u and %u)\n",
                         int(task.size()), task.data(), arguments.size(), filename ? unsigned(filename->kind) : 0,
                         target ? unsigned(target->kind) : 0);
            return false;
        }
        auto memory_it = memories.find(&named->symbol);
        if (memory_it == memories.end())
        {
            std::fprintf(stderr, "sn-slang: %.*s target '%.*s' is not an SN memory\n", int(task.size()), task.data(),
                         int(named->symbol.name.size()), named->symbol.name.data());
            return false;
        }
        const Memory& memory = memory_it->second;
        int64_t address = memory.load_start;
        if (arguments.size() >= 3)
        {
            auto start = constant_integer(*arguments[2]);
            if (!start)
            {
                std::fprintf(stderr, "sn-slang: %.*s start address is not constant\n", int(task.size()), task.data());
                return false;
            }
            address = *start;
        }
        std::optional<int64_t> finish;
        if (arguments.size() >= 4)
        {
            finish = constant_integer(*arguments[3]);
            if (!finish)
            {
                std::fprintf(stderr, "sn-slang: %.*s finish address is not constant\n", int(task.size()), task.data());
                return false;
            }
        }
        int64_t step = finish ? (*finish >= address ? 1 : -1) : memory.load_step;
        std::filesystem::path path(literal->getValue());
        if (path.is_relative())
            path = source_manager->getFullPath(call.sourceRange.start().buffer()).parent_path() / path;
        path = path.lexically_normal();
        std::vector<std::string> tokens;
        if (!tokenize_memory_file(path, tokens))
            return false;

        uint32_t width = sn_obj_width(module, memory.pair.out);
        uint64_t init_width = uint64_t(width) * memory.depth;
        if (init_width > UINT32_MAX)
        {
            std::fprintf(stderr, "sn-slang: memory initialization is wider than UINT32_MAX bits\n");
            return false;
        }
        MemoryInit& init = initializers[&named->symbol];
        if (init.data.empty())
        {
            init.data.resize(sn_const_word_count(uint32_t(init_width)));
            init.mask.resize(sn_const_word_count(uint32_t(init_width)));
        }
        for (const std::string& token : tokens)
        {
            if (!token.empty() && token[0] == '@')
            {
                auto explicit_address = parse_memory_address(token);
                if (!explicit_address || *explicit_address > uint64_t(INT64_MAX))
                {
                    std::fprintf(stderr, "sn-slang: invalid memory address token '%s' in '%s'\n", token.c_str(),
                                 path.c_str());
                    return false;
                }
                address = int64_t(*explicit_address);
                continue;
            }
            if (finish && ((step > 0 && address > *finish) || (step < 0 && address < *finish)))
                break;
            int64_t ordinal = address - memory.start_offset;
            if (ordinal < 0 || uint64_t(ordinal) >= memory.depth)
            {
                std::fprintf(stderr, "sn-slang: memory address %lld is outside '%.*s'\n", (long long)address,
                             int(named->symbol.name.size()), named->symbol.name.data());
                return false;
            }
            if (!store_memory_value(token, task == "$readmemh" ? 16 : 2, width, uint64_t(ordinal) * width, init))
            {
                std::fprintf(stderr, "sn-slang: invalid data token '%s' in '%s'\n", token.c_str(), path.c_str());
                return false;
            }
            address += step;
        }
        return true;
    }

    bool collect_memory_calls(const Statement& statement,
                              std::unordered_map<const ValueSymbol*, MemoryInit>& initializers)
    {
        if (const auto* timed = statement.as_if<TimedStatement>())
            return collect_memory_calls(timed->stmt, initializers);
        if (const auto* block = statement.as_if<BlockStatement>())
            return collect_memory_calls(block->body, initializers);
        if (const auto* list = statement.as_if<StatementList>())
        {
            for (const Statement* child : list->list)
                if (!collect_memory_calls(*child, initializers))
                    return false;
            return true;
        }
        if (const auto* expression = statement.as_if<ExpressionStatement>())
        {
            const auto* call = expression->expr.as_if<CallExpression>();
            if (call)
                return load_memory_call(*call, initializers);
            const auto* assignment = expression->expr.as_if<AssignmentExpression>();
            auto element = assignment ? memory_element(assignment->left()) : std::nullopt;
            if (!element)
                return true;
            auto address = constant_integer(*element->address);
            EvalContext local_context(*body->parentInstance);
            EvalContext& context = active_constant_context ? *active_constant_context : local_context;
            ConstantValue value = assignment->right().eval(context);
            const Memory& memory = memories.at(element->memory);
            uint32_t word_width = sn_obj_width(module, memory.pair.out);
            if (!address || !value || !value.isInteger() || value.integer().getBitWidth() != word_width)
            {
                std::fprintf(stderr, "sn-slang: initial memory assignment requires constant address and data\n");
                return false;
            }
            int64_t ordinal = *address - memory.start_offset;
            if (ordinal < 0 || uint64_t(ordinal) >= memory.depth)
                return false;
            uint64_t init_width_64 = uint64_t(word_width) * memory.depth;
            if (!init_width_64 || init_width_64 > UINT32_MAX)
            {
                std::fprintf(stderr, "sn-slang: initial memory image exceeds the SN constant-size limit\n");
                return false;
            }
            uint32_t init_width = uint32_t(init_width_64);
            MemoryInit& init = initializers[element->memory];
            if (init.data.empty())
            {
                init.data.resize(sn_const_word_count(init_width));
                init.mask.resize(sn_const_word_count(init_width));
            }
            for (uint32_t bit = 0; bit < word_width; bit++)
            {
                logic_t logic = value.integer()[int32_t(bit)];
                uint64_t packed_bit = uint64_t(ordinal) * word_width + bit;
                if (!logic.isUnknown() && logic.value)
                    set_packed_bit(init.data, packed_bit);
                if (!logic.isUnknown())
                    set_packed_bit(init.mask, packed_bit);
            }
            init.loaded = true;
            return true;
        }
        if (const auto* conditional = statement.as_if<ConditionalStatement>())
            return collect_memory_calls(conditional->ifTrue, initializers) &&
                   (!conditional->ifFalse || collect_memory_calls(*conditional->ifFalse, initializers));
        if (const auto* loop = statement.as_if<ForLoopStatement>())
        {
            if (loop->loopVars.size() || !loop->stopExpr)
                return false;
            EvalContext local_loop_context(*body->parentInstance);
            EvalContext& loop_context = active_constant_context ? *active_constant_context : local_loop_context;
            EvalFrameGuard loop_frame(loop_context);
            LoopConstantGuard loop_constants(active_loop_constants);
            for (const Expression* initializer : loop->initializers)
            {
                const auto* assignment = initializer->as_if<AssignmentExpression>();
                const auto* named = assignment ? assignment->left().as_if<NamedValueExpression>() : nullptr;
                ConstantValue* local = named ? loop_context.createLocal(&named->symbol) : nullptr;
                if (!local || !initializer->eval(loop_context))
                    return false;
                loop_constants.bind(&named->symbol, local);
            }
            EvalContext* previous_context = active_constant_context;
            active_constant_context = &loop_context;
            for (uint32_t iteration = 0; iteration < 1000000; iteration++)
            {
                ConstantValue stop = loop->stopExpr->eval(loop_context);
                if (!stop || !stop.isInteger() || stop.integer().hasUnknown())
                    break;
                if (!stop.isTrue())
                {
                    active_constant_context = previous_context;
                    return true;
                }
                if (!collect_memory_calls(loop->body, initializers))
                {
                    active_constant_context = previous_context;
                    return false;
                }
                for (const Expression* step : loop->steps)
                    if (!step->eval(loop_context))
                    {
                        active_constant_context = previous_context;
                        return false;
                    }
            }
            active_constant_context = previous_context;
            std::fprintf(stderr, "sn-slang: initial memory loop is nonconstant or exceeds the unrolling limit\n");
            return false;
        }
        return true;
    }

    bool load_memory_initializers()
    {
        std::unordered_map<const ValueSymbol*, MemoryInit> initializers;
        for (const ProceduralBlockSymbol* procedural : procedural_blocks)
            if (procedural->procedureKind == ProceduralBlockKind::Initial &&
                !collect_memory_calls(procedural->getBody(), initializers))
                std::fprintf(stderr, "sn-slang: ignoring unsupported initial block while collecting memory data\n");
        for (auto& [symbol, init] : initializers)
        {
            if (!init.loaded)
                continue;
            const Memory& memory = memories.at(symbol);
            uint32_t bits = uint32_t(uint64_t(sn_obj_width(module, memory.pair.out)) * memory.depth);
            sn_obj_id_t data = sn_module_add_const(module, bits, false, init.data.data(), nullptr);
            sn_obj_id_t mask = sn_module_add_const(module, bits, false, init.mask.data(), nullptr);
            sn_mem_set_init(module, memory.pair.out, data, mask);
        }
        return true;
    }

    static bool collect_event_controls(const TimingControl& timing,
                                       std::vector<const SignalEventControl*>& events)
    {
        if (const auto* signal = timing.as_if<SignalEventControl>())
        {
            events.push_back(signal);
            return true;
        }
        if (const auto* list = timing.as_if<EventListControl>())
        {
            for (const TimingControl* event : list->events)
                if (!collect_event_controls(*event, events))
                    return false;
            return true;
        }
        return false;
    }

    static const TimedStatement* timed_body(const ProceduralBlockSymbol& procedural)
    {
        return procedural.getBody().as_if<TimedStatement>();
    }

    static const Statement* unwrap_single_statement(const Statement* statement)
    {
        while (statement)
        {
            if (const auto* block = statement->as_if<BlockStatement>())
                statement = &block->body;
            else if (const auto* list = statement->as_if<StatementList>(); list && list->list.size() == 1)
                statement = list->list[0];
            else
                break;
        }
        return statement;
    }

    static std::vector<const Statement*> statement_sequence(const Statement* statement)
    {
        while (const auto* block = statement ? statement->as_if<BlockStatement>() : nullptr)
            statement = &block->body;
        if (const auto* list = statement ? statement->as_if<StatementList>() : nullptr)
            return {list->list.begin(), list->list.end()};
        return statement ? std::vector<const Statement*>{statement} : std::vector<const Statement*>{};
    }

    struct SignalGuard
    {
        const ValueSymbol* symbol;
        bool true_when_one;
    };

    std::optional<SignalGuard> signal_guard(const Expression& expression) const
    {
        if (const auto* conversion = expression.as_if<ConversionExpression>())
        {
            const Type& source = *conversion->operand().type;
            const Type& destination = *conversion->type;
            if (!source.isIntegral() || !destination.isIntegral() || source.isSigned() || destination.isSigned() ||
                width(destination) < 1)
                return std::nullopt;
            return signal_guard(conversion->operand());
        }
        if (const auto* named = expression.as_if<NamedValueExpression>())
            return width(*named->type) == 1 ? std::optional<SignalGuard>{{&named->symbol, true}} : std::nullopt;
        if (const auto* unary = expression.as_if<UnaryExpression>();
            unary && (unary->op == UnaryOperator::LogicalNot || unary->op == UnaryOperator::BitwiseNot) &&
            width(*unary->operand().type) == 1)
        {
            auto guard = signal_guard(unary->operand());
            if (guard)
                guard->true_when_one = !guard->true_when_one;
            return guard;
        }
        const auto* binary = expression.as_if<BinaryExpression>();
        if (!binary || (binary->op != BinaryOperator::Equality && binary->op != BinaryOperator::CaseEquality &&
                        binary->op != BinaryOperator::Inequality && binary->op != BinaryOperator::CaseInequality))
            return std::nullopt;

        auto match = [&](const Expression& value_expression, const Expression& constant_expression) {
            auto guard = signal_guard(value_expression);
            auto constant = constant_integer(constant_expression);
            if (!guard || !constant || (*constant != 0 && *constant != 1))
                return std::optional<SignalGuard>{};
            bool equality = binary->op == BinaryOperator::Equality || binary->op == BinaryOperator::CaseEquality;
            bool true_when_expression_one = equality ? *constant == 1 : *constant == 0;
            guard->true_when_one = guard->true_when_one == true_when_expression_one;
            return guard;
        };
        auto guard = match(binary->left(), binary->right());
        return guard ? guard : match(binary->right(), binary->left());
    }

    bool event_activates_guard(const SignalEventControl& event, const SignalGuard& condition) const
    {
        auto event_guard = signal_guard(event.expr);
        if (!event_guard || event_guard->symbol != condition.symbol)
            return false;
        bool event_expression_becomes_one = event.edge == EdgeKind::PosEdge;
        bool root_becomes_one = event_expression_becomes_one == event_guard->true_when_one;
        return root_becomes_one == condition.true_when_one;
    }

    struct TimingAsyncBranch
    {
        const SignalEventControl* event;
        const Statement* body;
    };

    struct SequentialTiming
    {
        const SignalEventControl* clock = nullptr;
        const Statement* synchronous_body = nullptr;
        std::vector<const Statement*> prologue;
        std::vector<TimingAsyncBranch> asynchronous;
    };

    void report_timing_error(SourceLocation location, const char* message) const
    {
        location = source_manager->getFullyOriginalLoc(location);
        std::string path = location ? source_manager->getFullPath(location.buffer()).string() : "<unknown>";
        size_t line = location ? source_manager->getLineNumber(location) : 0;
        std::fprintf(stderr, "sn-slang: %s:%zu: %s\n", path.c_str(), line, message);
    }

    static bool contains_edge_event(const TimingControl& timing)
    {
        if (const auto* signal = timing.as_if<SignalEventControl>())
            return signal->edge == EdgeKind::PosEdge || signal->edge == EdgeKind::NegEdge ||
                   signal->edge == EdgeKind::BothEdges;
        if (const auto* list = timing.as_if<EventListControl>())
            for (const TimingControl* event : list->events)
                if (contains_edge_event(*event))
                    return true;
        return false;
    }

    bool interpret_sequential_timing(const ProceduralBlockSymbol& procedural, SequentialTiming& result) const
    {
        const TimedStatement* timed = timed_body(procedural);
        if (!timed)
            return false;

        bool implicit = false;
        std::vector<const SignalEventControl*> triggers;
        auto collect = [&](auto&& self, const TimingControl& timing) -> bool {
            if (const auto* list = timing.as_if<EventListControl>())
            {
                for (const TimingControl* event : list->events)
                    if (!self(self, *event))
                        return false;
                return true;
            }
            if (const auto* signal = timing.as_if<SignalEventControl>())
            {
                if (signal->iffCondition)
                {
                    report_timing_error(signal->iffCondition->sourceRange.start(),
                                        "event iff conditions are not supported in sequential logic");
                    return false;
                }
                if (signal->edge == EdgeKind::PosEdge || signal->edge == EdgeKind::NegEdge)
                {
                    triggers.push_back(signal);
                    return true;
                }
                if (signal->edge == EdgeKind::BothEdges)
                {
                    report_timing_error(signal->sourceRange.start(),
                                        "dual-edge sequential event controls are not supported");
                    return false;
                }
                implicit = true;
                return true;
            }
            if (timing.as_if<ImplicitEventControl>())
            {
                implicit = true;
                return true;
            }
            report_timing_error(timing.sourceRange.start(), "unsupported timing control in sequential logic");
            return false;
        };
        if (!collect(collect, timed->timing))
            return false;
        if (implicit && !triggers.empty())
        {
            report_timing_error(timed->timing.sourceRange.start(),
                                "cannot mix edge-triggered and implicit event controls");
            return false;
        }
        if (implicit || triggers.empty())
        {
            report_timing_error(timed->timing.sourceRange.start(),
                                "sequential logic requires an edge-triggered event control");
            return false;
        }

        const Statement* statement = &timed->stmt;
        bool changed = true;
        while (changed)
        {
            changed = false;
            if (const auto* block = statement->as_if<BlockStatement>())
            {
                statement = &block->body;
                changed = true;
                continue;
            }
            if (const auto* list = statement->as_if<StatementList>(); list && triggers.size() > 1)
            {
                std::vector<const Statement*> pending;
                for (size_t i = 0; i < list->list.size(); i++)
                {
                    const Statement* item = list->list[i];
                    if (item->as_if<ExpressionStatement>() || item->as_if<VariableDeclStatement>())
                    {
                        pending.push_back(item);
                        continue;
                    }
                    if (i + 1 != list->list.size())
                        break;
                    result.prologue.insert(result.prologue.end(), pending.begin(), pending.end());
                    statement = item;
                    pending.clear();
                    changed = true;
                    break;
                }
            }
        }

        while (triggers.size() > 1)
        {
            const auto* conditional = statement->as_if<ConditionalStatement>();
            if (!conditional || conditional->check != UniquePriorityCheck::None || conditional->conditions.size() != 1 ||
                conditional->conditions[0].pattern || !conditional->ifFalse)
            {
                report_timing_error(statement->sourceRange.start(),
                                    "asynchronous events require a matching outer if / else branch");
                return false;
            }
            auto guard = signal_guard(*conditional->conditions[0].expr);
            if (!guard)
            {
                report_timing_error(conditional->conditions[0].expr->sourceRange.start(),
                                    "asynchronous event guard is not a safe one-bit signal test");
                return false;
            }
            auto found = std::find_if(triggers.begin(), triggers.end(), [&](const SignalEventControl* event) {
                auto event_guard = signal_guard(event->expr);
                return event_guard && event_guard->symbol == guard->symbol;
            });
            if (found == triggers.end())
            {
                report_timing_error(conditional->conditions[0].expr->sourceRange.start(),
                                    "asynchronous event guard does not match an event-list signal");
                return false;
            }
            if (!event_activates_guard(**found, *guard))
            {
                report_timing_error(conditional->conditions[0].expr->sourceRange.start(),
                                    "asynchronous event edge and branch polarity disagree");
                return false;
            }
            result.asynchronous.push_back({*found, &conditional->ifTrue});
            triggers.erase(found);
            statement = conditional->ifFalse;
        }

        result.clock = triggers.front();
        result.synchronous_body = statement;
        if (result.asynchronous.size() > 1)
        {
            report_timing_error(timed->timing.sourceRange.start(),
                                "multiple asynchronous controls are recognized but not representable in SN yet");
            return false;
        }
        return true;
    }

    static bool is_sequential_block(const ProceduralBlockSymbol& procedural)
    {
        const TimedStatement* timed = timed_body(procedural);
        return timed && contains_edge_event(timed->timing);
    }

    bool collect_analyzed_procedural_lvalue(const sn_lvalue_t& lvalue, std::vector<const ValueSymbol*>& targets,
                                            std::vector<SelectedValue>& selected_targets,
                                            std::unordered_set<const ValueSymbol*>& seen,
                                            std::unordered_set<SelectedValue, SelectedValueHash>& selected_seen,
                                            uint32_t target_offset = 0, uint32_t target_width = 0)
    {
        if (!target_width)
            target_width = lvalue.width;
        if (const auto* variable = std::get_if<sn_lvalue_t::variable_t>(&lvalue.descriptor))
        {
            if (is_automatic_value(*variable->symbol))
                return true; // An automatic block-local temporary is not persistent state.
            uint32_t total_width = width(variable->symbol->getType());
            if (!target_offset && target_width == total_width)
            {
                if (seen.emplace(variable->symbol).second)
                    targets.push_back(variable->symbol);
                return true;
            }
            if (uint64_t(target_offset) + target_width > total_width)
                return false;
            if (!variable->symbol->getType().hasFixedRange())
            {
                // Structs have a well-defined bitstream layout but no scalar index range. Use physical bit
                // positions as selected targets so disjoint fields can be updated by separate generated processes.
                for (uint32_t physical = target_offset; physical < target_offset + target_width; physical++)
                {
                    SelectedValue selected{variable->symbol, physical};
                    if (selected_seen.emplace(selected).second)
                        selected_targets.push_back(selected);
                }
                return true;
            }
            ConstantRange range = variable->symbol->getType().getFixedRange();
            for (uint32_t physical = target_offset; physical < target_offset + target_width; physical++)
            {
                int64_t index = range.isDescending() ? int64_t(range.right) + physical
                                                     : int64_t(range.right) - physical;
                SelectedValue selected{variable->symbol, index};
                if (selected_seen.emplace(selected).second)
                    selected_targets.push_back(selected);
            }
            return true;
        }
        if (const auto* element = std::get_if<sn_lvalue_t::array_element_t>(&lvalue.descriptor))
        {
            if (is_automatic_value(*element->symbol))
                return true;
            if (!element->constant_index)
                return false;
            SelectedValue selected{element->symbol, *element->constant_index};
            uint32_t total_width = selected_width(selected);
            const Type* element_type = selected.symbol->getType().getArrayElementType();
            if (!target_offset && target_width == total_width)
            {
                if (selected_seen.emplace(selected).second)
                    selected_targets.push_back(selected);
                return true;
            }
            if (!element_type || !element_type->hasFixedRange() || uint64_t(target_offset) + target_width > total_width)
                return false;
            ConstantRange range = element_type->getFixedRange();
            const Type* child_type = element_type->getArrayElementType();
            uint32_t child_width = child_type ? width(*child_type) : 1;
            if (!child_width)
                return false;
            if (!child_type || child_width == 1)
            {
                for (uint32_t physical = target_offset; physical < target_offset + target_width; physical++)
                {
                    int64_t index = range.isDescending() ? int64_t(range.right) + physical
                                                         : int64_t(range.right) - physical;
                    SelectedValue selected_bit{element->symbol, *element->constant_index, index};
                    if (selected_seen.emplace(selected_bit).second)
                        selected_targets.push_back(selected_bit);
                }
                return true;
            }
            uint32_t first_child = target_offset / child_width;
            uint32_t last_child = (target_offset + target_width - 1) / child_width;
            for (uint32_t physical = first_child; physical <= last_child; physical++)
            {
                int64_t index = range.isDescending() ? int64_t(range.right) + physical
                                                     : int64_t(range.right) - physical;
                SelectedValue selected_bit{element->symbol, *element->constant_index, index};
                if (selected_seen.emplace(selected_bit).second)
                    selected_targets.push_back(selected_bit);
            }
            return true;
        }
        if (std::holds_alternative<sn_lvalue_t::memory_element_t>(lvalue.descriptor))
            return true;
        if (const auto* stream = std::get_if<sn_lvalue_t::stream_t>(&lvalue.descriptor))
            return collect_analyzed_procedural_lvalue(*stream->inner, targets, selected_targets, seen,
                                                      selected_seen, 0, stream->inner->width);
        if (const auto* select = std::get_if<sn_lvalue_t::select_t>(&lvalue.descriptor))
        {
            auto offset = static_select_offset(*select, lvalue.width);
            return offset && collect_analyzed_procedural_lvalue(*select->inner, targets, selected_targets, seen,
                                                                selected_seen, target_offset + *offset,
                                                                target_width);
        }
        if (const auto* member = std::get_if<sn_lvalue_t::member_t>(&lvalue.descriptor))
            return collect_analyzed_procedural_lvalue(*member->inner, targets, selected_targets, seen,
                                                      selected_seen, target_offset + uint32_t(member->bit_offset),
                                                      target_width);
        if (const auto* concat = std::get_if<sn_lvalue_t::concat_t>(&lvalue.descriptor))
        {
            for (const sn_lvalue_t& element : concat->elements)
                if (!collect_analyzed_procedural_lvalue(element, targets, selected_targets, seen, selected_seen,
                                                        0, element.width))
                    return false;
            return true;
        }
        return false;
    }

    bool collect_dynamic_lvalue_roots(const sn_lvalue_t& lvalue, std::vector<const ValueSymbol*>& targets,
                                      std::vector<SelectedValue>& selected_targets,
                                      std::unordered_set<const ValueSymbol*>& seen,
                                      std::unordered_set<SelectedValue, SelectedValueHash>& selected_seen,
                                      uint64_t offset = 0, uint32_t span = 0)
    {
        if (const auto* variable = std::get_if<sn_lvalue_t::variable_t>(&lvalue.descriptor))
        {
            if (is_automatic_value(*variable->symbol))
                return true;
            uint32_t total_width = width(variable->symbol->getType());
            if (!span)
                span = lvalue.width;
            if (offset + span > total_width)
                return false;
            if (!offset && span == total_width)
            {
                if (seen.emplace(variable->symbol).second)
                    targets.push_back(variable->symbol);
                return true;
            }
            for (uint32_t physical = uint32_t(offset); physical < offset + span; physical++)
            {
                int64_t index = physical;
                if (variable->symbol->getType().hasFixedRange())
                {
                    ConstantRange range = variable->symbol->getType().getFixedRange();
                    index = range.isDescending() ? int64_t(range.right) + physical
                                                 : int64_t(range.right) - physical;
                }
                SelectedValue selected{variable->symbol, index};
                if (selected_seen.emplace(selected).second)
                    selected_targets.push_back(selected);
            }
            return true;
        }
        if (const auto* element = std::get_if<sn_lvalue_t::array_element_t>(&lvalue.descriptor))
        {
            const Type& type = element->symbol->getType();
            if (!type.hasFixedRange())
                return false;
            ConstantRange range = type.getFixedRange();
            if (element->constant_index)
            {
                if (*element->constant_index < INT32_MIN || *element->constant_index > INT32_MAX ||
                    !range.containsPoint(int32_t(*element->constant_index)))
                    return true;
                return collect_dynamic_lvalue_roots(
                    sn_lvalue_t{sn_lvalue_t::variable_t{element->symbol}, width(type), true}, targets,
                    selected_targets, seen, selected_seen,
                    offset + uint64_t(range.translateIndex(int32_t(*element->constant_index))) * lvalue.width,
                    span ? span : lvalue.width);
            }
            if (!offset && !span && !is_automatic_value(*element->symbol))
            {
                for (int64_t index = range.lower(); index <= range.upper(); index++)
                {
                    SelectedValue selected{element->symbol, index};
                    if (selected_seen.emplace(selected).second)
                        selected_targets.push_back(selected);
                }
                return true;
            }
            for (int64_t index = range.lower(); index <= range.upper(); index++)
                if (!collect_dynamic_lvalue_roots(
                        sn_lvalue_t{sn_lvalue_t::variable_t{element->symbol}, width(type), true}, targets,
                        selected_targets, seen, selected_seen,
                        offset + uint64_t(range.translateIndex(int32_t(index))) * lvalue.width,
                        span ? span : lvalue.width))
                    return false;
            return true;
        }
        if (const auto* select = std::get_if<sn_lvalue_t::select_t>(&lvalue.descriptor))
        {
            if (auto selected_offset = static_select_offset(*select, lvalue.width))
                return collect_dynamic_lvalue_roots(*select->inner, targets, selected_targets, seen,
                                                    selected_seen, offset + *selected_offset,
                                                    span ? span : lvalue.width);
            if (!select->input_type || !select->input_type->hasFixedRange())
                return false;
            ConstantRange range = select->input_type->getFixedRange();
            const Type* input_element = select->input_type->getArrayElementType();
            uint32_t stride = input_element ? width(*input_element) : 1;
            if (!stride)
                return false;
            for (int64_t index = range.lower(); index <= range.upper(); index++)
            {
                ConstantRange selected{int32_t(index), int32_t(index)};
                if (!select->element)
                {
                    int64_t selection_width = select->constant_right.value_or(lvalue.width);
                    if (selection_width <= 0 || selection_width > INT32_MAX ||
                        select->selection_kind == RangeSelectionKind::Simple)
                        continue;
                    auto indexed = ConstantRange::getIndexedRange(
                        int32_t(index), int32_t(selection_width), range.isDescending(),
                        select->selection_kind == RangeSelectionKind::IndexedUp);
                    if (!indexed)
                        continue;
                    selected = *indexed;
                }
                if (!range.containsPoint(selected.left) || !range.containsPoint(selected.right))
                    continue;
                int32_t ordinal = range.translateIndex(selected.right);
                if (ordinal < 0)
                    continue;
                uint64_t next_offset = offset + uint64_t(ordinal) * stride;
                if (!collect_dynamic_lvalue_roots(*select->inner, targets, selected_targets, seen,
                                                  selected_seen, next_offset,
                                                  span ? span : lvalue.width))
                    return false;
            }
            return true;
        }
        if (const auto* member = std::get_if<sn_lvalue_t::member_t>(&lvalue.descriptor))
            return collect_dynamic_lvalue_roots(*member->inner, targets, selected_targets, seen,
                                                selected_seen, offset + member->bit_offset,
                                                span ? span : lvalue.width);
        if (const auto* stream = std::get_if<sn_lvalue_t::stream_t>(&lvalue.descriptor))
            return collect_dynamic_lvalue_roots(*stream->inner, targets, selected_targets, seen, selected_seen);
        if (const auto* concat = std::get_if<sn_lvalue_t::concat_t>(&lvalue.descriptor))
        {
            for (const sn_lvalue_t& element : concat->elements)
                if (!collect_dynamic_lvalue_roots(element, targets, selected_targets, seen, selected_seen))
                    return false;
            return true;
        }
        return std::holds_alternative<sn_lvalue_t::memory_element_t>(lvalue.descriptor);
    }

    static const ValueSymbol* direct_selected_symbol(const Expression& expression)
    {
        const Expression* value = nullptr;
        if (const auto* element = expression.as_if<ElementSelectExpression>())
            value = &element->value();
        else if (const auto* range = expression.as_if<RangeSelectExpression>())
            value = &range->value();
        const auto* named = value ? value->as_if<NamedValueExpression>() : nullptr;
        return named ? &named->symbol : nullptr;
    }

    bool collect_procedural_lvalue(const Expression& expression, std::vector<const ValueSymbol*>& targets,
                                   std::vector<SelectedValue>& selected_targets,
                                   std::unordered_set<const ValueSymbol*>& seen,
                                   std::unordered_set<SelectedValue, SelectedValueHash>& selected_seen)
    {
        if (auto selected_bit = named_element_bit(expression))
        {
            if (selected_seen.emplace(*selected_bit).second)
                selected_targets.push_back(*selected_bit);
            return true;
        }
        if (auto selected = named_element(expression))
        {
            // Only arrays that actually survived memory eligibility are handled as memory ports. Rejected
            // candidates (for example a small register array or latch-based SCM) still need ordinary procedural
            // targets for each selected element.
            if (memories.contains(selected->symbol))
                return true;
            if (selected_seen.emplace(*selected).second)
                selected_targets.push_back(*selected);
            return true;
        }
        if (const auto* range = expression.as_if<RangeSelectExpression>())
            if (auto selected = named_element(range->value()))
            {
                auto left = constant_integer(range->left());
                auto right = constant_integer(range->right());
                const Type* first = selected->symbol->getType().getArrayElementType();
                const Type* scalar = first ? first->getArrayElementType() : nullptr;
                uint32_t bits = width(*range->type);
                if (!left || !right || !first || !first->hasFixedRange() || (scalar && width(*scalar) != 1))
                {
                    if (selected_seen.emplace(*selected).second)
                        selected_targets.push_back(*selected);
                    return true;
                }
                auto selected_range = selected_index_range(*range, *left, *right);
                if (!selected_range)
                    return false;
                for (uint32_t offset = 0; offset < bits; offset++)
                {
                    int64_t index = selected_bit_index(*selected_range, offset);
                    SelectedValue bit{selected->symbol, selected->index, index};
                    if (selected_seen.emplace(bit).second)
                        selected_targets.push_back(bit);
                }
                return true;
            }
        if (const auto* concat = expression.as_if<ConcatenationExpression>())
        {
            for (const Expression* operand : concat->operands())
                if (!collect_procedural_lvalue(*operand, targets, selected_targets, seen, selected_seen))
                    return false;
            return true;
        }
        if (const auto* pattern = expression.as_if<SimpleAssignmentPatternExpression>(); pattern && pattern->isLValue)
        {
            for (const Expression* element : pattern->elements())
                if (!collect_procedural_lvalue(*element, targets, selected_targets, seen, selected_seen))
                    return false;
            return true;
        }
        std::string error;
        auto analyzed = analyze_lvalue(expression, error, true);
        // Keep direct packed selections as independent targets when separate processes drive disjoint bits. Nested
        // selections still use the recursive descriptor, for example array[constant][slice].
        if (analyzed && (analyzed->is_static || analyzed_lvalue_has_memory(*analyzed)) &&
            !direct_selected_symbol(expression))
        {
            if (collect_analyzed_procedural_lvalue(*analyzed, targets, selected_targets, seen, selected_seen))
                return true;
            SourceLocation location = source_manager->getFullyOriginalLoc(expression.sourceRange.start());
            std::string path = location ? source_manager->getFullPath(location.buffer()).string() : "<unknown>";
            size_t line = location ? source_manager->getLineNumber(location) : 0;
            const auto* element = expression.as_if<ElementSelectExpression>();
            const ValueSymbol* base = element ? referenced_value(element->value()) : nullptr;
            auto index = element ? constant_integer(element->selector()) : std::nullopt;
            std::fprintf(stderr,
                         "sn-slang: %s:%zu: cannot collect procedural target (descriptor=%zu, width=%u, "
                         "element_base=%s, element_index=%s)\n",
                         path.c_str(), line, analyzed->descriptor.index(), analyzed->width,
                         base ? "yes" : "no", index ? "constant" : "dynamic");
            return false;
        }
        if (analyzed && !analyzed->is_static && !analyzed_lvalue_has_memory(*analyzed))
        {
            bool collected =
                collect_dynamic_lvalue_roots(*analyzed, targets, selected_targets, seen, selected_seen);
            if (!collected)
            {
                SourceLocation location = source_manager->getFullyOriginalLoc(expression.sourceRange.start());
                std::string path = location ? source_manager->getFullPath(location.buffer()).string() : "<unknown>";
                size_t line = location ? source_manager->getLineNumber(location) : 0;
                std::fprintf(stderr,
                             "sn-slang: %s:%zu: cannot collect dynamic procedural target "
                             "(descriptor=%zu, width=%u)\n",
                             path.c_str(), line, analyzed->descriptor.index(), analyzed->width);
            }
            return collected;
        }
        if (const auto* assignment = expression.as_if<AssignmentExpression>();
            assignment && assignment->right().as_if<EmptyArgumentExpression>())
        {
            return collect_procedural_lvalue(assignment->left(), targets, selected_targets, seen, selected_seen);
        }
        if (const auto* conversion = expression.as_if<ConversionExpression>())
            return collect_procedural_lvalue(conversion->operand(), targets, selected_targets, seen, selected_seen);
        if (memory_element(expression))
            return true;
        if (auto selected = named_element(expression))
        {
            if (selected_seen.emplace(*selected).second)
                selected_targets.push_back(*selected);
            return true;
        }
        if (const auto* element = expression.as_if<ElementSelectExpression>())
        {
            const auto* element_named = element->value().as_if<NamedValueExpression>();
            if (!element_named)
            {
                std::fprintf(stderr, "sn-slang: unsupported procedural element-selection lvalue\n");
                return false;
            }
            if (element_named->symbol.getType().isUnpackedArray() &&
                element_named->symbol.getType().hasFixedRange())
            {
                ConstantRange range = element_named->symbol.getType().getFixedRange();
                for (int64_t index = range.lower(); index <= range.upper(); index++)
                {
                    SelectedValue selected{&element_named->symbol, index};
                    if (selected_seen.emplace(selected).second)
                        selected_targets.push_back(selected);
                }
                return true;
            }
            if (seen.emplace(&element_named->symbol).second)
                targets.push_back(&element_named->symbol);
            return true;
        }
        if (const auto* range = expression.as_if<RangeSelectExpression>())
        {
            const auto* range_named = range->value().as_if<NamedValueExpression>();
            auto left = constant_integer(range->left());
            auto right = constant_integer(range->right());
            uint32_t bits = width(*range->type);
            if (!range_named || !right || !bits)
            {
                std::fprintf(stderr, "sn-slang: unsupported procedural range-selection lvalue\n");
                return false;
            }
            if (!left)
            {
                if (range->getSelectionKind() == RangeSelectionKind::Simple)
                {
                    std::fprintf(stderr, "sn-slang: unsupported procedural range-selection lvalue\n");
                    return false;
                }
                if (seen.emplace(&range_named->symbol).second)
                    targets.push_back(&range_named->symbol);
                return true;
            }
            auto selected_range = selected_index_range(*range, *left, *right);
            if (!selected_range)
                return false;
            int64_t least_index = selected_range->right;
            for (uint32_t offset = 0; offset < bits; offset++)
            {
                int64_t index = selected_bit_index(*selected_range, offset);
                SelectedValue selected{&range_named->symbol, index};
                if (selected_seen.emplace(selected).second)
                    selected_targets.push_back(selected);
            }
            return true;
        }
        if (const auto* member = expression.as_if<MemberAccessExpression>())
        {
            if (const auto* value = member->member.as_if<ValueSymbol>())
            {
                if (!is_automatic_value(*value) && seen.emplace(value).second)
                    targets.push_back(value);
                return true;
            }
            return collect_procedural_lvalue(member->value(), targets, selected_targets, seen, selected_seen);
        }
        if (const ValueSymbol* value = referenced_value(expression))
        {
            if (is_automatic_value(*value))
                return true;
            if (seen.emplace(value).second)
                targets.push_back(value);
            return true;
        }
        std::fprintf(stderr, "sn-slang: unsupported procedural lvalue kind %u (%s)\n",
                     unsigned(expression.kind), error.empty() ? "no descriptor" : error.c_str());
        return false;
    }

    template<typename Callback>
    bool unroll_foreach(const ForeachLoopStatement& loop, Callback&& callback)
    {
        EvalContext local_context(*body->parentInstance);
        EvalContext& context = active_constant_context ? *active_constant_context : local_context;
        EvalFrameGuard frame(context);
        LoopConstantGuard constants(active_loop_constants);
        std::vector<ConstantValue*> locals(loop.loopDims.size());
        uint64_t iterations = 1;
        for (size_t dimension = 0; dimension < loop.loopDims.size(); dimension++)
        {
            const auto& dim = loop.loopDims[dimension];
            if (!dim.range || dim.range->width() <= 0 ||
                iterations > 1000000 / uint64_t(dim.range->width()))
            {
                std::fprintf(stderr, "sn-slang: foreach requires bounded static dimensions\n");
                return false;
            }
            iterations *= uint64_t(dim.range->width());
            if (dim.loopVar)
            {
                locals[dimension] = context.createLocal(dim.loopVar);
                constants.bind(dim.loopVar, locals[dimension]);
            }
        }
        auto visit = [&](auto&& self, size_t dimension) -> bool {
            if (dimension == loop.loopDims.size())
            {
                EvalContext* previous = active_constant_context;
                active_constant_context = &context;
                bool result = callback();
                active_constant_context = previous;
                return result;
            }
            const auto& dim = loop.loopDims[dimension];
            int64_t index = dim.range->left;
            int64_t step = dim.range->left <= dim.range->right ? 1 : -1;
            while (true)
            {
                if (locals[dimension])
                {
                    uint32_t bits = width(dim.loopVar->getType());
                    *locals[dimension] = ConstantValue(SVInt(bits, uint64_t(index), true));
                }
                if (!self(self, dimension + 1))
                    return false;
                if (index == dim.range->right)
                    break;
                index += step;
            }
            return true;
        };
        return visit(visit, 0);
    }

    bool collect_sequential_targets(const Statement& statement, std::vector<const ValueSymbol*>& targets,
                                    std::vector<SelectedValue>& selected_targets,
                                    std::unordered_set<const ValueSymbol*>& seen,
                                    std::unordered_set<SelectedValue, SelectedValueHash>& selected_seen,
                                    bool require_nonblocking)
    {
        if (const auto* timed = statement.as_if<TimedStatement>())
            return collect_sequential_targets(timed->stmt, targets, selected_targets, seen, selected_seen,
                                              require_nonblocking);
        if (const auto* block = statement.as_if<BlockStatement>())
            return collect_sequential_targets(block->body, targets, selected_targets, seen, selected_seen,
                                              require_nonblocking);
        if (const auto* list = statement.as_if<StatementList>())
        {
            for (const Statement* child : list->list)
                if (!collect_sequential_targets(*child, targets, selected_targets, seen, selected_seen,
                                                require_nonblocking))
                    return false;
            return true;
        }
        if (const auto* conditional = statement.as_if<ConditionalStatement>())
        {
            if (prune_procedural_constants && conditional->conditions.size() == 1 &&
                !conditional->conditions[0].pattern)
                if (auto truth = constant_truth(*conditional->conditions[0].expr))
                    return *truth ? collect_sequential_targets(conditional->ifTrue, targets, selected_targets, seen,
                                                               selected_seen, require_nonblocking)
                                  : !conditional->ifFalse ||
                                        collect_sequential_targets(*conditional->ifFalse, targets, selected_targets,
                                                                   seen, selected_seen, require_nonblocking);
            if (!collect_sequential_targets(conditional->ifTrue, targets, selected_targets, seen, selected_seen,
                                            require_nonblocking))
                return false;
            return !conditional->ifFalse ||
                   collect_sequential_targets(*conditional->ifFalse, targets, selected_targets, seen, selected_seen,
                                              require_nonblocking);
        }
        if (const auto* case_statement = statement.as_if<CaseStatement>())
        {
            if (prune_procedural_constants && case_statement->condition == CaseStatementCondition::Normal)
                if (auto constant_case = constant_integer(case_statement->expr))
                {
                    const Statement* matching_statement = nullptr;
                    bool all_items_constant = true;
                    for (const CaseStatement::ItemGroup& item : case_statement->items)
                        for (const Expression* item_expression : item.expressions)
                        {
                            auto constant_item = constant_integer(*item_expression);
                            if (!constant_item)
                            {
                                all_items_constant = false;
                                break;
                            }
                            if (!matching_statement && *constant_item == *constant_case)
                                matching_statement = item.stmt;
                        }
                    // A constant case selector does not make dynamic item expressions constant. In particular,
                    // "case (1'b1)" is a common priority-mux idiom and every dynamic item can be selected.
                    if (all_items_constant)
                        return matching_statement
                                   ? collect_sequential_targets(*matching_statement, targets, selected_targets,
                                                                seen, selected_seen, require_nonblocking)
                                   : !case_statement->defaultCase ||
                                         collect_sequential_targets(*case_statement->defaultCase, targets,
                                                                    selected_targets, seen, selected_seen,
                                                                    require_nonblocking);
                }
            for (const CaseStatement::ItemGroup& item : case_statement->items)
                if (!collect_sequential_targets(*item.stmt, targets, selected_targets, seen, selected_seen,
                                                require_nonblocking))
                    return false;
            return !case_statement->defaultCase ||
                   collect_sequential_targets(*case_statement->defaultCase, targets, selected_targets, seen,
                                              selected_seen, require_nonblocking);
        }
        if (const auto* repeat = statement.as_if<RepeatLoopStatement>())
        {
            auto count = constant_integer(repeat->count);
            if (!count || *count < 0 || *count > 1000000)
            {
                std::fprintf(stderr, "sn-slang: repeat-loop count must be a bounded nonnegative constant\n");
                return false;
            }
            for (int64_t iteration = 0; iteration < *count; iteration++)
                if (!collect_sequential_targets(repeat->body, targets, selected_targets, seen, selected_seen,
                                                require_nonblocking))
                    return false;
            return true;
        }
        if (const auto* loop = statement.as_if<WhileLoopStatement>())
            return collect_sequential_targets(loop->body, targets, selected_targets, seen, selected_seen,
                                              require_nonblocking);
        if (const auto* loop = statement.as_if<ForeachLoopStatement>())
            return unroll_foreach(*loop, [&] {
                return collect_sequential_targets(loop->body, targets, selected_targets, seen, selected_seen,
                                                  require_nonblocking);
            });
        if (const auto* loop = statement.as_if<ForLoopStatement>())
        {
            if (!loop->stopExpr)
            {
                std::fprintf(stderr, "sn-slang: procedural for-loop target discovery requires a stop condition\n");
                return false;
            }
            EvalContext local_loop_context(*body->parentInstance);
            EvalContext& loop_context = active_constant_context ? *active_constant_context : local_loop_context;
            EvalFrameGuard loop_frame(loop_context);
            LoopConstantGuard loop_constants(active_loop_constants);
            for (const VariableSymbol* variable : loop->loopVars)
            {
                const Expression* initializer = variable->getInitializer();
                ConstantValue initial = initializer ? initializer->eval(loop_context) : ConstantValue{};
                if (!initial && initializer)
                    if (auto integer = constant_integer(*initializer))
                        initial = ConstantValue(SVInt(width(variable->getType()), uint64_t(*integer),
                                                      variable->getType().isSigned()));
                ConstantValue* local = initial ? loop_context.createLocal(variable, std::move(initial)) : nullptr;
                if (!local)
                {
                    std::fprintf(stderr, "sn-slang: procedural for-loop variable requires a constant initializer\n");
                    return false;
                }
                loop_constants.bind(variable, local);
            }
            for (const Expression* initializer : loop->initializers)
            {
                const auto* assignment = initializer->as_if<AssignmentExpression>();
                const auto* named = assignment ? assignment->left().as_if<NamedValueExpression>() : nullptr;
                ConstantValue* local = named ? loop_context.createLocal(&named->symbol) : nullptr;
                if (!local || !initializer->eval(loop_context))
                {
                    std::fprintf(stderr, "sn-slang: unsupported procedural for-loop initializer\n");
                    return false;
                }
                loop_constants.bind(&named->symbol, local);
            }
            uint32_t dynamic_iteration_limit = 0;
            const auto* stop_binary = loop->stopExpr->as_if<BinaryExpression>();
            if (loop->loopVars.size() == 1 && loop->steps.size() == 1 && stop_binary &&
                (stop_binary->op == BinaryOperator::LessThan || stop_binary->op == BinaryOperator::LessThanEqual) &&
                loop->loopVars[0]->getInitializer() &&
                constant_integer(*loop->loopVars[0]->getInitializer()) == 0)
            {
                auto strip_conversions = [](const Expression* expression) {
                    while (const auto* conversion = expression->as_if<ConversionExpression>())
                        expression = &conversion->operand();
                    return expression;
                };
                const Expression* stop_left = &stop_binary->left();
                stop_left = strip_conversions(stop_left);
                const auto* stop_variable = stop_left->as_if<NamedValueExpression>();
                const Expression* step = strip_conversions(loop->steps[0]);
                const auto* increment = step->as_if<UnaryExpression>();
                const Expression* increment_operand = increment ? &increment->operand() : nullptr;
                increment_operand = increment_operand ? strip_conversions(increment_operand) : nullptr;
                const auto* increment_variable =
                    increment_operand ? increment_operand->as_if<NamedValueExpression>() : nullptr;
                bool increments = increment &&
                                  (increment->op == UnaryOperator::Preincrement ||
                                   increment->op == UnaryOperator::Postincrement) &&
                                  increment_variable && &increment_variable->symbol == loop->loopVars[0];
                if (const auto* assignment = step->as_if<AssignmentExpression>())
                {
                    const auto* lhs = strip_conversions(&assignment->left())->as_if<NamedValueExpression>();
                    const auto* add = strip_conversions(&assignment->right())->as_if<BinaryExpression>();
                    const auto* add_lhs = add ? strip_conversions(&add->left())->as_if<NamedValueExpression>()
                                              : nullptr;
                    increments = lhs && &lhs->symbol == loop->loopVars[0] && add &&
                                 add->op == BinaryOperator::Add && add_lhs &&
                                 &add_lhs->symbol == loop->loopVars[0] && constant_integer(add->right()) == 1;
                }
                if (stop_variable && &stop_variable->symbol == loop->loopVars[0] && increments)
                {
                    FixedLoopIndexBound bound(loop->loopVars[0]);
                    loop->body.visit(bound);
                    dynamic_iteration_limit = bound.limit;
                }
            }
            if (!dynamic_iteration_limit)
                dynamic_iteration_limit = countdown_loop_limit(*loop).value_or(0);
            for (uint32_t iteration = 0; iteration < 1000000; iteration++)
            {
                ConstantValue stop = loop->stopExpr->eval(loop_context);
                if (!stop || !stop.isInteger() || stop.integer().hasUnknown())
                {
                    if (!dynamic_iteration_limit || iteration >= dynamic_iteration_limit)
                    {
                        std::fprintf(stderr, "sn-slang: procedural for-loop condition has no supported bound\n");
                        return false;
                    }
                }
                else if (!stop.isTrue())
                    return true;
                EvalContext* previous_constant_context = active_constant_context;
                active_constant_context = &loop_context;
                bool body_ok = collect_sequential_targets(loop->body, targets, selected_targets, seen, selected_seen,
                                                          require_nonblocking);
                active_constant_context = previous_constant_context;
                if (!body_ok)
                    return false;
                for (const Expression* step : loop->steps)
                {
                    if (!step->eval(loop_context))
                    {
                        std::fprintf(stderr, "sn-slang: unsupported procedural for-loop step\n");
                        return false;
                    }
                }
                if (dynamic_iteration_limit && iteration + 1 == dynamic_iteration_limit)
                    return true;
            }
            std::fprintf(stderr, "sn-slang: procedural for loop exceeds the unrolling limit\n");
            return false;
        }
        if (const auto* expression_statement = statement.as_if<ExpressionStatement>())
        {
            const auto* assignment = expression_statement->expr.as_if<AssignmentExpression>();
            const auto* unary = expression_statement->expr.as_if<UnaryExpression>();
            const auto* call = expression_statement->expr.as_if<CallExpression>();
            bool translate_off_diagnostic = call && call->isSystemCall() &&
                                            (call->getSubroutineName() == "$fatal" ||
                                             call->getSubroutineName() == "$error" ||
                                             call->getSubroutineName() == "$warning" ||
                                             call->getSubroutineName() == "$info") &&
                                            source_is_translate_off(call->sourceRange.start());
            if (is_ignored_system_task(call) || translate_off_diagnostic)
                return true;
            bool decrement = false;
            if (unary && increment_or_decrement(unary->op, decrement))
                return collect_procedural_lvalue(unary->operand(), targets, selected_targets, seen, selected_seen);
            if (call && !call->isSystemCall())
            {
                const SubroutineSymbol* subroutine = std::get<0>(call->subroutine);
                auto formals = subroutine->getArguments();
                if ((subroutine->subroutineKind != SubroutineKind::Task &&
                     subroutine->subroutineKind != SubroutineKind::Function) ||
                    formals.size() != call->arguments().size() || !active_subroutines.emplace(subroutine).second)
                {
                    std::fprintf(stderr, "sn-slang: unsupported or recursive procedural task '%.*s'\n",
                                 int(call->getSubroutineName().size()), call->getSubroutineName().data());
                    return false;
                }
                bool collected = collect_sequential_targets(subroutine->getBody(), targets, selected_targets, seen,
                                                            selected_seen, require_nonblocking);
                active_subroutines.erase(subroutine);
                if (!collected)
                    return false;
                for (size_t i = 0; i < formals.size(); i++)
                {
                    ArgumentDirection direction = formals[i]->direction;
                    if (direction != ArgumentDirection::Out && direction != ArgumentDirection::InOut &&
                        direction != ArgumentDirection::Ref)
                        continue;
                    const auto* argument = call->arguments()[i]->as_if<AssignmentExpression>();
                    const Expression* lvalue = argument && argument->isLValueArg() ? &argument->left()
                                                                                   : call->arguments()[i];
                    if (!collect_procedural_lvalue(*lvalue, targets, selected_targets, seen, selected_seen))
                        return false;
                }
                return true;
            }
            if (!assignment)
            {
                std::fprintf(stderr, "sn-slang: unsupported procedural expression kind %u\n",
                             unsigned(expression_statement->expr.kind));
                return false;
            }
            if (!collect_procedural_lvalue(assignment->left(), targets, selected_targets, seen, selected_seen))
                return false;
            const Expression* right = &assignment->right();
            while (const auto* conversion = right->as_if<ConversionExpression>())
                right = &conversion->operand();
            const auto* function_call = right->as_if<CallExpression>();
            if (!function_call || function_call->isSystemCall())
                return true;
            const SubroutineSymbol* subroutine = std::get<0>(function_call->subroutine);
            auto formals = subroutine->getArguments();
            if (formals.size() != function_call->arguments().size())
                return false;
            for (size_t i = 0; i < formals.size(); i++)
            {
                ArgumentDirection direction = formals[i]->direction;
                if (direction != ArgumentDirection::Out && direction != ArgumentDirection::InOut &&
                    direction != ArgumentDirection::Ref)
                    continue;
                const auto* argument = function_call->arguments()[i]->as_if<AssignmentExpression>();
                const Expression* lvalue = argument && argument->isLValueArg() ? &argument->left()
                                                                                : function_call->arguments()[i];
                if (!collect_procedural_lvalue(*lvalue, targets, selected_targets, seen, selected_seen))
                    return false;
            }
            return true;
        }
        if (statement.as_if<VariableDeclStatement>())
            return true;
        if (statement.as_if<WaitStatement>())
        {
            report_timing_error(statement.sourceRange.start(),
                                "wait statements have no current synthesizable SN representation");
            return false;
        }
        // Assertions and formal statements do not contribute synthesized dataflow. Pickled synthesis units
        // commonly retain immediate and concurrent assertions even after translate-off processing.
        if (statement.as_if<ImmediateAssertionStatement>() || statement.as_if<ConcurrentAssertionStatement>())
            return handle_formal_statement(statement);
        if (statement.as_if<ReturnStatement>() || statement.as_if<BreakStatement>() ||
            statement.as_if<ContinueStatement>())
            return true;
        if (statement.as_if<EmptyStatement>())
            return true;
        std::fprintf(stderr, "sn-slang: unsupported sequential statement kind %u\n", unsigned(statement.kind));
        return false;
    }

    bool prepare_sequential_blocks()
    {
        // Allocate state outputs before lowering combinational logic so feedback
        // expressions can reference the current value. REG_IN fanins are filled
        // later, after the next-state expressions have been lowered.
        for (const ProceduralBlockSymbol* procedural : procedural_blocks)
        {
            if (!is_sequential_block(*procedural))
                continue;
            const TimedStatement* timed = timed_body(*procedural);
            SequentialTiming timing;
            if (!timed || !interpret_sequential_timing(*procedural, timing))
                return false;
            const SignalEventControl* clock_event = timing.clock;
            const SignalEventControl* reset_event =
                timing.asynchronous.empty() ? nullptr : timing.asynchronous.front().event;

            auto scalar_event = [&](const SignalEventControl& event, const char* kind) {
                if (width(*event.expr.type) != 1)
                {
                    std::string message = std::string(kind) + " event expression must be exactly one bit";
                    report_timing_error(event.expr.sourceRange.start(), message.c_str());
                    return SN_INVALID_ID;
                }
                sn_obj_id_t value = lower_expression(event.expr);
                return value != SN_INVALID_ID && sn_obj_width(module, value) == 1 ? value : SN_INVALID_ID;
            };
            sn_obj_id_t clock = scalar_event(*clock_event, "clock");
            sn_obj_id_t reset = reset_event ? scalar_event(*reset_event, "asynchronous reset") : SN_INVALID_ID;
            if (clock == SN_INVALID_ID || (reset_event && reset == SN_INVALID_ID))
                return false;
            uint32_t flags = clock_event->edge == EdgeKind::NegEdge ? SN_REG_CLOCK_NEGEDGE : 0;
            if (reset_event)
            {
                flags |= SN_REG_RESET_ASYNC;
                if (reset_event->edge == EdgeKind::NegEdge)
                    flags |= SN_REG_RESET_NEGEDGE;
            }

            SequentialBlock sequential{procedural,
                                       timing.synchronous_body,
                                       timing.asynchronous.empty() ? nullptr : timing.asynchronous.front().body,
                                       std::move(timing.prologue),
                                       clock,
                                       reset,
                                       flags,
                                       {},
                                       {}};
            std::unordered_set<const ValueSymbol*> seen;
            std::unordered_set<SelectedValue, SelectedValueHash> selected_seen;
            std::vector<const ValueSymbol*> syntactic_targets;
            std::vector<SelectedValue> syntactic_selected_targets;
            std::unordered_set<const ValueSymbol*> syntactic_seen;
            std::unordered_set<SelectedValue, SelectedValueHash> syntactic_selected_seen;
            prune_procedural_constants = false;
            bool syntactic_ok = collect_sequential_targets(timed->stmt, syntactic_targets,
                                                            syntactic_selected_targets, syntactic_seen,
                                                            syntactic_selected_seen, true);
            prune_procedural_constants = !preserve_state;
            if (!syntactic_ok)
                return false;
            if (!collect_sequential_targets(timed->stmt, sequential.targets, sequential.selected_targets, seen,
                                            selected_seen, true))
                return false;
            for (const ValueSymbol* target : syntactic_targets)
                if (!seen.contains(target) && !sequential_registers.contains(target))
                    constant_dead_values.emplace(target);
            for (const SelectedValue& target : syntactic_selected_targets)
                if (!selected_seen.contains(target) && !sequential_selected_registers.contains(target))
                    constant_dead_selected_values.emplace(target);
            for (const ValueSymbol* target : sequential.targets)
                constant_dead_values.erase(target);
            for (const SelectedValue& target : sequential.selected_targets)
                constant_dead_selected_values.erase(target);
            // A block can reset a packed variable as a whole and update slices of it in normal operation.
            // Represent that variable with one register; partial assignments below merge into its complete value.
            std::erase_if(sequential.selected_targets,
                          [&](const SelectedValue& target) {
                              if (seen.contains(target.symbol))
                                  return true;
                              SelectedValue whole = target;
                              whole.bit = -1;
                              return target.bit >= 0 && selected_seen.contains(whole);
                          });
            for (const ValueSymbol* target : sequential.targets)
            {
                if (undriven_values.erase(target))
                    values.erase(target);
                if (sequential_registers.contains(target) || values.contains(target) || assignments.contains(target))
                {
                    std::fprintf(stderr, "sn-slang: sequential variable '%.*s' has multiple drivers\n",
                                 int(target->name.size()), target->name.data());
                    return false;
                }
                uint32_t bits = width(target->getType());
                if (!bits)
                    return false;
                std::string name(target->name);
                if (!register_name(*target, name))
                    return false;
                sn_obj_pair_t pair = sn_module_add_reg_pair(module, bits, target->getType().isSigned(), name.c_str(),
                                                            nullptr, clock);
                add_metadata(pair.out, *target);
                if (!add_sec_identity(pair.out, *target))
                    return false;
                sn_reg_set_flags(module, pair.out, flags & SN_REG_CLOCK_NEGEDGE);
                sequential_registers.emplace(target, pair);
                values.emplace(target, pair.out);
            }
            for (const SelectedValue& target : sequential.selected_targets)
            {
                if (undriven_selected_values.erase(target))
                    selected_values.erase(target);
                if (sequential_selected_registers.contains(target) || selected_values.contains(target) ||
                    selected_assignments.contains(target))
                {
                    std::fprintf(stderr, "sn-slang: sequential selected variable '%.*s[%lld][%lld]' has multiple "
                                         "drivers\n",
                                 int(target.symbol->name.size()), target.symbol->name.data(),
                                 static_cast<long long>(target.index), static_cast<long long>(target.bit));
                    return false;
                }
                uint32_t bits = selected_width(target);
                if (!bits)
                    return false;
                std::string name = selected_name(target);
                sn_obj_pair_t pair =
                    sn_module_add_reg_pair(module, bits, selected_is_signed(target), name.c_str(), nullptr, clock);
                add_metadata(pair.out, *target.symbol);
                sn_reg_set_flags(module, pair.out, flags & SN_REG_CLOCK_NEGEDGE);
                sequential_selected_registers.emplace(target, pair);
                selected_values.emplace(target, pair.out);
            }
            sequential_blocks.push_back(std::move(sequential));
        }
        return true;
    }

    bool prepare_combinational_blocks()
    {
        for (const ProceduralBlockSymbol* procedural : procedural_blocks)
        {
            if (is_sequential_block(*procedural))
                continue;
            if (procedural->procedureKind == ProceduralBlockKind::Initial ||
                procedural->procedureKind == ProceduralBlockKind::Final)
                continue;
            if (procedural->procedureKind != ProceduralBlockKind::Always &&
                procedural->procedureKind != ProceduralBlockKind::AlwaysComb &&
                procedural->procedureKind != ProceduralBlockKind::AlwaysLatch)
            {
                std::fprintf(stderr, "sn-slang: only combinational always blocks are currently supported\n");
                return false;
            }
            std::vector<const ValueSymbol*> targets;
            std::vector<SelectedValue> selected_targets;
            std::unordered_set<const ValueSymbol*> seen;
            std::unordered_set<SelectedValue, SelectedValueHash> selected_seen;
            std::vector<const ValueSymbol*> syntactic_targets;
            std::vector<SelectedValue> syntactic_selected_targets;
            std::unordered_set<const ValueSymbol*> syntactic_seen;
            std::unordered_set<SelectedValue, SelectedValueHash> syntactic_selected_seen;
            prune_procedural_constants = false;
            bool syntactic_ok = collect_sequential_targets(procedural->getBody(), syntactic_targets,
                                                            syntactic_selected_targets, syntactic_seen,
                                                            syntactic_selected_seen, false);
            prune_procedural_constants = true;
            if (!syntactic_ok)
                return false;
            if (!collect_sequential_targets(procedural->getBody(), targets, selected_targets, seen, selected_seen,
                                            false))
                return false;
            for (const ValueSymbol* target : syntactic_targets)
                if (!seen.contains(target) && !values.contains(target) && !assignments.contains(target) &&
                    !combinational_placeholders.contains(target))
                    constant_dead_values.emplace(target);
            for (const SelectedValue& target : syntactic_selected_targets)
                if (!selected_seen.contains(target) && !selected_values.contains(target) &&
                    !selected_assignments.contains(target) && !combinational_selected_placeholders.contains(target))
                    constant_dead_selected_values.emplace(target);
            for (const ValueSymbol* target : targets)
                constant_dead_values.erase(target);
            for (const SelectedValue& target : selected_targets)
                constant_dead_selected_values.erase(target);
            std::erase_if(selected_targets, [&](const SelectedValue& target) {
                if (seen.contains(target.symbol))
                    return true;
                SelectedValue whole = target;
                whole.bit = -1;
                return target.bit >= 0 && selected_seen.contains(whole);
            });
            // always_comb describes sensitivity and intent; it does not assign
            // omitted branches or unselected bits. Preserve their hold behavior
            // just as for always @* / always_latch, never substitute zero.
            for (const ValueSymbol* target : targets)
            {
                if (combinational_placeholders.contains(target))
                    continue;
                if (values.contains(target) || assignments.contains(target))
                {
                    std::fprintf(stderr, "sn-slang: combinational variable '%.*s' has multiple drivers\n",
                                 int(target->name.size()), target->name.data());
                    return false;
                }
                uint32_t bits = width(target->getType());
                if (!bits)
                    return false;
                std::string name(target->name);
                sn_obj_id_t placeholder =
                    sn_module_add_named_obj(module, SN_BUF, bits, target->getType().isSigned(), 1, name.c_str());
                combinational_placeholders.emplace(target, placeholder);
                values.emplace(target, placeholder);
            }
            for (const SelectedValue& target : selected_targets)
            {
                if (combinational_placeholders.contains(target.symbol))
                    continue;
                if (combinational_selected_placeholders.contains(target))
                    continue;
                if (undriven_selected_values.erase(target))
                    selected_values.erase(target);
                if (selected_values.contains(target) || selected_assignments.contains(target))
                {
                    std::fprintf(stderr,
                                 "sn-slang: combinational selected variable '%.*s[%lld][%lld]' has multiple "
                                 "drivers\n",
                                 int(target.symbol->name.size()), target.symbol->name.data(),
                                 static_cast<long long>(target.index), static_cast<long long>(target.bit));
                    return false;
                }
                uint32_t bits = selected_width(target);
                if (!bits)
                    return false;
                std::string name = selected_name(target);
                sn_obj_id_t placeholder =
                    sn_module_add_named_obj(module, SN_BUF, bits, selected_is_signed(target), 1, name.c_str());
                combinational_selected_placeholders.emplace(target, placeholder);
                selected_values.emplace(target, placeholder);
            }
        }
        return true;
    }

    template<typename MaskMap, typename Key>
    static bool mark_assignment_mask(MaskMap& masks, const Key& key, uint32_t bits, uint32_t offset,
                                     uint32_t count)
    {
        if (!bits || uint64_t(offset) + count > bits)
            return false;
        std::vector<uint32_t>& mask = masks[key];
        if (mask.empty())
            mask.resize(sn_const_word_count(bits));
        for (uint32_t bit = 0; bit < count; bit++)
            mask[(offset + bit) / 32] |= uint32_t(1) << ((offset + bit) % 32);
        return true;
    }

    bool mark_procedural_assigned(ProceduralValues& environment, const ValueSymbol* symbol, uint32_t offset,
                                  uint32_t count)
    {
        return mark_assignment_mask(environment.assigned_masks, symbol, width(symbol->getType()), offset, count);
    }

    bool mark_procedural_assigned(ProceduralValues& environment, const SelectedValue& selected, uint32_t offset,
                                  uint32_t count)
    {
        return mark_assignment_mask(environment.selected_assigned_masks, selected, selected_width(selected), offset,
                                    count);
    }

    template<typename MaskMap>
    static bool assignment_mask_is_full(const MaskMap& masks, const typename MaskMap::key_type& key, uint32_t bits)
    {
        auto found = masks.find(key);
        if (found == masks.end() || found->second.size() != sn_const_word_count(bits))
            return false;
        for (uint32_t bit = 0; bit < bits; bit++)
            if (((found->second[bit / 32] >> (bit % 32)) & 1u) == 0)
                return false;
        return true;
    }

    template<typename MaskMap>
    static void intersect_assignment_masks(const MaskMap& first, const MaskMap& second, MaskMap& result)
    {
        result.clear();
        for (const auto& [key, first_mask] : first)
        {
            auto second_it = second.find(key);
            if (second_it == second.end() || first_mask.size() != second_it->second.size())
                continue;
            std::vector<uint32_t> common(first_mask.size());
            bool any = false;
            for (size_t word = 0; word < common.size(); word++)
            {
                common[word] = first_mask[word] & second_it->second[word];
                any = any || common[word] != 0;
            }
            if (any)
                result.emplace(key, std::move(common));
        }
    }

    template<typename MaskMap>
    static void intersect_assignment_masks(const MaskMap& fallback, const std::vector<ProceduralValues>& branches,
                                           MaskMap ProceduralValues::*member, MaskMap& result)
    {
        result = fallback;
        for (auto it = result.begin(); it != result.end();)
        {
            bool any = false;
            for (const ProceduralValues& branch : branches)
            {
                const MaskMap& branch_masks = branch.*member;
                auto branch_it = branch_masks.find(it->first);
                if (branch_it == branch_masks.end() || branch_it->second.size() != it->second.size())
                {
                    std::fill(it->second.begin(), it->second.end(), 0);
                    break;
                }
                for (size_t word = 0; word < it->second.size(); word++)
                    it->second[word] &= branch_it->second[word];
            }
            for (uint32_t word : it->second)
                any = any || word != 0;
            if (!any)
                it = result.erase(it);
            else
                ++it;
        }
    }

    sn_obj_id_t merge_partial_value(sn_obj_id_t current, sn_obj_id_t value, uint32_t total_width, uint32_t offset)
    {
        uint32_t value_width = sn_obj_width(module, value);
        std::vector<uint32_t> mask_words(sn_const_word_count(total_width));
        for (uint32_t bit = 0; bit < value_width; bit++)
            mask_words[(offset + bit) / 32] |= uint32_t(1) << ((offset + bit) % 32);
        sn_obj_id_t mask = sn_module_add_const(module, total_width, false, mask_words.data(), nullptr);
        sn_obj_id_t inverse = sn_module_add_operator(module, SN_BIT_NOT, total_width, false, 1, &mask, nullptr);
        sn_obj_id_t kept_fanins[2] = {current, inverse};
        sn_obj_id_t kept = sn_module_add_operator(module, SN_BIT_AND, total_width, false, 2, kept_fanins, nullptr);
        PartialDriver driver{offset, value_width, value};
        sn_obj_id_t placed = materialize_partial_drivers(total_width, false, {driver});
        sn_obj_id_t merged_fanins[2] = {kept, placed};
        return sn_module_add_operator(module, SN_BIT_OR, total_width, false, 2, merged_fanins, nullptr);
    }

    bool assign_dynamic_procedural_lvalue(const sn_lvalue_t& lvalue, sn_obj_id_t value,
                                          ProceduralValues& environment)
    {
        if (const auto* stream = std::get_if<sn_lvalue_t::stream_t>(&lvalue.descriptor))
        {
            sn_obj_id_t reordered = reorder_stream_value(value, stream->slice_size);
            return reordered != SN_INVALID_ID &&
                   assign_analyzed_procedural_lvalue(*stream->inner, reordered, environment);
        }
        struct Target
        {
            const ValueSymbol* symbol;
            uint32_t offset;
            std::vector<std::pair<sn_obj_id_t, int64_t>> conditions;
        };
        std::vector<Target> targets;
        auto enumerate = [&](auto&& self, const sn_lvalue_t& current, uint64_t offset,
                             std::vector<std::pair<sn_obj_id_t, int64_t>> conditions) -> bool {
            if (const auto* variable = std::get_if<sn_lvalue_t::variable_t>(&current.descriptor))
            {
                if (offset > UINT32_MAX)
                    return false;
                targets.push_back({variable->symbol, uint32_t(offset), std::move(conditions)});
                return true;
            }
            if (const auto* element = std::get_if<sn_lvalue_t::array_element_t>(&current.descriptor))
            {
                const Type& type = element->symbol->getType();
                if (!type.hasFixedRange())
                    return false;
                ConstantRange range = type.getFixedRange();
                auto add = [&](int64_t index, auto next_conditions) {
                    if (index < INT32_MIN || index > INT32_MAX || !range.containsPoint(int32_t(index)))
                        return true;
                    uint64_t next_offset = offset + uint64_t(range.translateIndex(int32_t(index))) * current.width;
                    if (next_offset > UINT32_MAX)
                        return false;
                    targets.push_back({element->symbol, uint32_t(next_offset), std::move(next_conditions)});
                    return true;
                };
                if (element->constant_index)
                    return add(*element->constant_index, std::move(conditions));
                sn_obj_id_t selector = lower_expression(*element->selector);
                if (selector == SN_INVALID_ID)
                    return false;
                for (int64_t index = range.lower(); index <= range.upper(); index++)
                {
                    auto next = conditions;
                    next.emplace_back(selector, index);
                    if (!add(index, std::move(next)))
                        return false;
                }
                return true;
            }
            if (const auto* select = std::get_if<sn_lvalue_t::select_t>(&current.descriptor))
            {
                if (auto static_offset = static_select_offset(*select, current.width))
                    return self(self, *select->inner, offset + *static_offset, std::move(conditions));
                if (!select->element || !select->input_type || !select->input_type->hasFixedRange())
                {
                    // Dynamic indexed part-selects are supported below; simple ranges must have constant bounds.
                    if (!select->width_expr || !select->input_type || !select->input_type->hasFixedRange() ||
                        select->selection_kind == RangeSelectionKind::Simple)
                        return false;
                }
                sn_obj_id_t selector = lower_expression(*select->selector);
                if (selector == SN_INVALID_ID)
                    return false;
                ConstantRange range = select->input_type->getFixedRange();
                const Type* input_element = select->input_type->getArrayElementType();
                uint32_t stride = input_element ? width(*input_element) : 1;
                if (!stride)
                    return false;
                for (int64_t index = range.lower(); index <= range.upper(); index++)
                {
                    ConstantRange selected{int32_t(index), int32_t(index)};
                    if (!select->element)
                    {
                        int64_t selection_width = select->constant_right.value_or(current.width);
                        if (selection_width <= 0 || selection_width > INT32_MAX ||
                            select->selection_kind == RangeSelectionKind::Simple)
                            continue;
                        auto indexed = ConstantRange::getIndexedRange(
                            int32_t(index), int32_t(selection_width), range.isDescending(),
                            select->selection_kind == RangeSelectionKind::IndexedUp);
                        if (!indexed)
                            continue;
                        selected = *indexed;
                    }
                    if (!range.containsPoint(selected.left) || !range.containsPoint(selected.right))
                        continue;
                    int32_t ordinal = range.translateIndex(selected.right);
                    if (ordinal < 0)
                        continue;
                    uint64_t next_offset = offset + uint64_t(ordinal) * stride;
                    if (next_offset > UINT32_MAX)
                        return false;
                    auto next = conditions;
                    next.emplace_back(selector, index);
                    if (!self(self, *select->inner, next_offset, std::move(next)))
                        return false;
                }
                return true;
            }
            if (const auto* member = std::get_if<sn_lvalue_t::member_t>(&current.descriptor))
                return self(self, *member->inner, offset + member->bit_offset, std::move(conditions));
            return false;
        };

        bool enumerated = enumerate(enumerate, lvalue, 0, {});
        if (!enumerated || targets.empty())
        {
            std::fprintf(stderr,
                         "sn-slang: unsupported dynamic procedural lvalue (descriptor=%zu, enumerated=%s, "
                         "targets=%zu)\n",
                         lvalue.descriptor.index(), enumerated ? "yes" : "no", targets.size());
            return false;
        }

        std::unordered_map<const ValueSymbol*, sn_obj_id_t> results;
        for (const Target& target : targets)
        {
            uint32_t total_width = width(target.symbol->getType());
            uint32_t value_width = sn_obj_width(module, value);
            if (!total_width || uint64_t(target.offset) + value_width > total_width)
                return false;
            sn_obj_id_t condition = SN_INVALID_ID;
            for (const auto& [selector, index] : target.conditions)
            {
                sn_obj_id_t constant = index_constant(sn_obj_width(module, selector), index);
                sn_obj_id_t equality_fanins[2] = {selector, constant};
                sn_obj_id_t equality =
                    sn_module_add_operator(module, SN_EQ, 1, false, 2, equality_fanins, nullptr);
                if (condition == SN_INVALID_ID)
                    condition = equality;
                else
                {
                    sn_obj_id_t and_fanins[2] = {condition, equality};
                    condition = sn_module_add_operator(module, SN_LOG_AND, 1, false, 2, and_fanins, nullptr);
                }
            }

            std::vector<SelectedValue> bit_targets;
            if (!environment.values.contains(target.symbol) &&
                !sequential_registers.contains(target.symbol) &&
                !combinational_placeholders.contains(target.symbol))
            {
                const Type* element_type = target.symbol->getType().getArrayElementType();
                uint32_t element_width = element_type ? width(*element_type) : 0;
                if (element_width && target.symbol->getType().hasFixedRange())
                {
                    uint32_t ordinal = target.offset / element_width;
                    uint32_t element_offset = target.offset % element_width;
                    ConstantRange range = target.symbol->getType().getFixedRange();
                    if (ordinal < uint32_t(range.width()) && element_offset + value_width <= element_width)
                    {
                        int64_t index = range.isDescending() ? int64_t(range.right) + ordinal
                                                             : int64_t(range.right) - ordinal;
                        SelectedValue selected{target.symbol, index};
                        if (environment.selected_values.contains(selected) ||
                            sequential_selected_registers.contains(selected) ||
                            combinational_selected_placeholders.contains(selected))
                        {
                            auto current = environment.selected_values.find(selected);
                            sn_obj_id_t old_value = current == environment.selected_values.end()
                                                        ? lower_selected(selected)
                                                        : current->second;
                            if (old_value == SN_INVALID_ID)
                                return false;
                            sn_obj_id_t candidate = !element_offset && value_width == element_width
                                                        ? value
                                                        : merge_partial_value(old_value, value, element_width,
                                                                              element_offset);
                            environment.selected_values[selected] =
                                condition == SN_INVALID_ID
                                    ? candidate
                                    : sn_module_add_mux(module, condition, candidate, old_value, nullptr);
                            if (condition == SN_INVALID_ID &&
                                !mark_procedural_assigned(environment, selected, element_offset, value_width))
                                return false;
                            continue;
                        }
                    }
                }
                bit_targets.reserve(value_width);
                for (uint32_t bit = 0; bit < value_width; bit++)
                {
                    uint32_t physical = target.offset + bit;
                    int64_t index = physical;
                    if (target.symbol->getType().hasFixedRange())
                    {
                        ConstantRange range = target.symbol->getType().getFixedRange();
                        index = range.isDescending() ? int64_t(range.right) + physical
                                                     : int64_t(range.right) - physical;
                    }
                    SelectedValue selected{target.symbol, index};
                    if (!environment.selected_values.contains(selected) &&
                        !sequential_selected_registers.contains(selected) &&
                        !combinational_selected_placeholders.contains(selected))
                    {
                        bit_targets.clear();
                        break;
                    }
                    bit_targets.push_back(selected);
                }
            }
            if (bit_targets.size() == value_width)
            {
                for (uint32_t bit = 0; bit < value_width; bit++)
                {
                    const SelectedValue& selected = bit_targets[bit];
                    auto current = environment.selected_values.find(selected);
                    sn_obj_id_t old_value = current == environment.selected_values.end() ? lower_selected(selected)
                                                                                          : current->second;
                    if (old_value == SN_INVALID_ID)
                        return false;
                    sn_obj_id_t new_value = sn_module_add_slice(module, value, int32_t(bit), int32_t(bit), nullptr);
                    environment.selected_values[selected] =
                        condition == SN_INVALID_ID
                            ? new_value
                            : sn_module_add_mux(module, condition, new_value, old_value, nullptr);
                    if (condition == SN_INVALID_ID && !mark_procedural_assigned(environment, selected, 0, 1))
                        return false;
                }
                continue;
            }
            auto result_it = results.find(target.symbol);
            if (result_it == results.end())
            {
                auto current = environment.values.find(target.symbol);
                sn_obj_id_t initial = current == environment.values.end() ? lower_value(*target.symbol)
                                                                          : current->second;
                if (initial == SN_INVALID_ID)
                    return false;
                result_it = results.emplace(target.symbol, initial).first;
            }
            sn_obj_id_t candidate =
                merge_partial_value(result_it->second, value, total_width, target.offset);
            result_it->second = condition == SN_INVALID_ID
                                    ? candidate
                                    : sn_module_add_mux(module, condition, candidate, result_it->second, nullptr);
            if (condition == SN_INVALID_ID &&
                !mark_procedural_assigned(environment, target.symbol, target.offset,
                                          sn_obj_width(module, value)))
                return false;
        }
        for (const auto& [symbol, result] : results)
            environment.values[symbol] = result;
        return true;
    }

    bool assign_analyzed_procedural_lvalue(const sn_lvalue_t& lvalue, sn_obj_id_t value,
                                           ProceduralValues& environment, uint32_t target_offset = 0)
    {
        uint32_t value_width = sn_obj_width(module, value);
        if (!value_width || value_width > lvalue.width || uint64_t(target_offset) + value_width > lvalue.width)
            return false;

        // A static selection inside a packed aggregate can be handled uniformly as one physical bit span. This
        // also covers nested packed arrays such as data[word][byte * 8 +: 8], whose recursive descriptor carries
        // a different stride at each level.
        if (!target_offset && lvalue.is_static &&
            !std::holds_alternative<sn_lvalue_t::variable_t>(lvalue.descriptor))
        {
            const ValueSymbol* root = nullptr;
            uint32_t offset = 0;
            if (static_lvalue_span(lvalue, root, offset) && root &&
                (environment.values.contains(root) || sequential_registers.contains(root) ||
                 combinational_placeholders.contains(root)))
            {
                uint32_t total_width = width(root->getType());
                if (uint64_t(offset) + value_width > total_width)
                    return false;
                auto current = environment.values.find(root);
                sn_obj_id_t old_value = current == environment.values.end() ? lower_value(*root) : current->second;
                if (old_value == SN_INVALID_ID)
                    return false;
                environment.values[root] = !offset && value_width == total_width
                                               ? value
                                               : merge_partial_value(old_value, value, total_width, offset);
                return mark_procedural_assigned(environment, root, offset, value_width);
            }
        }

        if (const auto* variable = std::get_if<sn_lvalue_t::variable_t>(&lvalue.descriptor))
        {
            uint32_t total_width = width(variable->symbol->getType());
            if ((target_offset || value_width != total_width) &&
                !environment.values.contains(variable->symbol) &&
                !sequential_registers.contains(variable->symbol) &&
                !combinational_placeholders.contains(variable->symbol))
            {
                std::vector<SelectedValue> bit_targets;
                bit_targets.reserve(value_width);
                for (uint32_t bit = 0; bit < value_width; bit++)
                {
                    uint32_t physical = target_offset + bit;
                    int64_t index = physical;
                    if (variable->symbol->getType().hasFixedRange())
                    {
                        ConstantRange range = variable->symbol->getType().getFixedRange();
                        index = range.isDescending() ? int64_t(range.right) + physical
                                                     : int64_t(range.right) - physical;
                    }
                    SelectedValue target{variable->symbol, index};
                    if (!environment.selected_values.contains(target) &&
                        !sequential_selected_registers.contains(target) &&
                        !combinational_selected_placeholders.contains(target))
                    {
                        bit_targets.clear();
                        break;
                    }
                    bit_targets.push_back(target);
                }
                if (bit_targets.size() == value_width)
                {
                    for (uint32_t bit = 0; bit < value_width; bit++)
                    {
                        sn_obj_id_t slice = sn_module_add_slice(module, value, int32_t(bit), int32_t(bit), nullptr);
                        environment.selected_values[bit_targets[bit]] = slice;
                        if (!mark_procedural_assigned(environment, bit_targets[bit], 0, 1))
                            return false;
                    }
                    return true;
                }
            }
            if (!target_offset && value_width == total_width)
                environment.values[variable->symbol] = value;
            else
            {
                auto current = environment.values.find(variable->symbol);
                sn_obj_id_t old_value = current == environment.values.end() ? lower_value(*variable->symbol)
                                                                            : current->second;
                if (old_value == SN_INVALID_ID || uint64_t(target_offset) + value_width > total_width)
                    return false;
                environment.values[variable->symbol] =
                    merge_partial_value(old_value, value, total_width, target_offset);
            }
            return mark_procedural_assigned(environment, variable->symbol, target_offset, value_width);
        }

        if (const auto* element = std::get_if<sn_lvalue_t::array_element_t>(&lvalue.descriptor))
        {
            if (!element->constant_index)
                return false;
            if (environment.values.contains(element->symbol) || sequential_registers.contains(element->symbol) ||
                combinational_placeholders.contains(element->symbol))
            {
                const Type& outer_type = element->symbol->getType();
                if (!outer_type.hasFixedRange() || *element->constant_index < INT32_MIN ||
                    *element->constant_index > INT32_MAX)
                    return false;
                ConstantRange range = outer_type.getFixedRange();
                if (!range.containsPoint(int32_t(*element->constant_index)))
                    return false;
                uint32_t total_width = width(outer_type);
                uint64_t offset = uint64_t(range.translateIndex(int32_t(*element->constant_index))) * lvalue.width +
                                  target_offset;
                if (offset + value_width > total_width || offset > UINT32_MAX)
                    return false;
                auto current = environment.values.find(element->symbol);
                sn_obj_id_t old_value = current == environment.values.end() ? lower_value(*element->symbol)
                                                                            : current->second;
                if (old_value == SN_INVALID_ID)
                    return false;
                environment.values[element->symbol] =
                    merge_partial_value(old_value, value, total_width, uint32_t(offset));
                return mark_procedural_assigned(environment, element->symbol, uint32_t(offset), value_width);
            }
            SelectedValue selected{element->symbol, *element->constant_index};
            uint32_t total_width = selected_width(selected);
            const Type* element_type = selected.symbol->getType().getArrayElementType();
            if ((target_offset || value_width != total_width) && element_type && element_type->hasFixedRange())
            {
                ConstantRange range = element_type->getFixedRange();
                const Type* child_type = element_type->getArrayElementType();
                uint32_t child_width = child_type ? width(*child_type) : 1;
                if (!child_width)
                    return false;
                uint32_t physical = target_offset / child_width;
                uint32_t child_offset = target_offset % child_width;
                if (child_offset + value_width <= child_width)
                {
                    int64_t index = range.isDescending() ? int64_t(range.right) + physical
                                                         : int64_t(range.right) - physical;
                    SelectedValue target{selected.symbol, selected.index, index};
                    if (environment.selected_values.contains(target) || sequential_selected_registers.contains(target) ||
                        combinational_selected_placeholders.contains(target))
                    {
                        auto current = environment.selected_values.find(target);
                        sn_obj_id_t old_value = current == environment.selected_values.end() ? lower_selected(target)
                                                                                              : current->second;
                        if (old_value == SN_INVALID_ID)
                            return false;
                        environment.selected_values[target] =
                            !child_offset && value_width == child_width
                                ? value
                                : merge_partial_value(old_value, value, child_width, child_offset);
                        return mark_procedural_assigned(environment, target, child_offset, value_width);
                    }
                }
                if (child_width == 1)
                {
                    std::vector<SelectedValue> bit_targets;
                    bit_targets.reserve(value_width);
                    for (uint32_t bit = 0; bit < value_width; bit++)
                    {
                        uint32_t bit_physical = target_offset + bit;
                        int64_t index = range.isDescending() ? int64_t(range.right) + bit_physical
                                                             : int64_t(range.right) - bit_physical;
                        SelectedValue target{selected.symbol, selected.index, index};
                        if (!environment.selected_values.contains(target) &&
                            !sequential_selected_registers.contains(target) &&
                            !combinational_selected_placeholders.contains(target))
                        {
                            bit_targets.clear();
                            break;
                        }
                        bit_targets.push_back(target);
                    }
                    if (bit_targets.size() == value_width)
                    {
                        for (uint32_t bit = 0; bit < value_width; bit++)
                        {
                            sn_obj_id_t slice =
                                sn_module_add_slice(module, value, int32_t(bit), int32_t(bit), nullptr);
                            environment.selected_values[bit_targets[bit]] = slice;
                            if (!mark_procedural_assigned(environment, bit_targets[bit], 0, 1))
                                return false;
                        }
                        return true;
                    }
                }
            }
            if (!target_offset && value_width == total_width)
                environment.selected_values[selected] = value;
            else
            {
                auto current = environment.selected_values.find(selected);
                sn_obj_id_t old_value = current == environment.selected_values.end() ? lower_selected(selected)
                                                                                      : current->second;
                if (old_value == SN_INVALID_ID || uint64_t(target_offset) + value_width > total_width)
                    return false;
                environment.selected_values[selected] =
                    merge_partial_value(old_value, value, total_width, target_offset);
            }
            return mark_procedural_assigned(environment, selected, target_offset, value_width);
        }

        if (const auto* memory_element = std::get_if<sn_lvalue_t::memory_element_t>(&lvalue.descriptor))
        {
            if (lowering_initial_block || !nonblocking_read_values)
            {
                std::fprintf(stderr, "sn-slang: memory writes require a nonblocking edge-triggered assignment\n");
                return false;
            }
            auto memory_it = memories.find(memory_element->symbol);
            sn_obj_id_t address = lower_expression(*memory_element->address);
            if (memory_it == memories.end() || address == SN_INVALID_ID)
                return false;
            const Memory& memory = memory_it->second;
            address = normalize_memory_address(memory, address);
            uint32_t total_width = sn_obj_width(module, memory.pair.out);
            if (address == SN_INVALID_ID || uint64_t(target_offset) + value_width > total_width)
                return false;
            sn_obj_id_t data = value;
            sn_obj_id_t mask = SN_INVALID_ID;
            if (target_offset || value_width != total_width)
            {
                sn_obj_id_t current = sn_module_add_mem_read(module, memory.pair.out, SN_INVALID_ID, SN_INVALID_ID,
                                                             address, nullptr);
                // A preceding write contributes to this read-modify-write value only when its runtime address and
                // enable match. Object identity is not a valid address comparison after expression lowering.
                for (const ProceduralValues::MemoryWrite& prior : environment.memory_writes)
                {
                    if (prior.memory != memory_element->symbol)
                        continue;
                    sn_obj_id_t address_fanins[2] = {prior.address, address};
                    sn_obj_id_t same_address =
                        sn_module_add_operator(module, SN_EQ, 1, false, 2, address_fanins, nullptr);
                    sn_obj_id_t match_fanins[2] = {prior.enable, same_address};
                    sn_obj_id_t match =
                        sn_module_add_operator(module, SN_LOG_AND, 1, false, 2, match_fanins, nullptr);
                    current = sn_module_add_mux(module, match, prior.data, current, nullptr);
                }
                data = merge_partial_value(current, value, total_width, target_offset);
                std::vector<uint32_t> mask_words(sn_const_word_count(total_width));
                for (uint32_t bit = 0; bit < value_width; bit++)
                    mask_words[(target_offset + bit) / 32] |= uint32_t(1) << ((target_offset + bit) % 32);
                mask = sn_module_add_const(module, total_width, false, mask_words.data(), nullptr);
            }
            const uint32_t one_word = 1;
            sn_obj_id_t enable = sn_module_add_const(module, 1, false, &one_word, nullptr);
            environment.memory_writes.push_back({memory_element->symbol, address, data, enable, mask});
            return true;
        }

        if (const auto* stream = std::get_if<sn_lvalue_t::stream_t>(&lvalue.descriptor))
        {
            if (target_offset || value_width != lvalue.width)
                return false;
            sn_obj_id_t reordered = reorder_stream_value(value, stream->slice_size);
            return reordered != SN_INVALID_ID &&
                   assign_analyzed_procedural_lvalue(*stream->inner, reordered, environment);
        }

        if (const auto* concat = std::get_if<sn_lvalue_t::concat_t>(&lvalue.descriptor))
        {
            uint32_t source_offset = 0;
            for (auto it = concat->elements.rbegin(); it != concat->elements.rend(); ++it)
            {
                sn_obj_id_t slice = sn_module_add_slice(module, value, int32_t(source_offset + it->width - 1),
                                                        int32_t(source_offset), nullptr);
                if (!assign_analyzed_procedural_lvalue(*it, slice, environment))
                    return false;
                source_offset += it->width;
            }
            return source_offset == value_width;
        }

        if (const auto* member = std::get_if<sn_lvalue_t::member_t>(&lvalue.descriptor))
        {
            if (member->bit_offset > UINT32_MAX - target_offset)
                return false;
            return assign_analyzed_procedural_lvalue(*member->inner, value, environment,
                                                     target_offset + uint32_t(member->bit_offset));
        }

        if (const auto* select = std::get_if<sn_lvalue_t::select_t>(&lvalue.descriptor))
        {
            auto offset = static_select_offset(*select, lvalue.width);
            if (!offset)
            {
                // A statically out-of-range procedural write has no effect in SystemVerilog. This occurs naturally
                // while conservatively unrolling a dynamically bounded loop through the full destination width.
                return select->constant_selector.has_value() && select->constant_right.has_value();
            }
            return assign_analyzed_procedural_lvalue(*select->inner, value, environment, target_offset + *offset);
        }
        return false;
    }

    bool assign_procedural_lvalue_legacy(const Expression& expression, sn_obj_id_t value,
                                         ProceduralValues& environment)
    {
        if (const auto* member = expression.as_if<MemberAccessExpression>())
            if (const auto* target = member->member.as_if<ValueSymbol>())
            {
                environment.values[target] = value;
                return mark_procedural_assigned(environment, target, 0, width(target->getType()));
            }
        if (auto selected_bit = named_element_bit(expression))
        {
            SelectedValue bit_target = *selected_bit;
            const auto* select = expression.as_if<ElementSelectExpression>();
            const Type* element_type = selected_bit->symbol->getType().getArrayElementType();
            auto index = select ? constant_integer(select->selector()) : std::nullopt;
            uint32_t bits = select && select->type ? width(*select->type) : 0;
            if (!element_type || !element_type->hasFixedRange() || !index || !bits ||
                bits != sn_obj_width(module, value) || *index < INT32_MIN || *index > INT32_MAX)
                return false;
            ConstantRange range = element_type->getFixedRange();
            if (!range.containsPoint(int32_t(*index)))
                return false;
            int32_t ordinal = range.translateIndex(int32_t(*index));
            uint64_t offset = uint64_t(ordinal) * bits;
            selected_bit->bit = -1;
            bool whole_element_target = environment.selected_values.contains(*selected_bit) ||
                                        sequential_selected_registers.contains(*selected_bit) ||
                                        combinational_selected_placeholders.contains(*selected_bit);
            if (!whole_element_target)
            {
                environment.selected_values[bit_target] = value;
                return mark_procedural_assigned(environment, bit_target, 0, bits);
            }
            uint32_t total_width = selected_width(*selected_bit);
            auto current = environment.selected_values.find(*selected_bit);
            sn_obj_id_t old_value = current == environment.selected_values.end() ? lower_selected(*selected_bit)
                                                                                  : current->second;
            if (ordinal < 0 || offset + bits > total_width || offset > UINT32_MAX || old_value == SN_INVALID_ID)
                return false;
            environment.selected_values[*selected_bit] =
                merge_partial_value(old_value, value, total_width, uint32_t(offset));
            return mark_procedural_assigned(environment, *selected_bit, uint32_t(offset), bits);
        }
        if (auto selected = named_element(expression))
        {
            bool whole_word_target = environment.values.contains(selected->symbol) ||
                                     combinational_placeholders.contains(selected->symbol) ||
                                     sequential_registers.contains(selected->symbol);
            if (!whole_word_target)
            {
                environment.selected_values[*selected] = value;
                return mark_procedural_assigned(environment, *selected, 0, sn_obj_width(module, value));
            }
        }
        if (const auto* element = expression.as_if<ElementSelectExpression>())
        {
            const auto* named = element->value().as_if<NamedValueExpression>();
            if (named && named->symbol.getType().isUnpackedArray() &&
                named->symbol.getType().hasFixedRange() && !memories.contains(&named->symbol))
            {
                const Type* element_type = named->symbol.getType().getArrayElementType();
                uint32_t bits = element_type ? width(*element_type) : 0;
                sn_obj_id_t selector = lower_expression(element->selector());
                if (!element_type || !bits || bits != sn_obj_width(module, value) || selector == SN_INVALID_ID)
                {
                    std::fprintf(stderr, "sn-slang: unsupported dynamic unpacked-array procedural lvalue\n");
                    return false;
                }
                ConstantRange range = named->symbol.getType().getFixedRange();
                for (int64_t index = range.lower(); index <= range.upper(); index++)
                {
                    SelectedValue selected{&named->symbol, index};
                    auto current_it = environment.selected_values.find(selected);
                    sn_obj_id_t current = current_it == environment.selected_values.end() ? SN_INVALID_ID
                                                                                           : current_it->second;
                    if (current == SN_INVALID_ID && is_automatic_value(named->symbol))
                    {
                        std::vector<uint32_t> words(sn_const_word_count(bits));
                        current = sn_module_add_const(module, bits, element_type->isSigned(), words.data(), nullptr);
                    }
                    else if (current == SN_INVALID_ID)
                        current = lower_selected(selected);
                    if (current == SN_INVALID_ID)
                        return false;
                    sn_obj_id_t index_value = index_constant(sn_obj_width(module, selector), index);
                    sn_obj_id_t equality_fanins[2] = {selector, index_value};
                    sn_obj_id_t equality =
                        sn_module_add_operator(module, SN_EQ, 1, false, 2, equality_fanins, nullptr);
                    environment.selected_values[selected] =
                        sn_module_add_mux(module, equality, value, current, nullptr);
                }
                return true;
            }
            uint32_t bits = named ? width(named->symbol.getType()) : 0;
            uint32_t element_bits = width(*element->type);
            if (!named || !bits || !element_bits || sn_obj_width(module, value) != element_bits)
            {
                std::fprintf(stderr, "sn-slang: unsupported procedural element-selection lvalue\n");
                return false;
            }
            auto current_it = environment.values.find(&named->symbol);
            sn_obj_id_t current =
                current_it == environment.values.end() ? lower_value(named->symbol) : current_it->second;
            sn_obj_id_t index = lower_expression(element->selector());
            if (current == SN_INVALID_ID || index == SN_INVALID_ID)
                return false;

            if (element_bits > 1)
            {
                ConstantRange range = named->symbol.getType().getFixedRange();
                if (uint64_t(range.width()) * element_bits != bits)
                    return false;
                std::vector<std::pair<int64_t, sn_obj_id_t>> alternatives;
                alternatives.reserve(size_t(range.width()));
                for (int64_t legal = range.lower(); legal <= range.upper(); legal++)
                {
                    int32_t physical = range.translateIndex(int32_t(legal)) * int32_t(element_bits);
                    alternatives.emplace_back(legal, merge_partial_value(current, value, bits, uint32_t(physical)));
                }
                environment.values[&named->symbol] = lower_sparse_selection(index, alternatives, current);
                return true;
            }

            std::vector<uint32_t> one_words(sn_const_word_count(bits));
            one_words[0] = 1;
            sn_obj_id_t one = sn_module_add_const(module, bits, false, one_words.data(), nullptr);
            sn_obj_id_t mask_fanins[2] = {one, index};
            sn_obj_id_t mask = sn_module_add_operator(module, SN_SHL, bits, false, 2, mask_fanins, nullptr);
            sn_obj_id_t inverse = sn_module_add_operator(module, SN_BIT_NOT, bits, false, 1, &mask, nullptr);
            sn_obj_id_t kept_fanins[2] = {current, inverse};
            sn_obj_id_t kept = sn_module_add_operator(module, SN_BIT_AND, bits, false, 2, kept_fanins, nullptr);
            sn_obj_id_t extended = sn_module_add_operator(module, SN_CAST, bits, false, 1, &value, nullptr);
            sn_obj_id_t shifted_fanins[2] = {extended, index};
            sn_obj_id_t shifted = sn_module_add_operator(module, SN_SHL, bits, false, 2, shifted_fanins, nullptr);
            sn_obj_id_t merged_fanins[2] = {kept, shifted};
            environment.values[&named->symbol] =
                sn_module_add_operator(module, SN_BIT_OR, bits, false, 2, merged_fanins, nullptr);
            auto constant_index = constant_integer(element->selector());
            if (constant_index)
            {
                int32_t bit_offset = named->symbol.getType().getFixedRange().translateIndex(int32_t(*constant_index));
                if (bit_offset < 0 || !mark_procedural_assigned(environment, &named->symbol,
                                                               uint32_t(bit_offset), 1))
                    return false;
            }
            return true;
        }
        if (const auto* range = expression.as_if<RangeSelectExpression>())
        {
            if (auto selected = named_element(range->value()))
            {
                auto left = constant_integer(range->left());
                auto right = constant_integer(range->right());
                const Type* element_type = selected->symbol->getType().getArrayElementType();
                uint32_t bits = width(*range->type);
                if (!left || !right || !element_type || !element_type->hasFixedRange() || !bits ||
                    bits != sn_obj_width(module, value))
                    return false;
                auto selected_range = selected_index_range(*range, *left, *right);
                if (!selected_range)
                    return false;
                int64_t least_index = selected_range->right;
                if (least_index < INT32_MIN || least_index > INT32_MAX)
                    return false;
                ConstantRange element_range = element_type->getFixedRange();
                if (!element_range.containsPoint(int32_t(least_index)))
                    return false;
                int32_t ordinal = element_range.translateIndex(int32_t(least_index));
                const Type* scalar_type = element_type->getArrayElementType();
                uint32_t scalar_width = scalar_type ? width(*scalar_type) : 1;
                bool whole_element_target = environment.selected_values.contains(*selected) ||
                                            sequential_selected_registers.contains(*selected) ||
                                            combinational_selected_placeholders.contains(*selected);
                if (!whole_element_target && scalar_width == 1)
                {
                    for (uint32_t bit = 0; bit < bits; bit++)
                    {
                        int64_t index = selected_bit_index(*selected_range, bit);
                        SelectedValue target{selected->symbol, selected->index, index};
                        sn_obj_id_t slice = sn_module_add_slice(module, value, int32_t(bit), int32_t(bit), nullptr);
                        environment.selected_values[target] = slice;
                        if (!mark_procedural_assigned(environment, target, 0, 1))
                            return false;
                    }
                    return true;
                }
                uint64_t offset = uint64_t(ordinal) * scalar_width;
                uint32_t total_width = selected_width(*selected);
                auto current = environment.selected_values.find(*selected);
                sn_obj_id_t old_value = current == environment.selected_values.end() ? lower_selected(*selected)
                                                                                      : current->second;
                if (ordinal < 0 || !scalar_width || offset + bits > total_width || offset > UINT32_MAX ||
                    old_value == SN_INVALID_ID)
                    return false;
                environment.selected_values[*selected] =
                    merge_partial_value(old_value, value, total_width, uint32_t(offset));
                return mark_procedural_assigned(environment, *selected, uint32_t(offset), bits);
            }
            const auto* named = range->value().as_if<NamedValueExpression>();
            auto left = constant_integer(range->left());
            auto right = constant_integer(range->right());
            uint32_t bits = width(*range->type);
            if (!named || !right || !bits || bits != sn_obj_width(module, value))
            {
                std::fprintf(stderr,
                             "sn-slang: unsupported procedural range-selection lvalue (named=%u, left=%u, "
                             "right=%u, width=%u, value_width=%u, kind=%u)\n",
                             named != nullptr, left.has_value(), right.has_value(), bits,
                             sn_obj_width(module, value), unsigned(range->getSelectionKind()));
                return false;
            }
            if (!left)
            {
                if (range->getSelectionKind() == RangeSelectionKind::Simple ||
                    !named->symbol.getType().hasFixedRange())
                {
                    std::fprintf(stderr, "sn-slang: unsupported dynamic procedural range-selection lvalue\n");
                    return false;
                }
                uint32_t whole_bits = width(named->symbol.getType());
                auto current = environment.values.find(&named->symbol);
                sn_obj_id_t old_value = current == environment.values.end() ? lower_value(named->symbol)
                                                                            : current->second;
                active_procedural_values = &environment;
                sn_obj_id_t selector = lower_expression(range->left());
                active_procedural_values = nullptr;
                uint32_t selector_bits = selector == SN_INVALID_ID ? 0 : sn_obj_width(module, selector);
                if (!whole_bits || old_value == SN_INVALID_ID || !selector_bits)
                    return false;

                ConstantRange whole_range = named->symbol.getType().getFixedRange();
                int64_t constant = 0;
                bool constant_minus_selector = !whole_range.isDescending();
                if (whole_range.isDescending())
                    constant = int64_t(whole_range.lower()) +
                               (range->getSelectionKind() == RangeSelectionKind::IndexedDown ? bits - 1 : 0);
                else
                    constant = int64_t(whole_range.upper()) -
                               (range->getSelectionKind() == RangeSelectionKind::IndexedUp ? bits - 1 : 0);
                sn_obj_id_t constant_value = index_constant(selector_bits, constant);
                sn_obj_id_t offset_fanins[2] = {constant_minus_selector ? constant_value : selector,
                                                constant_minus_selector ? selector : constant_value};
                sn_obj_id_t offset = sn_module_add_operator(module, SN_SUB, selector_bits, false, 2,
                                                             offset_fanins, nullptr);

                std::vector<uint32_t> mask_words(sn_const_word_count(whole_bits));
                for (uint32_t bit = 0; bit < bits; bit++)
                    mask_words[bit / 32] |= uint32_t(1) << (bit % 32);
                sn_obj_id_t base_mask = sn_module_add_const(module, whole_bits, false, mask_words.data(), nullptr);
                sn_obj_id_t mask_fanins[2] = {base_mask, offset};
                sn_obj_id_t mask =
                    sn_module_add_operator(module, SN_SHL, whole_bits, false, 2, mask_fanins, nullptr);
                sn_obj_id_t inverse = sn_module_add_operator(module, SN_BIT_NOT, whole_bits, false, 1, &mask,
                                                              nullptr);
                sn_obj_id_t kept_fanins[2] = {old_value, inverse};
                sn_obj_id_t kept =
                    sn_module_add_operator(module, SN_BIT_AND, whole_bits, false, 2, kept_fanins, nullptr);
                sn_obj_id_t extended = sn_module_add_operator(module, SN_CAST, whole_bits, false, 1, &value,
                                                               nullptr);
                sn_obj_id_t shifted_fanins[2] = {extended, offset};
                sn_obj_id_t shifted =
                    sn_module_add_operator(module, SN_SHL, whole_bits, false, 2, shifted_fanins, nullptr);
                sn_obj_id_t merged_fanins[2] = {kept, shifted};
                environment.values[&named->symbol] =
                    sn_module_add_operator(module, SN_BIT_OR, whole_bits, false, 2, merged_fanins, nullptr);
                // A dynamic part select does not statically cover any particular bit. A preceding whole-value
                // default assignment, when present, already supplies the full assignment mask.
                return true;
            }
            auto selected_range = selected_index_range(*range, *left, *right);
            if (!selected_range)
                return false;
            int64_t least_index = selected_range->right;
            bool whole_word_target = environment.values.contains(&named->symbol) ||
                                     combinational_placeholders.contains(&named->symbol) ||
                                     sequential_registers.contains(&named->symbol);
            if (whole_word_target)
            {
                uint32_t whole_bits = width(named->symbol.getType());
                ConstantRange whole_range = named->symbol.getType().getFixedRange();
                if (least_index < INT32_MIN || least_index > INT32_MAX ||
                    !whole_range.containsPoint(int32_t(least_index)))
                    return true; // A statically out-of-range procedural write has no effect.
                const Type* element_type = named->symbol.getType().getArrayElementType();
                uint32_t element_width = element_type ? width(*element_type) : 1;
                int32_t ordinal = whole_range.translateIndex(least_index);
                uint64_t bit_offset = ordinal < 0 ? UINT64_MAX : uint64_t(ordinal) * element_width;
                if (!whole_bits || !element_width || bit_offset > UINT32_MAX || bit_offset + bits > whole_bits)
                    return false;
                if (bit_offset == 0 && bits == whole_bits)
                {
                    environment.values[&named->symbol] = value;
                    return mark_procedural_assigned(environment, &named->symbol, 0, bits);
                }
                auto current = environment.values.find(&named->symbol);
                sn_obj_id_t old_value = current == environment.values.end() ? lower_value(named->symbol)
                                                                            : current->second;
                std::vector<uint32_t> mask_words(sn_const_word_count(whole_bits));
                for (uint32_t bit = 0; bit < bits; bit++)
                    mask_words[(uint32_t(bit_offset) + bit) / 32] |=
                        uint32_t(1) << ((uint32_t(bit_offset) + bit) % 32);
                sn_obj_id_t mask = sn_module_add_const(module, whole_bits, false, mask_words.data(), nullptr);
                sn_obj_id_t inverse = sn_module_add_operator(module, SN_BIT_NOT, whole_bits, false, 1, &mask, nullptr);
                sn_obj_id_t kept_fanins[2] = {old_value, inverse};
                sn_obj_id_t kept =
                    sn_module_add_operator(module, SN_BIT_AND, whole_bits, false, 2, kept_fanins, nullptr);
                sn_obj_id_t extended = sn_module_add_operator(module, SN_CAST, whole_bits, false, 1, &value, nullptr);
                uint32_t offset_word = uint32_t(bit_offset);
                sn_obj_id_t offset = sn_module_add_const(module, 32, false, &offset_word, nullptr);
                sn_obj_id_t shifted_fanins[2] = {extended, offset};
                sn_obj_id_t shifted =
                    sn_module_add_operator(module, SN_SHL, whole_bits, false, 2, shifted_fanins, nullptr);
                sn_obj_id_t merged_fanins[2] = {kept, shifted};
                environment.values[&named->symbol] =
                    sn_module_add_operator(module, SN_BIT_OR, whole_bits, false, 2, merged_fanins, nullptr);
                return mark_procedural_assigned(environment, &named->symbol, uint32_t(bit_offset), bits);
            }
            for (uint32_t offset = 0; offset < bits; offset++)
            {
                int64_t index = selected_bit_index(*selected_range, offset);
                SelectedValue selected{&named->symbol, index};
                sn_obj_id_t bit = sn_module_add_slice(module, value, int32_t(offset), int32_t(offset), nullptr);
                environment.selected_values[selected] = bit;
                if (!mark_procedural_assigned(environment, selected, 0, 1))
                    return false;
            }
            return true;
        }
        if (const auto* concat = expression.as_if<ConcatenationExpression>())
        {
            uint32_t offset = 0;
            for (auto it = concat->operands().rbegin(); it != concat->operands().rend(); ++it)
            {
                uint32_t bits = width(*(*it)->type);
                if (!bits || uint64_t(offset) + bits > sn_obj_width(module, value))
                {
                    std::fprintf(stderr, "sn-slang: invalid procedural concatenated assignment width\n");
                    return false;
                }
                sn_obj_id_t slice = sn_module_add_slice(module, value, int32_t(offset + bits - 1), int32_t(offset),
                                                        nullptr);
                if (!assign_procedural_lvalue(**it, slice, environment))
                    return false;
                offset += bits;
            }
            return offset == sn_obj_width(module, value);
        }
        if (const ValueSymbol* target = referenced_value(expression))
        {
            environment.values[target] = value;
            return mark_procedural_assigned(environment, target, 0, width(target->getType()));
        }
        std::fprintf(stderr, "sn-slang: unsupported procedural-assignment lvalue kind %u\n",
                     unsigned(expression.kind));
        return false;
    }

    bool assign_procedural_lvalue(const Expression& expression, sn_obj_id_t value, ProceduralValues& environment)
    {
        if (expression.as_if<ConcatenationExpression>())
            return assign_procedural_lvalue_legacy(expression, value, environment);
        if (auto selected = named_element_bit(expression); selected && !environment.values.contains(selected->symbol))
            return assign_procedural_lvalue_legacy(expression, value, environment);
        if (auto selected = named_element(expression); selected && !environment.values.contains(selected->symbol))
            return assign_procedural_lvalue_legacy(expression, value, environment);
        if (const auto* range = expression.as_if<RangeSelectExpression>();
            range && named_element(range->value()) &&
            !environment.values.contains(named_element(range->value())->symbol))
            return assign_procedural_lvalue_legacy(expression, value, environment);
        if (const auto* range = expression.as_if<RangeSelectExpression>();
            range && range->value().as_if<NamedValueExpression>())
            return assign_procedural_lvalue_legacy(expression, value, environment);
        std::string error;
        auto lvalue = analyze_lvalue(expression, error, true);
        if (lvalue && !lvalue->is_static && !analyzed_lvalue_has_memory(*lvalue))
        {
            bool assigned = assign_dynamic_procedural_lvalue(*lvalue, value, environment);
            if (!assigned)
                std::fprintf(stderr,
                             "sn-slang: dynamic assignment-target lowering failed (descriptor=%zu, width=%u)\n",
                             lvalue->descriptor.index(), lvalue->width);
            return assigned;
        }
        if (lvalue && (lvalue->is_static || std::holds_alternative<sn_lvalue_t::variable_t>(lvalue->descriptor) ||
                       analyzed_lvalue_has_memory(*lvalue)))
        {
            bool assigned = assign_analyzed_procedural_lvalue(*lvalue, value, environment);
            if (!assigned)
                std::fprintf(stderr,
                             "sn-slang: static assignment-target lowering failed (descriptor=%zu, width=%u)\n",
                             lvalue->descriptor.index(), lvalue->width);
            return assigned;
        }
        return assign_procedural_lvalue_legacy(expression, value, environment);
    }

    bool merge_procedural_values(sn_obj_id_t condition, const ProceduralValues& when_true,
                                 const ProceduralValues& when_false, ProceduralValues& result)
    {
        assert(sn_obj_width(module, condition) == 1);
        auto held_value = [&](const ValueSymbol* symbol) {
            auto reg = sequential_registers.find(symbol);
            if (reg != sequential_registers.end())
                return reg->second.out;
            auto placeholder = combinational_placeholders.find(symbol);
            if (placeholder != combinational_placeholders.end())
                return placeholder->second;
            return SN_INVALID_ID;
        };
        auto held_selected_value = [&](const SelectedValue& selected) {
            auto reg = sequential_selected_registers.find(selected);
            if (reg != sequential_selected_registers.end())
                return reg->second.out;
            auto placeholder = combinational_selected_placeholders.find(selected);
            if (placeholder != combinational_selected_placeholders.end())
                return placeholder->second;
            return SN_INVALID_ID;
        };
        result = when_false;
        for (const auto& [symbol, true_value] : when_true.values)
        {
            auto false_it = when_false.values.find(symbol);
            if (false_it == when_false.values.end())
            {
                if (is_automatic_value(*symbol))
                {
                    result.values.erase(symbol);
                    continue;
                }
                sn_obj_id_t held = held_value(symbol);
                if (held == SN_INVALID_ID)
                {
                    std::fprintf(stderr, "sn-slang: procedural assignment to '%.*s' infers a latch\n",
                                 int(symbol->name.size()), symbol->name.data());
                    return false;
                }
                result.values[symbol] = true_value == held
                                            ? true_value
                                            : sn_module_add_mux(module, condition, true_value, held, nullptr);
                continue;
            }
            result.values[symbol] = true_value == false_it->second
                                        ? true_value
                                        : sn_module_add_mux(module, condition, true_value, false_it->second, nullptr);
        }
        for (const auto& [symbol, false_value] : when_false.values)
        {
            if (!when_true.values.contains(symbol))
            {
                if (is_automatic_value(*symbol))
                {
                    result.values.erase(symbol);
                    continue;
                }
                sn_obj_id_t held = held_value(symbol);
                if (held == SN_INVALID_ID)
                {
                    std::fprintf(stderr, "sn-slang: procedural assignment to '%.*s' infers a latch\n",
                                 int(symbol->name.size()), symbol->name.data());
                    return false;
                }
                result.values[symbol] = false_value == held
                                            ? false_value
                                            : sn_module_add_mux(module, condition, held, false_value, nullptr);
            }
            (void)false_value;
        }

        result.selected_values = when_false.selected_values;
        for (const auto& [selected, true_value] : when_true.selected_values)
        {
            auto false_it = when_false.selected_values.find(selected);
            if (false_it == when_false.selected_values.end())
            {
                if (is_automatic_value(*selected.symbol))
                {
                    result.selected_values.erase(selected);
                    continue;
                }
                sn_obj_id_t held = held_selected_value(selected);
                if (held == SN_INVALID_ID)
                {
                    std::fprintf(stderr, "sn-slang: procedural assignment to '%.*s[%lld][%lld]' infers a latch\n",
                                 int(selected.symbol->name.size()), selected.symbol->name.data(),
                                 static_cast<long long>(selected.index), static_cast<long long>(selected.bit));
                    return false;
                }
                result.selected_values[selected] =
                    true_value == held
                        ? true_value
                        : sn_module_add_mux(module, condition, true_value, held, nullptr);
                continue;
            }
            result.selected_values[selected] =
                true_value == false_it->second
                    ? true_value
                    : sn_module_add_mux(module, condition, true_value, false_it->second, nullptr);
        }
        for (const auto& [selected, false_value] : when_false.selected_values)
        {
            if (!when_true.selected_values.contains(selected))
            {
                if (is_automatic_value(*selected.symbol))
                {
                    result.selected_values.erase(selected);
                    continue;
                }
                sn_obj_id_t held = held_selected_value(selected);
                if (held == SN_INVALID_ID)
                {
                    std::fprintf(stderr, "sn-slang: procedural assignment to '%.*s[%lld][%lld]' infers a latch\n",
                                 int(selected.symbol->name.size()), selected.symbol->name.data(),
                                 static_cast<long long>(selected.index), static_cast<long long>(selected.bit));
                    return false;
                }
                result.selected_values[selected] =
                    false_value == held
                        ? false_value
                        : sn_module_add_mux(module, condition, held, false_value, nullptr);
            }
            (void)false_value;
        }

        intersect_assignment_masks(when_true.assigned_masks, when_false.assigned_masks, result.assigned_masks);
        intersect_assignment_masks(when_true.selected_assigned_masks, when_false.selected_assigned_masks,
                                   result.selected_assigned_masks);

        size_t common_writes = 0;
        while (common_writes < when_true.memory_writes.size() &&
               common_writes < when_false.memory_writes.size() &&
               when_true.memory_writes[common_writes] == when_false.memory_writes[common_writes])
            common_writes++;
        result.memory_writes.assign(when_true.memory_writes.begin(),
                                    when_true.memory_writes.begin() + common_writes);
        auto append_writes = [&](const ProceduralValues& branch, sn_obj_id_t branch_enable) {
            for (size_t i = common_writes; i < branch.memory_writes.size(); i++)
            {
                ProceduralValues::MemoryWrite write = branch.memory_writes[i];
                sn_obj_id_t fanins[2] = {write.enable, branch_enable};
                write.enable = sn_module_add_operator(module, SN_LOG_AND, 1, false, 2, fanins, nullptr);
                result.memory_writes.push_back(write);
            }
        };
        append_writes(when_true, condition);
        if (when_false.memory_writes.size() > common_writes)
        {
            sn_obj_id_t not_condition =
                sn_module_add_operator(module, SN_LOG_NOT, 1, false, 1, &condition, nullptr);
            append_writes(when_false, not_condition);
        }
        auto merge_flag = [&](sn_obj_id_t when_true_flag, sn_obj_id_t when_false_flag) {
            if (when_true_flag == when_false_flag)
                return when_true_flag;
            const uint32_t zero_word = 0;
            sn_obj_id_t zero = sn_module_add_const(module, 1, false, &zero_word, nullptr);
            if (when_true_flag == SN_INVALID_ID)
                when_true_flag = zero;
            if (when_false_flag == SN_INVALID_ID)
                when_false_flag = zero;
            return sn_module_add_mux(module, condition, when_true_flag, when_false_flag, nullptr);
        };
        result.return_flag = merge_flag(when_true.return_flag, when_false.return_flag);
        result.break_flag = merge_flag(when_true.break_flag, when_false.break_flag);
        result.continue_flag = merge_flag(when_true.continue_flag, when_false.continue_flag);
        return true;
    }

    bool merge_procedural_values_pmux(const std::vector<sn_obj_id_t>& conditions,
                                      const std::vector<ProceduralValues>& branches,
                                      const ProceduralValues& fallback, ProceduralValues& result)
    {
        assert(!conditions.empty() && conditions.size() == branches.size());
        if (fallback.return_flag != SN_INVALID_ID || fallback.break_flag != SN_INVALID_ID ||
            fallback.continue_flag != SN_INVALID_ID)
            return false;
        for (const ProceduralValues& branch : branches)
        {
            if (branch.return_flag != SN_INVALID_ID || branch.break_flag != SN_INVALID_ID ||
                branch.continue_flag != SN_INVALID_ID)
                return false;
            if (branch.values.size() != fallback.values.size() ||
                branch.selected_values.size() != fallback.selected_values.size() ||
                branch.memory_writes != fallback.memory_writes)
                return false;
        }
        for (const auto& [symbol, value] : fallback.values)
            for (const ProceduralValues& branch : branches)
                if (!branch.values.contains(symbol))
                    return false;
        for (const auto& [selected, value] : fallback.selected_values)
            for (const ProceduralValues& branch : branches)
                if (!branch.selected_values.contains(selected))
                    return false;

        sn_obj_id_t select = sn_module_add_concat(module, uint32_t(conditions.size()), conditions.data(), nullptr);
        result = fallback;
        for (const auto& [symbol, default_value] : fallback.values)
        {
            std::vector<sn_obj_id_t> alternatives;
            alternatives.reserve(branches.size());
            bool changed = false;
            for (const ProceduralValues& branch : branches)
            {
                sn_obj_id_t value = branch.values.at(symbol);
                alternatives.push_back(value);
                changed = changed || value != default_value;
            }
            if (changed)
            {
                sn_obj_id_t packed =
                    sn_module_add_concat(module, uint32_t(alternatives.size()), alternatives.data(), nullptr);
                result.values[symbol] = sn_module_add_pmux(module, select, packed, default_value, nullptr);
            }
        }
        for (const auto& [selected, default_value] : fallback.selected_values)
        {
            std::vector<sn_obj_id_t> alternatives;
            alternatives.reserve(branches.size());
            bool changed = false;
            for (const ProceduralValues& branch : branches)
            {
                sn_obj_id_t value = branch.selected_values.at(selected);
                alternatives.push_back(value);
                changed = changed || value != default_value;
            }
            if (changed)
            {
                sn_obj_id_t packed =
                    sn_module_add_concat(module, uint32_t(alternatives.size()), alternatives.data(), nullptr);
                result.selected_values[selected] =
                    sn_module_add_pmux(module, select, packed, default_value, nullptr);
            }
        }

        intersect_assignment_masks(fallback.assigned_masks, branches, &ProceduralValues::assigned_masks,
                                   result.assigned_masks);
        intersect_assignment_masks(fallback.selected_assigned_masks, branches,
                                   &ProceduralValues::selected_assigned_masks, result.selected_assigned_masks);
        return true;
    }

    bool merge_procedural_values_bmux(sn_obj_id_t select, const std::vector<ProceduralValues>& branches,
                                      ProceduralValues& result)
    {
        if (branches.empty() || select == SN_INVALID_ID)
            return false;
        uint32_t select_width = sn_obj_width(module, select);
        if (select_width >= 31 || branches.size() != (size_t(1) << select_width))
            return false;
        const ProceduralValues& first = branches.front();
        for (const ProceduralValues& branch : branches)
        {
            if (branch.return_flag != SN_INVALID_ID || branch.break_flag != SN_INVALID_ID ||
                branch.continue_flag != SN_INVALID_ID)
                return false;
            if (branch.values.size() != first.values.size() ||
                branch.selected_values.size() != first.selected_values.size() ||
                branch.memory_writes != first.memory_writes)
                return false;
        }
        for (const auto& [symbol, value] : first.values)
            for (const ProceduralValues& branch : branches)
                if (!branch.values.contains(symbol))
                    return false;
        for (const auto& [selected, value] : first.selected_values)
            for (const ProceduralValues& branch : branches)
                if (!branch.selected_values.contains(selected))
                    return false;
        result = first;
        for (const auto& [symbol, first_value] : first.values)
        {
            std::vector<sn_obj_id_t> alternatives;
            alternatives.reserve(branches.size());
            bool changed = false;
            for (const ProceduralValues& branch : branches)
            {
                sn_obj_id_t value = branch.values.at(symbol);
                alternatives.push_back(value);
                changed = changed || value != first_value;
            }
            if (changed)
            {
                sn_obj_id_t packed =
                    sn_module_add_concat(module, uint32_t(alternatives.size()), alternatives.data(), nullptr);
                result.values[symbol] = sn_module_add_bmux(module, select, packed,
                                                           sn_obj_width(module, first_value),
                                                           sn_obj_is_signed(module, first_value), nullptr);
            }
        }
        for (const auto& [selected, first_value] : first.selected_values)
        {
            std::vector<sn_obj_id_t> alternatives;
            alternatives.reserve(branches.size());
            bool changed = false;
            for (const ProceduralValues& branch : branches)
            {
                sn_obj_id_t value = branch.selected_values.at(selected);
                alternatives.push_back(value);
                changed = changed || value != first_value;
            }
            if (changed)
            {
                sn_obj_id_t packed =
                    sn_module_add_concat(module, uint32_t(alternatives.size()), alternatives.data(), nullptr);
                result.selected_values[selected] = sn_module_add_bmux(module, select, packed,
                                                                      sn_obj_width(module, first_value),
                                                                      sn_obj_is_signed(module, first_value), nullptr);
            }
        }

        intersect_assignment_masks(first.assigned_masks, branches, &ProceduralValues::assigned_masks,
                                   result.assigned_masks);
        intersect_assignment_masks(first.selected_assigned_masks, branches,
                                   &ProceduralValues::selected_assigned_masks, result.selected_assigned_masks);
        return true;
    }

    sn_obj_id_t procedural_escape(const ProceduralValues& environment)
    {
        sn_obj_id_t escape = SN_INVALID_ID;
        for (sn_obj_id_t flag : {environment.return_flag, environment.break_flag, environment.continue_flag})
        {
            if (flag == SN_INVALID_ID)
                continue;
            if (escape == SN_INVALID_ID)
                escape = flag;
            else
            {
                sn_obj_id_t fanins[2] = {escape, flag};
                escape = sn_module_add_operator(module, SN_LOG_OR, 1, false, 2, fanins, nullptr);
            }
        }
        return escape;
    }

    bool lower_guarded_statement(const Statement& statement, ProceduralValues& environment)
    {
        sn_obj_id_t escape = procedural_escape(environment);
        if (escape == SN_INVALID_ID)
            return lower_statement(statement, environment);
        ProceduralValues branch = environment;
        branch.return_flag = SN_INVALID_ID;
        branch.break_flag = SN_INVALID_ID;
        branch.continue_flag = SN_INVALID_ID;
        if (!lower_statement(statement, branch))
            return false;
        sn_obj_id_t active = sn_module_add_operator(module, SN_LOG_NOT, 1, false, 1, &escape, nullptr);
        ProceduralValues merged;
        if (!merge_procedural_values(active, branch, environment, merged))
            return false;
        environment = std::move(merged);
        return true;
    }

    bool lower_statement(const Statement& statement, ProceduralValues& environment)
    {
        ProceduralWriteGuard write_guard(active_procedural_writes, environment);
        if (const auto* timed = statement.as_if<TimedStatement>())
        {
            if (lowering_initial_block)
            {
                const auto* delay = timed->timing.as_if<DelayControl>();
                auto delay_value = delay ? constant_integer(delay->expr) : std::nullopt;
                if (!delay_value || *delay_value != 0)
                {
                    std::fprintf(stderr, "sn-slang: initial blocks support only constant #0 delays\n");
                    return false;
                }
            }
            return lower_statement(timed->stmt, environment);
        }
        if (const auto* block = statement.as_if<BlockStatement>())
            return lower_statement(block->body, environment);
        if (const auto* list = statement.as_if<StatementList>())
        {
            for (const Statement* child : list->list)
                if (!lower_guarded_statement(*child, environment))
                    return false;
            return true;
        }
        if (statement.as_if<EmptyStatement>())
            return true;
        if (statement.as_if<WaitStatement>())
        {
            report_timing_error(statement.sourceRange.start(),
                                "wait statements have no current synthesizable SN representation");
            return false;
        }
        if (statement.as_if<ImmediateAssertionStatement>() || statement.as_if<ConcurrentAssertionStatement>())
            return handle_formal_statement(statement);
        if (const auto* return_statement = statement.as_if<ReturnStatement>())
        {
            if (!active_return_value || !return_statement->expr)
            {
                std::fprintf(stderr, "sn-slang: void or out-of-function return statements are unsupported\n");
                return false;
            }
            active_procedural_values = &environment;
            sn_obj_id_t value = lower_expression(*return_statement->expr);
            active_procedural_values = nullptr;
            if (value == SN_INVALID_ID)
                return false;
            environment.values[active_return_value] = value;
            const uint32_t one_word = 1;
            environment.return_flag = sn_module_add_const(module, 1, false, &one_word, nullptr);
            return true;
        }
        if (statement.as_if<BreakStatement>())
        {
            if (!procedural_loop_depth)
                return false;
            const uint32_t one_word = 1;
            environment.break_flag = sn_module_add_const(module, 1, false, &one_word, nullptr);
            return true;
        }
        if (statement.as_if<ContinueStatement>())
        {
            if (!procedural_loop_depth)
                return false;
            const uint32_t one_word = 1;
            environment.continue_flag = sn_module_add_const(module, 1, false, &one_word, nullptr);
            return true;
        }
        if (const auto* declaration = statement.as_if<VariableDeclStatement>())
        {
            const Expression* initializer = declaration->symbol.getInitializer();
            if (!initializer)
                return true;
            active_procedural_values = nonblocking_read_values ? nonblocking_read_values : &environment;
            sn_obj_id_t value = lower_expression(*initializer);
            active_procedural_values = nullptr;
            if (value == SN_INVALID_ID)
                return false;
            environment.values[&declaration->symbol] = value;
            return true;
        }
        if (const auto* expression_statement = statement.as_if<ExpressionStatement>())
        {
            const auto* assignment = expression_statement->expr.as_if<AssignmentExpression>();
            const auto* unary = expression_statement->expr.as_if<UnaryExpression>();
            const auto* call = expression_statement->expr.as_if<CallExpression>();
            if (is_ignored_system_task(call))
                return true;
            bool decrement = false;
            if (unary && increment_or_decrement(unary->op, decrement))
            {
                active_procedural_values = &environment;
                sn_obj_id_t old_value = lower_expression(unary->operand());
                active_procedural_values = nullptr;
                uint32_t bits = width(*unary->operand().type);
                if (old_value == SN_INVALID_ID || !bits)
                    return false;
                std::vector<uint32_t> words(sn_const_word_count(bits));
                words[0] = 1;
                sn_obj_id_t one = sn_module_add_const(module, bits, false, words.data(), nullptr);
                sn_obj_id_t fanins[2] = {old_value, one};
                sn_obj_id_t updated = sn_module_add_operator(module, decrement ? SN_SUB : SN_ADD, bits,
                                                              unary->operand().type->isSigned(), 2, fanins, nullptr);
                return assign_procedural_lvalue(unary->operand(), updated, environment);
            }
            if (call && !call->isSystemCall())
            {
                const SubroutineSymbol* subroutine = std::get<0>(call->subroutine);
                auto formals = subroutine->getArguments();
                std::string_view name = call->getSubroutineName();
                if ((subroutine->subroutineKind != SubroutineKind::Task &&
                     subroutine->subroutineKind != SubroutineKind::Function) ||
                    formals.size() != call->arguments().size() || !active_subroutines.emplace(subroutine).second)
                {
                    std::fprintf(stderr, "sn-slang: unsupported or recursive procedural task '%.*s'\n",
                                 int(name.size()), name.data());
                    return false;
                }
                ProceduralValues task_values = environment;
                bool arguments_ok = true;
                for (size_t i = 0; i < formals.size(); i++)
                {
                    ArgumentDirection direction = formals[i]->direction;
                    sn_obj_id_t argument = SN_INVALID_ID;
                    if (direction == ArgumentDirection::In || direction == ArgumentDirection::InOut ||
                        direction == ArgumentDirection::Ref)
                    {
                        active_procedural_values = nonblocking_read_values ? nonblocking_read_values : &environment;
                        argument = lower_expression(*call->arguments()[i]);
                        active_procedural_values = nullptr;
                    }
                    else if (direction == ArgumentDirection::Out)
                    {
                        uint32_t bits = width(formals[i]->getType());
                        std::vector<uint32_t> words(sn_const_word_count(bits));
                        argument = sn_module_add_const(module, bits, formals[i]->getType().isSigned(), words.data(),
                                                       nullptr);
                    }
                    if (argument == SN_INVALID_ID)
                    {
                        arguments_ok = false;
                        break;
                    }
                    task_values.values[formals[i]] = argument;
                }
                const ProceduralValues* saved_values = active_procedural_values;
                const ProceduralValues* saved_nonblocking = nonblocking_read_values;
                const VariableSymbol* saved_return_value = active_return_value;
                nonblocking_read_values = nullptr;
                active_return_value = nullptr;
                bool lowered = arguments_ok && lower_statement(subroutine->getBody(), task_values);
                active_procedural_values = saved_values;
                nonblocking_read_values = saved_nonblocking;
                active_return_value = saved_return_value;
                active_subroutines.erase(subroutine);
                if (!lowered)
                    return false;
                for (const auto& [symbol, value] : task_values.values)
                    if (!is_automatic_value(*symbol))
                        environment.values[symbol] = value;
                for (const auto& [selected, value] : task_values.selected_values)
                    if (!is_automatic_value(*selected.symbol))
                        environment.selected_values[selected] = value;
                for (const auto& [symbol, mask] : task_values.assigned_masks)
                    if (!is_automatic_value(*symbol))
                        environment.assigned_masks[symbol] = mask;
                for (const auto& [selected, mask] : task_values.selected_assigned_masks)
                    if (!is_automatic_value(*selected.symbol))
                        environment.selected_assigned_masks[selected] = mask;
                environment.memory_writes = std::move(task_values.memory_writes);
                for (size_t i = 0; i < formals.size(); i++)
                {
                    ArgumentDirection direction = formals[i]->direction;
                    if (direction != ArgumentDirection::Out && direction != ArgumentDirection::InOut &&
                        direction != ArgumentDirection::Ref)
                        continue;
                    auto value = task_values.values.find(formals[i]);
                    const auto* assignment = call->arguments()[i]->as_if<AssignmentExpression>();
                    const Expression* lvalue = assignment && assignment->isLValueArg() ? &assignment->left()
                                                                                       : call->arguments()[i];
                    if (value == task_values.values.end() ||
                        !assign_procedural_lvalue(*lvalue, value->second, environment))
                    {
                        std::fprintf(stderr, "sn-slang: task '%.*s' output argument has an unsupported lvalue\n",
                                     int(name.size()), name.data());
                        return false;
                    }
                }
                return true;
            }
            if (!assignment)
            {
                if (call)
                    std::fprintf(stderr, "sn-slang: unsupported procedural call '%.*s'\n",
                                 int(call->getSubroutineName().size()), call->getSubroutineName().data());
                else
                    std::fprintf(stderr, "sn-slang: unsupported procedural expression statement kind %u\n",
                                 unsigned(expression_statement->expr.kind));
                return false;
            }
            active_procedural_values = assignment->isNonBlocking() ? nonblocking_read_values : &environment;
            if (!active_procedural_values)
                active_procedural_values = &environment;
            sn_obj_id_t value = assignment->isCompound() ? lower_expression(*assignment)
                                                          : lower_expression(assignment->right());
            if (auto element = memory_element(assignment->left()))
            {
                sn_obj_id_t address = lower_expression(*element->address);
                active_procedural_values = nullptr;
                if (lowering_initial_block)
                    return value != SN_INVALID_ID && address != SN_INVALID_ID;
                if (!nonblocking_read_values || value == SN_INVALID_ID || address == SN_INVALID_ID)
                {
                    std::fprintf(stderr,
                                 "sn-slang: module '%s': memory '%.*s' writes require an edge-triggered process\n",
                                 sn_name_get(&module->design->names, module->name),
                                 int(element->memory->name.size()), element->memory->name.data());
                    return false;
                }
                address = normalize_memory_address(memories.at(element->memory), address);
                if (address == SN_INVALID_ID)
                    return false;
                const uint32_t one = 1;
                sn_obj_id_t enable = sn_module_add_const(module, 1, false, &one, nullptr);
                environment.memory_writes.push_back({element->memory, address, value, enable, SN_INVALID_ID});
                return true;
            }
            bool assigned = value != SN_INVALID_ID &&
                            assign_procedural_lvalue(assignment->left(), value, environment);
            active_procedural_values = nullptr;
            if (!assigned)
            {
                SourceLocation location = source_manager->getFullyOriginalLoc(assignment->sourceRange.start());
                std::string path = location ? source_manager->getFullPath(location.buffer()).string() : "<unknown>";
                size_t line = location ? source_manager->getLineNumber(location) : 0;
                std::fprintf(stderr,
                             "sn-slang: %s:%zu: procedural assignment failed (lvalue kind=%u, width=%u, "
                             "value_width=%u)\n",
                             path.c_str(), line, unsigned(assignment->left().kind), width(*assignment->left().type),
                             value == SN_INVALID_ID ? 0 : sn_obj_width(module, value));
            }
            return assigned;
        }
        if (const auto* conditional = statement.as_if<ConditionalStatement>())
        {
            if (conditional->conditions.size() != 1 || conditional->conditions[0].pattern)
            {
                std::fprintf(stderr, "sn-slang: patterned or multi-condition procedural if is unsupported\n");
                return false;
            }
            if (auto truth = constant_truth(*conditional->conditions[0].expr))
                return *truth ? lower_statement(conditional->ifTrue, environment)
                              : !conditional->ifFalse || lower_statement(*conditional->ifFalse, environment);
            active_procedural_values = nonblocking_read_values ? nonblocking_read_values : &environment;
            sn_obj_id_t condition = lower_expression(*conditional->conditions[0].expr);
            active_procedural_values = nullptr;
            if (condition == SN_INVALID_ID)
                return false;
            // Procedural truth is true when any condition bit is one. Reduce wide legacy-Verilog conditions first;
            // case equality then makes an all-X/Z condition select the false branch instead of propagating X.
            condition = normalize_condition(condition);
            const uint32_t one_word = 1;
            sn_obj_id_t one = sn_module_add_const(module, 1, false, &one_word, nullptr);
            sn_obj_id_t truth_fanins[2] = {condition, one};
            condition = sn_module_add_operator(module, SN_CASE_EQ, 1, false, 2, truth_fanins, nullptr);
            ProceduralValues when_true = environment;
            ProceduralValues when_false = environment;
            if (!lower_statement(conditional->ifTrue, when_true) ||
                (conditional->ifFalse && !lower_statement(*conditional->ifFalse, when_false)))
                return false;
            return merge_procedural_values(condition, when_true, when_false, environment);
        }
        if (const auto* case_statement = statement.as_if<CaseStatement>())
        {
            if (case_statement->items.empty())
            {
                std::fprintf(stderr, "sn-slang: unsupported procedural case condition\n");
                return false;
            }
            if (case_statement->condition == CaseStatementCondition::Normal)
            {
                auto constant_case = procedural_constant_integer(case_statement->expr, environment);
                if (constant_case)
                {
                    const Statement* matching_statement = nullptr;
                    bool all_items_constant = true;
                    for (const CaseStatement::ItemGroup& item : case_statement->items)
                        for (const Expression* item_expression : item.expressions)
                        {
                            auto constant_item = constant_integer(*item_expression);
                            if (!constant_item)
                            {
                                all_items_constant = false;
                                break;
                            }
                            if (!matching_statement && *constant_item == *constant_case)
                                matching_statement = item.stmt;
                        }
                    if (all_items_constant)
                    {
                        if (matching_statement)
                            return lower_statement(*matching_statement, environment);
                        return !case_statement->defaultCase ||
                               lower_statement(*case_statement->defaultCase, environment);
                    }
                }
            }
            active_procedural_values = nonblocking_read_values ? nonblocking_read_values : &environment;
            sn_obj_id_t case_value = lower_expression(case_statement->expr);
            active_procedural_values = nullptr;
            if (case_value == SN_INVALID_ID)
                return false;

            ProceduralValues result = environment;
            size_t item_count = case_statement->items.size();
            bool exhaustive_two_state = false;
            bool mutually_exclusive = false;
            uint32_t case_bits = width(*case_statement->expr.type);
            const Expression* binary_case_expression = &case_statement->expr;
            while (const auto* conversion = binary_case_expression->as_if<ConversionExpression>())
            {
                if (!conversion->isImplicit())
                    break;
                binary_case_expression = &conversion->operand();
            }
            uint32_t binary_case_bits = width(*binary_case_expression->type);
            std::vector<size_t> dense_groups;
            struct CaseCube
            {
                std::vector<int8_t> bits;
                size_t group;
            };
            std::vector<CaseCube> cubes;
            if (case_bits)
            {
                bool all_constant = true;
                for (size_t group = 0; group < case_statement->items.size(); group++)
                {
                    const CaseStatement::ItemGroup& item = case_statement->items[group];
                    for (const Expression* item_expression : item.expressions)
                    {
                        EvalContext context(*body->parentInstance);
                        ConstantValue constant = item_expression->eval(context);
                        if (!constant || !constant.isInteger() || constant.integer().getBitWidth() != case_bits)
                        {
                            all_constant = false;
                            break;
                        }
                        CaseCube cube;
                        cube.group = group;
                        cube.bits.reserve(case_bits);
                        for (uint32_t bit = 0; bit < case_bits; bit++)
                        {
                            logic_t value = constant.integer()[int32_t(bit)];
                            bool wildcard = case_statement->condition == CaseStatementCondition::WildcardXOrZ &&
                                            value.isUnknown();
                            if (case_statement->condition == CaseStatementCondition::WildcardJustZ &&
                                value.value == logic_t::z.value)
                                wildcard = true;
                            if (value.isUnknown() && !wildcard)
                            {
                                all_constant = false;
                                break;
                            }
                            cube.bits.push_back(wildcard ? -1 : int8_t(value.value != 0));
                        }
                        if (!all_constant)
                            break;
                        cubes.push_back(std::move(cube));
                    }
                    if (!all_constant)
                        break;
                }
                // Constant case cubes need only a pairwise overlap test; no SAT solver is necessary. Keep casez
                // priority lowering until its distinction between X and Z wildcards is represented explicitly.
                mutually_exclusive = all_constant &&
                                     case_statement->condition != CaseStatementCondition::WildcardJustZ;
                for (size_t i = 0; mutually_exclusive && i < cubes.size(); i++)
                    for (size_t j = i + 1; mutually_exclusive && j < cubes.size(); j++)
                    {
                        if (cubes[i].group == cubes[j].group)
                            continue;
                        bool overlap = true;
                        for (uint32_t bit = 0; overlap && bit < case_bits; bit++)
                            if (cubes[i].bits[bit] >= 0 && cubes[j].bits[bit] >= 0 &&
                                cubes[i].bits[bit] != cubes[j].bits[bit])
                                overlap = false;
                        mutually_exclusive = !overlap;
                    }
                if (!case_statement->defaultCase && all_constant)
                {
                    size_t visited = 0;
                    auto covers = [&](auto&& self, const std::vector<size_t>& active, uint32_t depth) -> bool {
                        if (++visited > 1000000 || active.empty())
                            return false;
                        if (depth == case_bits)
                            return true;
                        uint32_t bit = case_bits - depth - 1;
                        for (size_t index : active)
                        {
                            bool covers_remainder = true;
                            for (uint32_t remaining_depth = depth; remaining_depth < case_bits; remaining_depth++)
                                covers_remainder = covers_remainder &&
                                                   cubes[index].bits[case_bits - remaining_depth - 1] < 0;
                            if (covers_remainder)
                                return true;
                        }
                        std::vector<size_t> zero;
                        std::vector<size_t> one;
                        zero.reserve(active.size());
                        one.reserve(active.size());
                        for (size_t index : active)
                        {
                            int8_t value = cubes[index].bits[bit];
                            if (value <= 0)
                                zero.push_back(index);
                            if (value != 0)
                                one.push_back(index);
                        }
                        return self(self, zero, depth + 1) && self(self, one, depth + 1);
                    };
                    std::vector<size_t> active(cubes.size());
                    for (size_t i = 0; i < active.size(); i++)
                        active[i] = i;
                    exhaustive_two_state = all_constant && covers(covers, active, 0);
                }
            }
            // A unique / unique0 promise does not change source-order behavior when constant items actually
            // overlap. Only use a parallel mux for dynamic items, or after the constant-cube overlap proof above.
            if ((case_statement->check == UniquePriorityCheck::Unique ||
                 case_statement->check == UniquePriorityCheck::Unique0) &&
                cubes.empty())
                mutually_exclusive = true;
            // Unsized Verilog case-item integers retain their 32-bit self-determined type in slang, even when
            // every value fits the narrower selector. Recognize a complete nonnegative table using the values
            // after their normal case comparison conversion, rather than requiring identical source widths.
            if (case_statement->condition == CaseStatementCondition::Normal && binary_case_bits &&
                binary_case_bits < 20 && !binary_case_expression->type->isSigned())
            {
                size_t value_count = size_t(1) << binary_case_bits;
                dense_groups.assign(value_count, SIZE_MAX);
                size_t filled = 0;
                for (size_t group = 0; !dense_groups.empty() && group < case_statement->items.size(); group++)
                    for (const Expression* item_expression : case_statement->items[group].expressions)
                    {
                        auto item_value = constant_integer(*item_expression);
                        if (!item_value || *item_value < 0 || uint64_t(*item_value) >= value_count)
                        {
                            dense_groups.clear();
                            break;
                        }
                        // The first matching item of a normal case wins; a later
                        // item repeating the same value is unreachable.
                        if (dense_groups[size_t(*item_value)] == SIZE_MAX)
                        {
                            dense_groups[size_t(*item_value)] = group;
                            filled++;
                        }
                    }
                // Uncovered selector values take the explicit default branch.
                // Without one an unmatched selector means holding the previous
                // value, which the latch-inference and priority paths must see
                // in their expected form. Require the table to be at least
                // half full, so a genuinely sparse case keeps its comparator
                // chain instead of paying for a mostly-default binary mux tree.
                if (!dense_groups.empty() && filled < value_count &&
                    (!case_statement->defaultCase || filled * 2 < value_count))
                    dense_groups.clear();
            }
            if (!dense_groups.empty())
            {
                std::vector<ProceduralValues> group_branches(case_statement->items.size());
                std::vector<bool> lowered(case_statement->items.size());
                ProceduralValues fallback_branch;
                bool fallback_lowered = false;
                std::vector<ProceduralValues> branches;
                branches.reserve(dense_groups.size());
                for (size_t group : dense_groups)
                {
                    if (group == SIZE_MAX)
                    {
                        if (!fallback_lowered)
                        {
                            fallback_branch = environment;
                            if (case_statement->defaultCase &&
                                !lower_statement(*case_statement->defaultCase, fallback_branch))
                                return false;
                            fallback_lowered = true;
                        }
                        branches.push_back(fallback_branch);
                        continue;
                    }
                    assert(group < case_statement->items.size());
                    if (!lowered[group])
                    {
                        group_branches[group] = environment;
                        if (!lower_statement(*case_statement->items[group].stmt, group_branches[group]))
                            return false;
                        lowered[group] = true;
                    }
                    branches.push_back(group_branches[group]);
                }
                ProceduralValues binary_result;
                active_procedural_values = nonblocking_read_values ? nonblocking_read_values : &environment;
                sn_obj_id_t binary_case_value = lower_expression(*binary_case_expression);
                active_procedural_values = nullptr;
                if (binary_case_value != SN_INVALID_ID &&
                    merge_procedural_values_bmux(binary_case_value, branches, binary_result))
                {
                    environment = std::move(binary_result);
                    return true;
                }
            }
            bool synthesis_full_case = source_range_contains(case_statement->sourceRange, "full_case");
            if (case_statement->defaultCase)
            {
                if (!lower_statement(*case_statement->defaultCase, result))
                    return false;
            }
            else if (exhaustive_two_state || synthesis_full_case)
            {
                // An exhaustive normal case is combinational in SN's two-state domain even without a default.
                // Legacy full_case directives likewise declare unmatched selector values to be synthesis don't
                // cares. Use the final item as the concrete fallback while building the mux chain.
                if (!lower_statement(*case_statement->items.back().stmt, result))
                    return false;
                item_count--;
            }
            // Without a default, no matching item performs no assignment.
            // The incoming procedural environment therefore is the fallback;
            // for sequential logic this precisely represents state holding.

            auto lower_item_condition = [&](const CaseStatement::ItemGroup& item) {
                sn_obj_id_t condition = SN_INVALID_ID;
                for (const Expression* item_expression : item.expressions)
                {
                    if (case_statement->condition == CaseStatementCondition::Inside)
                    {
                        active_procedural_values = nonblocking_read_values ? nonblocking_read_values : &environment;
                        sn_obj_id_t hit = SN_INVALID_ID;
                        if (const auto* range = item_expression->as_if<ValueRangeExpression>())
                        {
                            sn_obj_id_t lower = lower_expression(range->left());
                            sn_obj_id_t upper = lower_expression(range->right());
                            if (range->rangeKind != ValueRangeKind::Simple || lower == SN_INVALID_ID ||
                                upper == SN_INVALID_ID)
                            {
                                active_procedural_values = nullptr;
                                return SN_INVALID_ID;
                            }
                            sn_obj_id_t lower_fanins[2] = {case_value, lower};
                            sn_obj_id_t upper_fanins[2] = {case_value, upper};
                            sn_obj_id_t at_least = sn_module_add_operator(
                                module, SN_GE, 1, range->left().type->isSigned(), 2, lower_fanins, nullptr);
                            sn_obj_id_t at_most = sn_module_add_operator(
                                module, SN_LE, 1, range->right().type->isSigned(), 2, upper_fanins, nullptr);
                            sn_obj_id_t range_fanins[2] = {at_least, at_most};
                            hit = sn_module_add_operator(module, SN_LOG_AND, 1, false, 2, range_fanins, nullptr);
                        }
                        else
                        {
                            sn_obj_id_t candidate = lower_expression(*item_expression);
                            if (candidate != SN_INVALID_ID)
                                hit = lower_equality(BinaryOperator::WildcardEquality, case_value, candidate);
                        }
                        active_procedural_values = nullptr;
                        if (hit == SN_INVALID_ID)
                            return SN_INVALID_ID;
                        if (condition == SN_INVALID_ID)
                            condition = hit;
                        else
                        {
                            sn_obj_id_t or_fanins[2] = {condition, hit};
                            condition = sn_module_add_operator(module, SN_LOG_OR, 1, false, 2, or_fanins, nullptr);
                        }
                        continue;
                    }
                    active_procedural_values = nonblocking_read_values ? nonblocking_read_values : &environment;
                    sn_obj_id_t item_value = lower_expression(*item_expression);
                    active_procedural_values = nullptr;
                    if (item_value == SN_INVALID_ID)
                        return SN_INVALID_ID;
                    // A plain case compares with case equality, so an item holding X or Z bits can never match
                    // a two-state selector; casez likewise never matches an item X bit (only Z is its wildcard).
                    {
                        auto valid = constant_valid_masks.find(item_value);
                        auto z = constant_z_masks.find(item_value);
                        bool has_unknown = valid != constant_valid_masks.end();
                        bool unmatchable = false;
                        if (case_statement->condition == CaseStatementCondition::Normal)
                            unmatchable = has_unknown;
                        else if (case_statement->condition == CaseStatementCondition::WildcardJustZ && has_unknown)
                            unmatchable = !constant_is_all_ones_where(valid->second, z);
                        if (unmatchable)
                        {
                            uint32_t zero = 0;
                            sn_obj_id_t never = sn_module_add_const(module, 1, false, &zero, nullptr);
                            if (condition == SN_INVALID_ID)
                                condition = never;
                            continue;
                        }
                    }
                    sn_obj_id_t compared_value = case_value;
                    sn_obj_id_t compared_item = item_value;
                    sn_obj_id_t item_has_x = SN_INVALID_ID;
                    if (case_statement->condition == CaseStatementCondition::WildcardXOrZ ||
                        case_statement->condition == CaseStatementCondition::WildcardJustZ)
                    {
                        sn_obj_id_t mask = SN_INVALID_ID;
                        auto valid = constant_valid_masks.find(item_value);
                        auto z = constant_z_masks.find(item_value);
                        if (case_statement->condition == CaseStatementCondition::WildcardXOrZ &&
                            valid != constant_valid_masks.end())
                            mask = valid->second;
                        else if (case_statement->condition == CaseStatementCondition::WildcardJustZ &&
                                 z != constant_z_masks.end())
                        {
                            mask = sn_module_add_operator(module, SN_BIT_NOT, sn_obj_width(module, item_value),
                                                          false, 1, &z->second, nullptr);
                            if (valid != constant_valid_masks.end())
                            {
                                sn_obj_id_t invalid = sn_module_add_operator(
                                    module, SN_BIT_NOT, sn_obj_width(module, item_value), false, 1,
                                    &valid->second, nullptr);
                                sn_obj_id_t x_fanins[2] = {invalid, mask};
                                sn_obj_id_t x_bits = sn_module_add_operator(
                                    module, SN_BIT_AND, sn_obj_width(module, item_value), false, 2,
                                    x_fanins, nullptr);
                                item_has_x = sn_module_add_operator(module, SN_REDUCE_OR, 1, false, 1,
                                                                   &x_bits, nullptr);
                            }
                        }
                        if (mask != SN_INVALID_ID)
                        {
                            sn_obj_id_t value_fanins[2] = {case_value, mask};
                            compared_value = sn_module_add_operator(module, SN_BIT_AND,
                                                                    sn_obj_width(module, case_value), false, 2,
                                                                    value_fanins, nullptr);
                            sn_obj_id_t item_fanins[2] = {item_value, mask};
                            compared_item = sn_module_add_operator(module, SN_BIT_AND,
                                                                   sn_obj_width(module, item_value), false, 2,
                                                                   item_fanins, nullptr);
                        }
                    }
                    sn_obj_id_t equality_fanins[2] = {compared_value, compared_item};
                    sn_obj_id_t equality =
                        sn_module_add_operator(module, SN_CASE_EQ, 1, false, 2, equality_fanins, nullptr);
                    if (item_has_x != SN_INVALID_ID)
                    {
                        sn_obj_id_t no_x = sn_module_add_operator(module, SN_LOG_NOT, 1, false, 1,
                                                                 &item_has_x, nullptr);
                        sn_obj_id_t valid_fanins[2] = {equality, no_x};
                        equality = sn_module_add_operator(module, SN_LOG_AND, 1, false, 2,
                                                          valid_fanins, nullptr);
                    }
                    if (condition == SN_INVALID_ID)
                        condition = equality;
                    else
                    {
                        sn_obj_id_t or_fanins[2] = {condition, equality};
                        condition = sn_module_add_operator(module, SN_LOG_OR, 1, false, 2, or_fanins, nullptr);
                    }
                }
                return condition;
            };

            if (mutually_exclusive && item_count > 1)
            {
                std::vector<sn_obj_id_t> conditions;
                std::vector<ProceduralValues> branches;
                conditions.reserve(item_count);
                branches.reserve(item_count);
                bool valid = true;
                for (size_t index = 0; valid && index < item_count; index++)
                {
                    sn_obj_id_t condition = lower_item_condition(case_statement->items[index]);
                    if (condition == SN_INVALID_ID)
                    {
                        valid = false;
                        break;
                    }
                    ProceduralValues branch = environment;
                    if (!lower_statement(*case_statement->items[index].stmt, branch))
                        return false;
                    conditions.push_back(condition);
                    branches.push_back(std::move(branch));
                }
                ProceduralValues parallel_result;
                if (valid && merge_procedural_values_pmux(conditions, branches, result, parallel_result))
                {
                    environment = std::move(parallel_result);
                    return true;
                }
            }

            for (size_t reverse = item_count; reverse > 0; reverse--)
            {
                const CaseStatement::ItemGroup& item = case_statement->items[reverse - 1];
                sn_obj_id_t condition = lower_item_condition(item);
                if (condition == SN_INVALID_ID)
                {
                    std::fprintf(stderr, "sn-slang: procedural case item has no expressions\n");
                    return false;
                }
                ProceduralValues branch = environment;
                if (!lower_statement(*item.stmt, branch))
                    return false;
                ProceduralValues merged;
                if (!merge_procedural_values(condition, branch, result, merged))
                    return false;
                result = std::move(merged);
            }
            environment = std::move(result);
            return true;
        }
        if (const auto* loop = statement.as_if<ForLoopStatement>())
        {
            if (!loop->stopExpr)
            {
                std::fprintf(stderr, "sn-slang: procedural for loops require a stop condition\n");
                return false;
            }
            EvalContext local_loop_context(*body->parentInstance);
            EvalContext& loop_context = active_constant_context ? *active_constant_context : local_loop_context;
            EvalFrameGuard loop_frame(loop_context);
            LoopConstantGuard loop_constants(active_loop_constants);
            for (const VariableSymbol* variable : loop->loopVars)
            {
                const Expression* initializer = variable->getInitializer();
                ConstantValue initial = initializer ? initializer->eval(loop_context) : ConstantValue{};
                if (!initial && initializer)
                    if (auto integer = constant_integer(*initializer))
                        initial = ConstantValue(SVInt(width(variable->getType()), uint64_t(*integer),
                                                      variable->getType().isSigned()));
                ConstantValue* local = initial ? loop_context.createLocal(variable, std::move(initial)) : nullptr;
                if (!local)
                {
                    std::fprintf(stderr, "sn-slang: procedural for-loop variable requires a constant initializer\n");
                    return false;
                }
                loop_constants.bind(variable, local);
            }
            for (const Expression* initializer : loop->initializers)
            {
                const auto* assignment = initializer->as_if<AssignmentExpression>();
                const auto* named = assignment ? assignment->left().as_if<NamedValueExpression>() : nullptr;
                ConstantValue* local = named ? loop_context.createLocal(&named->symbol) : nullptr;
                if (!local || !initializer->eval(loop_context))
                {
                    std::fprintf(stderr, "sn-slang: unsupported procedural for-loop initializer\n");
                    return false;
                }
                loop_constants.bind(&named->symbol, local);
            }

            uint32_t dynamic_iteration_limit = 0;
            ProceduralLoopGuard flow_guard(environment, procedural_loop_depth);
            const auto* stop_binary = loop->stopExpr->as_if<BinaryExpression>();
            auto strip_conversions = [](const Expression* expression) {
                while (const auto* conversion = expression->as_if<ConversionExpression>())
                    expression = &conversion->operand();
                return expression;
            };
            if (loop->initializers.size() == 1 && loop->steps.size() == 1 && stop_binary &&
                (stop_binary->op == BinaryOperator::LessThan || stop_binary->op == BinaryOperator::LessThanEqual))
            {
                const auto* initializer = loop->initializers[0]->as_if<AssignmentExpression>();
                const auto* loop_variable = initializer ? initializer->left().as_if<NamedValueExpression>() : nullptr;
                const auto* step = loop->steps[0]->as_if<AssignmentExpression>();
                const auto* step_variable = step ? step->left().as_if<NamedValueExpression>() : nullptr;
                const auto* step_add = step ? strip_conversions(&step->right())->as_if<BinaryExpression>() : nullptr;
                const auto* step_add_variable =
                    step_add ? strip_conversions(&step_add->left())->as_if<NamedValueExpression>() : nullptr;
                const Expression* stop_left = strip_conversions(&stop_binary->left());
                const Expression* stop_right = strip_conversions(&stop_binary->right());
                const auto* stop_variable = stop_left->as_if<NamedValueExpression>();
                uint32_t limit_bits = width(*stop_right->type);
                if (loop_variable && stop_variable && &loop_variable->symbol == &stop_variable->symbol &&
                    step_variable && &step_variable->symbol == &loop_variable->symbol && step_add &&
                    step_add->op == BinaryOperator::Add && step_add_variable &&
                    &step_add_variable->symbol == &loop_variable->symbol &&
                    constant_integer(initializer->right()) == 0 &&
                    constant_integer(step_add->right()) == 1 && !stop_right->type->isSigned() && limit_bits < 20)
                    dynamic_iteration_limit = 1u << limit_bits;
            }
            if (!dynamic_iteration_limit && loop->steps.size() == 1 && stop_binary &&
                (stop_binary->op == BinaryOperator::LessThan || stop_binary->op == BinaryOperator::LessThanEqual))
            {
                const ValueSymbol* loop_variable = nullptr;
                bool starts_at_zero = false;
                if (loop->loopVars.size() == 1)
                {
                    loop_variable = loop->loopVars[0];
                    starts_at_zero = loop_variable->getInitializer() &&
                                     constant_integer(*loop_variable->getInitializer()) == 0;
                }
                else if (loop->initializers.size() == 1)
                {
                    const auto* initializer = loop->initializers[0]->as_if<AssignmentExpression>();
                    const auto* named = initializer ? initializer->left().as_if<NamedValueExpression>() : nullptr;
                    loop_variable = named ? &named->symbol : nullptr;
                    starts_at_zero = initializer && constant_integer(initializer->right()) == 0;
                }
                const auto* stop_variable = strip_conversions(&stop_binary->left())->as_if<NamedValueExpression>();
                const Expression* step_expression = strip_conversions(loop->steps[0]);
                const auto* step_unary = step_expression->as_if<UnaryExpression>();
                const auto* step_operand =
                    step_unary ? strip_conversions(&step_unary->operand())->as_if<NamedValueExpression>() : nullptr;
                bool increments = step_unary &&
                                  (step_unary->op == UnaryOperator::Preincrement ||
                                   step_unary->op == UnaryOperator::Postincrement) &&
                                  step_operand && loop_variable && &step_operand->symbol == loop_variable;
                if (starts_at_zero && stop_variable && &stop_variable->symbol == loop_variable &&
                    (increments || loop->loopVars.size() == 1))
                {
                    FixedLoopIndexBound bound(loop_variable);
                    loop->body.visit(bound);
                    dynamic_iteration_limit = bound.limit;
                }
            }
            if (!dynamic_iteration_limit)
                dynamic_iteration_limit = countdown_loop_limit(*loop).value_or(0);

            for (uint32_t iteration = 0; iteration < 1000000; iteration++)
            {
                ConstantValue stop = loop->stopExpr->eval(loop_context);
                if (stop && stop.isInteger() && !stop.integer().hasUnknown())
                {
                    if (!stop.isTrue())
                        return true;
                    EvalContext* previous_constant_context = active_constant_context;
                    active_constant_context = &loop_context;
                    bool body_ok = lower_guarded_statement(loop->body, environment);
                    active_constant_context = previous_constant_context;
                    if (!body_ok)
                        return false;
                    flow_guard.next_iteration();
                }
                else
                {
                    if (!dynamic_iteration_limit || iteration >= dynamic_iteration_limit)
                    {
                        std::fprintf(stderr, "sn-slang: procedural for-loop condition has no supported bound\n");
                        return false;
                    }
                    EvalContext* previous_constant_context = active_constant_context;
                    active_constant_context = &loop_context;
                    active_procedural_values = nonblocking_read_values ? nonblocking_read_values : &environment;
                    sn_obj_id_t condition = lower_expression(*loop->stopExpr);
                    active_procedural_values = nullptr;
                    if (condition == SN_INVALID_ID)
                    {
                        active_constant_context = previous_constant_context;
                        return false;
                    }
                    condition = normalize_condition(condition);
                    ProceduralValues branch = environment;
                    bool body_ok = lower_guarded_statement(loop->body, branch);
                    active_constant_context = previous_constant_context;
                    if (!body_ok)
                        return false;
                    branch.continue_flag = SN_INVALID_ID;
                    ProceduralValues merged;
                    if (!merge_procedural_values(condition, branch, environment, merged))
                        return false;
                    environment = std::move(merged);
                }
                for (const Expression* step : loop->steps)
                {
                    ConstantValue result = step->eval(loop_context);
                    if (!result)
                    {
                        std::fprintf(stderr, "sn-slang: unsupported procedural for-loop step\n");
                        return false;
                    }
                }
                if (dynamic_iteration_limit && iteration + 1 == dynamic_iteration_limit)
                    return true;
            }
            std::fprintf(stderr, "sn-slang: procedural for loop exceeds the unrolling limit\n");
            return false;
        }
        if (const auto* loop = statement.as_if<WhileLoopStatement>())
        {
            struct ContinueFinder : ASTVisitor<ContinueFinder, VisitFlags::Statements>
            {
                bool found = false;

                void handle(const ContinueStatement&)
                {
                    found = true;
                }
            };
            auto strip = [](const Expression* expression) {
                while (const auto* conversion = expression->as_if<ConversionExpression>())
                    expression = &conversion->operand();
                return expression;
            };
            const auto* condition = strip(&loop->cond)->as_if<BinaryExpression>();
            const auto* counter = condition ? strip(&condition->left())->as_if<NamedValueExpression>() : nullptr;
            const Statement* trailing = &loop->body;
            while (const auto* block = trailing->as_if<BlockStatement>())
                trailing = &block->body;
            if (const auto* list = trailing->as_if<StatementList>())
                trailing = list->list.empty() ? nullptr : list->list.back();
            const auto* expression_statement = trailing ? trailing->as_if<ExpressionStatement>() : nullptr;
            const Expression* step = expression_statement ? strip(&expression_statement->expr) : nullptr;
            bool increments = false;
            if (const auto* unary = step ? step->as_if<UnaryExpression>() : nullptr)
            {
                const auto* operand = strip(&unary->operand())->as_if<NamedValueExpression>();
                increments = operand && counter && &operand->symbol == &counter->symbol &&
                             (unary->op == UnaryOperator::Preincrement ||
                              unary->op == UnaryOperator::Postincrement);
            }
            if (const auto* assignment = step ? step->as_if<AssignmentExpression>() : nullptr)
            {
                const auto* lhs = strip(&assignment->left())->as_if<NamedValueExpression>();
                const auto* add = strip(&assignment->right())->as_if<BinaryExpression>();
                const auto* add_lhs = add ? strip(&add->left())->as_if<NamedValueExpression>() : nullptr;
                increments = lhs && counter && &lhs->symbol == &counter->symbol && add &&
                             add->op == BinaryOperator::Add && add_lhs &&
                             &add_lhs->symbol == &counter->symbol && constant_integer(add->right()) == 1;
            }
            auto initial = counter ? procedural_constant_integer(*counter, environment) : std::nullopt;
            uint32_t iteration_limit = 0;
            bool zero_iterations = false;
            if (condition && condition->op == BinaryOperator::LessThan && counter && increments && initial == 0)
            {
                auto fixed = procedural_constant_integer(condition->right(), environment);
                if (fixed && *fixed == 0)
                    zero_iterations = true;
                else if (fixed && *fixed > 0 && *fixed <= 1000000)
                    iteration_limit = uint32_t(*fixed);
                else
                {
                    uint32_t counter_bits = width(counter->symbol.getType());
                    uint32_t limit_bits = width(*condition->right().type);
                    if (!condition->right().type->isSigned() && limit_bits < 20 && counter_bits >= limit_bits)
                        iteration_limit = 1u << limit_bits;
                }
            }
            if (zero_iterations)
                return true;
            ContinueFinder continue_finder;
            loop->body.visit(continue_finder);
            if (continue_finder.found)
            {
                report_timing_error(loop->body.sourceRange.start(),
                                    "bounded while loop contains a continue that can bypass its increment");
                return false;
            }
            if (!iteration_limit)
            {
                report_timing_error(loop->sourceRange.start(),
                                    "while loop has no provable finite incrementing bound");
                return false;
            }

            ProceduralLoopGuard flow_guard(environment, procedural_loop_depth);
            for (uint32_t iteration = 0; iteration < iteration_limit; iteration++)
            {
                auto known = procedural_constant_integer(loop->cond, environment);
                if (known && !*known)
                    return true;
                if (known)
                {
                    if (!lower_guarded_statement(loop->body, environment))
                        return false;
                    flow_guard.next_iteration();
                    continue;
                }

                active_procedural_values = nonblocking_read_values ? nonblocking_read_values : &environment;
                sn_obj_id_t condition_value = lower_expression(loop->cond);
                active_procedural_values = nullptr;
                if (condition_value == SN_INVALID_ID)
                    return false;
                condition_value = normalize_condition(condition_value);
                const uint32_t one_word = 1;
                sn_obj_id_t one = sn_module_add_const(module, 1, false, &one_word, nullptr);
                sn_obj_id_t truth_fanins[2] = {condition_value, one};
                condition_value =
                    sn_module_add_operator(module, SN_CASE_EQ, 1, false, 2, truth_fanins, nullptr);
                ProceduralValues branch = environment;
                if (!lower_guarded_statement(loop->body, branch))
                    return false;
                branch.continue_flag = SN_INVALID_ID;
                ProceduralValues merged;
                if (!merge_procedural_values(condition_value, branch, environment, merged))
                    return false;
                environment = std::move(merged);
                flow_guard.next_iteration();
            }
            return true;
        }
        if (const auto* repeat = statement.as_if<RepeatLoopStatement>())
        {
            auto count = constant_integer(repeat->count);
            if (!count || *count < 0 || *count > 1000000)
            {
                std::fprintf(stderr, "sn-slang: repeat-loop count must be a bounded nonnegative constant\n");
                return false;
            }
            ProceduralLoopGuard flow_guard(environment, procedural_loop_depth);
            for (int64_t iteration = 0; iteration < *count; iteration++)
            {
                if (!lower_guarded_statement(repeat->body, environment))
                    return false;
                flow_guard.next_iteration();
            }
            return true;
        }
        if (const auto* loop = statement.as_if<ForeachLoopStatement>())
        {
            ProceduralLoopGuard flow_guard(environment, procedural_loop_depth);
            return unroll_foreach(*loop, [&] {
                bool lowered = lower_guarded_statement(loop->body, environment);
                flow_guard.next_iteration();
                return lowered;
            });
        }
        std::fprintf(stderr, "sn-slang: unsupported procedural statement kind %u\n", unsigned(statement.kind));
        return false;
    }

    bool lower_procedural_blocks()
    {
        const ProceduralBlockSymbol* last_combinational = nullptr;
        for (const ProceduralBlockSymbol* procedural : procedural_blocks)
            if (!is_sequential_block(*procedural) && procedural->procedureKind != ProceduralBlockKind::Initial &&
                procedural->procedureKind != ProceduralBlockKind::Final)
                last_combinational = procedural;

        // A packed aggregate is often driven field-by-field by several always_comb blocks. Slang has already
        // checked procedural driver legality. Lower all combinational processes into one aggregate environment so
        // disjoint field assignments share one placeholder and are connected only after the last process.
        ProceduralValues environment;
        std::unordered_map<const ValueSymbol*, size_t> declaration_order;
        collect_declaration_order(*body, declaration_order);
        auto declaration_rank = [&](const ValueSymbol* symbol) {
            auto it = declaration_order.find(symbol);
            return it == declaration_order.end() ? SIZE_MAX : it->second;
        };
        for (const auto& [symbol, placeholder] : combinational_placeholders)
            environment.values.emplace(symbol, placeholder);
        for (const auto& [selected, placeholder] : combinational_selected_placeholders)
            if (!combinational_placeholders.contains(selected.symbol))
                environment.selected_values.emplace(selected, placeholder);

        for (const ProceduralBlockSymbol* procedural : procedural_blocks)
        {
            if (is_sequential_block(*procedural))
                continue;
            if (procedural->procedureKind == ProceduralBlockKind::Initial ||
                procedural->procedureKind == ProceduralBlockKind::Final)
                continue;
            if (procedural->procedureKind != ProceduralBlockKind::Always &&
                procedural->procedureKind != ProceduralBlockKind::AlwaysComb &&
                procedural->procedureKind != ProceduralBlockKind::AlwaysLatch)
            {
                std::fprintf(stderr, "sn-slang: only combinational always blocks are currently supported\n");
                return false;
            }
            std::vector<const ValueSymbol*> targets;
            std::vector<SelectedValue> selected_targets;
            std::unordered_set<const ValueSymbol*> seen;
            std::unordered_set<SelectedValue, SelectedValueHash> selected_seen;
            if (std::getenv("SN_PROGRESS"))
            {
                SourceLocation location = source_manager->getFullyOriginalLoc(procedural->location);
                std::fprintf(stderr,
                             "sn-slang: procedural block line %zu begins (values=%zu selected=%zu objects=%zu)\n",
                             location ? source_manager->getLineNumber(location) : 0, environment.values.size(),
                             environment.selected_values.size(), module->obj_types.size);
            }
            if (!collect_sequential_targets(procedural->getBody(), targets, selected_targets, seen, selected_seen,
                                            false))
                return false;
            if (std::getenv("SN_PROGRESS"))
                std::fprintf(stderr, "sn-slang: procedural targets collected (values=%zu selected=%zu)\n",
                             targets.size(), selected_targets.size());
            if (!lower_statement(procedural->getBody(), environment))
                return false;
            if (std::getenv("SN_PROGRESS"))
                std::fprintf(stderr,
                             "sn-slang: procedural block lowered (values=%zu selected=%zu objects=%zu)\n",
                             environment.values.size(), environment.selected_values.size(), module->obj_types.size);
            if (procedural != last_combinational)
                continue;
            auto connect_value = [&](sn_obj_id_t placeholder, sn_obj_id_t value, uint32_t bits,
                                     bool is_signed, bool fully_assigned,
                                     const std::vector<PartialDriver>* external_drivers,
                                     const ValueSymbol& target, int64_t index = 0, int64_t bit = -1) -> bool {
                // The procedural graph is a DAG apart from its unresolved placeholder. Cache whether each object
                // reaches that placeholder. Re-running a complete DFS at every node made this substitution
                // quadratic on large case statements (and caused allocator growth into many GiB on Ara's SIMD
                // ALU despite its pre-substitution graph containing only about 12K objects).
                std::vector<uint8_t> dependency(module->obj_types.size);
                auto depends_on = [&](auto&& self, sn_obj_id_t object) -> bool {
                    if (object == placeholder)
                        return true;
                    if (object == SN_INVALID_ID)
                        return false;
                    if (object >= dependency.size())
                        dependency.resize(size_t(object) + 1);
                    if (dependency[object])
                        return dependency[object] == 3;
                    dependency[object] = 1; // Visiting; an edge back here is not itself a path to placeholder.
                    bool depends = false;
                    for (uint32_t i = 0; !depends && i < sn_obj_fanin_count(module, object); i++)
                        depends = self(self, sn_obj_fanin(module, object, i));
                    dependency[object] = depends ? 3 : 2;
                    return depends;
                };
                if (fully_assigned || (external_drivers && !external_drivers->empty()))
                {
                    sn_obj_id_t replacement = SN_INVALID_ID;
                    if (external_drivers && !external_drivers->empty())
                        replacement = materialize_partial_drivers(bits, is_signed, *external_drivers);
                    else
                    {
                        std::vector<uint32_t> zero_words(sn_const_word_count(bits));
                        replacement = sn_module_add_const(module, bits, is_signed, zero_words.data(), nullptr);
                    }
                    std::unordered_map<sn_obj_id_t, sn_obj_id_t> replacements;
                    replacements.emplace(placeholder, replacement);
                    auto substitute = [&](auto&& self, sn_obj_id_t object) -> sn_obj_id_t {
                        auto replacement = replacements.find(object);
                        if (replacement != replacements.end())
                            return replacement->second;
                        if (!depends_on(depends_on, object))
                            return object;
                        sn_obj_type_t type = sn_obj_type(module, object);
                        uint32_t fanin_count = sn_obj_fanin_count(module, object);
                        std::vector<sn_obj_id_t> fanins(fanin_count);
                        for (uint32_t i = 0; i < fanin_count; i++)
                        {
                            fanins[i] = self(self, sn_obj_fanin(module, object, i));
                            if (fanins[i] == SN_INVALID_ID)
                                return SN_INVALID_ID;
                        }
                        sn_obj_id_t result = SN_INVALID_ID;
                        if (type == SN_SLICE)
                        {
                            sn_slice_info_t info = sn_obj_slice_info(module, object);
                            result = sn_module_add_slice(module, fanins[0], info.left_index, info.right_index,
                                                         nullptr);
                        }
                        else if (type == SN_REPLICATE)
                            result = sn_module_add_repeat(module, fanins[0], sn_obj_repeat_count(module, object),
                                                          nullptr);
                        else if (sn_obj_type_is_operator(type))
                            result = sn_module_add_operator(module, type, sn_obj_width(module, object),
                                                            sn_obj_is_signed(module, object), fanin_count,
                                                            fanins.data(), nullptr);
                        replacements.emplace(object, result);
                        return result;
                    };
                    value = substitute(substitute, value);
                    if (value == SN_INVALID_ID)
                    {
                        std::fprintf(stderr, "sn-slang: cannot resolve the base of a procedural value\n");
                        return false;
                    }
                }
                if (!depends_on(depends_on, value))
                {
                    sn_obj_connect(module, placeholder, 0, value);
                    return true;
                }

                // Copy the pool-backed name before any new object can intern
                // names. The placeholder stays a wire; state gets its source
                // identity rather than an object-order-dependent anonymous ID.
                std::string name(sn_obj_name(module, placeholder));
                if (!register_name(target, name))
                    return false;
                sn_obj_pair_t latch = sn_module_add_reg_pair(module, bits, is_signed, name.c_str(), nullptr,
                                                              SN_INVALID_ID);
                add_metadata(latch.out, target);
                latch_declarations.emplace(latch.out, SelectedValue{&target, index, bit});
                sn_reg_set_flags(module, latch.out, SN_REG_LATCH);
                uint32_t zero_word = 0;
                uint32_t one_word = 1;
                std::vector<uint32_t> zero_words(sn_const_word_count(bits));
                sn_obj_id_t zero_data = sn_module_add_const(module, bits, is_signed, zero_words.data(), nullptr);
                sn_obj_id_t zero_enable = sn_module_add_const(module, 1, false, &zero_word, nullptr);
                sn_obj_id_t one_enable = sn_module_add_const(module, 1, false, &one_word, nullptr);
                auto separate_hold = [&](auto&& self, sn_obj_id_t object,
                                         bool branch_value) -> std::pair<sn_obj_id_t, sn_obj_id_t> {
                    if (object == placeholder)
                        return {zero_data, zero_enable};
                    if (!depends_on(depends_on, object))
                        return {object, one_enable};
                    if (sn_obj_type(module, object) == SN_MUX)
                    {
                        sn_obj_id_t select = sn_obj_fanin(module, object, SN_MUX_SELECT);
                        auto selected = self(self, sn_obj_fanin(module, object, SN_MUX_SELECTED), true);
                        auto default_value = self(self, sn_obj_fanin(module, object, SN_MUX_DEFAULT), true);
                        if (selected.first == SN_INVALID_ID || default_value.first == SN_INVALID_ID)
                            return {SN_INVALID_ID, SN_INVALID_ID};
                        return {sn_module_add_mux(module, select, selected.first, default_value.first, nullptr),
                                sn_module_add_mux(module, select, selected.second, default_value.second, nullptr)};
                    }
                    if (sn_obj_type(module, object) == SN_BMUX)
                    {
                        sn_obj_id_t select = sn_obj_fanin(module, object, SN_BMUX_SELECT);
                        sn_obj_id_t packed = sn_obj_fanin(module, object, SN_BMUX_ALTERNATIVES);
                        uint32_t select_width = sn_obj_width(module, select);
                        if (select_width >= 31)
                            return {SN_INVALID_ID, SN_INVALID_ID};
                        uint32_t count = 1u << select_width;
                        if (uint64_t(sn_obj_width(module, packed)) != uint64_t(count) * bits)
                            return {SN_INVALID_ID, SN_INVALID_ID};
                        std::vector<sn_obj_id_t> data_values, enable_values;
                        data_values.reserve(count);
                        enable_values.reserve(count);
                        for (uint32_t i = 0; i < count; i++)
                        {
                            sn_obj_id_t alternative_object;
                            if (sn_obj_type(module, packed) == SN_CONCAT &&
                                sn_obj_fanin_count(module, packed) == count)
                                alternative_object = sn_obj_fanin(module, packed, i);
                            else
                            {
                                uint32_t low = i * bits;
                                alternative_object =
                                    sn_module_add_slice(module, packed, int32_t(low + bits - 1), int32_t(low), nullptr);
                            }
                            auto alternative = self(self, alternative_object, true);
                            if (alternative.first == SN_INVALID_ID)
                                return {SN_INVALID_ID, SN_INVALID_ID};
                            data_values.push_back(alternative.first);
                            enable_values.push_back(alternative.second);
                        }
                        sn_obj_id_t data_packed = sn_module_add_concat(module, count, data_values.data(), nullptr);
                        sn_obj_id_t enable_packed = sn_module_add_concat(module, count, enable_values.data(), nullptr);
                        return {sn_module_add_bmux(module, select, data_packed, bits, is_signed, nullptr),
                                sn_module_add_bmux(module, select, enable_packed, 1, false, nullptr)};
                    }
                    if (sn_obj_type(module, object) == SN_PMUX)
                    {
                        sn_obj_id_t select = sn_obj_fanin(module, object, SN_PMUX_SELECT);
                        sn_obj_id_t packed = sn_obj_fanin(module, object, SN_PMUX_ALTERNATIVES);
                        uint32_t count = sn_obj_width(module, select);
                        if (uint64_t(sn_obj_width(module, packed)) != uint64_t(count) * bits)
                            return {SN_INVALID_ID, SN_INVALID_ID};
                        std::vector<sn_obj_id_t> data_values, enable_values;
                        data_values.reserve(count);
                        enable_values.reserve(count);
                        for (uint32_t i = 0; i < count; i++)
                        {
                            sn_obj_id_t alternative_object;
                            if (sn_obj_type(module, packed) == SN_CONCAT &&
                                sn_obj_fanin_count(module, packed) == count)
                                alternative_object = sn_obj_fanin(module, packed, i);
                            else
                            {
                                uint32_t low = i * bits;
                                alternative_object =
                                    sn_module_add_slice(module, packed, int32_t(low + bits - 1), int32_t(low), nullptr);
                            }
                            auto alternative = self(self, alternative_object, true);
                            if (alternative.first == SN_INVALID_ID)
                                return {SN_INVALID_ID, SN_INVALID_ID};
                            data_values.push_back(alternative.first);
                            enable_values.push_back(alternative.second);
                        }
                        auto default_value = self(self, sn_obj_fanin(module, object, SN_PMUX_DEFAULT), true);
                        if (default_value.first == SN_INVALID_ID)
                            return {SN_INVALID_ID, SN_INVALID_ID};
                        sn_obj_id_t data_packed =
                            sn_module_add_concat(module, count, data_values.data(), nullptr);
                        sn_obj_id_t enable_packed =
                            sn_module_add_concat(module, count, enable_values.data(), nullptr);
                        return {sn_module_add_pmux(module, select, data_packed, default_value.first, nullptr),
                                sn_module_add_pmux(module, select, enable_packed, default_value.second, nullptr)};
                    }
                    if (branch_value)
                        return {object, one_enable};
                    return {SN_INVALID_ID, SN_INVALID_ID};
                };
                auto [data, enable] = separate_hold(separate_hold, value, false);
                if (data == SN_INVALID_ID)
                {
                    std::fprintf(stderr, "sn-slang: inferred latch does not have a simple enable condition\n");
                    return false;
                }
                sn_obj_connect(module, placeholder, 0, latch.out);
                sn_obj_connect(module, latch.in, 0, data);
                sn_reg_set_fanin(module, latch.out, SN_REG_ENABLE, enable);
                return true;
            };
            auto drivers_overlap_mask = [](const std::vector<PartialDriver>& drivers,
                                           const std::vector<uint32_t>* mask) {
                if (!mask)
                    return false;
                for (const PartialDriver& driver : drivers)
                    for (uint32_t bit = driver.offset; bit < driver.offset + driver.width; bit++)
                        if (((*mask)[bit / 32] >> (bit % 32)) & 1u)
                            return true;
                return false;
            };
            std::vector<const ValueSymbol*> ordered_targets;
            for (const auto& entry : environment.values)
                if (!is_automatic_value(*entry.first))
                    ordered_targets.push_back(entry.first);
            std::sort(ordered_targets.begin(), ordered_targets.end(), [&](auto* a, auto* b) {
                return declaration_rank(a) < declaration_rank(b);
            });
            for (const ValueSymbol* symbol : ordered_targets)
            {
                sn_obj_id_t value = environment.values.at(symbol);
                if (is_automatic_value(*symbol))
                    continue; // Automatic block and loop variables do not become module outputs or latches.
                auto placeholder = combinational_placeholders.find(symbol);
                if (placeholder == combinational_placeholders.end())
                {
                    std::fprintf(stderr, "sn-slang: undeclared combinational procedural target '%.*s'\n",
                                 int(symbol->name.size()), symbol->name.data());
                    return false;
                }
                uint32_t bits = width(symbol->getType());
                bool fully_assigned = assignment_mask_is_full(environment.assigned_masks, symbol, bits);
                auto external = partial_value_drivers.find(symbol);
                const std::vector<PartialDriver>* drivers =
                    external == partial_value_drivers.end() ? nullptr : &external->second;
                auto mask = environment.assigned_masks.find(symbol);
                if (drivers && drivers_overlap_mask(*drivers,
                                                    mask == environment.assigned_masks.end() ? nullptr
                                                                                             : &mask->second))
                {
                    std::fprintf(stderr, "sn-slang: procedural and continuous drivers overlap for '%.*s'\n",
                                 int(symbol->name.size()), symbol->name.data());
                    return false;
                }
                if (!connect_value(placeholder->second, value, bits, symbol->getType().isSigned(),
                                   fully_assigned, drivers, *symbol))
                {
                    std::fprintf(stderr, "sn-slang: failed to connect combinational target '%.*s'\n",
                                 int(symbol->name.size()), symbol->name.data());
                    return false;
                }
            }
            std::vector<SelectedValue> ordered_selected;
            for (const auto& entry : environment.selected_values)
                ordered_selected.push_back(entry.first);
            std::sort(ordered_selected.begin(), ordered_selected.end(), [&](const auto& a, const auto& b) {
                return std::tuple(declaration_rank(a.symbol), a.index, a.bit) <
                       std::tuple(declaration_rank(b.symbol), b.index, b.bit);
            });
            for (const SelectedValue& selected : ordered_selected)
            {
                sn_obj_id_t value = environment.selected_values.at(selected);
                auto placeholder = combinational_selected_placeholders.find(selected);
                if (placeholder == combinational_selected_placeholders.end())
                {
                    std::fprintf(stderr, "sn-slang: undeclared combinational selected target '%.*s[%lld][%lld]'\n",
                                 int(selected.symbol->name.size()), selected.symbol->name.data(),
                                 static_cast<long long>(selected.index), static_cast<long long>(selected.bit));
                    return false;
                }
                uint32_t bits = selected_width(selected);
                bool fully_assigned =
                    assignment_mask_is_full(environment.selected_assigned_masks, selected, bits);
                auto external = partial_selected_drivers.find(selected);
                const std::vector<PartialDriver>* drivers =
                    external == partial_selected_drivers.end() ? nullptr : &external->second;
                auto mask = environment.selected_assigned_masks.find(selected);
                if (drivers && drivers_overlap_mask(*drivers,
                                                    mask == environment.selected_assigned_masks.end()
                                                        ? nullptr
                                                        : &mask->second))
                    return false;
                if (!connect_value(placeholder->second, value, bits, selected_is_signed(selected),
                                   fully_assigned, drivers, *selected.symbol, selected.index, selected.bit))
                {
                    std::fprintf(stderr, "sn-slang: failed to connect combinational target '%.*s[%lld][%lld]'\n",
                                 int(selected.symbol->name.size()), selected.symbol->name.data(),
                                 static_cast<long long>(selected.index), static_cast<long long>(selected.bit));
                    return false;
                }
            }
        }
        for (const auto& [symbol, placeholder] : combinational_placeholders)
        {
            if (sn_obj_fanin(module, placeholder, 0) == SN_INVALID_ID)
            {
                std::fprintf(stderr, "sn-slang: combinational variable '%.*s' was not assigned\n",
                             int(symbol->name.size()), symbol->name.data());
                return false;
            }
        }
        for (const auto& [selected, placeholder] : combinational_selected_placeholders)
        {
            if (sn_obj_fanin(module, placeholder, 0) == SN_INVALID_ID)
            {
                std::fprintf(stderr, "sn-slang: combinational selected variable '%.*s[%lld]' was not assigned\n",
                             int(selected.symbol->name.size()), selected.symbol->name.data(),
                             static_cast<long long>(selected.index));
                return false;
            }
        }
        return true;
    }

    static bool has_initial_assignment(const Statement& statement)
    {
        if (const auto* timed = statement.as_if<TimedStatement>())
            return has_initial_assignment(timed->stmt);
        if (const auto* block = statement.as_if<BlockStatement>())
            return has_initial_assignment(block->body);
        if (const auto* list = statement.as_if<StatementList>())
        {
            for (const Statement* child : list->list)
                if (has_initial_assignment(*child))
                    return true;
            return false;
        }
        if (const auto* conditional = statement.as_if<ConditionalStatement>())
            return has_initial_assignment(conditional->ifTrue) ||
                   (conditional->ifFalse && has_initial_assignment(*conditional->ifFalse));
        if (const auto* case_statement = statement.as_if<CaseStatement>())
        {
            for (const CaseStatement::ItemGroup& item : case_statement->items)
                if (has_initial_assignment(*item.stmt))
                    return true;
            return case_statement->defaultCase && has_initial_assignment(*case_statement->defaultCase);
        }
        if (const auto* loop = statement.as_if<ForLoopStatement>())
            return has_initial_assignment(loop->body);
        if (const auto* loop = statement.as_if<WhileLoopStatement>())
            return has_initial_assignment(loop->body);
        if (const auto* expression_statement = statement.as_if<ExpressionStatement>())
            return expression_statement->expr.as_if<AssignmentExpression>() != nullptr;
        if (const auto* declaration = statement.as_if<VariableDeclStatement>())
            return declaration->symbol.getInitializer() != nullptr;
        if (statement.as_if<EmptyStatement>())
            return false;
        return true; // Let lowering diagnose an unknown statement instead of silently dropping it.
    }

    bool lower_initial_blocks()
    {
        auto set_initial_value = [&](sn_obj_pair_t pair, sn_obj_id_t value) {
            sn_obj_id_t masked_value = value;
            value = materialize_constant_slice(value);
            auto mask_it = constant_valid_masks.find(masked_value);
            if (mask_it == constant_valid_masks.end())
                mask_it = constant_valid_masks.find(value);
            if (sn_obj_type(module, value) == SN_BUF && mask_it != constant_valid_masks.end())
            {
                sn_obj_id_t payload = sn_obj_fanin(module, value, 0);
                sn_obj_type_t payload_type = sn_obj_type(module, payload);
                if (payload_type == SN_CONST0 || payload_type == SN_CONST1 || payload_type == SN_CONST)
                    value = payload;
            }
            sn_obj_type_t type = sn_obj_type(module, value);
            if (type != SN_CONST0 && type != SN_CONST1 && type != SN_CONST)
            {
                std::fprintf(stderr, "sn-slang: initial register value must be constant\n");
                return false;
            }
            if (sn_obj_reg_init_data(module, pair.out) != SN_INVALID_ID)
            {
                std::fprintf(stderr, "sn-slang: register has multiple initial values\n");
                return false;
            }
            sn_obj_id_t mask = SN_INVALID_ID;
            if (mask_it != constant_valid_masks.end())
                mask = mask_it->second;
            else
            {
                uint32_t bits = sn_obj_width(module, pair.out);
                std::vector<uint32_t> mask_words(sn_const_word_count(bits), UINT32_MAX);
                if (bits & 31)
                    mask_words.back() &= (uint32_t(1) << (bits & 31)) - 1;
                mask = sn_module_add_const(module, bits, false, mask_words.data(), nullptr);
            }
            sn_reg_set_init(module, pair.out, value, mask);
            return true;
        };

        // One source variable may be represented by several selected SN registers
        // (for example, separate always blocks driving q[0] and q[15:1]). An
        // initializer belongs to the source bits, not to a particular SN owner.
        auto set_symbol_initial_value = [&](const ValueSymbol& symbol, sn_obj_id_t value,
                                             bool allow_unused) {
            auto reg = sequential_registers.find(&symbol);
            if (reg != sequential_registers.end())
                return set_initial_value(reg->second, value);
            bool found = false;
            for (const auto& [selected, pair] : sequential_selected_registers)
            {
                if (selected.symbol != &symbol)
                    continue;
                const Type& outer = symbol.getType();
                const Type* element = outer.getArrayElementType();
                uint32_t element_bits = element ? width(*element) : 1;
                uint64_t offset;
                if (outer.hasFixedRange())
                {
                    ConstantRange range = outer.getFixedRange();
                    if (selected.index < INT32_MIN || selected.index > INT32_MAX ||
                        !range.containsPoint(int32_t(selected.index)))
                        return false;
                    offset = uint64_t(range.translateIndex(int32_t(selected.index))) * element_bits;
                }
                else
                {
                    if (selected.index < 0)
                        return false;
                    offset = uint64_t(selected.index) * element_bits;
                }
                uint32_t bits = sn_obj_width(module, pair.out);
                if (selected.bit >= 0)
                {
                    if (!element || !element->hasFixedRange() || selected.bit > INT32_MAX)
                        return false;
                    ConstantRange range = element->getFixedRange();
                    if (!range.containsPoint(int32_t(selected.bit)))
                        return false;
                    offset += uint64_t(range.translateIndex(int32_t(selected.bit))) * bits;
                }
                if (!bits || offset + bits > sn_obj_width(module, value) || offset + bits > uint64_t(INT32_MAX) + 1)
                {
                    std::fprintf(stderr, "sn-slang: initialized selected-register span is out of range\n");
                    return false;
                }
                sn_obj_id_t part = sn_module_add_slice(module, value, int32_t(offset + bits - 1),
                                                       int32_t(offset), nullptr);
                // X/Z validity belongs to the original expression identity. Slice
                // it along with the data, before constant materialization loses it.
                auto mask = constant_valid_masks.find(value);
                if (mask != constant_valid_masks.end())
                {
                    sn_obj_id_t part_mask = sn_module_add_slice(module, mask->second,
                                                                int32_t(offset + bits - 1), int32_t(offset), nullptr);
                    constant_valid_masks[part] = materialize_constant_slice(part_mask);
                }
                if (!set_initial_value(pair, part))
                    return false;
                found = true;
            }
            if (!found && !allow_unused)
                std::fprintf(stderr, "sn-slang: initial assignment target '%.*s' is not a register\n",
                             int(symbol.name.size()), symbol.name.data());
            return found || allow_unused;
        };

        for (const auto& [symbol, expression] : variable_initializers)
        {
            sn_obj_id_t value = lower_expression(*expression);
            if (value == SN_INVALID_ID)
                return false;
            // Declaration initializers on unused generated variables have no synthesized effect.
            if (!set_symbol_initial_value(*symbol, value, true))
                return false;
        }

        for (const ProceduralBlockSymbol* procedural : procedural_blocks)
        {
            if (procedural->procedureKind != ProceduralBlockKind::Initial)
                continue;
            if (!has_initial_assignment(procedural->getBody()))
                continue; // Calls such as $readmemh currently produce no explicit SN state update.
            ProceduralValues initial_values;
            lowering_initial_block = true;
            bool lowered = lower_statement(procedural->getBody(), initial_values);
            lowering_initial_block = false;
            if (!lowered || !initial_values.memory_writes.empty())
                return false;

            for (const auto& [symbol, value] : initial_values.values)
            {
                if (is_automatic_value(*symbol))
                    continue; // Block-local variables in parameter-checking initial blocks are not hardware.
                if (!set_symbol_initial_value(*symbol, value, false))
                    return false;
            }
            for (const auto& [selected, value] : initial_values.selected_values)
            {
                auto reg = sequential_selected_registers.find(selected);
                if (reg == sequential_selected_registers.end())
                {
                    std::fprintf(stderr, "sn-slang: selected initial assignment target is not a register\n");
                    return false;
                }
                if (!set_initial_value(reg->second, value))
                    return false;
            }
        }
        return true;
    }

    bool lower_sequential_blocks()
    {
        auto report_block_targets = [&](const SequentialBlock& sequential, const char* phase) {
            std::fprintf(stderr, "sn-slang: failed to lower sequential %s for", phase);
            for (const ValueSymbol* target : sequential.targets)
                std::fprintf(stderr, " %.*s", int(target->name.size()), target->name.data());
            for (const SelectedValue& target : sequential.selected_targets)
                std::fprintf(stderr, " %.*s[%lld]", int(target.symbol->name.size()), target.symbol->name.data(),
                             static_cast<long long>(target.index));
            std::fprintf(stderr, "\n");
        };
        for (const SequentialBlock& sequential : sequential_blocks)
        {
            const Statement* normal_statement = sequential.synchronous_body;
            if (!normal_statement)
                return false;
            std::unordered_set<const ValueSymbol*> unreset_targets;
            std::unordered_set<SelectedValue, SelectedValueHash> unreset_selected_targets;
            if (sequential.reset != SN_INVALID_ID)
            {
                if (!sequential.asynchronous_body)
                    return false;
                ProceduralValues reset_values;
                for (const Statement* prologue : sequential.prologue)
                    if (!lower_statement(*prologue, reset_values))
                    {
                        report_block_targets(sequential, "procedural prologue");
                        return false;
                    }
                if (!lower_statement(*sequential.asynchronous_body, reset_values))
                {
                    report_block_targets(sequential, "reset branch");
                    return false;
                }
                auto configure_reset = [&](sn_obj_pair_t pair, sn_obj_id_t reset_value) {
                    reset_value = materialize_constant_slice(reset_value);
                    sn_obj_type_t reset_type = sn_obj_type(module, reset_value);
                    bool all_ones = reset_type != SN_CONST0;
                    if (reset_type != SN_CONST0 && reset_type != SN_CONST1 && reset_type != SN_CONST)
                        all_ones = false;
                    else
                        for (uint32_t bit = 0; bit < sn_obj_width(module, reset_value); bit++)
                            all_ones = all_ones && sn_const_bit(module, reset_value, bit);

                    if (reset_type == SN_CONST0)
                    {
                        sn_reg_set_fanin(module, pair.out, SN_REG_RESET, sequential.reset);
                        sn_reg_set_flags(module, pair.out, sequential.flags);
                        return true;
                    }
                    if (all_ones)
                    {
                        uint32_t flags = sequential.flags & SN_REG_CLOCK_NEGEDGE;
                        flags |= SN_REG_SET_ASYNC;
                        if (sequential.flags & SN_REG_RESET_NEGEDGE)
                            flags |= SN_REG_SET_NEGEDGE;
                        sn_reg_set_fanin(module, pair.out, SN_REG_SET, sequential.reset);
                        sn_reg_set_flags(module, pair.out, flags);
                        return true;
                    }
                    // SystemVerilog permits an asynchronous load value, for example a boot address sampled while
                    // reset is active. SN_REG_RESET_VALUE is a general data fanin and intentionally represents
                    // this case; constants zero and one above retain their more compact specialized encodings.
                    sn_reg_set_fanin(module, pair.out, SN_REG_RESET, sequential.reset);
                    sn_reg_set_fanin(module, pair.out, SN_REG_RESET_VALUE, reset_value);
                    sn_reg_set_flags(module, pair.out, sequential.flags);
                    return true;
                };
                for (const ValueSymbol* target : sequential.targets)
                {
                    auto reset_it = reset_values.values.find(target);
                    if (reset_it == reset_values.values.end())
                    {
                        unreset_targets.emplace(target);
                        continue;
                    }
                    if (!configure_reset(sequential_registers.at(target), reset_it->second))
                    {
                        std::fprintf(stderr, "sn-slang: asynchronous reset failed for register '%.*s'\n",
                                     int(target->name.size()), target->name.data());
                        return false;
                    }
                }
                for (const SelectedValue& target : sequential.selected_targets)
                {
                    auto reset_it = reset_values.selected_values.find(target);
                    if (reset_it == reset_values.selected_values.end())
                    {
                        unreset_selected_targets.emplace(target);
                        continue;
                    }
                    if (!configure_reset(sequential_selected_registers.at(target), reset_it->second))
                    {
                        std::string name = selected_name(target);
                        std::fprintf(stderr, "sn-slang: asynchronous reset failed for register '%s'\n",
                                     name.c_str());
                        return false;
                    }
                }
            }

            ProceduralValues next_values;
            for (const ValueSymbol* target : sequential.targets)
                next_values.values.emplace(target, sequential_registers.at(target).out);
            for (const SelectedValue& target : sequential.selected_targets)
                next_values.selected_values.emplace(target, sequential_selected_registers.at(target).out);
            ProceduralValues previous_values = next_values;
            bool lowered = true;
            for (const Statement* prologue : sequential.prologue)
                lowered = lowered && lower_statement(*prologue, next_values);
            // Blocking prologue assignments are visible to the following reset decision and nonblocking RHS.
            // Persistent state retains its pre-edge value because prologue locals were excluded from target discovery.
            previous_values = next_values;
            nonblocking_read_values = &previous_values;
            lowered = lowered && lower_statement(*normal_statement, next_values);
            nonblocking_read_values = nullptr;
            if (!lowered)
            {
                report_block_targets(sequential, "next-state branch");
                return false;
            }

            if (!unreset_targets.empty() || !unreset_selected_targets.empty())
            {
                sn_obj_id_t reset_inactive = sequential.reset;
                if (!(sequential.flags & SN_REG_RESET_NEGEDGE))
                    reset_inactive =
                        sn_module_add_operator(module, SN_LOG_NOT, 1, false, 1, &sequential.reset, nullptr);
                for (const ValueSymbol* target : unreset_targets)
                {
                    sn_obj_pair_t pair = sequential_registers.at(target);
                    next_values.values[target] =
                        sn_module_add_mux(module, reset_inactive, next_values.values.at(target), pair.out, nullptr);
                }
                for (const SelectedValue& target : unreset_selected_targets)
                {
                    sn_obj_pair_t pair = sequential_selected_registers.at(target);
                    next_values.selected_values[target] = sn_module_add_mux(
                        module, reset_inactive, next_values.selected_values.at(target), pair.out, nullptr);
                }
            }

            for (const ValueSymbol* target : sequential.targets)
            {
                sn_obj_pair_t pair = sequential_registers.at(target);
                sn_obj_id_t next = next_values.values.at(target);
                sn_obj_id_t data = next;
                sn_obj_id_t enable = SN_INVALID_ID;
                if (sn_obj_type(module, next) == SN_MUX)
                {
                    sn_obj_id_t selected = sn_obj_fanin(module, next, SN_MUX_SELECTED);
                    sn_obj_id_t default_value = sn_obj_fanin(module, next, SN_MUX_DEFAULT);
                    if (default_value == pair.out)
                    {
                        enable = sn_obj_fanin(module, next, SN_MUX_SELECT);
                        data = selected;
                    }
                    else if (selected == pair.out)
                    {
                        sn_obj_id_t select = sn_obj_fanin(module, next, SN_MUX_SELECT);
                        enable = sn_module_add_operator(module, SN_LOG_NOT, 1, false, 1, &select, nullptr);
                        data = default_value;
                    }
                }
                sn_obj_connect(module, pair.in, 0, data);
                if (enable != SN_INVALID_ID)
                    sn_reg_set_fanin(module, pair.out, SN_REG_ENABLE, enable);
            }
            for (const SelectedValue& target : sequential.selected_targets)
            {
                sn_obj_pair_t pair = sequential_selected_registers.at(target);
                sn_obj_id_t next = next_values.selected_values.at(target);
                sn_obj_connect(module, pair.in, 0, next);
            }
            std::vector<ProceduralValues::MemoryWrite> writes = next_values.memory_writes;
            // SN memory ports write complete words. Preserve source-order, masked-write semantics by folding an
            // earlier word into the unmodified bits of a later partial write when their enabled addresses collide,
            // then disabling the superseded earlier port for that address.
            for (size_t i = 0; i < writes.size(); i++)
                for (size_t j = i + 1; j < writes.size(); j++)
                {
                    if (writes[i].memory != writes[j].memory)
                        continue;
                    sn_obj_id_t address_fanins[2] = {writes[i].address, writes[j].address};
                    sn_obj_id_t same_address =
                        sn_module_add_operator(module, SN_EQ, 1, false, 2, address_fanins, nullptr);
                    if (writes[j].mask != SN_INVALID_ID)
                    {
                        uint32_t bits = sn_obj_width(module, writes[j].data);
                        sn_obj_id_t inverse = sn_module_add_operator(module, SN_BIT_NOT, bits, false, 1,
                                                                     &writes[j].mask, nullptr);
                        sn_obj_id_t selected_fanins[2] = {writes[j].data, writes[j].mask};
                        sn_obj_id_t selected =
                            sn_module_add_operator(module, SN_BIT_AND, bits, false, 2, selected_fanins, nullptr);
                        sn_obj_id_t preserved_fanins[2] = {writes[i].data, inverse};
                        sn_obj_id_t preserved =
                            sn_module_add_operator(module, SN_BIT_AND, bits, false, 2, preserved_fanins, nullptr);
                        sn_obj_id_t combined_fanins[2] = {selected, preserved};
                        sn_obj_id_t combined =
                            sn_module_add_operator(module, SN_BIT_OR, bits, false, 2, combined_fanins, nullptr);
                        sn_obj_id_t prior_collision_fanins[2] = {writes[i].enable, same_address};
                        sn_obj_id_t prior_collision = sn_module_add_operator(module, SN_LOG_AND, 1, false, 2,
                                                                            prior_collision_fanins, nullptr);
                        writes[j].data =
                            sn_module_add_mux(module, prior_collision, combined, writes[j].data, nullptr);
                    }
                    sn_obj_id_t collision_fanins[2] = {writes[j].enable, same_address};
                    sn_obj_id_t collision =
                        sn_module_add_operator(module, SN_LOG_AND, 1, false, 2, collision_fanins, nullptr);
                    sn_obj_id_t no_collision =
                        sn_module_add_operator(module, SN_LOG_NOT, 1, false, 1, &collision, nullptr);
                    sn_obj_id_t enable_fanins[2] = {writes[i].enable, no_collision};
                    writes[i].enable =
                        sn_module_add_operator(module, SN_LOG_AND, 1, false, 2, enable_fanins, nullptr);
                }
            for (const ProceduralValues::MemoryWrite& write : writes)
            {
                if (sequential.flags & SN_REG_CLOCK_NEGEDGE)
                {
                    sn_obj_id_t inverted_clock =
                        sn_module_add_operator(module, SN_LOG_NOT, 1, false, 1, &sequential.clock, nullptr);
                    const Memory& memory = memories.at(write.memory);
                    sn_module_add_mem_write(module, memory.pair.in, inverted_clock, write.enable, write.data,
                                            write.address, nullptr);
                    continue;
                }
                const Memory& memory = memories.at(write.memory);
                sn_module_add_mem_write(module, memory.pair.in, sequential.clock, write.enable, write.data,
                                        write.address, nullptr);
            }
        }
        return true;
    }

    bool finish_structured_assignments()
    {
        // Structured lvalues establish drivers for their individual pieces. Bind them before lowering ordinary
        // assignments so consumers do not depend on the textual order of continuous assignments.
        for (const AssignmentExpression* assignment : structured_assignments)
            if (!lower_structured_assignment(*assignment))
                return false;
        return true;
    }

    bool finish_assignments()
    {
        for (const ValueSymbol* value : assignment_order)
        {
            if (is_zero_width(value->getType()))
                continue;
            if (lower_value(*value) == SN_INVALID_ID)
                return false;
        }
        for (const SelectedValue& selected : selected_assignment_order)
        {
            if (is_zero_width(selected.symbol->getType()))
                continue;
            if (lower_selected(selected) == SN_INVALID_ID)
                return false;
        }
        return true;
    }

    bool declare_inst(const InstanceSymbol& inst)
    {
        if (!inst.isModule())
        {
            std::fprintf(stderr, "sn-slang: only module insts are currently supported\n");
            return false;
        }
        auto module_it = body_modules->find(canonical_body(inst.body));
        sn_library_t* library = module->design->library;
        uint32_t cell = sn_library_find_cell(library, std::string(inst.body.getDefinition().name).c_str());
        if (cell != SN_LIB_NONE && !sn_library_scalar_cell(library, cell))
            cell = SN_LIB_NONE; // non-scalar library macros use ordinary opaque SN instances
        if (cell == SN_LIB_NONE && module_it == body_modules->end())
        {
            std::fprintf(stderr, "sn-slang: internal error: missing child specialization\n");
            return false;
        }
        uint32_t child_output_count = cell != SN_LIB_NONE ? sn_library_port_count(library, cell, SN_LIB_OUTPUT) :
                                     sn_design_module_output_count(module->design, module_it->second);
        if (child_output_count == 0)
        {
            // An outputless instance cannot affect synthesized dataflow. Assertion monitors and ignored unknown
            // modules frequently elaborate this way; SN instances intentionally require at least one output.
            return true;
        }

        std::vector<std::pair<const Expression*, uint32_t>> outputs;
        struct InterfaceOutput
        {
            const ValueSymbol* value;
            uint32_t index;
        };
        std::vector<InterfaceOutput> interface_outputs;
        uint32_t input_count = 0;
        uint32_t output_index = 0;
        for (const Symbol* symbol : inst.body.getPortList())
        {
            const auto* port = symbol->as_if<PortSymbol>();
            if (!port)
            {
                const auto* interface_port = symbol->as_if<InterfacePortSymbol>();
                if (!interface_port)
                {
                    std::fprintf(stderr, "sn-slang: unsupported module port kind\n");
                    return false;
                }
                auto [connection, modport] = interface_port->getConnection();
                if (!for_each_interface_member(
                        *interface_port, connection, modport, [&](const ModportPortSymbol& member,
                                                                 const ValueSymbol& value, uint32_t, uint32_t) {
                        if (member.direction == ArgumentDirection::In ||
                            member.direction == ArgumentDirection::InOut)
                            input_count++;
                        if (member.direction == ArgumentDirection::Out ||
                            member.direction == ArgumentDirection::InOut)
                            interface_outputs.push_back({&value, output_index++});
                        return true;
                    }))
                    return false;
                continue;
            }
            if (is_zero_width(port->getType()))
                continue;
            const PortConnection* connection = inst.getPortConnection(*port);
            const Expression* expression = connection ? connection->getExpression() : nullptr;
            if (port->direction == ArgumentDirection::In || port->direction == ArgumentDirection::InOut)
            {
                input_count++;
            }
            if (port->direction == ArgumentDirection::Out || port->direction == ArgumentDirection::InOut)
            {
                if (expression)
                    outputs.emplace_back(expression, output_index);
                output_index++;
            }
            if (port->direction != ArgumentDirection::In && port->direction != ArgumentDirection::Out &&
                port->direction != ArgumentDirection::InOut)
            {
                std::fprintf(stderr, "sn-slang: inout and ref inst ports are unsupported\n");
                return false;
            }
        }

        std::vector<sn_obj_id_t> inputs(input_count, SN_INVALID_ID);
        // Generate scopes and instance arrays are flattened inside an SN
        // module. Keep their relative elaborated path, not just the repeated
        // leaf name (for example bank[3].ram). Ordinary direct instances keep
        // their raw identifier spelling, including escaped mapped names.
        std::string name(inst.name);
        if (&inst.getParentScope()->asSymbol() != body || !inst.arrayPath.empty())
        {
            std::string path = inst.getHierarchicalPath();
            std::string prefix = body->getHierarchicalPath() + ".";
            if (path.starts_with(prefix))
                name = path.substr(prefix.size());
        }
        sn_obj_id_t object = cell != SN_LIB_NONE ?
            sn_module_add_library_gate(module, cell, inputs.data(), name.c_str(), nullptr) :
            sn_module_add_inst(module, module_it->second, input_count, inputs.data(), name.c_str(), nullptr);
        add_metadata(object, inst);
        if (preserve_state)
        {
            bool restored_identity = false;
            for (const AttributeSymbol* attribute : body->getCompilation().getAttributes(inst))
                if (attribute->name == "sn_sec_instance")
                {
                    std::string identity;
                    if (!register_name(inst, identity, "sn_sec_instance"))
                        return false;
                    sn_module_add_attribute_record(module, object, "sn_sec_instance", identity.c_str());
                    restored_identity = true;
                    break;
            }
            // A writer-generated instance name is not a source occurrence key.
            // It is usable only when the explicit annotation above restores the key.
            if (!restored_identity && !inst.name.empty())
            {
                auto path = sec_relative_path(inst, SecPathPolicy::General);
                if (path)
                    sn_module_add_attribute_record(module, object, "sn_sec_instance", path->c_str());
            }
        }
        if (cell != SN_LIB_NONE)
            for (const AttributeSymbol* attribute : body->getCompilation().getAttributes(inst))
                if (attribute->name == "sn_state_phase")
                {
                    const auto& value = attribute->getValue();
                    auto phase = value.isInteger() ? value.integer().as<int64_t>() : std::nullopt;
                    if (!phase || (*phase != 0 && *phase != 1))
                    {
                        std::fprintf(stderr, "sn-slang: malformed sn_state_phase correspondence annotation\n");
                        return false;
                    }
                    sn_module_add_attribute_record(module, object, "sn_state_phase", *phase ? "1" : "0");
                }
                else if (attribute->name == "sn_state_name")
                {
                    std::string logical_name;
                    if (!register_name(inst, logical_name, "sn_state_name"))
                        return false;
                    sn_module_add_attribute_record(module, object, "sn_state_name", logical_name.c_str());
                }
        for (auto [expression, index] : outputs)
        {
            if (index >= child_output_count)
            {
                std::fprintf(stderr, "sn-slang: child output count does not match elaborated port list\n");
                return false;
            }
            const auto* assignment = expression->as_if<AssignmentExpression>();
            if (assignment)
            {
                // Width plus signedness changes can put more than one conversion around Slang's
                // placeholder RHS; isLValueArg() recognizes only one conversion in some Slang versions.
                const Expression* rhs = &assignment->right();
                while (const auto* conversion = rhs->as_if<ConversionExpression>())
                    rhs = &conversion->operand();
                if (rhs->as_if<EmptyArgumentExpression>())
                    expression = &assignment->left();
            }
            // A widening output connection may wrap the target in a conversion to the port width.
            // The destination is the operand; apply the actual assignment conversion to the source below.
            while (const auto* conversion = expression->as_if<ConversionExpression>())
                expression = &conversion->operand();
            // Output ports behave as assignments from the child's declared type to the connected target.
            // Slang's lvalue argument does not itself lower that conversion: resize here, before splitting
            // concatenations or selected targets. Widen using the source port's signedness.
            sn_obj_id_t value = sn_owner_output(module, object, index);
            uint32_t target_width = width(*expression->type);
            if (target_width && target_width != sn_obj_width(module, value))
                value = sn_module_add_operator(module, SN_CAST, target_width, sn_obj_is_signed(module, value),
                                                1, &value, nullptr);
            if (target_width && expression->type->isSigned() != sn_obj_is_signed(module, value))
                value = sn_module_add_operator(module, SN_CAST, target_width, expression->type->isSigned(),
                                                1, &value, nullptr);
            if (!bind_lvalue(*expression, value))
                return false;
        }
        for (const InterfaceOutput& output : interface_outputs)
        {
            if (output.index >= child_output_count)
            {
                std::fprintf(stderr, "sn-slang: child interface output count does not match elaborated port list\n");
                return false;
            }
            sn_obj_id_t fan = sn_owner_output(module, object, output.index);
            if (!bind_value_symbol(*output.value, fan))
                return false;
        }
        if (output_index != child_output_count)
        {
            std::fprintf(stderr, "sn-slang: child output count does not match elaborated port list\n");
            return false;
        }
        pending_insts.push_back({&inst, object});
        return true;
    }

    bool declare_insts(const Scope& scope)
    {
        for (const Symbol& symbol : scope.members())
        {
            if (const auto* unknown = symbol.as_if<UninstantiatedDefSymbol>())
            {
                std::string name(unknown->definitionName);
                if (warned_unknown_modules.insert(name).second)
                    std::fprintf(stderr, "sn-slang: warning: dropping unknown module '%s' in '%s': no port model. "
                                         "Supply Liberty (-L) or a Verilog stub with -B; "
                                         "use -s to reject this.\n",
                                 name.c_str(), sn_name_get(&module->design->names, module->name));
                continue;
            }
            if (const auto* inst = symbol.as_if<InstanceSymbol>())
            {
                if (inst->isInterface())
                    continue;
                if (!declare_inst(*inst))
                    return false;
                continue;
            }
            if (const auto* generate = symbol.as_if<GenerateBlockSymbol>(); generate && generate->isUninstantiated)
                continue;
            if (const Scope* child_scope = symbol.as_if<Scope>())
                if (!declare_insts(*child_scope))
                    return false;
        }
        return true;
    }

    bool has_inst_combinational_cycle() const
    {
        // State and explicit loop-breaker outputs start new combinational cones.
        struct Frame
        {
            sn_obj_id_t object;
            uint32_t next_fanin;
        };
        auto is_boundary = [&](sn_obj_id_t object) {
            sn_obj_type_t type = sn_obj_type(module, object);
            return type == SN_REG_OUT || type == SN_MEM_OUT || type == SN_LOOP_OUT;
        };

        std::vector<uint8_t> marks(module->obj_types.size, 0); // 0 = unseen, 1 = active, 2 = complete
        std::vector<Frame> stack;
        for (sn_obj_id_t root = 0; root < module->obj_types.size; root++)
        {
            if (marks[root])
                continue;
            if (is_boundary(root))
            {
                marks[root] = 2;
                continue;
            }
            marks[root] = 1;
            stack.push_back({root, 0});
            while (!stack.empty())
            {
                Frame& frame = stack.back();
                if (frame.next_fanin == sn_obj_fanin_count(module, frame.object))
                {
                    marks[frame.object] = 2;
                    stack.pop_back();
                    continue;
                }
                sn_obj_id_t fanin = sn_obj_fanin(module, frame.object, frame.next_fanin++);
                if (fanin == SN_INVALID_ID)
                    continue;
                if (marks[fanin] == 1)
                    return true;
                if (marks[fanin] == 2)
                    continue;
                if (is_boundary(fanin))
                {
                    marks[fanin] = 2;
                    continue;
                }
                marks[fanin] = 1;
                stack.push_back({fanin, 0});
            }
        }
        return false;
    }

    sn_obj_id_t cut_inst_cycle(sn_obj_id_t inst, sn_obj_id_t input, std::string_view port_name)
    {
        // Instances are atomic SN objects, so an input whose combinational cone reaches the same inst closes a cycle
        // in the parent module's object graph. Cut only that back-edge. Ordinary feed-forward inst chains must remain
        // intact; cutting every inst-to-inst dependency needlessly abstracts acyclic hierarchy during AIG blasting.
        // The pair is named after the instance input it feeds ("inst/port"), a stable identity that survives
        // flattening and reconstruction, so blasts before and after @put can match the cut by name.
        std::string loop_name;
        if (sn_obj_name_id(module, inst) != SN_INVALID_ID)
        {
            loop_name = sn_obj_name(module, inst);
            loop_name += '/';
            loop_name.append(port_name);
        }
        sn_obj_pair_t loop = sn_module_add_loop_pair(module, sn_obj_width(module, input),
                                                     sn_obj_is_signed(module, input),
                                                     loop_name.empty() ? nullptr : loop_name.c_str(), nullptr);
        sn_obj_connect(module, loop.in, 0, input);
        return loop.out;
    }

    bool break_inst_cycles()
    {
        // The previous implementation searched the transitive fanin cone independently for every instance input.
        // Generated interface arrays have hundreds of thousands of inputs with almost identical cones, making that
        // work quadratic. Instead, maintain the reverse graph and propagate reachability for small instance groups.
        // An input closes a cycle exactly when it is reachable from the instance through fanouts already installed
        // for earlier instances. Inputs of the current instance can be classified together: adding inst -> input
        // cannot create a new path from another input back to inst. Processing instances in their original order
        // therefore chooses exactly the same loop-breaker edges as the former per-input algorithm.
        if (pending_insts.empty())
            return true;
        const uint32_t object_count = module->obj_types.size;
        std::vector<uint8_t> pending_inst(object_count, 0);
        for (const PendingInstance& pending : pending_insts)
            pending_inst[pending.object] = 1;

        auto is_boundary = [&](sn_obj_id_t object) {
            sn_obj_type_t type = sn_obj_type(module, object);
            return type == SN_REG_OUT || type == SN_MEM_OUT || type == SN_LOOP_OUT;
        };
        std::vector<uint32_t> fanout_offsets(object_count + 1, 0);
        std::vector<uint32_t> indegrees(object_count, 0);
        for (sn_obj_id_t object = 0; object < object_count; object++)
        {
            if (is_boundary(object) || pending_inst[object])
                continue;
            for (uint32_t i = 0; i < sn_obj_fanin_count(module, object); i++)
            {
                sn_obj_id_t fanin = sn_obj_fanin(module, object, i);
                if (fanin != SN_INVALID_ID)
                {
                    assert(fanin < object_count);
                    fanout_offsets[fanin + 1]++;
                    indegrees[object]++;
                }
            }
        }
        for (uint32_t i = 1; i <= object_count; i++)
            fanout_offsets[i] += fanout_offsets[i - 1];
        std::vector<sn_obj_id_t> fanouts(fanout_offsets.back());
        std::vector<uint32_t> cursors = fanout_offsets;
        for (sn_obj_id_t object = 0; object < object_count; object++)
        {
            if (is_boundary(object) || pending_inst[object])
                continue;
            for (uint32_t i = 0; i < sn_obj_fanin_count(module, object); i++)
            {
                sn_obj_id_t fanin = sn_obj_fanin(module, object, i);
                if (fanin != SN_INVALID_ID)
                    fanouts[cursors[fanin]++] = object;
            }
        }

        // The graph left after removing instance-input edges is acyclic. Its topological order lets each batch of 64
        // instances propagate a word of direct dependencies through the graph with one cache-friendly pass.
        std::vector<sn_obj_id_t> topo;
        topo.reserve(object_count);
        for (sn_obj_id_t object = 0; object < object_count; object++)
            if (indegrees[object] == 0)
                topo.push_back(object);
        for (size_t head = 0; head < topo.size(); head++)
        {
            sn_obj_id_t object = topo[head];
            for (uint32_t i = fanout_offsets[object]; i < fanout_offsets[object + 1]; i++)
            {
                sn_obj_id_t fanout = fanouts[i];
                assert(indegrees[fanout] > 0);
                if (--indegrees[fanout] == 0)
                    topo.push_back(fanout);
            }
        }
        if (topo.size() != object_count)
        {
            std::fprintf(stderr, "sn-slang: combinational cycle exists independently of instance inputs\n");
            return false;
        }

        const size_t inst_count = pending_insts.size();
        const size_t word_count = (inst_count + 63) / 64;
        std::vector<uint32_t> input_offsets(inst_count + 1, 0);
        for (size_t i = 0; i < inst_count; i++)
        {
            uint64_t next = uint64_t(input_offsets[i]) + sn_obj_fanin_count(module, pending_insts[i].object);
            assert(next < UINT32_MAX);
            input_offsets[i + 1] = uint32_t(next);
        }
        const size_t input_count = input_offsets.back();
        assert(word_count == 0 || input_count <= std::numeric_limits<size_t>::max() / word_count);
        std::vector<uint64_t> direct_dependencies(input_count * word_count, 0);
        std::vector<uint64_t> masks(object_count, 0);
        for (size_t word = 0; word < word_count; word++)
        {
            std::fill(masks.begin(), masks.end(), 0);
            size_t first = word * 64;
            size_t last = std::min(first + 64, inst_count);
            for (size_t index = first; index < last; index++)
                masks[pending_insts[index].object] = UINT64_C(1) << (index - first);
            for (sn_obj_id_t object : topo)
            {
                uint64_t mask = masks[object];
                if (!mask)
                    continue;
                for (uint32_t i = fanout_offsets[object]; i < fanout_offsets[object + 1]; i++)
                    masks[fanouts[i]] |= mask;
            }
            for (size_t index = 0; index < inst_count; index++)
                for (uint32_t i = 0; i < sn_obj_fanin_count(module, pending_insts[index].object); i++)
                {
                    sn_obj_id_t input = sn_obj_fanin(module, pending_insts[index].object, i);
                    direct_dependencies[(size_t(input_offsets[index]) + i) * word_count + word] = masks[input];
                }
        }

        // Incrementally maintain the transitive closure of the much smaller instance-dependency graph. This exactly
        // reproduces the former declaration-order greedy policy without revisiting the word-level object graph.
        std::vector<uint64_t> descendants(inst_count * word_count, 0);
        std::vector<uint64_t> ancestors(inst_count * word_count, 0);
        std::vector<uint64_t> new_ancestors(word_count, 0);
        for (size_t i = 0; i < inst_count; i++)
        {
            descendants[i * word_count + i / 64] |= UINT64_C(1) << (i % 64);
            ancestors[i * word_count + i / 64] |= UINT64_C(1) << (i % 64);
        }
        auto add_dependencies = [&](size_t consumer, const uint64_t* dependencies) {
            const uint64_t* consumer_descendants = &descendants[consumer * word_count];
            for (size_t word = 0; word < word_count; word++)
                if (dependencies[word] & consumer_descendants[word])
                    return false;

            std::fill(new_ancestors.begin(), new_ancestors.end(), 0);
            for (size_t word = 0; word < word_count; word++)
            {
                uint64_t bits = dependencies[word];
                while (bits)
                {
                    unsigned bit = std::countr_zero(bits);
                    size_t producer = word * 64 + bit;
                    const uint64_t* producer_ancestors = &ancestors[producer * word_count];
                    for (size_t w = 0; w < word_count; w++)
                        new_ancestors[w] |= producer_ancestors[w];
                    bits &= bits - 1;
                }
            }
            uint64_t* consumer_ancestors = &ancestors[consumer * word_count];
            bool changes = false;
            for (size_t word = 0; word < word_count; word++)
            {
                new_ancestors[word] &= ~consumer_ancestors[word];
                changes |= new_ancestors[word] != 0;
            }
            if (!changes)
                return true;

            for (size_t word = 0; word < word_count; word++)
            {
                uint64_t bits = new_ancestors[word];
                while (bits)
                {
                    unsigned bit = std::countr_zero(bits);
                    size_t ancestor = word * 64 + bit;
                    uint64_t* ancestor_descendants = &descendants[ancestor * word_count];
                    for (size_t w = 0; w < word_count; w++)
                        ancestor_descendants[w] |= consumer_descendants[w];
                    bits &= bits - 1;
                }
                bits = consumer_descendants[word];
                while (bits)
                {
                    unsigned bit = std::countr_zero(bits);
                    size_t descendant = word * 64 + bit;
                    uint64_t* descendant_ancestors = &ancestors[descendant * word_count];
                    for (size_t w = 0; w < word_count; w++)
                        descendant_ancestors[w] |= new_ancestors[w];
                    bits &= bits - 1;
                }
            }
            return true;
        };

        for (size_t index = 0; index < inst_count; index++)
        {
            const PendingInstance& pending = pending_insts[index];
            uint32_t input_index = 0;
            auto classify_input = [&](sn_obj_id_t input, std::string_view port_name) {
                const uint64_t* dependencies =
                    &direct_dependencies[(size_t(input_offsets[index]) + input_index) * word_count];
                if (!add_dependencies(index, dependencies))
                    sn_obj_connect(module, pending.object, input_index,
                                   cut_inst_cycle(pending.object, input, port_name));
                input_index++;
            };
            for (const Symbol* symbol : pending.symbol->body.getPortList())
            {
                const auto* port = symbol->as_if<PortSymbol>();
                if (!port)
                {
                    const auto* interface_port = symbol->as_if<InterfacePortSymbol>();
                    if (!interface_port)
                        continue;
                    auto [connection, modport] = interface_port->getConnection();
                    if (!for_each_interface_member(
                            *interface_port, connection, modport,
                            [&](const ModportPortSymbol& member, const ValueSymbol&, uint32_t, uint32_t) {
                                if (member.direction != ArgumentDirection::In &&
                                    member.direction != ArgumentDirection::InOut)
                                    return true;
                                sn_obj_id_t input = sn_obj_fanin(module, pending.object, input_index);
                                classify_input(input, std::string(interface_port->name) + "." +
                                                          std::string(member.name));
                                return true;
                            }))
                        return false;
                    continue;
                }
                if ((port->direction != ArgumentDirection::In && port->direction != ArgumentDirection::InOut) ||
                    is_zero_width(port->getType()))
                    continue;
                sn_obj_id_t input = sn_obj_fanin(module, pending.object, input_index);
                classify_input(input, port->name);
            }
            assert(input_index == sn_obj_fanin_count(module, pending.object));
        }
        if (has_inst_combinational_cycle())
        {
            std::fprintf(stderr, "sn-slang: combinational cycle remains after instance loop breaking\n");
            return false;
        }
        return true;
    }

    bool connect_insts()
    {
        for (const PendingInstance& pending : pending_insts)
        {
            uint32_t input_index = 0;
            for (const Symbol* symbol : pending.symbol->body.getPortList())
            {
                const auto* port = symbol->as_if<PortSymbol>();
                if (!port)
                {
                    const auto* interface_port = symbol->as_if<InterfacePortSymbol>();
                    if (!interface_port)
                        continue;
                    auto [connection, modport] = interface_port->getConnection();
                    if (!for_each_interface_member(
                            *interface_port, connection, modport, [&](const ModportPortSymbol& member,
                                                                     const ValueSymbol& value, uint32_t,
                                                                     uint32_t) {
                            if (member.direction != ArgumentDirection::In &&
                                member.direction != ArgumentDirection::InOut)
                                return true;
                            sn_obj_id_t input = lower_value(value);
                            if (input == SN_INVALID_ID)
                                return false;
                            sn_obj_connect(module, pending.object, input_index++, input);
                            return true;
                        }))
                        return false;
                    continue;
                }
                if (port->direction != ArgumentDirection::In && port->direction != ArgumentDirection::InOut)
                    continue;
                if (is_zero_width(port->getType()))
                    continue;
                const PortConnection* connection = pending.symbol->getPortConnection(*port);
                const Expression* expression = connection ? connection->getExpression() : nullptr;
                sn_obj_id_t input = SN_INVALID_ID;
                if (expression)
                    input = lower_expression(*expression);
                else
                    input = lower_zero(port->getType());
                if (input == SN_INVALID_ID)
                    return false;
                sn_obj_connect(module, pending.object, input_index++, input);
            }
            assert(input_index == sn_obj_fanin_count(module, pending.object));
        }
        return break_inst_cycles();
    }

    bool add_outputs(const InstanceBodySymbol& body)
    {
        for (const Symbol* symbol : body.getPortList())
        {
            const auto* port = symbol->as_if<PortSymbol>();
            if (!port)
            {
                const auto* interface_port = symbol->as_if<InterfacePortSymbol>();
                if (!interface_port)
                    return false;
                auto [connection, modport] = interface_port->getConnection();
                if (!for_each_interface_member(
                        *interface_port, connection, modport, [&](const ModportPortSymbol& member,
                                                                 const ValueSymbol& value, uint32_t index,
                                                                 uint32_t count) {
                        if (member.direction != ArgumentDirection::Out &&
                            member.direction != ArgumentDirection::InOut)
                            return true;
                        sn_obj_id_t driver = lower_value(value);
                        if (driver == SN_INVALID_ID)
                            return false;
                        std::string name(interface_port->name);
                        if (count > 1)
                            name += "[" + std::to_string(index) + "]";
                        name += ".";
                        name += member.name;
                        sn_obj_id_t output = sn_module_add_po(module, width(member.getType()),
                                                              member.getType().isSigned(), name.c_str(), driver);
                        add_metadata(output, value);
                        return true;
                    }))
                    return false;
                continue;
            }
            if (is_zero_width(port->getType()))
                continue;
            if (port->direction == ArgumentDirection::In)
                continue;
            if (port->direction != ArgumentDirection::Out && port->direction != ArgumentDirection::InOut)
            {
                std::fprintf(stderr, "sn-slang: inout and ref ports are currently unsupported\n");
                return false;
            }
            const auto* value = port->internalSymbol ? port->internalSymbol->as_if<ValueSymbol>() : nullptr;
            uint32_t bits = width(port->getType());
            sn_obj_id_t driver = SN_INVALID_ID;
            if (value && port->direction == ArgumentDirection::InOut)
            {
                auto assignment = inout_assignments.find(value);
                if (assignment != inout_assignments.end())
                    driver = lower_expression(*assignment->second);
                else
                    // Preserve the output slot of every inout so subsequent
                    // inst output indices remain aligned. SN is two-state,
                    // so an undriven Z is represented by zero.
                    driver = lower_zero(port->getType());
            }
            else if (value)
                driver = lower_value(*value);
            if (!value || driver == SN_INVALID_ID || !bits)
            {
                std::fprintf(stderr, "sn-slang: module '%s': output port '%.*s' does not have a supported driver\n",
                             sn_name_get(&module->design->names, module->name), int(port->name.size()),
                             port->name.data());
                return false;
            }
            std::string name(port->name);
            sn_obj_id_t output = sn_module_add_po(module, bits, port->getType().isSigned(), name.c_str(), driver);
            add_metadata(output, *value);
        }
        return true;
    }

    // An opaque module is a library-cell boundary, not RTL to be lowered. Preserve its exact elaborated interface;
    // each output is intentionally undriven inside the black-box module and becomes an abstract input when blasted.
    bool add_blackbox_outputs(const InstanceBodySymbol& body)
    {
        struct Output
        {
            uint32_t bits;
            bool is_signed;
            std::string name;
        };
        std::vector<Output> outputs;
        for (const Symbol* symbol : body.getPortList())
        {
            const auto* port = symbol->as_if<PortSymbol>();
            if (!port)
            {
                const auto* interface_port = symbol->as_if<InterfacePortSymbol>();
                if (!interface_port)
                    return false;
                auto [connection, modport] = interface_port->getConnection();
                if (!for_each_interface_member(
                        *interface_port, connection, modport, [&](const ModportPortSymbol& member,
                                                                 const ValueSymbol&, uint32_t index,
                                                                 uint32_t count) {
                        if (member.direction != ArgumentDirection::Out &&
                            member.direction != ArgumentDirection::InOut)
                            return true;
                        std::string name(interface_port->name);
                        if (count > 1)
                            name += "[" + std::to_string(index) + "]";
                        name += ".";
                        name += member.name;
                        outputs.push_back({width(member.getType()), member.getType().isSigned(), std::move(name)});
                        return true;
                    }))
                    return false;
                continue;
            }
            if (is_zero_width(port->getType()) || port->direction == ArgumentDirection::In)
                continue;
            if (port->direction != ArgumentDirection::Out && port->direction != ArgumentDirection::InOut)
            {
                std::fprintf(stderr, "sn-slang: black-box ref ports are currently unsupported\n");
                return false;
            }
            outputs.push_back({width(port->getType()), port->getType().isSigned(), std::string(port->name)});
        }

        for (const Output& output : outputs)
            sn_module_add_blackbox_po(module, output.bits, output.is_signed, output.name.c_str());
        return true;
    }
};

static std::string_view blackbox_reason(const Compilation& compilation, const DefinitionSymbol& definition)
{
    if (definition.cellDefine)
        return "`celldefine";
    for (const AttributeSymbol* attribute : compilation.getAttributes(definition))
        if ((attribute->name == "blackbox" || attribute->name == "black_box" ||
             attribute->name == "syn_black_box") &&
            !attribute->getValue().isFalse())
            return attribute->name;
    return {};
}

static bool scope_has_synthesizable_body(const Scope& scope)
{
    for (const Symbol& symbol : scope.members())
    {
        if (symbol.as_if<ContinuousAssignSymbol>() || symbol.as_if<ProceduralBlockSymbol>() ||
            symbol.as_if<InstanceSymbol>() || symbol.as_if<PrimitiveInstanceSymbol>())
            return true;
        if (const auto* value = symbol.as_if<ValueSymbol>(); value && value->getInitializer())
            return true;
        if (const auto* generate = symbol.as_if<GenerateBlockSymbol>(); generate && generate->isUninstantiated)
            continue;
        if (const Scope* child = symbol.as_if<Scope>(); child && scope_has_synthesizable_body(*child))
            return true;
    }
    return false;
}

static std::string_view blackbox_reason(const Compilation& compilation, const InstanceBodySymbol& body,
                                        const std::unordered_set<std::string>& named_blackboxes,
                                        bool blackbox_empty_modules)
{
    std::string_view reason = blackbox_reason(compilation, body.getDefinition());
    if (!reason.empty())
        return reason;
    if (named_blackboxes.contains(std::string(body.getDefinition().name)))
        return "-B";
    if (blackbox_empty_modules && !scope_has_synthesizable_body(body))
        return "-E";
    return {};
}

static bool discover_body(const Compilation& compilation, const InstanceBodySymbol& candidate,
                          std::vector<const InstanceBodySymbol*>& postorder,
                          std::unordered_set<const InstanceBodySymbol*>& active,
                          std::unordered_set<const InstanceBodySymbol*>& complete,
                          const std::unordered_set<std::string>& named_blackboxes,
                          bool blackbox_empty_modules);

static bool discover_scope(const Compilation& compilation, const Scope& scope,
                           std::vector<const InstanceBodySymbol*>& postorder,
                           std::unordered_set<const InstanceBodySymbol*>& active,
                           std::unordered_set<const InstanceBodySymbol*>& complete,
                           const std::unordered_set<std::string>& named_blackboxes,
                           bool blackbox_empty_modules)
{
    for (const Symbol& symbol : scope.members())
    {
        if (const auto* inst = symbol.as_if<InstanceSymbol>())
        {
            if (inst->isModule() && !discover_body(compilation, inst->body, postorder, active, complete,
                                                   named_blackboxes, blackbox_empty_modules))
                return false;
            continue;
        }
        if (const auto* generate = symbol.as_if<GenerateBlockSymbol>(); generate && generate->isUninstantiated)
            continue;
        if (const Scope* child_scope = symbol.as_if<Scope>())
            if (!discover_scope(compilation, *child_scope, postorder, active, complete, named_blackboxes,
                                blackbox_empty_modules))
                return false;
    }
    return true;
}

static bool discover_body(const Compilation& compilation, const InstanceBodySymbol& candidate,
                          std::vector<const InstanceBodySymbol*>& postorder,
                          std::unordered_set<const InstanceBodySymbol*>& active,
                          std::unordered_set<const InstanceBodySymbol*>& complete,
                          const std::unordered_set<std::string>& named_blackboxes,
                          bool blackbox_empty_modules)
{
    const InstanceBodySymbol* body = canonical_body(candidate);
    if (complete.contains(body))
        return true;
    if (!active.emplace(body).second)
    {
        std::fprintf(stderr, "sn-slang: recursive module specialization cycle is unsupported\n");
        return false;
    }
    // Technology-library leaves can contain timing checks, collision behavior, and latch-based X propagation that
    // intentionally are not synthesizable RTL. Do not discover or lower anything behind their declared interface.
    if (blackbox_reason(compilation, *body, named_blackboxes, blackbox_empty_modules).empty() &&
        !discover_scope(compilation, *body, postorder, active, complete, named_blackboxes,
                        blackbox_empty_modules))
        return false;
    active.erase(body);
    complete.emplace(body);
    postorder.push_back(body);
    return true;
}

struct RepairWarnings
{
    static constexpr size_t detail_limit = 10;
    size_t missing_fanins = 0;
    size_t mux_resizes = 0;

    static const char* type_name(sn_obj_type_t type)
    {
        switch (type)
        {
        case SN_PO:       return "po";
        case SN_INST:     return "inst";
        case SN_REG_OUT:  return "reg_out";
        case SN_REG_IN:   return "reg_in";
        case SN_MEM_READ: return "mem_read";
        case SN_MEM_WRITE: return "mem_write";
        case SN_LOOP_OUT: return "loop_out";
        case SN_LOOP_IN:  return "loop_in";
        case SN_MUX:      return "mux";
        default:          return "operator";
        }
    }

    void missing_fanin(const sn_module_t* module, sn_obj_id_t object, uint32_t input, uint32_t width)
    {
        if (missing_fanins++ >= detail_limit)
            return;
        std::fprintf(stderr,
                     "sn-slang: warning: module '%s': object %u (%s, type %u) has missing fanin %u; "
                     "using a %u-bit zero\n",
                     sn_name_get(&module->design->names, module->name), object,
                     type_name(sn_obj_type(module, object)), unsigned(sn_obj_type(module, object)), input, width);
    }

    void mux_resize(const sn_module_t* module, sn_obj_id_t object, const char* branch,
                    uint32_t old_width, uint32_t new_width)
    {
        if (mux_resizes++ >= detail_limit)
            return;
        std::fprintf(stderr,
                     "sn-slang: warning: module '%s': mux object %u has a %u-bit %s branch; "
                     "inserting an explicit %u-bit cast\n",
                     sn_name_get(&module->design->names, module->name), object, old_width, branch, new_width);
    }

    void report_suppressed() const
    {
        if (missing_fanins > detail_limit)
            std::fprintf(stderr,
                         "sn-slang: warning: suppressed %zu additional missing-fanin warnings "
                         "(%zu total)\n",
                         missing_fanins - detail_limit, missing_fanins);
        if (mux_resizes > detail_limit)
            std::fprintf(stderr,
                         "sn-slang: warning: suppressed %zu additional mux-width warnings (%zu total)\n",
                         mux_resizes - detail_limit, mux_resizes);
    }
};

static sn_obj_id_t add_zero(sn_module_t* module, uint32_t width, bool is_signed)
{
    assert(width);
    std::vector<uint32_t> words(sn_const_word_count(width));
    return sn_module_add_const(module, width, is_signed, words.data(), nullptr);
}

static uint32_t missing_fanin_width(const sn_module_t* module, sn_obj_id_t object, uint32_t input)
{
    sn_obj_type_t type = sn_obj_type(module, object);
    if (type == SN_INST)
    {
        const sn_module_t* child = sn_design_get_module_const(module->design, sn_inst_module_id(module, object));
        if (input < child->type_objects[SN_PI].size)
            return sn_obj_width(child, sn_vec_at(sn_obj_id_t, &child->type_objects[SN_PI], input));
    }
    if ((type == SN_MUX && input == SN_MUX_SELECT) || type == SN_LUT || type == SN_GATE)
        return 1;
    if (type == SN_MEM_WRITE && (input == SN_MEM_WRITE_CLOCK || input == SN_MEM_WRITE_ENABLE))
        return 1;
    return sn_obj_width(module, object);
}

// Slang accepts some legacy constructs whose elaborated dead or partial paths do not carry a concrete driver. Keep
// those paths explicit in two-state SN by grounding required missing fanins. Also materialize the implicit assignment
// conversion when a procedural mux branch is narrower or wider than the mux result. This runs before topological
// cleanup, so newly inserted constants and casts are placed in dependency order by the normal reconstruction pass.
static void repair_module_connections(sn_module_t* module, RepairWarnings& warnings)
{
    size_t object_count = module->obj_types.size;
    for (sn_obj_id_t object = 0; object < object_count; object++)
    {
        sn_obj_type_t type = sn_obj_type(module, object);
        for (uint32_t input = 0; input < sn_obj_fanin_count(module, object); input++)
        {
            if (sn_obj_fanin(module, object, input) != SN_INVALID_ID ||
                sn_obj_fanin_may_be_invalid(module, type, input))
                continue;
            uint32_t width = missing_fanin_width(module, object, input);
            warnings.missing_fanin(module, object, input, width);
            sn_obj_connect(module, object, input,
                           add_zero(module, width, sn_obj_is_signed(module, object)));
        }
        if (type != SN_MUX || sn_obj_fanin_count(module, object) != SN_MUX_FANIN_COUNT)
            continue;
        uint32_t width = sn_obj_width(module, object);
        const uint32_t branch_inputs[] = {SN_MUX_SELECTED, SN_MUX_DEFAULT};
        const char* branch_names[] = {"selected", "default"};
        for (size_t branch = 0; branch < 2; branch++)
        {
            sn_obj_id_t value = sn_obj_fanin(module, object, branch_inputs[branch]);
            if (sn_obj_width(module, value) == width)
                continue;
            warnings.mux_resize(module, object, branch_names[branch], sn_obj_width(module, value), width);
            sn_obj_id_t cast = sn_module_add_operator(module, SN_CAST, width, sn_obj_is_signed(module, object),
                                                      1, &value, nullptr);
            sn_obj_connect(module, object, branch_inputs[branch], cast);
        }
    }
}

} // namespace

static sn_design_t* read_files_top(int file_count, const char* const* file_paths, const char* top_module,
                                   int define_count, const char* const* defines, int blackbox_count,
                                   const char* const* blackboxes, bool blackbox_empty_modules,
                                   bool memories_from_attributes_only, bool preserve_metadata,
                                   sn_slang_assertion_policy_t assertion_policy,
                                   sn_slang_timing_t* timing, const char* liberty_file = nullptr,
                                   int liberty_count = 0, const char* const* liberty_files = nullptr,
                                   sn_slang_unknown_module_policy_t unknown_policy = SN_SLANG_UNKNOWN_DEFAULT,
                                   const char* liberty_cache_dir = nullptr,
                                   int include_directory_count = 0, const char* const* include_directories = nullptr,
                                   int library_source_count = 0, const char* const* library_sources = nullptr,
                                   const char* port_layout_file = nullptr, bool preserve_state = false)
{
    using clock = std::chrono::steady_clock;
    if (timing)
        *timing = {};
    auto parse_start = clock::now();
    if (liberty_count < 0 || (liberty_count && !liberty_files) ||
        unknown_policy < SN_SLANG_UNKNOWN_DEFAULT || unknown_policy > SN_SLANG_UNKNOWN_WARN_DROP)
    {
        std::fprintf(stderr, "sn-slang: invalid library list or unknown-module policy\n");
        return nullptr;
    }
    std::vector<const char*> libraries;
    if (liberty_file)
        libraries.push_back(liberty_file);
    for (int index = 0; index < liberty_count; index++)
        libraries.push_back(liberty_files[index]);
    bool strict_modules = unknown_policy == SN_SLANG_UNKNOWN_ERROR ||
        (unknown_policy == SN_SLANG_UNKNOWN_DEFAULT && !libraries.empty());
    if (file_count <= 0 || !file_paths)
    {
        std::fprintf(stderr, "sn-slang: at least one source file is required\n");
        return nullptr;
    }
    if (assertion_policy < SN_SLANG_ASSERT_WARN || assertion_policy > SN_SLANG_ASSERT_ERROR)
    {
        std::fprintf(stderr, "sn-slang: invalid assertion policy value %u\n", unsigned(assertion_policy));
        return nullptr;
    }

    std::unordered_set<std::string> named_blackboxes;
    for (int i = 0; i < blackbox_count; i++)
    {
        if (!blackboxes || !blackboxes[i] || !*blackboxes[i])
        {
            std::fprintf(stderr, "sn-slang: black-box module name cannot be empty\n");
            return nullptr;
        }
        named_blackboxes.emplace(blackboxes[i]);
    }

    driver::Driver driver;
    driver.addStandardArgs();
    if (include_directory_count < 0 || (include_directory_count && !include_directories) ||
        library_source_count < 0 || (library_source_count && !library_sources))
    {
        std::fprintf(stderr, "sn-slang: invalid include-directory or library-source list\n");
        return nullptr;
    }
    for (int i = 0; i < include_directory_count; ++i)
    {
        if (!include_directories[i] || !*include_directories[i] ||
            driver.sourceManager.addUserDirectories(include_directories[i]))
        {
            std::fprintf(stderr, "sn-slang: invalid include directory\n");
            return nullptr;
        }
    }
    for (int i = 0; i < library_source_count; ++i)
    {
        if (!library_sources[i] || !*library_sources[i])
        {
            std::fprintf(stderr, "sn-slang: library source path cannot be empty\n");
            return nullptr;
        }
        driver.sourceLoader.addLibraryFiles({}, library_sources[i]);
    }
    // Large legacy Verilog designs commonly declare nets and localparams after their first textual use.
    driver.options.compilationFlags.at(CompilationFlags::AllowUseBeforeDeclare) = true;
    // Synthesis tools traditionally accept implicit conversions between integral values and enum types. The
    // pickled benchmark units retain several such constructs from production RTL.
    driver.options.compilationFlags.at(CompilationFlags::RelaxEnumConversions) = true;
    // A retained SN top has an explicit bit-level boundary. Slang's synthesized interface instances let the
    // importer expand a top-level modport into deterministic "port.member" PIs and POs using the same path as a
    // connected child interface.
    driver.options.compilationFlags.at(CompilationFlags::AllowTopLevelIfacePorts) = true;
    // Unknown modules have no reliable port boundary; permissive legacy mode warns before dropping them.
    driver.options.compilationFlags.at(CompilationFlags::IgnoreUnknownModules) = !strict_modules;
    driver.options.compilationFlags.at(CompilationFlags::DisallowRefsToUnknownInstances) = true;
    // A default time scale avoids a compilation error when concatenated pickles mix modules with and without an
    // explicit `timescale directive. Timing controls are still interpreted by the normal SN timing-pattern code.
    driver.options.timeScale = "1ns/1ns";
    driver.options.translateOffOptions.emplace_back("synopsys,translate_off,translate_on");
    driver.options.translateOffOptions.emplace_back("synthesis,translate_off,translate_on");
    // Some synthesis-oriented RTL uses this spelling around unavailable simulation-only includes, so filtering
    // must happen before parsing and elaboration.
    driver.options.translateOffOptions.emplace_back("pragma,translate_off,translate_on");
    driver.options.keywordMapping.emplace_back("...*.v", parsing::KeywordVersion::v1364_2005);
    // Legacy parameterized functions often contain out-of-range references in case branches that are unreachable
    // for a particular specialization. Commercial Verilog tools traditionally accept this synthesis idiom.
    driver.options.warningOptions.emplace_back("no-index-oob");
    driver.options.warningOptions.emplace_back("no-range-oob");
    driver.options.warningOptions.emplace_back("no-range-width-oob");
    if (top_module && *top_module)
    {
        driver.options.topModules.emplace_back(top_module);
        // Synthesis imports only the selected hierarchy. Unreferenced modules
        // may have invalid defaults intended to be overridden by other tops.
        // Referenced instances still receive full semantic checking.
        driver.options.compilationFlags[CompilationFlags::IgnoreUninstantiatedModules] = true;
    }
    for (int i = 0; i < define_count; i++)
    {
        if (!defines || !defines[i] || !*defines[i])
        {
            std::fprintf(stderr, "sn-slang: preprocessor definition cannot be empty\n");
            return nullptr;
        }
        driver.options.defines.emplace_back(defines[i]);
    }
    for (int i = 0; i < file_count; i++)
    {
        if (!file_paths[i])
        {
            std::fprintf(stderr, "sn-slang: source file path cannot be null\n");
            return nullptr;
        }
        add_source_with_legacy_parameter_compat(driver, file_paths[i]);
    }
    if (!driver.processOptions() || !driver.parseAllSources())
        return nullptr;

    sn_library_t* parsed_library = nullptr;
    if (!libraries.empty() &&
        !sn_slang_liberty::add_interfaces(driver, libraries, top_module, liberty_cache_dir, parsed_library))
        return nullptr;
    std::unique_ptr<sn_library_t, decltype(&sn_library_release)> library(parsed_library, sn_library_release);

    auto parse_end = clock::now();

    auto compilation = driver.createCompilation();
    driver.reportCompilation(*compilation, true);
    if (!driver.reportDiagnostics(true))
    {
        const auto& diagnostics = compilation->getAllDiagnostics();
        if (strict_modules && std::any_of(diagnostics.begin(), diagnostics.end(),
                [](const auto& diagnostic) { return diagnostic.code == diag::UnknownModule; }))
            std::fprintf(stderr, "sn-slang: unknown modules require another -L library or a Verilog stub with -B <module>; "
                                 "-B alone cannot supply missing port declarations.\n");
        return nullptr;
    }

    auto tops = compilation->getRoot().topInstances;
    if (tops.size() != 1 || !tops[0]->isModule())
    {
        std::fprintf(stderr, "sn-slang: exactly one top-level module is currently required\n");
        return nullptr;
    }
    std::printf("Top level design units: %.*s  Build succeeded: %d errors, %d warnings\n",
                int(tops[0]->name.size()), tops[0]->name.data(), driver.diagEngine.getNumErrors(),
                driver.diagEngine.getNumWarnings());

    auto elaborate_end = clock::now();

    const InstanceSymbol& top = *tops[0];
    std::vector<const InstanceBodySymbol*> bodies;
    std::unordered_set<const InstanceBodySymbol*> active;
    std::unordered_set<const InstanceBodySymbol*> complete;
    if (!discover_body(*compilation, top.body, bodies, active, complete, named_blackboxes,
                       blackbox_empty_modules))
        return nullptr;

    for (const InstanceBodySymbol* body : bodies)
    {
        std::string_view name = body->getDefinition().name;
        if (name.size() >= 5 && name.compare(0, 5, "__sn_") == 0)
        {
            std::fprintf(stderr,
                         "sn-slang: module name '%.*s' uses the reserved '__sn_' technology-primitive prefix\n",
                         int(name.size()), name.data());
            return nullptr;
        }
    }

    sn_design_t* design = sn_design_create();
    design->library = library.release();
    // Declaration-only slang bodies supply elaboration interfaces, but never
    // become SN modules. Instances refer directly to parser-order cell IDs.
    if (design->library)
        std::erase_if(bodies, [&](const InstanceBodySymbol* body) {
            uint32_t cell = sn_library_find_cell(design->library, std::string(body->getDefinition().name).c_str());
            return sn_library_scalar_cell(design->library, cell);
        });
    TranslateOffCache translate_off_cache(compilation->getSourceManager());
    std::unordered_map<const InstanceBodySymbol*, sn_module_id_t> body_modules;
    std::unordered_map<const DefinitionSymbol*, const InstanceBodySymbol*> definition_owners;
    RepairWarnings repair_warnings;
    ApproximationCounters approximation_counters;
    FormalStatementCounters formal_statement_counters;
    for (const InstanceBodySymbol* body : bodies)
        definition_owners.try_emplace(&body->getDefinition(), body);
    definition_owners[&top.body.getDefinition()] = canonical_body(top.body);

    std::unordered_map<std::string, uint32_t> definition_counts;
    std::unordered_set<std::string> module_names;
    for (const InstanceBodySymbol* body : bodies)
        module_names.emplace(body->getDefinition().name);
    for (const InstanceBodySymbol* body : bodies)
    {
        std::string base(body->getDefinition().name);
        bool owns_definition_name = definition_owners.at(&body->getDefinition()) == body;
        std::string name = base;
        if (!owns_definition_name)
        {
            do
                name = base + "__sn_spec_" + std::to_string(++definition_counts[base]);
            while (module_names.contains(name));
            module_names.emplace(name);
        }
        body_modules.emplace(body, sn_design_add_module(design, name.c_str()));
    }

    for (const InstanceBodySymbol* body : bodies)
    {
        sn_module_t* module = sn_design_get_module(design, body_modules.at(body));
        if (std::getenv("SN_PROGRESS"))
            std::fprintf(stderr, "sn-slang: importing module '%.*s'\n",
                         int(body->getDefinition().name.size()), body->getDefinition().name.data());
        ModuleImporter importer(module, body, &body_modules, compilation->getSourceManager(), &translate_off_cache,
                                &approximation_counters, &formal_statement_counters,
                                memories_from_attributes_only, preserve_metadata, assertion_policy);
        importer.preserve_state = preserve_state;
        importer.add_module_metadata(*body);
        auto stage_start = clock::now();
        auto report_stage = [&](const char* stage) {
            if (std::getenv("SN_PROGRESS"))
            {
                auto now = clock::now();
                std::fprintf(stderr, "sn-slang: module '%.*s' finished %s (%.6f s)\n",
                             int(body->getDefinition().name.size()), body->getDefinition().name.data(), stage,
                             std::chrono::duration<double>(now - stage_start).count());
                stage_start = now;
            }
        };
        auto stage_failed = [&](const char* stage) {
            std::fprintf(stderr, "sn-slang: module '%.*s' failed during %s\n",
                         int(body->getDefinition().name.size()), body->getDefinition().name.data(), stage);
            sn_design_destroy(design);
            return nullptr;
        };
        if (!importer.add_inputs(*body))
            return stage_failed("input creation");
        report_stage("input creation");
        std::string_view opaque_reason =
            blackbox_reason(*compilation, *body, named_blackboxes, blackbox_empty_modules);
        if (!opaque_reason.empty())
        {
            sn_module_set_blackbox(module, true);
            if (!importer.add_blackbox_outputs(*body))
                return stage_failed("black-box output creation");
            std::fprintf(stderr,
                         "sn-slang: treating module '%.*s' marked by %.*s as an opaque technology primitive\n",
                         int(body->getDefinition().name.size()), body->getDefinition().name.data(),
                         int(opaque_reason.size()), opaque_reason.data());
            if (!sn_module_is_topo(module))
                return stage_failed("black-box topological validation");
            continue;
        }
        if (!importer.collect_port_initializers(*body))
            return stage_failed("port-initializer collection");
        if (!importer.collect_assignments(*body))
            return stage_failed("assignment collection");
        report_stage("assignment collection");
        if (!importer.prepare_memories())
            return stage_failed("memory preparation");
        if (!importer.load_memory_initializers())
            return stage_failed("memory initialization");
        if (!importer.declare_insts(*body))
            return stage_failed("inst declaration");
        report_stage("inst declaration");
        if (!importer.prepare_combinational_blocks())
            return stage_failed("combinational preparation");
        if (!importer.prepare_sequential_blocks())
            return stage_failed("sequential preparation");
        if (!importer.finish_structured_assignments())
            return stage_failed("structured assignment lowering");
        if (!importer.lower_procedural_blocks())
            return stage_failed("procedural lowering");
        report_stage("procedural lowering");
        if (!importer.finish_assignments())
            return stage_failed("continuous assignment lowering");
        if (!importer.connect_insts())
            return stage_failed("inst connection");
        report_stage("inst connection");
        if (!importer.lower_sequential_blocks())
            return stage_failed("sequential lowering");
        if (!importer.lower_initial_blocks())
            return stage_failed("initial-block lowering");
        if (!importer.add_outputs(*body))
            return stage_failed("output creation");
        report_stage("output creation");
        importer.order_state_declarations();
        repair_module_connections(module, repair_warnings);
        if (preserve_state)
            sn_design_reorder_module_topo(design, body_modules.at(body));
        else
            sn_design_cleanup_module_topo(design, body_modules.at(body));
        report_stage("topological cleanup");
        if (!sn_module_is_topo(sn_design_get_module_const(design, body_modules.at(body))))
        {
            std::fprintf(stderr, "sn-slang: module '%.*s' could not be topologically ordered\n",
                         int(body->getDefinition().name.size()), body->getDefinition().name.data());
            sn_design_destroy(design);
            return nullptr;
        }
    }

    repair_warnings.report_suppressed();
    approximation_counters.report();
    formal_statement_counters.report(assertion_policy);

    if (!sn_design_is_topo(design))
    {
        std::fprintf(stderr, "sn-slang: imported design is not topologically ordered\n");
        sn_design_destroy(design);
        return nullptr;
    }
    if (!sn_design_check(design, stderr, false))
    {
        std::fprintf(stderr, "sn-slang: imported design failed SN consistency checking\n");
        sn_design_destroy(design);
        return nullptr;
    }
    if (port_layout_file)
    {
        // Inspect types only after building/checking SN. Reporting must not
        // affect allocation order while pointer-keyed importer maps are live.
        try
        {
            if (!sn_slang_ports::write(port_layout_file, sn_slang_ports::layout(top.body)))
                throw std::runtime_error("cannot create new port layout");
        }
        catch (const std::runtime_error& error)
        {
            std::fprintf(stderr, "sn-slang: %s '%s'\n", error.what(), port_layout_file);
            sn_design_destroy(design);
            return nullptr;
        }
        catch (...)
        {
            sn_design_destroy(design);
            throw;
        }
    }
    auto import_end = clock::now();
    if (timing)
    {
        timing->parse_seconds = std::chrono::duration<double>(parse_end - parse_start).count();
        timing->elaborate_seconds = std::chrono::duration<double>(elaborate_end - parse_end).count();
        timing->import_seconds = std::chrono::duration<double>(import_end - elaborate_end).count();
    }
    return design;
}

extern "C" sn_design_t* sn_slang_read_files_top(int file_count, const char* const* file_paths, const char* top_module)
{
    return read_files_top(file_count, file_paths, top_module, 0, nullptr, 0, nullptr, false, false, false,
                          SN_SLANG_ASSERT_WARN, nullptr);
}

extern "C" sn_design_t* sn_slang_read_files_top_timed(int file_count, const char* const* file_paths,
                                                       const char* top_module, sn_slang_timing_t* timing)
{
    return read_files_top(file_count, file_paths, top_module, 0, nullptr, 0, nullptr, false, false, false,
                          SN_SLANG_ASSERT_WARN, timing);
}

extern "C" sn_design_t* sn_slang_read_files(int file_count, const char* const* file_paths)
{
    return sn_slang_read_files_top(file_count, file_paths, nullptr);
}

extern "C" bool sn_slang_write_binary_files_top_timed(int file_count, const char* const* file_paths,
                                                        const char* top_module, const char* output_path,
                                                        sn_slang_timing_t* timing)
{
    return sn_slang_write_binary_files_top_defines_timed(file_count, file_paths, top_module, 0, nullptr,
                                                          output_path, timing);
}

extern "C" bool sn_slang_write_binary_files_top_defines_timed(int file_count, const char* const* file_paths,
                                                                const char* top_module, int define_count,
                                                                const char* const* defines,
                                                                const char* output_path,
                                                                sn_slang_timing_t* timing)
{
    sn_slang_options_t options = {};
    options.define_count = define_count;
    options.defines = defines;
    return sn_slang_write_binary_files_top_options_timed(file_count, file_paths, top_module, &options,
                                                          output_path, timing);
}

extern "C" sn_design_t* sn_slang_read_files_top_options_timed(int file_count, const char* const* file_paths,
                                                                const char* top_module,
                                                                const sn_slang_options_t* options,
                                                                sn_slang_timing_t* timing)
{
    const sn_slang_options_t empty = {};
    options = options ? options : &empty;
    return read_files_top(file_count, file_paths, top_module, options->define_count, options->defines,
                          options->blackbox_count, options->blackboxes, options->blackbox_empty_modules,
                          options->memories_from_attributes_only, options->preserve_metadata,
                          options->assertion_policy, timing, options->liberty_file,
                          options->liberty_count, options->liberty_files, options->unknown_module_policy,
                          options->liberty_cache_dir, options->include_directory_count, options->include_directories,
                          options->library_source_count, options->library_sources, options->port_layout_file,
                          options->preserve_state);
}

extern "C" bool sn_slang_write_binary_files_top_options_timed(int file_count, const char* const* file_paths,
                                                                const char* top_module,
                                                                const sn_slang_options_t* options,
                                                                const char* output_path,
                                                                sn_slang_timing_t* timing)
{
    assert(output_path);
    if (options && options->port_layout_file)
    {
        std::error_code first_error, second_error;
        auto output = std::filesystem::weakly_canonical(output_path, first_error);
        auto layout = std::filesystem::weakly_canonical(options->port_layout_file, second_error);
        if (first_error || second_error || output == layout)
        {
            std::fprintf(stderr, "sn-slang: SN output and port layout need distinct valid paths\n");
            return false;
        }
    }
    sn_design_t* design =
        sn_slang_read_files_top_options_timed(file_count, file_paths, top_module, options, timing);
    if (!design)
        return false;
    bool success = sn_design_write_binary_file(design, output_path);
    sn_design_destroy(design);
    if (!success)
    {
        std::remove(output_path);
        std::fprintf(stderr, "sn-slang: cannot finish writing output file '%s'\n", output_path);
    }
    return success;
}
