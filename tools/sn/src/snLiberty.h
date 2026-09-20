/**CFile****************************************************************

  FileName    [snLiberty.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Slang-to-SN RTL frontend.]

  Synopsis    [Liberty-backed declaration interfaces for Slang elaboration.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snLiberty.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#pragma once

#include "snLibrary.h"
#include "slang/driver/Driver.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"
#include <memory>
#include <map>
#include <set>
#include <unordered_set>

// Deliberately interface-only: no Liberty expressions are lowered here.
namespace sn_slang_liberty
{
using namespace slang;

inline bool error(const std::string& message)
{
    std::fprintf(stderr, "sn-slang: Liberty: %s\n", message.c_str());
    return false;
}

// Always escape, including keywords. Reject whitespace / control characters
// which cannot occur inside a Verilog escaped identifier.
inline std::string identifier(const std::string& name)
{
    if (name.empty())
        return {};
    for (unsigned char c : name)
        if (c <= 32 || c >= 127)
            return {};
    return "\\" + name + " ";
}

struct Scan : syntax::SyntaxVisitor<Scan>
{
    std::set<std::string> definitions;
    std::vector<const syntax::HierarchyInstantiationSyntax*> instances;
    void handle(const syntax::ModuleDeclarationSyntax& node)
    {
        definitions.emplace(node.header->name.valueText());
        visitDefault(node);
    }
    void handle(const syntax::HierarchyInstantiationSyntax& node)
    {
        instances.push_back(&node);
        visitDefault(node);
    }
};

// Loads one library argument: a binary model file as is; a text file either
// from a matching cached binary (same source size and hash) or by parsing,
// in which case the parsed model is written to the cache when one is given.
// Cache problems are reported but never fatal: the text is still available.
inline sn_lib_t* load_library(const char* path, const char* cache_dir)
{
    if (sn_lib_is_binary_file(path))
        return sn_lib_load_binary(path);
    std::string cached;
    if (cache_dir && *cache_dir)
    {
        const char* base = std::strrchr(path, '/');
        cached = std::string(cache_dir) + "/" + (base ? base + 1 : path) + ".snlib";
        uint64_t source_size = 0, source_hash = 0, cached_size = 0, cached_hash = 0;
        bool functional_only = false;
        if (FILE* in = std::fopen(cached.c_str(), "rb"))
        {
            bool identified = sn_lib_binary_identity(in, &cached_size, &cached_hash, &functional_only);
            std::fclose(in);
            if (identified && !functional_only && sn_lib_source_identity(path, &source_size, &source_hash) &&
                source_size == cached_size && source_hash == cached_hash)
            {
                sn_lib_t* model = sn_lib_load_binary(cached.c_str());
                if (sn_lib_ok(model))
                    return model;
                std::fprintf(stderr, "sn-slang: Liberty: ignoring unreadable cache %s\n", cached.c_str());
                sn_lib_destroy(model);
            }
        }
    }
    sn_lib_t* model = sn_lib_load(path);
    if (sn_lib_ok(model) && !cached.empty() && !sn_lib_write_binary_file(model, cached.c_str(), nullptr))
        std::fprintf(stderr, "sn-slang: Liberty: cannot write cache %s\n", cached.c_str());
    return model;
}

inline bool add_interfaces(driver::Driver& driver, const std::vector<const char*>& paths, const char* top,
                           const char* cache_dir, sn_library_t*& library)
{
    if (!top || !*top)
        return error("an explicit -M top is required with -L");
    std::unique_ptr<sn_library_t, decltype(&sn_library_release)> owner(nullptr, sn_library_release);
    for (const char* path : paths)
    {
        if (!path || !*path)
            return error("empty library path");
        std::unique_ptr<sn_lib_t, decltype(&sn_lib_destroy)> model(load_library(path, cache_dir), sn_lib_destroy);
        if (!sn_lib_ok(model.get()))
            return error(model && model->error ? model->error
                                               : "cannot load library (allocation or read failure)");
        for (uint32_t warning = 0; warning < model->warnings_count; ++warning)
            std::fprintf(stderr, "sn-slang: Liberty warning: %s\n", model->warnings[warning]);
        std::set<std::string> names;
        for (uint32_t cell = 0; cell < model->cells_count; ++cell)
        {
            std::string name(sn_lib_name(model.get(), model->cells[cell].name));
            if (!names.insert(name).second || sn_library_find_cell(owner.get(), name.c_str()) != SN_LIB_NONE)
                return error("duplicate cell definition: " + name);
        }
        auto* addition = sn_library_create(model.release());
        if (!addition)
            return error("cannot allocate shared library");
        if (!owner)
            owner.reset(addition);
        else if (!sn_library_append(owner.get(), addition))
        {
            sn_library_release(addition);
            return error("cannot append shared library");
        }
    }
    std::map<std::string, uint32_t> cells;
    for (uint32_t cell = 0; cell < owner->cell_count; ++cell)
        cells.emplace(sn_library_cell_name(owner.get(), cell), cell);
    Scan scan;
    for (auto& tree : driver.syntaxTrees)
        tree->root().visit(scan);
    for (const auto& name : scan.definitions)
        if (cells.contains(name))
            return error("RTL/library definition collision: " + name);
    std::set<std::string> selected;
    for (auto* inst : scan.instances)
    {
        std::string name(inst->type.valueText());
        if (!cells.contains(name))
            continue;
        selected.insert(name);
        if (inst->parameters)
            return error("cell parameters are unsupported: " + name);
        for (auto* instance : inst->instances)
        {
            if (instance->decl && !instance->decl->dimensions.empty())
                return error("cell instance arrays are unsupported: " + name);
            for (auto* conn : instance->connections)
                if (conn->kind != syntax::SyntaxKind::NamedPortConnection)
                    return error("only named cell connections are supported: " + name);
        }
    }
    std::string source;
    for (const auto& name : selected)
    {
        const auto& entry = owner->cells[cells.at(name)];
        const auto* model = entry.model;
        const auto& cell = model->cells[entry.local_id];
        if (cell.invalid)
            return error("invalid cell: " + name);
        auto escaped = identifier(name);
        if (escaped.empty())
            return error("unrepresentable cell name: " + name);
        source += "(* blackbox *) module " + escaped + "(";
        std::set<std::string> pins;
        unsigned outputs = 0;
        bool first = true;
        for (uint32_t p = cell.pin_first; p < cell.pin_first + cell.pin_count; ++p)
        {
            const auto& pin = model->pins[p];
            // Supplies are implicit in this initial logical-netlist policy.
            if (pin.in_test_cell || pin.kind == SN_LIB_PIN_PG || pin.direction == SN_LIB_INTERNAL)
                continue;
            if (pin.kind == SN_LIB_PIN_BIT)
                continue; // declared through its parent vector port below
            if (pin.invalid || (pin.kind != SN_LIB_PIN_SCALAR && pin.kind != SN_LIB_PIN_BUS) ||
                (pin.direction != SN_LIB_INPUT && pin.direction != SN_LIB_OUTPUT))
                return error("unsupported or invalid signal interface in cell: " + name);
            if (pin.kind == SN_LIB_PIN_BUS)
                for (uint32_t bit = cell.pin_first; bit < cell.pin_first + cell.pin_count; ++bit)
                    if (model->pins[bit].parent == p &&
                        (model->pins[bit].invalid || model->pins[bit].direction != pin.direction))
                        return error("mixed-direction or invalid bus in cell: " + name);
            std::string port(sn_lib_name(model, pin.name));
            auto ep = identifier(port);
            if (ep.empty() || !pins.insert(port).second)
                return error("invalid/duplicate pin in cell: " + name);
            source += first ? "" : ", ";
            first = false;
            source += pin.direction == SN_LIB_INPUT ? "input wire " : "output wire ";
            if (pin.kind == SN_LIB_PIN_BUS)
                source += "[" + std::to_string(pin.bus_from) + ":" + std::to_string(pin.bus_to) + "] ";
            source += ep;
            outputs += pin.direction == SN_LIB_OUTPUT;
        }
        if (!outputs)
            return error("outputless cells cannot be preserved by SN: " + name);
        source += "); endmodule\n";
        if (!entry.scalar)
            std::fprintf(stderr,
                         "sn-slang: Liberty: retaining non-scalar cell '%s' as an opaque macro module\n",
                         name.c_str());
    }
    if (!source.empty())
    {
        auto tree = syntax::SyntaxTree::fromText(source, driver.sourceManager, "<Liberty interfaces>");
        tree->isLibraryUnit = true;
        driver.syntaxTrees.push_back(std::move(tree));
    }
    library = owner.release();
    return true;
}
} // namespace sn_slang_liberty
