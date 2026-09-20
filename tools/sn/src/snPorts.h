/**CFile****************************************************************

  FileName    [snPorts.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Slang-to-SN RTL frontend.]

  Synopsis    [Elaborated top-port bit layout for explicit correspondence checks.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snPorts.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_SLANG_PORTS_H
#define SN_SLANG_PORTS_H

#include <cstdio>
#include <stdexcept>
#include <string>
#include <vector>

#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/text/Json.h"

namespace sn_slang_ports
{
// Report declaration selectors separately from normalized SN offsets. In
// particular, ascending ranges and nonzero bounds must not be guessed from width.
inline void bits(slang::JsonWriter& json, const slang::ast::Type& original,
                 uint64_t offset, std::vector<std::string>& selectors)
{
    using namespace slang::ast;
    const Type& type = original.getCanonicalType();
    if (!type.isIntegral() || type.isPackedUnion() || selectors.size() > 128)
        throw std::runtime_error("port layout requires non-union packed integral ports");
    if (const auto* structure = type.as_if<PackedStructType>())
    {
        for (const auto& field : structure->membersOfType<FieldSymbol>())
        {
            selectors.emplace_back(field.name);
            bits(json, field.getType(), offset + field.bitOffset, selectors);
            selectors.pop_back();
        }
    }
    else if (const auto* array = type.as_if<PackedArrayType>())
    {
        uint64_t stride = array->elementType.getBitWidth();
        for (uint64_t bit = 0; bit < array->range.width(); ++bit)
        {
            int64_t index = int64_t(array->range.right) +
                (array->range.left >= array->range.right ? int64_t(bit) : -int64_t(bit));
            selectors.push_back(std::to_string(index));
            bits(json, array->elementType, offset + bit * stride, selectors);
            selectors.pop_back();
        }
    }
    else
    {
        uint64_t width = type.getBitWidth();
        for (uint64_t bit = 0; bit < width; ++bit)
        {
            json.startObject();
            json.writeProperty("offset"); json.writeValue(offset + bit);
            json.writeProperty("selectors"); json.startArray();
            for (const auto& selector : selectors) json.writeValue(selector);
            // Atom integer and enum values have an implicit [width-1:0] range.
            if (width > 1) json.writeValue(std::to_string(bit));
            json.endArray();
            json.endObject();
        }
    }
}

inline std::string layout(const slang::ast::InstanceBodySymbol& body)
{
    using namespace slang::ast;
    slang::JsonWriter json;
    json.startObject();
    json.writeProperty("schema"); json.writeValue(uint64_t(1));
    json.writeProperty("top"); json.writeValue(body.getDefinition().name);
    json.writeProperty("ports"); json.startArray();
    uint64_t total_bits = 0;
    for (const Symbol* symbol : body.getPortList())
    {
        const auto* port = symbol->as_if<PortSymbol>();
        if (!port || (port->direction != ArgumentDirection::In && port->direction != ArgumentDirection::Out))
            throw std::runtime_error("port layout requires simple input/output data ports");
        const Type& type = port->getType();
        uint64_t width = type.getBitWidth();
        if (!type.isIntegral() || !width || width > 1048576 || (total_bits += width) > 1048576)
            throw std::runtime_error("port layout requires 1..1048576 total packed integral bits");
        json.startObject();
        json.writeProperty("name"); json.writeValue(port->name);
        json.writeProperty("direction");
        json.writeValue(std::string_view(port->direction == ArgumentDirection::In ? "input" : "output"));
        json.writeProperty("width"); json.writeValue(width);
        json.writeProperty("signed"); json.writeValue(type.isSigned());
        json.writeProperty("bits"); json.startArray();
        std::vector<std::string> selectors;
        bits(json, type, 0, selectors);
        json.endArray();
        json.endObject();
    }
    json.endArray();
    json.endObject();
    return std::string(json.view()) + "\n";
}

// Never overwrite an input, an earlier report, or the requested SN output.
// An existing path (including a symlink) is an error. Layout is diagnostic only:
// it does not alter the SN representation or prove any signal correspondence.
inline bool write(const char* path, const std::string& text)
{
    FILE* file = std::fopen(path, "wx");
    if (!file) return false;
    bool success = std::fwrite(text.data(), 1, text.size(), file) == text.size();
    if (std::fclose(file)) success = false;
    if (!success) std::remove(path);
    return success;
}
}
#endif
