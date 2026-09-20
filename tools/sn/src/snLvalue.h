/**CFile****************************************************************

  FileName    [snLvalue.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Slang-to-SN RTL frontend.]

  Synopsis    [Layout and selection helpers for SystemVerilog assignment targets.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snLvalue.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#pragma once

#include <cstdint>
#include <cstdlib>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <variant>
#include <vector>

#include "slang/ast/Expression.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/ConversionExpression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/ValueSymbol.h"
#include "slang/ast/types/Type.h"
#include "slang/ast/types/AllTypes.h"

namespace sn_slang_detail
{

// Frontend-only description of an assignment target. Keeping analysis separate from emission lets continuous,
// combinational, sequential, and initial assignments use the same SystemVerilog bit-layout rules.
struct sn_lvalue_t
{
    struct variable_t
    {
        const slang::ast::ValueSymbol* symbol;
    };

    struct array_element_t
    {
        const slang::ast::ValueSymbol* symbol;
        const slang::ast::Expression* selector;
        std::optional<int64_t> constant_index;
    };

    struct memory_element_t
    {
        const slang::ast::ValueSymbol* symbol;
        const slang::ast::Expression* address;
    };

    struct select_t
    {
        std::unique_ptr<sn_lvalue_t> inner;
        const slang::ast::Expression* selector;
        const slang::ast::Expression* width_expr;
        const slang::ast::Type* input_type;
        slang::ast::RangeSelectionKind selection_kind;
        std::optional<int64_t> constant_selector;
        std::optional<int64_t> constant_right;
        bool element;
    };

    struct concat_t
    {
        std::vector<sn_lvalue_t> elements;
    };

    struct member_t
    {
        std::unique_ptr<sn_lvalue_t> inner;
        uint64_t bit_offset;
    };

    struct stream_t
    {
        std::unique_ptr<sn_lvalue_t> inner;
        uint32_t slice_size;
    };

    using descriptor_t =
        std::variant<variable_t, array_element_t, memory_element_t, select_t, concat_t, member_t, stream_t>;

    descriptor_t descriptor;
    uint32_t width;
    bool is_static;
};

struct sn_lvalue_context_t
{
    std::function<std::optional<int64_t>(const slang::ast::Expression&)> constant_integer;
    std::function<bool(const slang::ast::ValueSymbol&)> is_memory;
    bool split_packed_elements = false;
};

// Slang records unpacked-struct field offsets in declaration order, while bitstream operations use LSB-first
// physical offsets. Packed aggregates already use physical offsets directly.
inline uint64_t sn_lvalue_member_offset(const slang::ast::FieldSymbol& member)
{
    const slang::ast::Symbol& parent = member.getParentScope()->asSymbol();
    if (!slang::ast::Type::isKind(parent.kind))
        return UINT64_MAX;
    uint64_t offset = member.bitOffset;
    const slang::ast::Type& type = parent.as<slang::ast::Type>();
    if (type.isUnpackedStruct())
    {
        const auto& unpacked = type.as<slang::ast::UnpackedStructType>();
        if (unpacked.bitstreamWidth != unpacked.selectableWidth ||
            member.getType().getBitstreamWidth() > unpacked.bitstreamWidth - offset)
            return UINT64_MAX;
        offset = unpacked.bitstreamWidth - offset - member.getType().getBitstreamWidth();
    }
    return offset;
}

inline std::optional<sn_lvalue_t> sn_lvalue_analyze(const slang::ast::Expression& expression,
                                                     const sn_lvalue_context_t& context, std::string& error)
{
    using namespace slang::ast;
    auto bit_width = [](const Type& type) -> std::optional<uint32_t> {
        if (!type.isFixedSize())
            return std::nullopt;
        uint64_t width = type.getBitstreamWidth();
        if (!width || width > UINT32_MAX)
            return std::nullopt;
        return uint32_t(width);
    };

    std::optional<uint32_t> result_width;
    if (const auto* streaming = expression.as_if<StreamingConcatenationExpression>())
    {
        uint64_t bits = streaming->getBitstreamWidth();
        if (bits && bits <= UINT32_MAX)
            result_width = uint32_t(bits);
    }
    else
        result_width = bit_width(*expression.type);
    if (!result_width)
    {
        error = "assignment target does not have a fixed nonzero 32-bit width";
        return std::nullopt;
    }

    if (const auto* named = expression.as_if<NamedValueExpression>())
        return sn_lvalue_t{sn_lvalue_t::variable_t{&named->symbol}, *result_width, true};

    // Slang represents each target in an lvalue assignment pattern as an assignment whose right side is an
    // EmptyArgumentExpression. The nested assignment supplies context for the aggregate element; its left side is
    // the actual target.
    if (const auto* assignment = expression.as_if<AssignmentExpression>();
        assignment && assignment->right().as_if<EmptyArgumentExpression>())
        return sn_lvalue_analyze(assignment->left(), context, error);

    if (const auto* conversion = expression.as_if<ConversionExpression>())
    {
        auto operand_width = bit_width(*conversion->operand().type);
        if (operand_width && *operand_width == *result_width)
            return sn_lvalue_analyze(conversion->operand(), context, error);
        error = "assignment-target conversion changes the bit width";
        return std::nullopt;
    }

    if (const auto* streaming = expression.as_if<StreamingConcatenationExpression>())
    {
        auto streams = streaming->streams();
        std::vector<sn_lvalue_t> elements;
        elements.reserve(streams.size());
        bool is_static = true;
        uint64_t total = 0;
        for (const auto& stream : streams)
        {
            if (stream.withExpr)
            {
                error = "streaming assignment targets with a with-clause are unsupported";
                return std::nullopt;
            }
            auto element = sn_lvalue_analyze(*stream.operand, context, error);
            if (!element)
                return std::nullopt;
            total += element->width;
            is_static = is_static && element->is_static;
            elements.push_back(std::move(*element));
        }
        if (total != *result_width || elements.empty())
        {
            error = "streaming assignment target has inconsistent width";
            return std::nullopt;
        }
        sn_lvalue_t packed{sn_lvalue_t::concat_t{std::move(elements)}, *result_width, is_static};
        uint64_t slice_size = streaming->getSliceSize();
        if (!slice_size)
            return packed;
        if (slice_size > UINT32_MAX || *result_width % uint32_t(slice_size))
        {
            error = "streaming assignment target has an irregular slice size";
            return std::nullopt;
        }
        // A reordered stream is not one contiguous static span even if all of its leaves are static.
        return sn_lvalue_t{sn_lvalue_t::stream_t{std::make_unique<sn_lvalue_t>(std::move(packed)),
                                                uint32_t(slice_size)},
                           *result_width, false};
    }

    if (const auto* pattern = expression.as_if<SimpleAssignmentPatternExpression>(); pattern && pattern->isLValue)
    {
        std::vector<sn_lvalue_t> elements;
        elements.reserve(pattern->elements().size());
        bool is_static = true;
        uint64_t total = 0;
        for (const Expression* operand : pattern->elements())
        {
            auto element = sn_lvalue_analyze(*operand, context, error);
            if (!element)
                return std::nullopt;
            total += element->width;
            is_static = is_static && element->is_static;
            elements.push_back(std::move(*element));
        }
        if (total != *result_width)
        {
            error = "assignment-pattern target has inconsistent width";
            return std::nullopt;
        }
        return sn_lvalue_t{sn_lvalue_t::concat_t{std::move(elements)}, *result_width, is_static};
    }

    if (const auto* concat = expression.as_if<ConcatenationExpression>())
    {
        std::vector<sn_lvalue_t> elements;
        elements.reserve(concat->operands().size());
        bool is_static = true;
        uint64_t total = 0;
        for (const Expression* operand : concat->operands())
        {
            auto element = sn_lvalue_analyze(*operand, context, error);
            if (!element)
                return std::nullopt;
            total += element->width;
            is_static = is_static && element->is_static;
            elements.push_back(std::move(*element));
        }
        if (total != *result_width)
        {
            error = "concatenated assignment target has inconsistent width";
            return std::nullopt;
        }
        return sn_lvalue_t{sn_lvalue_t::concat_t{std::move(elements)}, *result_width, is_static};
    }

    if (const auto* member = expression.as_if<MemberAccessExpression>())
    {
        if (member->member.kind != SymbolKind::Field)
        {
            error = "assignment target is not a data field";
            return std::nullopt;
        }
        const auto& field = member->member.as<FieldSymbol>();
        auto inner = sn_lvalue_analyze(member->value(), context, error);
        uint64_t offset = sn_lvalue_member_offset(field);
        if (!inner || offset == UINT64_MAX || offset + *result_width > inner->width)
        {
            if (error.empty())
                error = "assignment-target field has an invalid bitstream offset";
            return std::nullopt;
        }
        bool is_static = inner->is_static;
        return sn_lvalue_t{sn_lvalue_t::member_t{std::make_unique<sn_lvalue_t>(std::move(*inner)), offset},
                           *result_width, is_static};
    }

    if (const auto* element = expression.as_if<ElementSelectExpression>())
    {
        const auto* named = element->value().as_if<NamedValueExpression>();
        // Keep complete elements of unpacked arrays and multidimensional packed arrays as independent values.
        // A one-bit selection of an ordinary packed vector remains a bit select of the containing value.
        if (named && (named->symbol.getType().isUnpackedArray() ||
                      (context.split_packed_elements && *result_width > 1)))
        {
            auto index = context.constant_integer(element->selector());
            if (context.is_memory(named->symbol))
                return sn_lvalue_t{sn_lvalue_t::memory_element_t{&named->symbol, &element->selector()},
                                   *result_width, false};
            return sn_lvalue_t{sn_lvalue_t::array_element_t{&named->symbol, &element->selector(), index},
                               *result_width, index.has_value()};
        }
        auto inner = sn_lvalue_analyze(element->value(), context, error);
        if (!inner)
            return std::nullopt;
        auto selector = context.constant_integer(element->selector());
        bool is_static = inner->is_static && selector.has_value();
        return sn_lvalue_t{sn_lvalue_t::select_t{std::make_unique<sn_lvalue_t>(std::move(*inner)),
                                                &element->selector(), nullptr, element->value().type,
                                                RangeSelectionKind::Simple,
                                                selector, int64_t(1), true},
                           *result_width, is_static};
    }

    if (const auto* range = expression.as_if<RangeSelectExpression>())
    {
        auto inner = sn_lvalue_analyze(range->value(), context, error);
        if (!inner)
            return std::nullopt;
        auto selector = context.constant_integer(range->left());
        auto right = context.constant_integer(range->right());
        bool is_static = inner->is_static && selector.has_value() && right.has_value();
        return sn_lvalue_t{sn_lvalue_t::select_t{std::make_unique<sn_lvalue_t>(std::move(*inner)),
                                                &range->left(), &range->right(), range->value().type,
                                                range->getSelectionKind(), selector, right, false},
                           *result_width, is_static};
    }

    error = "unsupported assignment-target expression kind " + std::to_string(unsigned(expression.kind));
    return std::nullopt;
}

} // namespace sn_slang_detail
