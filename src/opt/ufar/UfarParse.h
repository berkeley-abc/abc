/**CFile****************************************************************

  FileName    [UfarParse.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Uninterpreted-function abstraction and refinement.]

  Synopsis    [Parses the existing filename and simulation option patterns.]

  Author      [ABC contributors.]

  Date        [Ver. 1.0. Started - November 9, 2026.]

***********************************************************************/

#ifndef ABC_OPT_UFAR_PARSE_H
#define ABC_OPT_UFAR_PARSE_H

#include <locale>
#include <string>
#include "misc/util/abc_namespaces.h"

ABC_NAMESPACE_CXX_HEADER_START
namespace UFAR {

// These fixed patterns need only a word suffix or a decimal scan. Replacing
// std::regex avoids GCC 13 library-template warnings in optimized builds
// while preserving the former search, capture and stoi behavior.

/**Function*************************************************************

  Synopsis    [Matches the trailing word followed by .v, as in the old regex.]

  Description [The optional slash is outside the capture. A nonmatching
               string is returned unchanged.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
inline std::string ParseVerilogName(const std::string& text, bool keepSuffix)
{
    if (text.size() < 3 || text.compare(text.size() - 2, 2, ".v") != 0)
        return text;
    const size_t end = text.size() - 2;
    size_t begin = end;
    const std::locale locale;
    while (begin && (text[begin - 1] == '_' || std::isalnum(text[begin - 1], locale)))
        --begin;
    return begin == end ? text : text.substr(begin, (keepSuffix ? text.size() : end) - begin);
}

/**Function*************************************************************

  Synopsis    [Finds the first key followed by a colon and decimal digits.]

  Description [Preserves the old regex search and stoi conversion behavior.]

  SideEffects [Updates value only when a match is found.]

  SeeAlso     []

***********************************************************************/
inline void ParseSimValue(const std::string& text, char key, int& value)
{
    const std::locale locale;
    for (size_t begin = 0; begin + 2 < text.size(); ++begin)
    {
        if (text[begin] != key || text[begin + 1] != ':' || !std::isdigit(text[begin + 2], locale))
            continue;
        size_t end = begin + 3;
        while (end < text.size() && std::isdigit(text[end], locale))
            ++end;
        value = std::stoi(text.substr(begin + 2, end - begin - 2));
        return;
    }
}

} // namespace UFAR
ABC_NAMESPACE_CXX_HEADER_END

#endif
