#ifndef ABC__ext_pa__paMath_h
#define ABC__ext_pa__paMath_h

#include "misc/util/abc_namespaces.h"

#include <cmath>
#include <cstdint>
#include <cstring>
#include <limits>

ABC_NAMESPACE_HEADER_START

// Density footprints use a half-open upper bound. For positive finite IEEE
// doubles, the predecessor is exactly nextafter(Upper, Lower), without a
// libm call. Keep the general operation for other formats/boundary cases.
static inline double Pa_PreviousBoundary( double Upper, double Lower )
{
    if constexpr ( std::numeric_limits<double>::is_iec559
                && sizeof(double) == sizeof(uint64_t) )
    {
        if ( Upper > 0.0 && Lower < Upper && std::isfinite(Upper) )
        {
            uint64_t Bits;
            std::memcpy(&Bits, &Upper, sizeof(Bits));
            --Bits;
            std::memcpy(&Upper, &Bits, sizeof(Upper));
            return Upper;
        }
    }
    return std::nextafter(Upper, Lower);
}

ABC_NAMESPACE_HEADER_END

#endif
