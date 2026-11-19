#ifndef ABC__ext_agr__agrMath_h
#define ABC__ext_agr__agrMath_h

#include "misc/util/abc_namespaces.h"

#include <cmath>
#include <cstdint>
#include <cstring>
#include <limits>

ABC_NAMESPACE_HEADER_START

// Density footprints use a half-open upper bound. For positive finite IEEE
// doubles, the predecessor is exactly nextafter(Upper, Lower), without a
// libm call. Keep the general operation for other formats/boundary cases.
static inline double Agr_PreviousBoundary(double Upper, double Lower)
{
    {
        if (Upper > 0.0 && Lower < Upper && std::isfinite(Upper))
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
