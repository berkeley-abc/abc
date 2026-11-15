/* SCMap: standard-cell mapping with electrical cover refinement. */
#ifndef ABC__aig__gia__giaScmap_h
#define ABC__aig__gia__giaScmap_h
#include "gia.h"
ABC_NAMESPACE_HEADER_START
Gia_Man_t * Gia_ManScmap( Gia_Man_t * pGia, int fVerbose, int fVeryVerbose );
Gia_Man_t * Gia_ManScmapQuality( Gia_Man_t * pGia, int fVerbose, int fVeryVerbose );
ABC_NAMESPACE_HEADER_END
#endif
