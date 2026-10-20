// Original four-input selector on one immutable GIA snapshot.
#ifndef ABC__opt__drw__drwGia_h
#define ABC__opt__drw__drwGia_h
#include "aig/gia/gia.h"
ABC_NAMESPACE_HEADER_START
typedef struct Drw_Gia_t_ Drw_Gia_t;
extern Drw_Gia_t * Drw_GiaStart( Gia_Man_t * pGia );
extern Vec_Int_t * Drw_GiaSelect( Drw_Gia_t * p, int Id );
extern void Drw_GiaStop( Drw_Gia_t * p );
ABC_NAMESPACE_HEADER_END
#endif
