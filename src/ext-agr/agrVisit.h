#ifndef ABC_AGR_VISIT_H
#define ABC_AGR_VISIT_H
#include "base/abc/abc.h"
ABC_NAMESPACE_HEADER_START
#ifdef __cplusplus
extern "C"
{
#endif
    const int *Agr_ReadVisitOrder(int *count);
    void Agr_SetVisitOrder(const int *order, int count);
#ifdef __cplusplus
}
#endif
ABC_NAMESPACE_HEADER_END
// Stable object IDs are looked up at each visit: a prior edit may delete a
// scheduled root. The snapshot never visits newly appended nodes in this pass.
#define Agr_NtkForEachVisit(n, obj, i, order, count)                                                \
    for ((i) = 0; (i) < ((order) ? (count) : Abc_NtkObjNumMax(n)); ++(i))                          \
        if (((obj) = Abc_NtkObj((n), (order) ? (order)[i] : (i))) == NULL || !Abc_ObjIsNode(obj))  \
        {                                                                                          \
        }                                                                                          \
        else
#endif
