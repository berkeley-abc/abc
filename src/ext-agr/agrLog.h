#ifndef ABC_EXT_AGR_LOG_H
#define ABC_EXT_AGR_LOG_H
#include "base/abc/abc.h"
ABC_NAMESPACE_HEADER_START
int Agr_IsVerbose(void);
ABC_NAMESPACE_HEADER_END
#define AGR_VERBOSE(...)                                                                            \
    do                                                                                             \
    {                                                                                              \
        if (Agr_IsVerbose())                                                                        \
            Abc_Print(1, __VA_ARGS__);                                                             \
    } while (0)
#endif
