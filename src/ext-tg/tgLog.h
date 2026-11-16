#ifndef ABC_EXT_TG_LOG_H
#define ABC_EXT_TG_LOG_H
#include "base/abc/abc.h"
ABC_NAMESPACE_HEADER_START
int Tg_IsVerbose(void);
ABC_NAMESPACE_HEADER_END
#define TG_VERBOSE(...)                                                                            \
    do                                                                                             \
    {                                                                                              \
        if (Tg_IsVerbose())                                                                        \
            Abc_Print(1, __VA_ARGS__);                                                             \
    } while (0)
#endif
