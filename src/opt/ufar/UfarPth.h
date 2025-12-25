//
// Created by Yen-Sheng Ho on 04/09/17.
//

#ifndef SRC_EXT2_UFAR_PTH_H
#define SRC_EXT2_UFAR_PTH_H

#include <vector>
#include <string>
#include "base/wlc/wlc.h"

ABC_NAMESPACE_CXX_HEADER_START

namespace UFAR
{
    int RunConcurrentSolver( Wlc_Ntk_t * pNtk, const std::vector<std::string>& vSolvers, Abc_Cex_t ** ppCex, struct timespec * timeout );
}

ABC_NAMESPACE_CXX_HEADER_END

#endif //SRC_EXT2_UFAR_PTH_H
