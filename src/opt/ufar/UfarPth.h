//
// Created by Yen-Sheng Ho on 04/09/17.
//

#ifndef SRC_EXT2_UFAR_PTH_H
#define SRC_EXT2_UFAR_PTH_H

#include "base/wlc/wlc.h"
#include <vector>
#include <string>

namespace UFAR
{
    int RunConcurrentSolver( Wlc_Ntk_t * pNtk, const std::vector<std::string>& vSolvers, Abc_Cex_t ** ppCex, struct timespec * timeout );
}

#endif //SRC_EXT2_UFAR_PTH_H
