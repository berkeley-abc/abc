/*
 * UifCmd.h
 *
 *  Created on: Aug 25, 2015
 *      Author: Yen-Sheng Ho
 */

#ifndef SRC_EXT2_UIF_UIFCMD_H_
#define SRC_EXT2_UIF_UIFCMD_H_

#include "base/main/mainInt.h"

ABC_NAMESPACE_HEADER_START

void Ufar_Init(Abc_Frame_t *pAbc);

typedef struct Wlc_Ntk_t_ Wlc_Ntk_t;
extern int Ufar_ProveWithTimeout( Wlc_Ntk_t * pNtk, int nTimeOut, int fVerbose, int (*pFuncStop)(int), int RunId );

ABC_NAMESPACE_HEADER_END

#endif /* SRC_EXT2_UIF_UIFCMD_H_ */
