/**CFile****************************************************************

  FileName    [utilSignal.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName []

  Synopsis    []

  Author      []
  
  Affiliation [UC Berkeley]

  Date        []

  Revision    []

***********************************************************************/
 
#ifndef __UTIL_SIGNAL_H__
#define __UTIL_SIGNAL_H__

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_HEADER_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== utilSignal.c ==========================================================*/

void Util_SignalCleanup();

void Util_SignalStartHandler();
void Util_SignalResetHandler();
void Util_SignalStopHandler();

void Util_SignalBlockSignals();
void Util_SignalUnblockSignals();

void Util_SignalAddChildPid(int pid);
void Util_SignalRemoveChildPid(int pid);

int Util_SignalTmpFile(const char* prefix, const char* suffix, char** out_name);
void Util_SignalTmpFileRemove(const char* fname, int fLeave);

int Util_SignalSystem(const char* cmd);

ABC_NAMESPACE_HEADER_END

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
