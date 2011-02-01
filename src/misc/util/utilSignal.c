/**CFile****************************************************************

  FileName    [utilSignal.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName []

  Synopsis    []

  Author      []
  
  Affiliation [UC Berkeley]

  Date        []

  Revision    []

***********************************************************************/

#ifndef _MSC_VER

#include <main.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include <hashGen.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/wait.h>

#include "abc_global.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Hash_Gen_t* watched_pid_hash = NULL;
static Hash_Gen_t* watched_tmp_files_hash = NULL;

static sigset_t* old_procmask;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description [Kills all watched child processes and remove all watched termporary files.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

void Util_SignalCleanup()
{
    int i;
    Hash_Gen_Entry_t* pEntry;
    
    // kill all watched child processes
    Hash_GenForEachEntry(watched_pid_hash, pEntry, i)
    {
        pid_t pid = (pid_t)pEntry->key;
        pid_t ppid = (pid_t)pEntry->data;
        
        if (getpid() == ppid)
        {
            kill(pid, SIGINT);
        }
    }

    // remove watched temporary files
    Hash_GenForEachEntry(watched_tmp_files_hash, pEntry, i)
    {
        int fname = (const char*)pEntry->key;
        pid_t ppid = (pid_t)pEntry->data;
        
        if( getpid() == ppid )
        {
            remove(fname);
        }
    }
}

/**Function*************************************************************

  Synopsis    []

  Description [Sets up data structures needed for cleanup in signal handler.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

void Util_SignalStartHandler()
{
    watched_pid_hash = Hash_GenAlloc(100, Hash_DefaultHashFuncInt, Hash_DefaultCmpFuncInt, 0);
    watched_tmp_files_hash = Hash_GenAlloc(100, Hash_DefaultHashFuncStr, strcmp, 1);
}

/**Function*************************************************************

  Synopsis    []

  Description [Frees data structures used for clean up in signal handler.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

void Util_SignalResetHandler()
{
    int i;
    Hash_Gen_Entry_t* pEntry;
    
    sigset_t procmask, old_procmask;
    
    sigemptyset(&procmask);
    sigaddset(&procmask, SIGINT);
    
    sigprocmask(SIG_BLOCK, &procmask, &old_procmask);
    
    Hash_GenFree(watched_pid_hash);
    watched_pid_hash = Hash_GenAlloc(100, Hash_DefaultHashFuncInt, Hash_DefaultCmpFuncInt, 0);
    
    Hash_GenFree(watched_tmp_files_hash);
    watched_tmp_files_hash = Hash_GenAlloc(100, Hash_DefaultHashFuncStr, strcmp, 1);
    
    sigprocmask(SIG_SETMASK, &old_procmask, NULL);
}

void Util_SignalStopHandler()
{
    int i;
    Hash_Gen_Entry_t* pEntry;
    
    Hash_GenFree(watched_pid_hash);
    watched_pid_hash = NULL;
    
    Hash_GenFree(watched_tmp_files_hash);
    watched_tmp_files_hash = NULL;
}


/**Function*************************************************************

  Synopsis    []

  Description [Blocks SIGINT. For use when updating watched processes and temporary files to prevent race conditions with the signal handler.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

static int nblocks = 0;

void Util_SignalBlockSignals()
{
    sigset_t procmask;

    assert(nblocks==0);
    nblocks ++ ;
    
    sigemptyset(&procmask);
    sigaddset(&procmask, SIGINT);
    
    sigprocmask(SIG_BLOCK, &procmask, &old_procmask);
}

/**Function*************************************************************

  Synopsis    []

  Description [Unblocks SIGINT after a call to Util_SignalBlockSignals.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

void Util_SignalUnblockSignals()
{
    assert( nblocks==1);
    nblocks--;
    
    sigprocmask(SIG_SETMASK, &old_procmask, NULL);
}


static void watch_tmp_file(const char* fname)
{
    if( watched_tmp_files_hash != NULL )
    {
        Hash_GenWriteEntry(watched_tmp_files_hash, Extra_UtilStrsav(fname), (void*)getpid() );
    }
}

static void unwatch_tmp_file(const char* fname)
{
    if ( watched_tmp_files_hash )
    {
        assert( Hash_GenExists(watched_tmp_files_hash, fname) );
        Hash_GenRemove(watched_tmp_files_hash, fname);
        assert( !Hash_GenExists(watched_tmp_files_hash, fname) );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description [Adds a process id to the list of processes that should be killed in a signal handler.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

void Util_SignalAddChildPid(int pid)
{
    if ( watched_pid_hash )
    {
        Hash_GenWriteEntry(watched_pid_hash, (void*)pid,  (void*)getpid());
    }
}

/**Function*************************************************************

  Synopsis    []

  Description [Removes a process id from the list of processes that should be killed in a signal handler.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

void Util_SignalRemoveChildPid(int pid)
{
    if ( watched_pid_hash )
    {
        Hash_GenRemove(watched_pid_hash, (void*)pid);
    }
}

// a dummy signal hanlder to make sure that SIGCHLD and SIGINT will cause sigsuspend() to return
static int null_sig_handler(int signum)
{
    return 0;
}


// enusre that sigsuspend() returns when signal signum occurs -- sigsuspend() does not return if a signal is ignored
static void replace_sighandler(int signum, struct sigaction* old_sa, int replace_dfl)
{
    sigaction(signum, NULL, old_sa);

    if( old_sa->sa_handler == SIG_IGN || old_sa->sa_handler==SIG_DFL && replace_dfl)
    {
        struct sigaction sa;
        memset(&sa, 0, sizeof(sa));
        
        sa.sa_handler = null_sig_handler;
        
        sigaction(signum, &sa, &old_sa);
    }
}

// 
static int do_waitpid(pid_t pid, sigset_t* old_procmask)
{
    int status;

    struct sigaction sigint_sa;
    struct sigaction sigchld_sa;
    sigset_t waitmask;
    
    // ensure SIGINT and SIGCHLD are not blocked during sigsuspend()
    memcpy(&waitmask, old_procmask, sizeof(sigset_t));
    
    sigdelset(&waitmask, SIGINT);
    sigdelset(&waitmask, SIGCHLD);

    // ensure sigsuspend() returns if SIGINT or SIGCHLD occur, and save the current settings for SIGCHLD and SIGINT
    
    replace_sighandler(SIGINT, &sigint_sa, 0);
    replace_sighandler(SIGCHLD, &sigchld_sa, 1);
    
    for(;;)
    {
        int rc;

        // wait for a signal -- returns if SIGINT or SIGCHLD (or any other signal that is unblocked and not ignored) occur
        sigsuspend(&waitmask);
        
        // check if pid has terminated
        rc = waitpid(pid, &status, WNOHANG);
        
        // stop if terminated or some other error occurs
        if( rc > 0 || rc == -1 && errno!=EINTR )
        {
            break;
        }
    }
    
    // process is dead, should no longer be watched
    Util_SignalRemoveChildPid(pid);
    
    // restore original behavior of SIGINT and SIGCHLD
    sigaction(SIGINT, &sigint_sa, NULL);
    sigaction(SIGCHLD, &sigchld_sa, NULL);
    
    return status;
}

static int do_system(const char* cmd, sigset_t* old_procmask)
{
    int pid;

    pid = fork();
    
    if (pid == -1)
    {
        // fork failed
        return -1;
    }
    else if( pid == 0)
    {
        // child process
        sigprocmask(SIG_SETMASK, old_procmask, NULL);
        execl("/bin/sh", "sh", "-c", cmd, NULL);
        _exit(127);
    }

    Util_SignalAddChildPid(pid);
    
    return do_waitpid(pid, old_procmask);
}

/**Function*************************************************************

  Synopsis    []

  Description [Replaces system() with a function that allows SIGINT to interrupt.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

int Util_SignalSystem(const char* cmd)
{
    int status;
    
    sigset_t procmask;
    sigset_t old_procmask;
 
    // if signal handler is not installed, run the original system()
    if ( ! watched_pid_hash && ! watched_tmp_files_hash )
        return system(cmd);
    
    // block SIGINT and SIGCHLD
    sigemptyset(&procmask);

    sigaddset(&procmask, SIGINT);
    sigaddset(&procmask, SIGCHLD);
    
    sigprocmask(SIG_BLOCK, &procmask, &old_procmask);

    // call the actual function    
    status = do_system(cmd, &old_procmask);
    
    // restore signal block mask
    sigprocmask(SIG_SETMASK, &old_procmask, NULL);
    return status;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

#else /* #ifndef _MSC_VER */

#include "abc_global.h"

ABC_NAMESPACE_IMPL_START

void Util_SignalCleanup()
{
}

void Util_SignalStartHandler()
{
}

void Util_SignalResetHandler()
{
}

void Util_SignalStopHandler()
{
}

void Util_SignalBlockSignals()
{
}

void Util_SignalUnblockSignals()
{
}

void watch_tmp_file(const char* fname)
{
}

void unwatch_tmp_file(const char* fname)
{
}

void Util_SignalAddChildPid(int pid)
{
}

void Util_SignalRemoveChildPid(int pid)
{
}

int Util_SignalSystem(const char* cmd)
{
    return system(cmd);
}

#endif  /* #ifdef _MSC_VER */

int tmpFile(const char* prefix, const char* suffix, char** out_name);

/**Function*************************************************************

  Synopsis    []

  Description [Create a temporary file and add it to the list of files to be cleaned up in the signal handler.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

int Util_SignalTmpFile(const char* prefix, const char* suffix, char** out_name)
{
    int fd;
    
    Util_SignalBlockSignals();
    
    fd  = tmpFile(prefix, suffix, out_name);
    
    if ( fd != -1 )
    {
        watch_tmp_file( *out_name );
    }
    
    Util_SignalUnblockSignals();
    
    return fd;
}

/**Function*************************************************************

  Synopsis    []

  Description [Remove a temporary file (and remove it from the watched files list.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

void Util_SignalTmpFileRemove(const char* fname, int fLeave)
{
    Util_SignalBlockSignals();
    
    unwatch_tmp_file(fname);
    
    if (! fLeave)
    {
        remove(fname);
    }
    
    Util_SignalUnblockSignals();
}

ABC_NAMESPACE_IMPL_END
