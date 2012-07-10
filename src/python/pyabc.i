%module pyabc

// -------------------------------------------------------------------
// SWIG typemap allowing us to grab a Python callable object
// -------------------------------------------------------------------

#ifdef SWIG<Python>

%typemap(in) PyObject *PyFunc 
{
  
  if ( !PyCallable_Check($source) ) 
  {
      PyErr_SetString(PyExc_TypeError, "Need a callable object!");
      return NULL;
  }
  
  $target = $source;
}

#endif /* #ifdef SWIG<Python> */

%{
    
#include <base/main/main.h>
#include <misc/util/utilCex.h>

#include <stdlib.h>
#include <signal.h>

#include <sys/prctl.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <fcntl.h>
    
int n_ands()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    if ( pNtk && Abc_NtkIsStrash(pNtk) )
    {        
        return Abc_NtkNodeNum(pNtk);
    }

    return -1;
}
    
int n_nodes()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    if ( pNtk )
    {        
        return Abc_NtkNodeNum(pNtk);
    }

    return -1;
}

int n_pis()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    if ( pNtk )
    {        
        return Abc_NtkPiNum(pNtk);
    }

    return -1;
}


int n_pos()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    if ( pNtk )
    {        
        return Abc_NtkPoNum(pNtk);
    }

    return -1;
}

int n_latches()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    if ( pNtk )
    {        
        return Abc_NtkLatchNum(pNtk);
    }

    return -1;
}

int n_levels()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    if ( pNtk )
    {        
        return Abc_NtkLevel(pNtk);
    }

    return -1;
}

int has_comb_model()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    return pNtk && pNtk->pModel;
}

int has_seq_model()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    return pNtk && pNtk->pSeqModel;
}

int n_bmc_frames()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    return Abc_FrameReadBmcFrames(pAbc);
}

int prob_status()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    return Abc_FrameReadProbStatus(pAbc);
}

int is_valid_cex()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    return pNtk && Abc_FrameReadCex(pAbc) && Abc_NtkIsValidCex( pNtk, Abc_FrameReadCex(pAbc) );
}

int is_true_cex()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    return pNtk && Abc_FrameReadCex(pAbc) && Abc_NtkIsTrueCex( pNtk, Abc_FrameReadCex(pAbc) );
}

int n_cex_pis()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();

    return Abc_FrameReadCex(pAbc) ? Abc_FrameReadCexPiNum( pAbc ) : -1;
}

int n_cex_regs()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();

    return Abc_FrameReadCex(pAbc) ? Abc_FrameReadCexRegNum( pAbc ) : -1;
}

int cex_po()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();

    return Abc_FrameReadCex(pAbc) ? Abc_FrameReadCexPo( pAbc ) : -1;
}

int cex_frame()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();

    return Abc_FrameReadCex(pAbc) ? Abc_FrameReadCexFrame( pAbc ) : -1;
}

int n_phases()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    return pNtk ? Abc_NtkPhaseFrameNum(pNtk) : 1;
}

Abc_Cex_t* _cex_get()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Cex_t* pCex = Abc_FrameReadCex(pAbc);
    
    if ( ! pCex )
    {
        return NULL;
    }

    return Abc_CexDup( pCex, -1 ); 
}

int _cex_get_vec_len()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
	Vec_Ptr_t* vCexVec = Abc_FrameReadCexVec(pAbc);
	
	if( ! vCexVec )
	{
		return 0;
	}
	
	return Vec_PtrSize(vCexVec);
}

Abc_Cex_t* _cex_get_vec(int i)
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
	Vec_Ptr_t* vCexVec = Abc_FrameReadCexVec(pAbc);
    
	if( ! vCexVec )
	{
		return NULL;
	}

	Abc_Cex_t* pCex = Vec_PtrEntry( vCexVec, i );

	if ( ! pCex )
	{
		return NULL;
	}

    return Abc_CexDup( pCex, -1 ); 
}

void _cex_put(Abc_Cex_t* pCex)
{
    if ( pCex )
    {
        pCex = Abc_CexDup(pCex, -1);
    }
    
    Abc_FrameSetCex( Abc_CexDup(pCex, -1) );
}

void _cex_free(Abc_Cex_t* pCex)
{
    Abc_CexFree(pCex);
}

int _cex_n_regs(Abc_Cex_t* pCex)
{
    return pCex->nRegs;
}

int _cex_n_pis(Abc_Cex_t* pCex)
{
    return pCex->nPis;
}

int _cex_get_po(Abc_Cex_t* pCex)
{
    return pCex->iPo;
}

int _cex_get_frame(Abc_Cex_t* pCex)
{
    return pCex->iFrame;
}

static PyObject* VecInt_To_PyList(Vec_Int_t* v)
{
    PyObject* pylist = PyList_New( Vec_IntSize(v) );
    
    int elem, i;
    
    Vec_IntForEachEntry( v, elem, i)
    {
        PyList_SetItem( pylist, i, PyInt_FromLong(elem) );
    }
    
    return pylist;
}

PyObject* iso_eq_classes()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Vec_Ptr_t *vPoEquivs = Abc_FrameReadPoEquivs(pAbc);
    
    PyObject* eq_classes;
    Vec_Int_t* pEntry;
    int i;
    
    if( ! vPoEquivs )
    {
        Py_RETURN_NONE;
    }
    
    eq_classes = PyList_New( Vec_PtrSize(vPoEquivs) );
    
    Vec_PtrForEachEntry( Vec_Int_t*, vPoEquivs, pEntry, i )
    {
        PyList_SetItem( eq_classes, i, VecInt_To_PyList(pEntry) );
    }

    return eq_classes;    
}

static PyObject* pyabc_internal_python_command_callback = 0;

void pyabc_internal_set_command_callback( PyObject* callback )
{
    Py_XINCREF(callback);
    Py_XDECREF(pyabc_internal_python_command_callback);

    pyabc_internal_python_command_callback = callback;
}

static int pyabc_internal_abc_command_callback(Abc_Frame_t * pAbc, int argc, char ** argv)
{
    int i;
    
    PyObject* args;
    PyObject* arglist;
    PyObject* res;
    
    PyGILState_STATE gstate;
    
    long lres;
    
    if ( !pyabc_internal_python_command_callback )
            return 0;
            
    gstate = PyGILState_Ensure();
            
    args = PyList_New(argc);
    
    for( i=0 ; i<argc ; i++ )
            PyList_SetItem(args, i, PyString_FromString(argv[i]) );

    arglist = Py_BuildValue("(O)", args);
    Py_INCREF(arglist);

    res = PyEval_CallObject( pyabc_internal_python_command_callback, arglist );
    Py_DECREF(arglist);

    if ( !res )
    {
        PyGILState_Release(gstate);
        return -1;
    }
    
    lres = PyInt_AsLong(res);
    Py_DECREF(res);

    PyGILState_Release(gstate);
    
    return lres;
}

int run_command(char* cmd)
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    int rc;
    
    Py_BEGIN_ALLOW_THREADS
    
    rc = Cmd_CommandExecute(pAbc, cmd);
    
    Py_END_ALLOW_THREADS
    
    return rc;
}

void pyabc_internal_register_command( char * sGroup, char * sName, int fChanges )
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();

    Cmd_CommandAdd( pAbc, sGroup, sName, (void*)pyabc_internal_abc_command_callback, fChanges);
}

static int sigchld_pipe_fd = -1;
    
static void sigchld_handler(int signum)
{
    while( write(sigchld_pipe_fd, "", 1) == -1 && errno==EINTR )
        ;
}

static void install_sigchld_handler(int sigchld_fd)
{
    sigchld_pipe_fd = sigchld_fd;
    signal(SIGCHLD, sigchld_handler);
}

static int sigint_pipe_fd = -1;

static void sigint_handler(int signum)
{
    unsigned char tmp = (unsigned char)signum;
    while( write(sigint_pipe_fd, &tmp, 1) == -1 && errno==EINTR )
        ;
}

static void install_sigint_handler(int sigint_fd)
{
    sigint_pipe_fd = sigint_fd;
    
    signal(SIGINT, sigint_handler);

    // try to catch other signals that ask the process to terminate    
    signal(SIGABRT, sigint_handler);
    signal(SIGQUIT, sigint_handler);
    signal(SIGTERM, sigint_handler);

    // try to ensure cleanup on exceptional conditions
    signal(SIGBUS, sigint_handler);
    signal(SIGILL, sigint_handler);
    signal(SIGSEGV, sigint_handler);
    
    // try to ensure cleanup before being killed due to resource limit
    signal(SIGXCPU, sigint_handler);
    signal(SIGXFSZ, sigint_handler);
}

sigset_t old_procmask;
static int nblocks = 0;

void block_sigint()
{
    sigset_t procmask;

    assert(nblocks==0);
    nblocks ++ ;
    
    sigemptyset(&procmask);
    sigaddset(&procmask, SIGINT);
    
    sigprocmask(SIG_BLOCK, &procmask, &old_procmask);
}

void unblock_sigint()
{
    assert( nblocks==1);
    nblocks--;
    
    sigprocmask(SIG_SETMASK, &old_procmask, NULL);
}

static PyObject* pyabc_internal_system_callback = 0;
static PyObject* pyabc_internal_tmpfile_callback = 0;
static PyObject* pyabc_internal_tmpfile_remove_callback = 0;

int Util_SignalSystem(const char* cmd)
{
    PyObject* arglist;
    PyObject* res;
    
    PyGILState_STATE gstate;

    long lres;
    
    if ( !pyabc_internal_system_callback )
            return -1;
            
    gstate = PyGILState_Ensure();
            
    arglist = Py_BuildValue("(O)", PyString_FromString(cmd));
    Py_INCREF(arglist);

    res = PyEval_CallObject( pyabc_internal_system_callback, arglist );
    Py_DECREF(arglist);

    if ( !res )
    {
        PyGILState_Release(gstate);
        return -1;
    }
    
    lres = PyInt_AsLong(res);
    Py_DECREF(res);

    PyGILState_Release(gstate);
    
    return lres;
}

int Util_SignalTmpFile(const char* prefix, const char* suffix, char** out_name)
{
    char* str;
    Py_ssize_t size;
    
    PyObject* arglist;
    PyObject* res;
    
    PyGILState_STATE gstate;
    
    *out_name = NULL;

    if ( !pyabc_internal_tmpfile_callback )
            return 0;
            
    gstate = PyGILState_Ensure();
            
    arglist = Py_BuildValue("(ss)", prefix, suffix);
    Py_INCREF(arglist);

    res = PyEval_CallObject( pyabc_internal_tmpfile_callback, arglist );
    Py_DECREF(arglist);

    if ( !res )
    {
        PyGILState_Release(gstate);
        return -1;
    }
    
    PyString_AsStringAndSize(res, &str, &size);
    
    *out_name = ABC_ALLOC(char, size+1);
    strcpy(*out_name, str);
    
    Py_DECREF(res);

    PyGILState_Release(gstate);
    
    return open(*out_name, O_WRONLY);
}

void Util_SignalTmpFileRemove(const char* fname, int fLeave)
{
    PyObject* arglist;
    PyObject* res;
    
    PyGILState_STATE gstate;

    if ( !pyabc_internal_tmpfile_remove_callback )
            return;
            
    gstate = PyGILState_Ensure();
            
    arglist = Py_BuildValue("(si)", fname, fLeave);
    Py_INCREF(arglist);

    res = PyEval_CallObject( pyabc_internal_tmpfile_remove_callback, arglist );
    Py_DECREF(arglist);
    Py_XDECREF(res);

    PyGILState_Release(gstate);
}

void pyabc_internal_set_util_callbacks( PyObject* system_callback, PyObject* tmpfile_callback, PyObject* tmpfile_remove_callback )
{
    Py_XINCREF(system_callback);
    Py_XDECREF(pyabc_internal_system_callback);

    pyabc_internal_system_callback = system_callback;

    Py_XINCREF(tmpfile_callback);
    Py_XDECREF(pyabc_internal_tmpfile_callback);

    pyabc_internal_tmpfile_callback = tmpfile_callback;

    Py_XINCREF(tmpfile_remove_callback);
    Py_XDECREF(pyabc_internal_tmpfile_remove_callback);

    pyabc_internal_tmpfile_remove_callback = tmpfile_remove_callback;
}

PyObject* _wait_no_hang()
{
    int status;
    int pid;
    
    pid = wait3(&status, WNOHANG, NULL);
    
    return Py_BuildValue("(iii)", pid, status, errno);
}

int _posix_kill(int pid, int signum)
{
    return kill(pid, signum);
}

void _set_death_signal()
{
    prctl(PR_SET_PDEATHSIG, SIGINT);
}

%}

%init 
%{
    Abc_Start();
%}

int n_ands();
int n_nodes();
int n_pis();
int n_pos();
int n_latches();
int n_levels();

int run_command(char* cmd);

int has_comb_model();
int has_seq_model();

int  n_bmc_frames();
int  prob_status();

int is_valid_cex();
int is_true_cex();
int  n_cex_pis();
int  n_cex_regs();
int  cex_po();
int  cex_frame();

int  n_phases();

Abc_Cex_t* _cex_get();
int _cex_get_vec_len();
Abc_Cex_t* _cex_get_vec(int i);
void _cex_put(Abc_Cex_t* pCex);
void _cex_free(Abc_Cex_t* pCex);
int _cex_n_regs(Abc_Cex_t* pCex);
int _cex_n_pis(Abc_Cex_t* pCex);
int _cex_get_po(Abc_Cex_t* pCex);
int _cex_get_frame(Abc_Cex_t* pCex);

PyObject* iso_eq_classes();

void pyabc_internal_set_command_callback( PyObject* callback );
void pyabc_internal_register_command( char * sGroup, char * sName, int fChanges );

void install_sigchld_handler(int sigint_fd);
void install_sigint_handler(int sigint_fd);

void block_sigint();
void unblock_sigint();

void pyabc_internal_set_util_callbacks( PyObject* system_callback, PyObject* tmpfile_callback, PyObject* tmpfile_remove_callback );

PyObject* _wait_no_hang();

void _set_death_signal();

int _posix_kill(int pid, int signum);
void _set_death_signal();

%pythoncode 
%{

class _Cex(object):

    def __init__(self, pCex):
        self.pCex = pCex
        
    def __del__(self):
        _cex_free(self.pCex)

    def n_regs(self):
        return _cex_n_regs(self.pCex)
        
    def n_pis(self):
        return _cex_n_pis(self.pCex)
    
    def get_po(self):
        return _cex_get_po(self.pCex)

    def get_frame(self):
        return _cex_get_frame(self.pCex)
       
def cex_get_vector():
    
    res = []
    
    for i in xrange(_cex_get_vec_len()):
        cex = _cex_get_vec(i)

        if cex is None:
            res.append(None)
        else:
            res.append(_Cex(cex))
    
    return res
       
def cex_get():

    cex = _cex_get()
    
    if cex is None:
        return None
        
    return _Cex(cex)

def cex_put(cex):

    assert cex is not None
    assert cex.pCex is not None
    
    return _cex_put(cex.pCex)
        
import threading
import select
import signal
import tempfile
import os
import errno
import sys, traceback
import subprocess

_active_lock = threading.Lock()
_die_flag = False

_active_pids = set()
_active_temp_files = set()

_terminated_pids_cond = threading.Condition(_active_lock)
_terminated_pids = {}

def add_temp_file(fname):
    with _active_lock:
        _active_temp_files.add(fname)
            
def remove_temp_file(fname):
    with _active_lock:
        _active_temp_files.remove(fname)
            
_old_os_wait3 = os.wait3
_select_select = select.select

def _retry_select(fd):
    while True:
        try:
            rrdy,_,_ = _select_select([fd],[],[])
            if fd in rrdy:
                return
        except select.error as e:
            if e[0] == errno.EINTR:
                continue
            raise

def _retry_read(fd):

    while True:
        try:
            return fd.read(1)
        except OSError as e:
            if e.errno == errno.EINTR:
                continue
            raise

def _retry_wait():

    while True:
        
        pid, status, e = _wait_no_hang()
        
        if pid>0:
            return pid, status
            
        elif pid==0:
            return 0,0
            
        elif pid == -1 and e == errno.ECHILD:
            return 0,0
            
        elif pid==-1 and e != errno.EINTR:
            raise OSError(e, 'unknown error in wait3()')

def _sigint_wait_thread_func(fd):

    global _die_flag
    
    while True:
        
        _retry_select(fd)
        _retry_read(fd) 

        with _active_lock:
        
            if _die_flag:
                os._exit(-1)
            
            _die_flag = True
        
            for pid in _active_pids:
                rc = _posix_kill(pid, signal.SIGINT)
    
            for fname in _active_temp_files:
                os.remove(fname)

            os._exit(-1)

def _child_wait_thread_func(fd):

    while True:
    
        _retry_select(fd)
        rc = _retry_read(fd)
                
        with _active_lock:
        
            while True:
            
                pid, status = _retry_wait()

                if pid==0:
                    break
                    
                if pid in _active_pids:
                    _active_pids.remove(pid)
                    
                _terminated_pids[pid] = status
                _terminated_pids_cond.notifyAll()

_sigint_pipe_read_fd = -1
_sigint_pipe_write_fd = -1

_sigchld_pipe_read_fd = -1
_sigchld_pipe_write_fd = -1

def _start_threads():

    global _sigint_pipe_read_fd, _sigint_pipe_write_fd
    
    _sigint_pipe_read_fd, _sigint_pipe_write_fd = os.pipe()
    sigint_read = os.fdopen(_sigint_pipe_read_fd, "r", 0 )
    
    sigint_wait_thread = threading.Thread(target=_sigint_wait_thread_func, name="SIGINT wait thread", args=(sigint_read,))
    sigint_wait_thread.setDaemon(True)
    sigint_wait_thread.start()
    
    install_sigint_handler(_sigint_pipe_write_fd)
    
    global _sigchld_pipe_read_fd, _sigchld_pipe_write_fd
  
    _sigchld_pipe_read_fd, _sigchld_pipe_write_fd = os.pipe()
    sigchld_read = os.fdopen(_sigchld_pipe_read_fd, "r", 0 )
    
    child_wait_thread = threading.Thread(target=_child_wait_thread_func, name="child process wait thread", args=(sigchld_read,))
    child_wait_thread.setDaemon(True)
    child_wait_thread.start()
    
    install_sigchld_handler(_sigchld_pipe_write_fd)

_close_on_fork = []

def close_on_fork(fd):
    _close_on_fork.append(fd)

def after_fork():

    _set_death_signal()

    global _close_on_fork

    for fd in _close_on_fork:
        os.close(fd)
        
    _close_on_fork = []

    os.close(_sigint_pipe_read_fd)
    os.close(_sigint_pipe_write_fd)
    
    os.close(_sigchld_pipe_read_fd)
    os.close(_sigchld_pipe_write_fd)
   
    global _active_lock
    _active_lock = threading.Lock()

    global _terminated_pids_cond
    _terminated_pids_cond = threading.Condition(_active_lock)
    
    global _terminated_pids
    _terminated_pids = {}
    
    global _active_pids
    _active_pids = set()
    
    global _active_temp_files
    _active_temp_files = set()
    
    _start_threads()

class _sigint_block_section(object):
    def __init__(self):
        self.blocked = False
        
    def __enter__(self):
        block_sigint()
        self.blocked = True
        
    def __exit__(self, type, value, traceback):
        self.release()
        
    def release(self):
        if self.blocked:
            self.blocked = False
            unblock_sigint()

_old_os_fork = os.fork

def _fork():

    ppid = os.getpid()

    with _sigint_block_section() as cs:
    
        with _active_lock:
        
            if _die_flag:
                os._exit(-1)
    
            pid = _old_os_fork()
    
            if pid == 0:
                after_fork()
            
            if pid > 0:
                _active_pids.add(pid)  
    
            return pid
    
def _waitpid(pid, options=0):
    
    while True:
    
        with _active_lock:
        
            if pid in _terminated_pids:
                status = _terminated_pids[pid]
                del _terminated_pids[pid]
                return pid, status
            
            if options==os.WNOHANG:
                return 0, 0
                
            _terminated_pids_cond.wait()

def _wait(options=0):

    while True:
        
        with _active_lock:
        
            for pid, status in _terminated_pids.iteritems():
                del _terminated_pids[pid]
                return pid, status
            
            if options==os.WNOHANG:
                return 0, 0
                
            _terminated_pids_cond.wait()

_old_os_kill = os.kill

def _kill(pid, sig):

    with _active_lock:
    
        if pid in _terminated_pids:
            return None
            
        return _old_os_kill(pid,sig)
    
os.kill = _kill
os.fork = _fork
os.wait = _wait
os.waitpid = _waitpid

def _split_command_line(cmd):
    
    args = []
    
    i=0
    
    while i<len(cmd):
        
        while i<len(cmd) and cmd[i] in [' ','\t','\f']:
            i += 1
            
        if i >= len(cmd):
            break
            
        arg = []
        
        in_quotes = None

        while i<len(cmd):
            
            if not in_quotes and cmd[i] in ['\'','\"','\'']:
                in_quotes = cmd[i]
                
            elif in_quotes and cmd[i]==in_quotes:
                in_quotes = None
                
            elif cmd[i] == '\\' and i<(len(cmd)+1):
                
                i += 1
                
                if cmd[i]=='\\':
                    arg.append('\\')
                elif cmd[i]=='\'':
                    arg.append('\'')
                elif cmd[i]=='\"':
                    arg.append('\'')
                elif cmd[i]=='\"':
                    arg.append('\"')
                elif cmd[i]=='a':
                    arg.append('\a')
                elif cmd[i]=='b':
                    arg.append('\b')
                elif cmd[i]=='n':
                    arg.append('\n')
                elif cmd[i]=='f':
                    arg.append('\f')
                elif cmd[i]=='r':
                    arg.append('\r')
                elif cmd[i]=='t':
                    arg.append('\t')
                elif cmd[i]=='v':
                    arg.append('\v')
                else:
                    arg.append(cmd[i])
                    
            elif not in_quotes and cmd[i] in [' ','\t','\f']:
                break
                
            else:
                arg.append(cmd[i])
                
            i += 1
        
        args.append( "".join(arg) )
    
    return args


def system(cmd):

    args = _split_command_line(cmd)
    
    if args[-2] == '>':
    
        with open(args[-1],'w') as fout:
            p = subprocess.Popen(args[:-2], stdout=fout)
            rc = p.wait()
            return rc
         
    else:
        p = subprocess.Popen(args)
        return p.wait()

def tmpfile(prefix, suffix):

    with _active_lock:
        with tempfile.NamedTemporaryFile(delete=False, prefix=prefix, suffix=suffix) as file:
            _active_temp_files.add(file.name)
            return file.name
       
def tmpfile_remove(fname, leave):

    with _active_lock:
        os.remove(fname)
        _active_temp_files.remove(fname) 

pyabc_internal_set_util_callbacks( system, tmpfile,tmpfile_remove )


_start_threads()


_registered_commands = {}

def _cmd_callback(args):
    try:
        assert len(args) > 0
        
        cmd = args[0]
        assert cmd in _registered_commands
    
        res = _registered_commands[cmd](args)
        
        assert type(res) == int, "User-defined Python command must return an integer."
        
        return res
    
    except Exception, e:
        import traceback
        traceback.print_exc()

    except SystemExit, se:
        pass
            
    return 0
    
pyabc_internal_set_command_callback( _cmd_callback )
    
def add_abc_command(fcmd, group, cmd, change):
    _registered_commands[ cmd ] = fcmd
    pyabc_internal_register_command( group, cmd, change)

import optparse

xxx = {} 

def cmd_python(cmd_args):
    
    usage = "usage: %prog [options] <Python files>"
    
    parser = optparse.OptionParser(usage, prog="python")
    
    parser.add_option("-c", "--cmd", dest="cmd", help="Execute Python command directly")
    parser.add_option("-v", "--version", action="store_true", dest="version", help="Display Python Version")

    options, args = parser.parse_args(cmd_args)
    
    if options.version:
        print sys.version
        return 0
    
    if options.cmd:
        exec options.cmd in xxx
        return 0
    
    scripts_dir = os.getenv('ABC_PYTHON_SCRIPTS', ".")
    scripts_dirs = scripts_dir.split(':')
    
    for fname in args[1:]:
        if os.path.isabs(fname):
            execfile(fname, xxx)
        else:
            for d in scripts_dirs:
                fname = os.path.join(scripts_dir, fname)
                if os.path.exists(fname):
                    execfile(fname, xxx)
                    break
    
    return 0
    
add_abc_command(cmd_python, "Python", "python", 0) 

%}
