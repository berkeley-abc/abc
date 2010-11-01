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
    
#include <main.h>
#include <stdlib.h>
#include <signal.h>

void sigint_signal_handler(int sig)
{
    _exit(1);
}

    
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

int n_pis()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    if ( pNtk && Abc_NtkIsStrash(pNtk) )
    {        
        return Abc_NtkPiNum(pNtk);
    }

    return -1;
}


int n_pos()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    if ( pNtk && Abc_NtkIsStrash(pNtk) )
    {        
        return Abc_NtkPoNum(pNtk);
    }

    return -1;
}

int n_latches()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    if ( pNtk && Abc_NtkIsStrash(pNtk) )
    {        
        return Abc_NtkLatchNum(pNtk);
    }

    return -1;
}

int run_command(char* cmd)
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    int fStatus = Cmd_CommandExecute(pAbc, cmd);
    
    return fStatus;
}

bool has_comb_model()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    return pNtk && pNtk->pModel;
}

bool has_seq_model()
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

bool is_valid_cex()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    return pNtk && Abc_FrameReadCex(pAbc) && Abc_NtkIsValidCex( pNtk, Abc_FrameReadCex(pAbc) );
}

bool is_true_cex()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    return pNtk && Abc_FrameReadCex(pAbc) && Abc_NtkIsTrueCex( pNtk, Abc_FrameReadCex(pAbc) );
}

int n_cex_pis()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();

    return Abc_FrameReadCex(pAbc) ? Abc_FrameReadCexPiNum( Abc_FrameReadCex(pAbc) ) : -1;
}

int n_cex_regs()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();

    return Abc_FrameReadCex(pAbc) ? Abc_FrameReadCexRegNum( Abc_FrameReadCex(pAbc) ) : -1;
}

int cex_po()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();

    return Abc_FrameReadCex(pAbc) ? Abc_FrameReadCexPo( Abc_FrameReadCex(pAbc) ) : -1;
}

int cex_frame()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();

    return Abc_FrameReadCex(pAbc) ? Abc_FrameReadCexFrame( Abc_FrameReadCex(pAbc) ) : -1;
}

int n_phases()
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    return pNtk ? Abc_NtkPhaseFrameNum(pNtk) : 1;
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
	long lres;
	
	if ( !pyabc_internal_python_command_callback )
		return 0;
		
	args = PyList_New(argc);
	
	for( i=0 ; i<argc ; i++ )
		PyList_SetItem(args, i, PyString_FromString(argv[i]) );

	arglist = Py_BuildValue("(O)", args);
	Py_INCREF(arglist);

	res = PyEval_CallObject( pyabc_internal_python_command_callback, arglist );
	Py_DECREF(arglist);

	lres = PyInt_AsLong(res);
	Py_DECREF(res);
	
	return lres;
}

void pyabc_internal_register_command( char * sGroup, char * sName, int fChanges )
{
    Abc_Frame_t* pAbc = Abc_FrameGetGlobalFrame();

	Cmd_CommandAdd( pAbc, sGroup, sName, (void*)pyabc_internal_abc_command_callback, fChanges);
}

%}

%init 
%{
    Abc_Start();
    signal(SIGINT, sigint_signal_handler);
%}

int n_ands();
int n_pis();
int n_pos();
int n_latches();

int run_command(char* cmd);

bool has_comb_model();
bool has_seq_model();

int  n_bmc_frames();
int  prob_status();

bool is_valid_cex();
bool is_true_cex();
int  n_cex_pis();
int  n_cex_regs();
int  cex_po();
int  cex_frame();

int  n_phases();

void pyabc_internal_set_command_callback( PyObject* callback );
void pyabc_internal_register_command( char * sGroup, char * sName, int fChanges );

%pythoncode 
%{

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
		print "Python error: ", e

	except SystemExit, se:
		pass
		
	return 0
    
pyabc_internal_set_command_callback( _cmd_callback )
    
def add_abc_command(fcmd, group, cmd, change):
    _registered_commands[ cmd ] = fcmd
    pyabc_internal_register_command( group, cmd, change)

import sys
import optparse
import os.path

import __main__

def cmd_python(cmd_args):
    global __main__
    
    usage = "usage: %prog [options] <Python files>"
    
    parser = optparse.OptionParser(usage)
    
    parser.add_option("-c", "--cmd", dest="cmd", help="Execute Python command directly")
    parser.add_option("-v", "--version", action="store_true", dest="version", help="Display Python Version")

    options, args = parser.parse_args(cmd_args)
    
    if options.version:
        print sys.version
        return 0
    
    if options.cmd:
        exec options.cmd in __main__.__dict__
        return 0
    
    scripts_dir = os.getenv('ABC_PYTHON_SCRIPTS', ".")
    scripts_dirs = scripts_dir.split(':')
    
    for fname in args[1:]:
        if os.path.isabs(fname):
            execfile(fname, __main__.__dict__)
        else:
            for d in scripts_dirs:
                fname = os.path.join(scripts_dir, fname)
                if os.path.exists(fname):
                    execfile(fname, __main__.__dict__)
                    break
    
    return 0
    
add_abc_command(cmd_python, "Python", "python", 0) 

%}
