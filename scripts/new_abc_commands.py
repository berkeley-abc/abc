
# You can use 'from pyabc import *' and then not need the pyabc. prefix everywhere

import os
import pyabc
import abc_common
import tempfile
import shutil
import redirect

# A new command is just a function that accepts a list of string arguments
#   The first argument is always the name of the command
#   It MUST return an integer. -1: user quits, -2: error. Return 0 for success.

# a command that calls prove(1) and returns success
def prove_cmd(args):
    result = abc_common.prove(1)
    print result
    return 0

# registers the command:
#   The first argument is the function
#   The second argument is the category (mainly for the ABC help command)
#   The third argument is the new command name
#   Keep the fourth argument 0, or consult with Alan

pyabc.add_abc_command(prove_cmd, "ZPython", "/prove", 0)

def read_cmd(args):
    if len(args)==2:
        abc_common.read_file_quiet(args[1])
    else:
        abc_common.read_file()
    return 0

pyabc.add_abc_command(read_cmd, "ZPython", "/rf", 0)

def chdir_cmd(args):
    os.chdir( args[1] )
    return 0

pyabc.add_abc_command(chdir_cmd, "ZPython", "/cd", 0)

def pwd_cmd(args):
    print os.getcwd()
    return 0

pyabc.add_abc_command(pwd_cmd, "ZPython", "/pwd", 0)

def ls_cmd(args):
    os.system("ls " + " ".join(args[1:]))
    return 0

pyabc.add_abc_command(ls_cmd, "ZPython", "/ls", 0)

pushd_temp_stack = []

def pushdtemp_cmd(args):
    tmpdir = tempfile.mkdtemp()
    pushd_temp_stack.append( (os.getcwd(), tmpdir) )
    os.chdir(tmpdir)
    return 0
    
pyabc.add_abc_command(pushdtemp_cmd, "ZPython", "/pushdtemp", 0)

def popdtemp_cmd(args):
    prev, temp = pushd_temp_stack.pop()
    os.chdir(prev)
    shutil.rmtree(temp, ignore_errors=True)
    return 0
    
pyabc.add_abc_command(popdtemp_cmd, "ZPython", "/popdtemp", 0)

pushredirect_stack = []

def push_redirect_cmd(args):
    fdout = redirect.start_redirect( redirect.null_file, sys.stdout)
    pushredirect_stack.append( (sys.stdout, fdout) )
    
    fderr = redirect.start_redirect( redirect.null_file, sys.stderr)
    pushredirect_stack.append( (sys.stderr, fderr) )
    
    return 0
    
pyabc.add_abc_command(push_redirect_cmd, "ZPython", "/pushredirect", 0)

def pop_redirect_cmd(args):
    err, fderr = pushredirect_stack.pop()
    redirect.end_redirect(err, fderr)
 
    out, fdout = pushredirect_stack.pop()
    redirect.end_redirect(out, fdout)
    
    return 0
    
pyabc.add_abc_command(pop_redirect_cmd, "ZPython", "/popredirect", 0)

def print_aiger_result(args):
    status = pyabc.prob_status()
    
    if status==1:
        print 0
    elif status==0:
        print 1
    else:
        print 2
    
    return 0
    
pyabc.add_abc_command(print_aiger_result, "ZPython", "/print_aiger_result", 0)

def super_prove_aiger_cmd(args):

    noisy = len(args)==2 and args[1]=='-n'

    if not noisy:
        pyabc.run_command('/pushredirect')
        pyabc.run_command('/pushdtemp')
    
    try:
        result = abc_common.super_prove()
    except:
        result = None
    
    if not noisy:
        pyabc.run_command('/popdtemp')
        pyabc.run_command('/popredirect')
            
    if result=="SAT":
        print 1
    elif result=="UNSAT":
        print 0
    else:
        print 2

    return 0
    
pyabc.add_abc_command(super_prove_aiger_cmd, "ZPython", "/super_prove_aiger", 0)


def prove_one_by_one_cmd(args):
    
    noisy = len(args)==2 and args[1]=='-n'

    # switch to a temporary directory
    pyabc.run_command('/pushdtemp')
    
    # write a copy of the original file in the temporary directory
    pyabc.run_command('w original_aig_file.aig')
    
    # iterate through the ouptus
    for po in range(0, pyabc.n_pos()):
        
        if not noisy:
            pyabc.run_command('/pushredirect')

        # replace the nework with the cone of the current PO
        pyabc.run_command( 'cone -O %d -s'%po )

        # run super_prove
        try:
            result = abc_common.super_prove()
        except:
            result = 'UNKNOWN'

        if not noisy:
            pyabc.run_command('/popredirect')

        print 'PO %d is %s'%(po, result)
        
        # stop if the result is not UNSAT
        if result != "UNSAT":
            break

        # read the original file for the next iteration
        pyabc.run_command('r original_aig_file.aig')
        
    # go back to the original directory
    pyabc.run_command('/popdtemp')

    return 0
    
pyabc.add_abc_command(prove_one_by_one_cmd, "ZPython", "/prove_one_by_one", 0)
