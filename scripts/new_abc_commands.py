import sys
import os
import pyabc
import par
import tempfile
import shutil
import redirect
import optparse

def read_cmd(args):
    if len(args)==2:
        par.read_file_quiet(args[1])
    else:
        par.read_file()
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

def proof_command_wrapper(prooffunc, category_name, command_name, change):

    def wrapper(argv):
        
        usage = "usage: %prog [options] <aig_file>"
    
        parser = optparse.OptionParser(usage, prog=command_name)
    
        parser.add_option("-n", "--no_redirect", dest="noisy", action="store_true", default=False, help="don't redirect output")
        parser.add_option("-d", "--current_dir", dest="current_dir", action="store_true", default=False, help="stay in current directory")

        options, args = parser.parse_args(argv)
        
        if len(args) != 2:
            print args
            parser.print_usage()
            return 0
            
        aig_filename = os.path.abspath(args[1])

        if not options.noisy:
            pyabc.run_command('/pushredirect')
            
        if not options.current_dir:
            pyabc.run_command('/pushdtemp')
            
        try:
            for d in os.environ['PATH'].split(':'):
                bip = os.path.join(d, 'bip')
                if os.path.exists(bip):
                    pyabc.run_command("load_plugin %s Bip"%bip)
                    break

            basename = os.path.basename( aig_filename )
            shutil.copyfile(aig_filename, basename)
            aig_filename = basename

            par.read_file_quiet(aig_filename)
            result = prooffunc()
            
            par.cex_list = []
        except:
            result = None

        if not options.current_dir:
            pyabc.run_command('/popdtemp')

        if not options.noisy:
            pyabc.run_command('/popredirect')
                
        if result=="SAT":
            print 1
        elif result=="UNSAT":
            print 0
        else:
            print 2

        return 0
    
    pyabc.add_abc_command(wrapper, category_name, command_name, change)

proof_command_wrapper(par.super_prove,  'HWMCC11', '/super_prove_aiger',  0)
proof_command_wrapper(par.simple_prove, 'HWMCC11', '/simple_prove_aiger', 0)
proof_command_wrapper(par.simple_bip,   'HWMCC11', '/simple_bip_aiger',   0)
