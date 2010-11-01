# You can use 'from pyabc import *' and then not need the pyabc. prefix everywhere

import sys
import optparse
import subprocess
import tempfile
import threading
import os
import os.path
from contextlib import contextmanager, nested

import pyabc


def wait_with_timeout(p, timeout):
    """ Wait for a subprocess.Popen object to terminate, or until timeout (in seconds) expires. """

    if timeout <= 0:
        timeout = None
    
    t = threading.Thread(target=lambda: p.wait())
    t.start()
    
    t.join(timeout)
    
    if t.is_alive():
        p.kill()
    
    t.join()
    
    return p.returncode

@contextmanager
def replace_sys_argv(argv):
    if 'argv' in sys.__dict__:
        old_argv = sys.argv
        sys.argv = argv
        yield
        sys.argv = old_argv
    else:
        sys.argv = argv
        yield
        del sys.argv

@contextmanager
def temp_file_name(suffix=""):
    file = tempfile.NamedTemporaryFile(delete=False, suffix=suffix)
    name = file.name
    file.close()

    try:
        yield name
    finally:
        os.unlink(name)

def cygpath(path):
    if sys.platform == "win32":
        if os.path.isabs(path):
            drive, tail = os.path.splitdrive(path)
            drive = drive.lower()
            tail = tail.split(os.path.sep)
            return '/cygdrive/%s'%drive[0] + '/'.join(tail) 
        else:
            path = path.split(os.path.sep)
            return "/".join(path)
    return path

def run_reachx_cmd(effort, timeout):
    with nested(temp_file_name(suffix=".aig"), temp_file_name()) as (tmpaig_name, tmplog_name):
        pyabc.run_command("write %s"%tmpaig_name)
        
        cmdline = [ 
            'read %s'%cygpath(tmpaig_name),
            'qua_ffix -effort %d -L %s'%(effort, cygpath(tmplog_name)),
            'quit'
            ]
            
        cmd = ["jabc", "-c", " ; ".join(cmdline)]
        
        p = subprocess.Popen(cmd, shell=False, stdout=sys.stdout, stderr=sys.stderr)
        
        rc = wait_with_timeout(p,timeout)
        
        if rc != 0:
            # jabc failed or stopped. Write a status file to update the status to unknown
            with open(tmplog_name, "w") as f:
                f.write('snl_UNK -1 unknown\n')
                f.write('NULL\n')
                f.write('NULL\n')
            
        pyabc.run_command("read_status %s"%tmplog_name)
        
        return rc

def reachx_cmd(argv):
    usage = "usage: %prog [options]"
    
    parser = optparse.OptionParser(usage)
    
    parser.add_option("-e", "--effort", dest="effort", type=int, default=0, help="effort level. [default=0, means unlimited]")
    parser.add_option("-t", "--timeout", dest="timeout", type=int, default=0, help="timeout in seconds [default=0, unlimited]")

    with replace_sys_argv(argv):
        options, args = parser.parse_args()

    rc = run_reachx_cmd(options.effort, options.timeout)
    print "%s command: jabc returned: %d"%(argv[0], rc)
    
    return 0

pyabc.add_abc_command(reachx_cmd, "Verification", "reachx", 0)
