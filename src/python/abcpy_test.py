# You can use 'from pyabc import *' and then not need the pyabc. prefix everywhere
import pyabc

# A new command is just a function that accepts a list of string arguments
#   The first argument is always the name of the command
#   It MUST return an integer. -1: user quits, -2: error. Return 0 for success.

# a simple command that just prints its arguments and returns success
def pytest1_cmd(args):
    print args
    return 0

# registers the command:
#   The first argument is the function
#   The second argument is the category (mainly for the ABC help command)
#   The third argument is the new command name
#   Keet the fourth argument 0, or consult with Alan
pyabc.add_abc_command(pytest1_cmd, "Python-Test", "pytest1", 0)

# a simple command that just prints its arguments and runs the command 'scorr -h'
def pytest2_cmd(args):
    print args
    pyabc.run_command('scorr -h')
    return 0

pyabc.add_abc_command(pytest2_cmd, "Python-Test", "pytest2", 0)

# Now a more complicated command with argument parsing
# This command gets two command line arguments -c and -v. -c cmd runs the command 'cmd -h' and -v prints the python version
# for more details see the optparse module: http://docs.python.org/library/optparse.html

import optparse

def pytest3_cmd(args):
    usage = "usage: %prog [options]"
    
    parser = optparse.OptionParser(usage, prog="pytest3")
    
    parser.add_option("-c", "--cmd", dest="cmd", help="command to ask help for")
    parser.add_option("-v", "--version", action="store_true", dest="version", help="display Python Version")

    options, args = parser.parse_args(args)
    
    if options.version:
        print sys.version
        return 0
    
    if options.cmd:
        pyabc.run_command("%s -h"%options.cmd)
        return 0
    
    return 0

pyabc.add_abc_command(pytest3_cmd, "Python-Test", "pytest3", 0)
