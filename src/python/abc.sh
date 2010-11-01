#!/bin/sh
#
# Setup the ABC/Py environment and run the ABC/Py executable
# (ABC/Py stands for ABC with embedded Python)
#
# ABC/Py expects the following directory structure
#
# abc_root/
#   bin/
#     abc - this script
#     abc_exe - the ABC executable
#      ... - Other scripts
#   lib/
#     pyabc.py - support file for pyabc extension
#     python_library.zip - The Python standard library. Only if not using the system Python interpreter.
#     *.so - Python extensions, Only if not using the system Python interpreter.
#   scripts/
#     *.py - default directory for python scripts
#             

# usage: abspath <dir>
# get the absolute path of <dir>
abspath()
{
    cwd="$(pwd)"
    cd "$1"
    echo "$(pwd)"
    cd "${cwd}"
}

self=$0

self_dir=$(dirname "${self}")
self_dir=$(abspath "${self_dir}")

abc_root=$(dirname "${self_dir}")

abc_exe="${abc_root}/bin/abc_exe"

PYTHONPATH="${abc_root}/lib":"${PYTHONPATH}"
export PYTHONPATH

if [ -d "${abc_root}/scripts" ] ; then
    ABC_PYTHON_SCRIPTS="${abc_root}/scripts"
    export ABC_PYTHON_SCRIPTS
    
    PYTHONPATH="${ABC_PYTHON_SCRIPTS}":"${PYTHONPATH}"
    export PYTHONPATH
fi

if [ -f "${abc_root}/scripts/abc.rc" ] ; then
    ABC_PYTHON_ABC_RC="${abc_root}/scripts/abc.rc"
    export ABC_PYTHON_ABC_RC
fi

if [ -f "${abc_root}/lib/python_library.zip" ] ; then
    PYTHONHOME="${abc_root}"
    export PYTHONHOME
    
    PYTHONPATH="${abc_root}/lib/python_library.zip":"${PYTHONPATH}"
    export PYTHONPATH
fi

PATH="${abc_root}/bin:$PATH"
export PATH

if [ "$1" = "--debug" ]; then
    shift
    abc_debugger="$1"
    shift
    
    echo export PYTHONHOME=$PYTHONHOME
    echo export PYTHONPATH=$PYTHONPATH
    echo export ABC_PYTHON_SCRIPTS=$ABC_PYTHON_SCRIPTS
    echo export ABC_PYTHON_ABC_RC=$ABC_PYTHON_ABC_RC
fi

exec ${abc_debugger} "${abc_exe}" "$@"
