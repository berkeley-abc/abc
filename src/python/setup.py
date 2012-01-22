import sys

from distutils.core import setup, Extension
from distutils.sysconfig import get_config_vars
from distutils import util

define_macros = []
libraries = []
library_dirs = []

if sys.platform == "win32":
    
    src_file = [ 'pyabc.i' ]
    
    define_macros.append( ('WIN32', 1) )
    define_macros.append( ('ABC_DLL', 'ABC_DLLEXPORT') )
    
    libraries.append('abcr')
    library_dirs.append('./../../lib')

else:

    src_file = [ 'pyabc_wrap.c' ]
    
    if get_config_vars()['SIZEOF_VOID_P'] > 4:
        define_macros.append( ('LIN64', 1) )
    else:
        define_macros.append( ('LIN', 1) )

    libraries.append( 'abc' )
    libraries.append( 'readline' )
    library_dirs.append('./../../')

ext = Extension(
    '_pyabc',
    src_file,
    define_macros=define_macros,
    include_dirs = ["../.."],
    library_dirs=library_dirs,
    libraries=libraries
    )

setup(
    name='pyabc',
    version='1.0',
    ext_modules=[ext],
    py_modules=['pyabc','getch','pyabc_split','redirect', 'reachx_cmd']
)
