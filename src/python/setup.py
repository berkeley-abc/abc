import sys

from distutils.core import setup, Extension
from distutils.sysconfig import get_config_vars
from distutils import util
from distutils.command.build_ext import build_ext
from distutils import sysconfig

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


# ugly hack to silence strict-prototype warnings

class build_ext_subclass( build_ext ):
    
    def build_extensions(self):
        
        CC = sysconfig.get_config_var("CC")
        
        if self.compiler.compiler_type == 'unix' and ( 'gcc' in CC or 'g++' in CC):
            for e in self.extensions:
                e.extra_compile_args.append( '-Wno-strict-prototypes' )
                
        build_ext.build_extensions(self)

ext = Extension(
    '_pyabc',
    src_file,
    define_macros=define_macros,
    include_dirs = ["../../src"],
    library_dirs=library_dirs,
    libraries=libraries
    )

setup(
    name='pyabc',
    version='1.0',
    ext_modules=[ext],
    py_modules=['pyabc','getch','pyabc_split','redirect', 'reachx_cmd'],
    cmdclass = {'build_ext': build_ext_subclass }
)
