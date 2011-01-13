"""

A simple context manager for redirecting streams in Python. 
The streams are redirected at the the C runtime level so that the output of C extensions
that use stdio will also be redirected.

null_file : a stream representing the null device (e.g. /dev/null on Unix)
redirect: a context manager for redirecting streams

Author: Baruch Sterin (sterin@berkeley.edu)

"""

import os
import sys

from contextlib import contextmanager

null_file = open( os.devnull, "w" )

@contextmanager
def _dup( f ):
    fd = os.dup( f.fileno() )
    yield fd
    os.close(fd)
    
@contextmanager
def redirect(dst = null_file, src = sys.stdout):
    
    """
    Redirect the src stream into dst.
    
    Example:
        with redirect( open("somefile.txt", sys.stdout ) ):
            do some stuff ...        
    """

    if src.fileno() == dst.fileno():
        yield 
        return
        
    with _dup( src ) as fd_dup_src:

        dst.flush()
        
        src.flush()
        os.close( src.fileno() )
        os.dup2( dst.fileno(), src.fileno() )

        yield

        src.flush()
        os.close( src.fileno() )
        os.dup2( fd_dup_src, src.fileno() ) 

def start_redirect(dst = null_file, src = sys.stdout):
    
    """
    Start redirection of src stream into dst. Return the duplicated file handle of the source.
    
    Example:
        fd = start_redirect( open("somefile.txt"), sys.stdout )
            ... do some stuff ...        
        end_redirect(sys.stdout, fd)
    """

    if src.fileno() == dst.fileno():
        return None
        
    fd_dup_src = os.dup( src.fileno() )
    
    dst.flush()
    src.flush()

    os.close( src.fileno() )
    os.dup2( dst.fileno(), src.fileno() )
    
    return fd_dup_src

def end_redirect(src, fd_dup_src):
    
    """
    End redirection of stream src.Redirect the src stream into dst. src is the source stream and fd_dup_src is the value returned by
    start_redirect()
    """

    if fd_dup_src is None:
        return

    src.flush()
    os.close( src.fileno() )
    os.dup2( fd_dup_src, src.fileno() ) 
    
    os.close(fd_dup_src)
