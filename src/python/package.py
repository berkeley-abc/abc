import os
import sys
import optparse
import zipfile
import tarfile
import tempfile
import time
import py_compile

def zip_library(f, extra_files = []):
    lib = "%s/lib/python%s/"%(sys.prefix,sys.version[:3])
    
    zf = zipfile.ZipFile(f, "w", zipfile.ZIP_DEFLATED)
    
    for root, _, files in os.walk(lib):
        arcroot = os.path.relpath(root, lib)
        for f in files:
            _, ext = os.path.splitext(f)
            if ext in ['.py']:
                zf.write(os.path.join(root,f), os.path.join(arcroot, f))

    for s, r in extra_files:
        zf.write( s, r )

    zf.close()
    
def add_python_lib(tf, lib_dir, lib, mtime):

    _, prefix = os.path.split(lib)
    
    for root, _, files in os.walk(lib):

        relpath = os.path.relpath(root, lib)

        if '.hg' in relpath.split('/'):
            continue

        if relpath=='.':
            arcroot = lib_dir
        else:
            arcroot = os.path.join( lib_dir, os.path.relpath(root, lib) )

        arcroot = os.path.join(arcroot, prefix)

        add_dir(tf, arcroot, mtime)
        
        for f in files:
            _, ext = os.path.splitext(f)
            if ext in ['.py', '.so']:
                add_file( tf, os.path.join(root,f), os.path.join(arcroot, f), 0666, mtime)

def add_dir(tf, dir, mtime):
    ti = tarfile.TarInfo(dir)
    ti.mode = 0777
    ti.mtime = mtime
    ti.type = tarfile.DIRTYPE
    
    tf.addfile(ti)

def add_fileobj(tf, f, arcname, mode, mtime):
    ti = tarfile.TarInfo(arcname)
    ti.mode = mode
    ti.mtime = mtime
    
    f.seek(0, os.SEEK_END)
    ti.size = f.tell()
    
    f.seek(0, os.SEEK_SET)
    tf.addfile(ti, f)
    
def add_file(tf, fname, arcname, mode, mtime):
    print "\t adding %s as %s"%(fname, arcname)
    
    with open(fname, "rb") as f:
        add_fileobj(tf, f, arcname, mode, mtime)

def package(pyabc_dir, extra_bin, extra_lib, extra_files, abc_exe, abc_sh, pyabc, ofname, scripts_dir, use_sys):
    
    mtime = time.time()
    
    tf = tarfile.open(ofname, "w:gz")
    
    add_dir(tf, "%s"%pyabc_dir, mtime)
    
    add_dir(tf, "%s/bin"%pyabc_dir, mtime)
    
    add_file(tf, abc_exe, "%s/bin/abc_exe"%pyabc_dir, 0777, mtime)
    add_file(tf, abc_sh, "%s/bin/abc"%pyabc_dir, 0777, mtime)

    if scripts_dir:
        for fn in os.listdir(scripts_dir):
            if fn.startswith('.'):
                continue
            fullname = os.path.join(scripts_dir, fn)
            if os.path.isfile(fullname):
                fnroot, fnext = os.path.splitext(fn)
                if fnext==".sh":
                    add_file( tf, fullname, os.path.join("%s/bin"%pyabc_dir, fnroot), 0777, mtime)
                elif fnext not in ( '.pyc', '.pyo'):
                    add_file( tf, fullname, os.path.join("%s/scripts"%pyabc_dir, fn), 0666, mtime)
    
    for bin in extra_bin:
        add_file( tf, bin, os.path.join("%s/bin"%pyabc_dir, os.path.basename(bin)), 0777, mtime)
        
    lib_dir = "%s/lib"%pyabc_dir

    add_dir(tf, lib_dir, mtime)

    for lib in extra_lib:
        add_python_lib( tf, lib_dir, lib, mtime)
    
    for file, dest in extra_files:
        add_file(tf, file, '%s/%s'%(pyabc_dir, dest), 0666, mtime)
    
    for entry in os.listdir(pyabc):
        if entry.endswith('.py'):
            add_file( tf, os.path.join(pyabc, entry), os.path.join("%s/lib"%pyabc_dir, entry), 0666, mtime)
    
    if not use_sys:
        # ZIP standard library    
        zf = tempfile.NamedTemporaryFile("w+b")
        #zip_library(zf, [(pyabc, "pyabc.py")])
        zip_library(zf, [])
        zf.flush()
        
        add_fileobj(tf, zf, "%s/lib/python_library.zip"%pyabc_dir, 0666, mtime)
        
        zf.close()
    
        # add all extensions
        
        lib_dynload = os.path.join(sys.exec_prefix,"lib", "python%s"%sys.version[:3], "lib-dynload")
        
        for fn in os.listdir(lib_dynload):
            fullname = os.path.join(lib_dynload, fn)
            if os.path.isfile(fullname):
                add_file( tf, fullname, os.path.join("%s/lib"%pyabc_dir, fn), 0666, mtime)
    
    tf.close()


def main(args):
    
    usage = "usage: %prog [options]"

    parser = optparse.OptionParser(usage)

    parser.add_option("-d", "--pyabc_dir", dest="pyabc_dir", help="name of generated directory" )
    parser.add_option("-b", "--extra_bin", dest="extra_bin", help="extra binaries to pack" )
    parser.add_option("-l", "--extra_lib", dest="extra_lib", help="extra directories in lib to pack" )
    parser.add_option("-f", "--extra_files", dest="extra_files", help="additional files (comma separated pairs of file:dest" )
    parser.add_option("-a", "--abc", dest="abc", help="location of the ABC exeutable")
    parser.add_option("-s", "--abc_sh", dest="abc_sh", help="location of the ABC setup script")
    parser.add_option("-p", "--pyabc", dest="pyabc", help="location of pyabc.py")
    parser.add_option("-o", "--out", dest="out", help="location of output tar gzipped file")
    parser.add_option("-x", "--scripts", dest="scripts", default="scripts", help="location of scripts")
    parser.add_option("-S", "--system", action="store_false", dest="sys", default=True, help="use default python installation")

    options, args = parser.parse_args(args)

    if len(args) > 1:
        parser.print_help()
        return 1
        
    if not options.pyabc_dir or not options.abc or not options.abc_sh or not options.pyabc or not options.out:
        parser.print_help()
        return 1

    extra_bin = options.extra_bin.split(',') if options.extra_bin else []
    extra_lib = options.extra_lib.split(',') if options.extra_lib else []
    extra_files = [ s.split(':') for s in options.extra_files.split(',')] if options.extra_files else []    

    return package(options.pyabc_dir, extra_bin, extra_lib, extra_files, options.abc, options.abc_sh, options.pyabc, options.out, options.scripts, options.sys)

if __name__=="__main__":
    main(sys.argv)
