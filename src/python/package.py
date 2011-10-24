import os
import sys
import optparse
import zipfile
import tarfile
import tempfile
import time

def zip_library(f, extra_files = []):
    lib = "%s/lib/python%s/"%(sys.prefix,sys.version[:3])
    
    zf = zipfile.ZipFile(f, "w", zipfile.ZIP_DEFLATED)
    
    for root, _, files in os.walk(lib):
        arcroot = os.path.relpath(root, lib)
        for f in files:
            _, ext = os.path.splitext(f)
            if ext in ['.py', '.pyo', '.pyc']:
                zf.write(os.path.join(root,f), os.path.join(arcroot, f))

    for s, r in extra_files:
        zf.write( s, r )

    zf.close()

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
    f = open(fname, "rb")
    add_fileobj(tf, f, arcname, mode, mtime)
    f.close()

def package(abc_exe, abc_sh, pyabc, ofname, scripts_dir, use_sys):
    mtime = time.time()
    
    tf = tarfile.open(ofname, "w:gz")
    
    add_dir(tf, "pyabc", mtime)
    
    add_dir(tf, "pyabc/bin", mtime)
    
    add_file(tf, abc_exe, "pyabc/bin/abc_exe", 0777, mtime)
    add_file(tf, abc_sh, "pyabc/bin/abc", 0777, mtime)

    if scripts_dir:
        for fn in os.listdir(scripts_dir):
            fullname = os.path.join(scripts_dir, fn)
            if os.path.isfile(fullname):
                fnroot, fnext = os.path.splitext(fn)
                if fnext==".sh":
                    add_file( tf, fullname, os.path.join("pyabc/bin", fnroot), 0777, mtime)
                else:
                    add_file( tf, fullname, os.path.join("pyabc/scripts", fn), 0666, mtime)
    
    add_dir(tf, "pyabc/lib", mtime)
    
    for entry in os.listdir(pyabc):
        if entry.endswith('.py'):
            add_file( tf, os.path.join(pyabc, entry), os.path.join("pyabc/lib", entry), 0666, mtime)
    
    if not use_sys:
        # ZIP standard library    
        zf = tempfile.NamedTemporaryFile("w+b")
        #zip_library(zf, [(pyabc, "pyabc.py")])
        zip_library(zf, [])
        zf.flush()
        
        add_fileobj(tf, zf, "pyabc/lib/python_library.zip", 0666, mtime)
        
        zf.close()
    
        # add all extensions
        
        lib_dynload = os.path.join(sys.exec_prefix,"lib", "python%s"%sys.version[:3], "lib-dynload")
        
        for fn in os.listdir(lib_dynload):
            fullname = os.path.join(lib_dynload, fn)
            if os.path.isfile(fullname):
                add_file( tf, fullname, os.path.join("pyabc/lib", fn), 0666, mtime)
    
    tf.close()


def main(args):
    
    usage = "usage: %prog [options]"

    parser = optparse.OptionParser(usage)

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
        
    if not options.abc or not options.abc_sh or not options.pyabc or not options.out:
        parser.print_help()
        return 1

    return package(options.abc, options.abc_sh, options.pyabc, options.out, options.scripts, options.sys)

if __name__=="__main__":
    main(sys.argv)
