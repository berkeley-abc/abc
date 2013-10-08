import os
import time
from datetime import *
##import par
##from abc_common import *
import abc_common

#this makes par the dominant module insteat of abc_common
from par import *

import sys
import math
import time
from  pyabc_split import *
##import pdb
##from IPython.Debugger import Tracer; debug_here = Tracer()


#x('source ../../abc.rc')
#abc_common.x('source ../../abc.rc')

def scorriter():
    """ apply scorr with increasing conflicts up to 100"""
    x('time')
    run_command('r p_0.aig')
    n = 20
    while n < 1000:
        print_circuit_stats()
        run_command('scorr -C %d'%n)
        x('ind -C %d'%1000)
        if is_unsat():
            print 'n = %d'%n
            break
        n = 2*n
    x('time')
     
def simplifyq():
    # set_globals()
    n=n_ands()
    if n > 30000:
        if n<45000:
            abc("&get;&scl;&dc2;&put;dr;&get;&lcorr;&dc2;&put;dr;&get;&scorr;&fraig;&dc2;&put;dr;&get;&scorr -F 2;&dc2;&put;w temp.aig")
        else:
            abc("&get;&scl;&dc2;&put;dr;&get;&lcorr;&dc2;&put;dr;&get;&scorr;&fraig;&dc2;&put;dr;&get;&dc2;&put;w temp.aig")
    n = n_ands()
    if n < 30000:
        if n > 15000:
            abc("scl;rw;dr;lcorr;rw;dr;scorr;fraig;dc2;dr;dc2rs;w temp.aig")
        else:
            abc("scl;rw;dr;lcorr;rw;dr;scorr;fraig;dc2;dr;scorr -F 2;dc2rs;w temp.aig")    
    if n < 10000:
        m = min( 30000/n, 8 )
        if m > 2:
            abc( "scorr -F %d"%m)
    run_command("ps")

def constraints():
    """Determine if a set of files in a set of
    directories has constraints and print out the results."""
    for s in directories:
        print("\ndirectory is "+s)
        jj=eval(s)
        print(jj)
        for j in range(len(jj)):
            x("\nr ../DIR/%s/p_%smp.aig"%(s,jj[j]))
            print("structural:")
            x('constr -s')
            print("inductive constraints:")
            x('constr ')

def help(s):
    run_command('%s -h'%s)

def strip():
    """Strip out each output of a multi-output example and write it
    into a separate file"""
    os.chdir('../DIR')
    abc('r p_all_smp.aig')
    po = n_pos()
    print_circuit_stats()
    for j in range(po):
        abc('r p_all_smp.aig')
        abc('cone -s -O %d'%j)
        abc('scl;rw;trm')
        abc('w p_%d.aig'%j)
        print_circuit_stats()

def fn_def(f,n):
    filename = f.__code__.co_filename
    firstline = f.__code__.co_firstlineno
    lines = open(filename, "r").readlines()
    print "".join(lines[firstline : n+firstline])

def lst(list,match):
    result = []
    for j in range(len(list)):
        if list[j][-len(match):] == match:
            result.append(list[j])
    return result

def lste(list,match,excp):
    result = []
    for j in range(len(list)):
        if list[j][-len(match):] == match:
            if excp in list[j]:
                continue
            result.append(list[j])
    return result

def blif2aig():
    """ converts blif files into aig files"""
    #os.chdir('../ibm-web')
    list_all = os.listdir('.')
    l_blif = lst(list_all,'.blif')
    for j in range(len(l_blif)):
        name = l_blif[j][:-5]
        print '%s '%name,
        abc('r %s.blif'%name)
        abc('st')
        abc('fold')
        abc('w %s.aig'%name)
        ps()

def la():
    return list_aig('')

def list_aig(s=''):
    """ prnts out the sizes of aig files"""
    #os.chdir('../ibm-web')
    list_all = os.listdir('.')
    dir = lst(list_all,'.aig')
    dir.sort()
    result = []
    for j in range(len(dir)):
        name = dir[j][:-4]
        if not s_in_s(s,name):
            continue
        print '%s '%name,
        abc('r %s.aig'%name)
        ps()
        result = result + [name]
    return result

def list_original():
    list_dir = os.listdir('.')
    list_dir.sort()
    out = []
    for i in range(len(list_dir)):
        name = '%s/original.aig'%list_dir[i]
        if os.access('%s'%name,os.R_OK):
            abc('r %s;&ps'%name)
            if n_latches() > 0 and n_pos() > 1:
                size = str(sizeof())
                print list_dir[i],
                ps()
                out = out + ['%s: %s'%(list_dir[i],size)]
    return out

def list_size(s=''):
    """ prnts out the sizes of aig files. Leaves .aig as part of name"""
    #os.chdir('../ibm-web')
    list_all = os.listdir('.')
    dir = lst(list_all,'.aig')
    dir.sort()
    result = []
    for j in range(len(dir)):
##        name = dir[j][:-4]
        name = dir[j] #leaves .aig as part of name
        if not s_in_s(s,name):
            continue
        print '%s '%name,
##        abc('r %s.aig'%name)
        abc('r %s'%name)
        ps()
        result = result + [name[:-4]] #takes .aig off of name
    return result

def rename(l=[]):
    for j in range(len(l)):
        name = l[j]
        name1 = name +'.aig'
        name2 = name[:-4]+'simp.aig' #take off _smp and put on simp
        os.rename(name1,name2)
    

def list_blif(s=''):
    """ prnts out the sizes of aig files"""
    #os.chdir('../ibm-web')
    list_all = os.listdir('.')
    dir = lst(list_all,'.blif')
    dir.sort()
    result = []
    for j in range(len(dir)):
        name = dir[j][:-5]
        if not s_in_s(s,name):
            continue
        print '%s: '%name,
        abc('read_blif %s.blif'%name)
        run_command('ps')
        abc('st;zero;w %s.aig'%name)
        result = result + [name]
    return result

def s_in_s(s1,s2):
    ls1 = len(s1)
    l = 1+len(s2)- ls1
    if l< 0:
        return False
    else:
        for j in range(l):
            if s1 == s2[j:j+ls1]:
                return True
            else:
                continue
        return False
            

def convert_ibm():
    """ converts blif files (with constraints?) into aig files"""
    os.chdir('../ibm-web')
    list_ibm = os.listdir('.')
    l_blif = lst(list_ibm,'.blif')
    for j in range(len(l_blif)):
        name = l_blif[j][:-5]
        run_command('read_blif %s.blif'%name)
        abc('undc')
        abc('st -i')
        abc('zero')
        run_command('w %s.aig'%name)
        """if a<100000000:
            f = min(8,max(1,40000/a))
            #run_command('scorr -c -F %d'%f)
            #print 'Result of scorr -F %d: '%f,
            print_circuit_stats()
            run_command('w p_%d.aig'%j)"""

def cl():
    cleanup()

def cleanup():
    list = os.listdir('.') 
    for j in range(len(list)):
        name = list[j]
        if ((s_in_s('_smp',name)) or (s_in_s('_save', name)) or (s_in_s('_backup', name)) or (s_in_s('_osave', name))
            or (s_in_s('_best', name)) or (s_in_s('_gsrm', name)) or (s_in_s('gore', name)) or 
            (s_in_s('_bip', name)) or (s_in_s('sm0', name)) or (s_in_s('gabs', name)) 
            or (s_in_s('temp', name)) or (s_in_s('__', name)) or (s_in_s('greg', name)) or (s_in_s('tf2', name))
            or (s_in_s('gsrm', name)) or (s_in_s('_rpm', name )) or (s_in_s('gsyn', name)) or (s_in_s('beforerpm', name))
            or (s_in_s('afterrpm', name)) or (s_in_s('initabs', name)) or (s_in_s('_init', name))
            or (s_in_s('_osave', name)) or (s_in_s('tt_', name)) or (s_in_s('_before', name)) or (s_in_s('_after', name))
            or (s_in_s('_and', name)) or (s_in_s('_spec', name)) or (s_in_s('temp.a', name))
            or (s_in_s('_sync', name)) or (s_in_s('_old', name)) or (s_in_s('_cone_', name)) or (s_in_s('_abs', name))
            or (s_in_s('_vabs', name)) or (s_in_s('_gla', name)) or (s_in_s('vabs', name)) or (s_in_s('_mp2', name))
            or (s_in_s('_sc1', name)) or (s_in_s('_sc2', name)) or (s_in_s('_after', name))
            or (s_in_s('_before', name)) or (s_in_s('_aigs_', name)) or (s_in_s('_cex.', name))
            or (s_in_s('_bmc1', name)) or (s_in_s('_p0_', name)) or (s_in_s('_p1_', name))
            or (s_in_s('_unsolv', name)) or (s_in_s('_iso1', name))
            ):
            os.remove(name)
        
def simp_mbi():
    os.chdir('../mbi')
    list_ibm = os.listdir('.')
    l_aig = lst(list_ibm,'.aig')
    for j in range(len(l_aig)):
        name = l_aig[j][:-4]
        run_command('r %s.aig'%name)
        run_command('st')
        print '\n%s: '%name
        print_circuit_stats()
        quick_simp()
        scorr_comp()
        simplify()
        run_command('w %s_smp.aig'%name)

def strip_names():
    os.chdir('../mbi')
    list_ibm = os.listdir('.')
    l_aig = lst(list_ibm,'.aig')
    for j in range(len(l_aig)):
        name = l_aig[j][:-4]
        run_command('r %s.aig'%name)
        run_command('st')
        print '\n%s: '%name
        print_circuit_stats()
        quick_simp()
        scorr_comp()
        simplify()
        run_command('w %s_smp.aig'%name)


def map_ibm():
    os.chdir('../ibmmike2')
    list_ibm = os.listdir('.')
    l_blif = lst(list_ibm,'.blif')
    result = []
    print len(l_blif)
    for j in range(len(l_blif)):
        name = l_blif[j][:-5]
        result.append('%s = %d'%(name,j))
    return result


def absn(a,c,s):
    """ testing Niklas abstraction with various conflict limits
    a= method (0 - regular cba,
               1 - pure pba,
               2 - cba with pba at the end,
               3 cba and pba interleaved at each step
    c = conflict limit
    s = No. of stable steps without cex"""
    global G_C, G_T, latches_before_abs, x_factor, f_name
    set_globals()
    latches_before_abs = n_latches()
    print 'Start: ',
    print_circuit_stats()
    print 'Een abstraction params: Method #%d, %d conflicts, %d stable'%(a,c,s)
    run_command('&get; &abs_newstart -v -A %d -C %d -S %d'%(a,c,s))
    bmcdepth = n_bmc_frames()
    print 'BMC depth = %d'%n_bmc_frames()
    abc('&w absn_greg.aig; &abs_derive; &put; w absn_gabs.aig')
    print 'Final abstraction: ',
    print_circuit_stats()
    write_file('absn')
    return "Done"

def time_stamp():
    d=datetime.today()
    s = d.strftime('%m.%d.%y-%X')
    return s

def apply_sp(list):
    global m_trace
    s = time_stamp()
    out_name = "%s-traces.txt"%s
    print out_name
    if os.access(out_name,os.R_OK):
        os.remove(out_name)
    f = open(out_name,'w')
    print f
    for j in range(len(list)):
        name = list[j]
        print '\n\n**** %s ****\n'%name
        f.write('\n\n****%s ****'%name)
        read_file_quiet(name)
        result = super_prove()
        trace = result[1]
        s = str(trace)
        f.write('\n\n')
        f.write(s)
        f.flush()
    f.close()
         
def xfiles():
    global f_name
    #output = sys.stdout
    #iterate over all ESS files
    #saveout = sys.stdout
    #output = open("ibm_log.txt",'w')
    # sys.stdout = output
    os.chdir('../ess/f58m')
    print 'Directories are %s'%directories
    for s in directories:
        sss=  '../%s'%s
        os.chdir(sss)
        print "\nDirectory is %s\n"%s
        jj=eval(s)
        print (jj)
        run_command('time')
        for j in range(len(jj)):
            print ' '
            set_fname('p_%dsmp23'%jj[j])#file f_name.aig is read in
            print 'p_%dsmp23'%jj[j]
            run_command('time')
            result = dprove3(1)
            print result
            run_command('time')
        run_command('time')
    os.chdir('../../python')
    #sys.stdout = saveout
    #output.close()

def sublist(L,I):
    z = []
    for i in range(len(I)):
        s = L[I[i]],
        s = list(s)
        z = z + s
    return z

def s2l(s):
    """ takes the string s divided by '\n' and makess a list of items"""
    result = []
    while len(s)>2:
        j = s.find('\n')
        result.append(s[:j])
        s = s[j+1:]
    return result

def select(lst, s):
    result = []
    print lst
    for j in range(len(lst)):
        if s in lst[j]:
            s1 = lst[j]
            k = s1.find(':')
            s1 = s1[:k]
            result.append(s1)
    return result

def process_result(name):
    f = open(name,'r')
    s = f.read()
    f.close()
    lst = s2l(s)
    result = select(lst,'Timeout')
    return result


def main():
    stackno = 0
    if len(sys.argv) != 2:
        print "usage: %s <aig filename>"%sys.argv[0]
        sys.exit(1)
    aig_filename = sys.argv[1]
    x("source ../../abc.rc")
    read(aig_filename)
    dprove3(1)
# a test to  whether the script is being called from the command line
if __name__=="__main__":
    main()
