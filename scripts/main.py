import os
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


#IBM directories
# directories = ['ibmhard']
ibmhard = (33,34,36,37,28,40,42,44,48,5,49,50,52,53,58,59,6,64,66,67,68,\
           69,70,71,72,73,74,75,76,78,79,80,81,82,83,84,86,9,87,89,90,0,10,\
           11,12,14,15,16,2,19,20,29,31,32)


#directories = ['IBM_converted']
#ibm_convert = (3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,\
#               27,28,29,30,31,32,33,34,35,36,37,38,39,40,41)
#IBM_converted = range(42)[3:]

#the smaller files in ascending order
#IBM_converted = (26,38,21,15,22,23,20,27,16,19,24,28,18,9,8,7,6,25,17,3,4)

#the larger file in order (skipping 39)
#IBM_converted = (39,5,40,41,13,12,10,14,11,31,33,36,29,34,35,37,30)
IBM_converted = (5,40,41,13,12,10,14,11,31,33,36,29,34,35,37,30)

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

def list_aig(s):
    """ prnts out the sizes of aig files"""
    #os.chdir('../ibm-web')
    list_all = os.listdir('.')
    dir = lst(list_all,'.aig')
    dir.sort()
    for j in range(len(dir)):
        name = dir[j][:-4]
        if not s in name:
            continue
        print '%s '%name,
        abc('r %s.aig'%name)
        ps()
    return dir

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
        if (('_smp' in name) or ('_save' in name) or ('_backup' in name) or ('_osave' in name)
            or ('_best' in name) or ('_gsrm' in name) or ('gore' in name) or 
            ('_bip' in name) or ('sm0' in name) or ('gabs' in name) 
            or ('temp' in name) or ('__' in name) or ('greg' in name) or ('tf2' in name)
            or ('gsrm' in name) or ('_rpm' in name ) or ('gsyn' in name) or ('beforerpm' in name)
            or ('afterrpm' in name) or ('initabs' in name) or ('.status' in name) or ('_init' in name)
            or ('_osave' in name) or ('tt_' in name) or ('_before' in name) or ('_after' in name)
            or ('_and' in name) or ('_final' in name) or ('_spec' in name) or ('temp.a' in name) or ('_sync' in name)
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
