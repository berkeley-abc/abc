from pyabc import *
import pyabc_split
import par
import redirect
import sys
import os
import time
import math


global G_C,G_T,latches_before_abs,latches_before_pba,n_pos_before,x_factor

"""
The functions that are currently available from module _abc are:

int n_ands();
int n_pis();
int n_pos();
int n_latches();
int n_bmc_frames();
int prob_status(); 1 = unsat, 0 = sat, -1 = unsolved

int run_command(char* cmd);

bool has_comb_model();
bool has_seq_model();
bool is_true_cex();
bool is_valid_cex();
  return 1 if the number of PIs in the current network and in the current counter-example are equal
int  n_cex_pis();
  return the number of PIs in the current counter-example
int  n_cex_regs();
  return the number of flops in the current counter-example
int  cex_po();
  returns the zero-based output PO number that is SAT by cex
int  cex_frame();
  return the zero-based frame number where the outputs is SAT
The last four APIs return -1, if the counter-example is not defined. 
"""

#global variables

stackno_gabs = stackno_gore = stackno_greg= 0
STATUS_UNKNOWN = -1
STATUS_SAT = 0
STATUS_UNSAT = 1
RESULT = ('SAT' , 'SAT', 'UNSAT', 'UNDECIDED', 'UNDECIDED,', 'UNDCIDED'  )
Sat_reg = 0
Sat_true = 1
Unsat = 2
Undecided_reduction = 3
Undecided_no_reduction = 4
Error = 5
Restart = 6
xfi = x_factor = 1  #set this to higher for larger problems or if you want to try harder during abstraction
max_bmc = -1
last_time = 0

# Function definitions:
# simple functions: ________________________________________________________________________
# set_globals, abc, q, x, has_any_model, is_sat, is_unsat, push, pop

# ALIASES
def p():
    return prove()

def ps():
    print_circuit_stats()

def n_real_inputs():
    """This gives the number of 'real' inputs. This is determined by trimming away inputs that
    have no connection to the logic. This is done by the ABC alias 'trm', which changes the current
    circuit. In some applications we do not want to change the circuit, but just to know how may inputs
    would go away if we did this. So the current circuit is saved and then restored afterwards."""
    abc('w %s_savetempreal.aig; logic; trim; st'%f_name)
    n = n_pis()
    abc('r %s_savetempreal.aig'%f_name)
    return n

def long(t):
    if t<20:
        t = t
    else:
        t = 20+(t-20)/3
    return max(10,t)

def rif():
    """Not used"""
    global f_name
    print 'Type in the name of the aig file to be read in'
    s = raw_input()
    if s[-5:] == '.blif':
        f_name = s[:-5]
    else:
        f_name = s
        s = s+'.blif'
    run_command(s)
    x('st;constr -i')
    print_circuit_stats()
    a = n_ands()
    f = max(1,30000/a)
    f = min (f,16)
    x('scorr -c -F %d'%f)
    x('fold')
    print_circuit_stats()
    x('w %s_c.aig'%f_name)

def abc(cmd):
    abc_redirect_all(cmd)
    

def abc_redirect( cmd, dst = redirect.null_file, src = sys.stdout ):
    """This is our main way of calling an ABC function. Redirect, means that we suppress any output from ABC"""
    with redirect.redirect( dst, src ):
        return run_command( cmd )


def abc_redirect_all( cmd ):
    """This is our main way of calling an ABC function. Redirect, means that we suppress any output from ABC, including error printouts"""
    with redirect.redirect( redirect.null_file, sys.stdout ):
        with redirect.redirect( redirect.null_file, sys.stderr ):
            return run_command( cmd )

def set_globals():
    """This sets global parameters that are used to limit the resources used by all the operations
    bmc, interpolation BDDs, abstract etc. There is a global factor 'x_factor' that can
    control all of the various resource limiting parameters"""
    global G_C,G_T,x_factor
    nl=n_latches()
    na=n_ands()
    np = n_pis()
    #G_C = min(500000,(3*na+500*(nl+np)))
    G_C = x_factor * min(100000,(3*na+500*(nl+np)))
    #G_T = min(250,G_C/2000)
    G_T = x_factor * min(75,G_C/2000)
    G_T = max(1,G_T)
    #print('Global values: BMC conflicts = %d, Max time = %d sec.'%(G_C,G_T))
    
def a():
    """this puts the system into direct abc input mode"""
    print "Entering ABC direct-input mode. Type q to quit ABC-mode"
    n = 0
    while True:
        print '     abc %d> '%n,
        n = n+1
        s = raw_input()
        if s == "q":
            break
        run_command(s) 

def set_fname(name):
    """ Another way to set an f_name, but currently this is not used"""
    global f_name
    s = name
    if s[-4:] == '.aig':
        f_name = s[:-4]
    else:
        f_name = s
        s = s+'.aig'
    #read in file
    run_command(s)
    #print_circuit_stats()

def read_file_quiet(fname=None):
    """This is the main program used for reading in a new circuit. The global file name is stored (f_name)
    Sometimes we want to know the initial starting name. The file name can have the .aig extension left off
    and it will assume that the .aig extension is implied. This should not be used for .blif files.
    Any time we want to process a new circuit, we should use this since otherwise we would not have the
    correct f_name."""
    global max_bmc,  f_name, d_name, initial_f_name, x_factor, init_initial_f_name
    x_factor = 1
    max_bmc = -1
    
    if fname is None:
        print 'Type in the name of the aig file to be read in'
        s = raw_input()
    else:
        s = fname
        
    if s[-4:] == '.aig':
        f_name = s[:-4]
    else:
        f_name = s
        s = s+'.aig'
        
    run_command(s)
    initial_f_name = f_name
    init_initial_f_name = f_name
    
def read_file():
    read_file_quiet()
    print_circuit_stats()

def rf():
    read_file()


def write_file(s):
    """this is the main method for writing the current circuit to an AIG file on disk.
    It manages the name of the file, by giving an extension (s). The file name 'f_name'
    keeps increasing as more extensions are written. A typical sequence is
    name, name_smp, name_smp_abs, name_smp_abs_spec, name_smp_abs_spec_final"""
    global f_name
    """Writes out the current file as an aig file using f_name appended with argument"""
    f_name = '%s_%s'%(f_name,s)
    ss = '%s.aig'%(f_name)
    print 'WRITING %s: '%ss,
    print_circuit_stats()
    abc('w '+ss)
    
def wf():
    """Not used"""
    print 'input type of file to be written'
    s = raw_input()
    write_file(s)

def bmc_depth():
    """ Finds the number of BMC frames that the latest operation has used. The operation could be BMC, reachability
    interpolation, abstract, speculate. max_bmc is continually increased. It reflects the maximum depth of any version of the circuit
    including g ones, for which it is known that there is not cex out to that depth."""
    global max_bmc
    b = n_bmc_frames()
    max_bmc = max(b,max_bmc)
    return max_bmc

def set_max_bmc(b):
    """ Keeps increasing max_bmc which is the maximum number of time frames for
    which the current circuit is known to be UNSAT for"""
    global max_bmc
    max_bmc = max(b,max_bmc)

def print_circuit_stats():
    """Stardard way of outputting statistice about the current circuit"""
    global max_bmc
    i = n_pis()
    o = n_pos()
    l = n_latches()
    a = n_ands()
    b = max(max_bmc,bmc_depth())
    c = cex_frame()
    if b>= 0:
        if c>=0:
            print 'PIs = %d, POs = %d, FF = %d, ANDs = %d, max depth = %d, CEX depth = %d'%(i,o,l,a,b,c)
        else:
            print 'PIs = %d, POs = %d, FF = %d, ANDs = %d, max depth = %d'%(i,o,l,a,b)
    else:
        if c>=0:
            print 'PIs = %d, POs = %d, FF = %d, ANDs = %d, CEX depth = %d'%(i,o,l,a,c)
        else:
            print 'PIs = %d, POs = %d, FF = %d, ANDs = %d'%(i,o,l,a)

def q():
    exit()

def x(s):
    """execute an ABC command"""
    print "RUNNING: ", s
    run_command(s)

def has_any_model():
    """ check if a satisfying assignment has been found"""
    res = has_comb_model() or has_seq_model()
    return res

def is_unsat():
    if prob_status() == 1:
        return True
    else:
        return False

def is_sat():
    if prob_status() == 0:
        return True
    else:
        return False

def wc(file):
    """writes <file> so that costraints are preserved explicitly"""
    abc('&get;&w %s'%file)

def rc(file):
    """reads <file> so that if constraints are explicit, it will preserve them"""
    abc('&r %s;&put'%file)                         



def fast_int(n):
    """This is used to eliminate easy-to-prove outputs. Arg n is conflict limit to be used
    in the interpolation routine. Typically n = 1 or 10"""
    n_po = n_pos()
    abc('int -k -C %d'%n)
    print 'Reduced POs from %d to %d'%(n_po,n_pos())

def refine_with_cex():
    """Refines the greg (which contains the original problem with the set of FF's that have been abstracted).
    This generates a new abstraction (gabs) and modifies the greg file to reflect which regs are in the
    current abstraction"""
    global f_name
    print 'CEX in frame %d for output %d'%(cex_frame(),cex_po())
    abc('&r %s_greg.aig; &abs_refine; &w %s_greg.aig'%(f_name,f_name))
    return

def generate_abs(n):
    """generates an abstracted  model (gabs) from the greg file. The gabs file is automatically
    generated in the & space by &abs_derive. We store it away using the f_name of the problem
    being solved at the moment. The f_name keeps changing with an extension given by the latest
    operation done - e.g. smp, abs, spec, final, group. """
    global f_name
    #we have a cex and we use this generate a new gabs file
    abc('&r %s_greg.aig; &abs_derive; &put; w %s_gabs.aig'%(f_name,f_name)) # do we still need the gabs file
    if n == 1:
        print 'New abstraction: ',
        print_circuit_stats()
    return   

    
#more complex functions: ________________________________________________________
#, abstract, pba, speculate, final_verify, dprove3


def simplify():
    """Our standard simplification of logic routine. What it does depende on the problem size.
    For large problems, we use the &methods which use a simple circuit based SAT solver. Also problem
    size dictates the level of k-step induction done in 'scorr' The stongest simplification is done if
    n_ands < 20000. Then it used the clause based solver and k-step induction where |k| depends
    on the problem size """
    # set_globals()
##    print 'simplify initial ',
##    ps()
    #abc('w t.aig')
    n=n_ands()
    abc('scl')
    if n > 40000:
        abc('&get;&scl;&put')
        n = n_ands()
        if n < 100000:
            abc("&dc2;&put;dr;&get;&lcorr;&dc2;&put;dr;&get;&scorr;&fraig;&dc2;&put;dr")
            run_command('ps')
            print '.',
            n = n_ands()
            if n<60000:
                abc("&get;&scorr -F 2;&put;dc2rs")
                print '.',
                #ps()
            else:
                abc("dc2rs")
                print '.',
                #ps()
            n = n_ands()
    n = n_ands()
    if n <= 40000:
        print '.',
        #ps()
        if n > 30000:
            abc("dc2rs")
            print '.',
##        else:
##            abc("scorr -F 2;dc2rs")
##            print '.',
##            ps()
    n = max(1,n_ands())
    #ps()
    if n < 30000:
        abc('scl;rw;dr;lcorr;rw;dr')
        m = int(min( 60000/n, 16))
        #print 'm = %d'%m
        if m >= 1:
            j = 1
            while j <= m:
                set_size()
                #print 'j - %d'%j
                #abc('scl;dr;dc2;scorr -C 5000 -F %d'%j)
                if j<8:
                    abc('dc2')
                else:
                    abc('dc2rs')
                abc('scorr -C 5000 -F %d'%j)
                if check_size():
                    break
                j = 2*j
                #ps()
                continue
            print '.',


def iterate_simulation(latches_before):
    """Subroutine of 'abstract' which does the refinement of the abstracted model,
    using counterexamples found by simulation. Simulation is controlled by the amount
    of memory it might use. At first wide but shallow simulation is done, bollowed by
    successively more narrow but deeper simulation"""
    global x_factor, f_name
##    print 'RUNNING simulation iteratively'
    f = 5
    w = 255
    for k in range(9):
        f = min(f *2, 3500)
        w = max(((w+1)/2)-1,1)
        print '.',
        abc('sim -m -F %d -W %d'%(f,w))
        if not is_sat():
            continue
        while True:
            refine_with_cex()
            if is_sat():
                print 'cex failed to refine abstraction '
                return Sat_true
            generate_abs(0)
            latches_after = n_latches()
            print 'Latches increased to %d'%latches_after
            if latches_after >= .99*latches_before:
                abc('r %s_savetempabs.aig'%f_name)
                print "No reduction!."
                return Undecided_no_reduction
            abc('sim -m -F %d -W %d'%(f,w))
            if not is_sat():
                break

def simulate():
    """Simulation is controlled by the amount
    of memory it might use. At first wide but shallow simulation is done, bollowed by
    successively more narrow but deeper simulation"""
    global x_factor, f_name
##    print 'RUNNING simulation iteratively'
    f = 5
    w = 255
    for k in range(9):
        f = min(f *2, 3500)
        w = max(((w+1)/2)-1,1)
        print '.',
        abc('sim -m -F %d -W %d'%(f,w))
        if is_sat():
            print 'cex found in frame %d'%cex_frame()
            return 'SAT'
    return 'UNDECIDED'
        

def iterate_abstraction_refinement(latches_before,NBF):
    """Subroutine of 'abstract' which does the refinement of the abstracted model,
    using counterexamples found by BMC or BDD reachability"""
    global x_factor, f_name
    if NBF == -1:
        F = 2000
    else:
        F = 2*NBF
    print '\nIterating BMC/PDR'
    always_reach = 0
    cexf = 0
    reach_failed = 0
    while True:
        #print 'Generating problem abstraction'
        generate_abs(1)
        set_globals()
        latches_after = n_latches()
        if latches_after >= .98*latches_before:
##            print 'No reduction'
##            abc('r &s_savetemp.aig'%f_name)
            break
        ri = n_real_inputs() # No. of inputs after trm
        nlri = n_latches()+ri
        #reach_allowed = ((nlri<150) or (((cexf>250))&(nlri<300)))
        reach_allowed = ((nlri<75) or (((cexf>250))&(nlri<300)))
        pdr_allowed  = True
        bmc = False
        t = max(1,G_T)
        if not F == -1:
            F = int(1.5*max_bmc)
        if (((reach_allowed  or pdr_allowed ) and not reach_failed)):
            #cmd = 'reach -B 200000 -F 3500 -T %f'%t
            #cmd = 'reachx -e %d -t %d'%(int(long(t)),max(10,int(t)))
            #cmd = 'reachx -t %d'%max(10,int(t))
            cmd = '&get;,pdr -vt=%f'%t
        else:
            #cmd = 'bmc3 -C %d -T %f -F %d'%(G_C,t,F)
            bmc = True
            cmd = '&get;,bmc -vt=%f'%(t)
            #cmd = '&get;,pdr -vt=%f'%(t)
        print '\n***RUNNING %s'%cmd
        #run_command(cmd)
        last_bmc = max_bmc
        abc(cmd)
        if prob_status() == 1:
            #print 'Depth reached %d frames, '%n_bmc_frames()
            print 'UNSAT'
            return Unsat
        cexf = cex_frame()
        #print 'cex depth = %d'%cexf
        #set_max_bmc(cexf -1)
        if ((not is_sat()) ):
            reach_failed = 1 # if ever reach failed, then we should not try it again on more refined models
        if is_sat():
            #print 'CEX in frame %d for output %d'%(cex_frame(),cex_po())
            #set_max_bmc(cexf-1)
            refine_with_cex() # if cex can't refine, status is set to Sat_true
            if is_sat():
                print 'cex did not refine. Implies true_sat'
                return Sat_true
        else:
            print "No CEX found in %d frames"%n_bmc_frames()
            set_max_bmc(n_bmc_frames())
            if bmc:
                break
            elif max_bmc> 1.2*last_bmc: # if pdr increased significantly over abs, the assume OK
                break
            else:
                continue
    latches_after = n_latches()
    if latches_after >= .98*latches_before:
        abc('r %s_savetempabs.aig'%f_name)
        print "No reduction!"
        return Undecided_no_reduction
    else:
        print 'Latches reduced from %d to %d'%(latches_before, n_latches())
        return Undecided_reduction


def abstract():
    """ abstracts using N Een's method 3 - cex/proof based abstraction. The result is further refined using
    simulation, BMC or BDD reachability"""
    global G_C, G_T, latches_before_abs, x_factor
    set_globals()
    latches_before_abs = n_latches()
    abc('w %s_savetempabs.aig'%f_name)
    print 'Start: ',
    print_circuit_stats()
    c = 1.5*G_C
    #t = max(1,1.25*G_T)
    t = 2*max(1,1.25*G_T)
    s = min(max(3,c/30000),10) # stability between 3 and 10
    time = max(1,.01*G_T)
    abc('&get;,bmc -vt=%f'%time)
    print 'BMC went %d frames'%n_bmc_frames()
    set_max_bmc(bmc_depth())
    f = max(2*max_bmc,20)
    b = min(max(10,max_bmc),200)
    cmd = '&get;,abs -bob=%d -stable=%d -timeout=%f -vt=%f -depth=%d'%(b,s,t,t,f)
    print '     Running %s'%cmd
    run_command(cmd)
    if is_sat():
        print 'Found true counterexample in frame %d'%cex_frame()
        return Sat_true
    NBF = bmc_depth()
    print 'Abstraction good to %d frames'%n_bmc_frames()
    set_max_bmc(NBF)
    abc('&w %s_greg.aig; &abs_derive; &put; w %s_gabs.aig'%(f_name,f_name))
##    print 'First abstraction: ',
##    print_circuit_stats()
    latches_after = n_latches()
    #if latches_before_abs == latches_after:
    if latches_after >= .98*latches_before_abs:
        abc('r %s_savetempabs.aig'%f_name)
        print "No reduction!"
        return Undecided_no_reduction    
    # refinement loop
    if (n_ands() + n_latches() + n_pis()) < 15000:
        print '\n***Running simulation iteratively'
        for i in range(5):
            result = iterate_simulation(latches_before_abs)
            if result == Restart:
                return result
            if result == Sat_true:
                return result
    result = iterate_abstraction_refinement(latches_before_abs, NBF)
    #if the result is 'Restart' we return and the calling routine increase
    #x_factor to try one more time.
    return result

def absv(n,v):
    """This is a version of 'abstract' which can control the methods used in Een's abstraction code (method = n)
    as well as whether we want to view the output of this (v = 1)"""
    global G_C, G_T, latches_before_abs, x_factor
    #input_x_factor()
    #x_factor = 3
    set_globals()
    latches_before_abs = n_latches()
    print 'Start: ',
    print_circuit_stats()
    c = 1.5*G_C
    t = max(1,1.25*G_T)
    s = min(max(3,c/30000),10) # stability between 3 and 10
    if max_bmc == -1:
        time = max(1,.01*G_T)
        #abc('bmc3 -C %d -T %f -F 165'%(.01*G_C, time))
        abc('&get;,bmc -vt=%f'%time)
        set_max_bmc(bmc_depth())
    f = min(250,1.5*max_bmc)
    f = max(20, f)
    f = 10*f
    b = x_factor*20
    if not n == 0:
        b = 10
        b = max(b,max_bmc+2)
        b = b*2**(x_factor-1)
        b = 2*b
    print 'Neen abstraction params: Method #%d, %d conflicts, %d stable, %f sec.'%(n,c/3,s,t)
    if v == 1:
        run_command('&get; &abs_newstart -v -B %f -A %d -C %d -S %d -V %f'%(b,n,c/3,s,t))
    else:
        abc('&get; &abs_newstart -v -B %f -A %d -C %d -S %d -T %f'%(b,n,c/3,s,t))
    set_max_bmc(n_bmc_frames())
    print 'Abstraction good to %d'%n_bmc_frames()
    abc('&w %s_greg.aig; &abs_derive; &put; w %s_gabs.aig'%(f_name,f_name))
    print 'Final abstraction: ',
    print_circuit_stats()
    latches_after = n_latches()    
    if latches_after >= .98*latches_before_abs:
        print "No reduction!"
        return Undecided_no_reduction
    return Undecided_reduction

def spec():
    """Main speculative reduction routine. Finds candidate sequential equivalences and refines them by simulation, BMC, or reachability
    using any cex found. """
    input_x_factor()
    global G_C,G_T,n_pos_before, x_factor, n_latches_before
    set_globals()
    n_pos_before = n_pos()
    n_latches_before = n_latches()    
    set_globals()
    t = max(1,.5*G_T)
    r = max(1,int(t))
    print '\n***Running &equiv2 with C = %d, T = %f sec., F = %d -S 1 -R %d'%(G_C,t,200,r)
    abc("&get; &equiv2 -C %d -F 200 -T %f -S 1 -R %d; &semi -F 50; &speci -F 20 -C 1000;&srm; r gsrm.aig; w %s_gsrm.aig; &w %s_gore.aig"%((G_C),t,r,f_name,f_name))
    print 'Initial speculation: ',
    print_circuit_stats()
    print 'Speculation good to %d frames'%n_bmc_frames()
    return

def speculate():
    """Main speculative reduction routine. Finds candidate sequential equivalences and refines them by simulation, BMC, or reachability
    using any cex found. """
    
    global G_C,G_T,n_pos_before, x_factor, n_latches_before
    set_globals()
    n_pos_before = n_pos()
    
    def refine_with_cex():
        """Refines the gore file to reflect equivalences that go away because of cex"""
        global f_name
        print 'CEX in frame %d for output %d'%(cex_frame(),cex_po())
        abc('&r %s_gore.aig; &resim -m; &w %s_gore.aig'%(f_name,f_name))
        #abc('&r %s_gore.aig; &equiv2 -vx ; &w %s_gore.aig'%(f_name,f_name))
        return
    
    def generate_srm(n):
        """generates a speculated reduced model (srm) from the gore file"""
        global f_name
        pos = n_pos()
        ab = n_ands()
        abc('&r %s_gore.aig; &srm ; r gsrm.aig; w %s_gsrm.aig'%(f_name,f_name)) #do we still need to write the gsrm file
        if n == 0:
            if ((pos == n_pos()) and (ab == n_ands())):
                print 'Failed to refine'
                return 'failed'
        if n == 1:
            print 'Spec. Red. Miter: ',
            print_circuit_stats()
        return 'OK'

    def run_simulation(n):
        f = 5
        w = (256/n)-1
        for k in range(9):
            f = min(f * 2, 3500)
            w = max(((w+1)/2)-1,1)
            print '.',
            #generate_srm(0)
            abc('sim -m -F %d -W %d'%(f,w))
            if not is_sat():
                continue                
            if cex_po() < n_pos_before:
                print 'Sim found true cex: Output = %d, Frame = %d'%(cex_po(),cex_frame())
                return Sat_true                    
            refine_with_cex()
            if n_pos_before == n_pos():            
                return Undecided_no_reduction
            while True:
                result = generate_srm(0)
                if result == 'failed':
                    return Sat_true
                abc('sim -m -F %d -W %d'%(f,w))
                if not is_sat():
                    break                
                if cex_po() < n_pos_before:
                    print 'Sim found true cex: Output = %d, Frame = %d'%(cex_po(),cex_frame())
                    return Sat_true                    
                refine_with_cex()
                if n_pos_before == n_pos():            
                    return Undecided_no_reduction
        return Undecided_no_reduction
    
    n_pos_before = n_pos()
    n_latches_before = n_latches()    
    set_globals()
    t = max(1,.5*G_T)
    r = max(1,int(t))
    abc('write spec_temp.aig')
    print '\n***Running &equiv2 with C = %d, T = %f sec., F = %d -S 1 -R %d'%(G_C,t,200,r)
##    abc("&get; &equiv2 -C %d -F 200 -T %f -S 1 -R %d; &semi -F 50; &speci -F 20 -C 1000;&srm; r gsrm.aig; w %s_gsrm.aig; &w %s_gore.aig"%((G_C),t,r,f_name,f_name))
    abc("&get; &equiv2 -C %d -F 200 -T %f -S 1 -R %d; &semi -W 63 -S 5 -C 500 -F 500; &speci -F 200 -C 5000;&srm; r gsrm.aig; w %s_gsrm.aig; &w %s_gore.aig"%((G_C),t,r,f_name,f_name))
    print 'Initial speculation: ',
    print_circuit_stats()
    #print 'Speculation good to %d frames'%n_bmc_frames()
    #simplify()
    if n_pos_before == n_pos():
        print 'No new outputs. Quitting speculate'
        return Undecided_no_reduction # return result is unknown
    if is_sat():
        #print '\nWARNING: if an abstraction was done, need to refine it further\n'
        return Sat_true
    if n_latches() > .98*n_latches_before:
        pre_simp()
        if n_latches() > .98*n_latches_before:
            print 'Quitting speculation - not enough gain'
            abc('r spec_temp.aig')
            return Undecided_no_reduction # not worth it
    k = n_ands() + n_latches() + n_pis()
    n = 0
    if k < 15000:
        n = 1
    elif k < 30000:
        n = 2
    elif k < 60000:
        n = 4
    elif k < 120000:
        n = 8
    if n > 0: # simulation can run out of memory for too large designs, so be careful
        print '\n***RUNNING simulation iteratively'          
        for i in range(5):
            result = run_simulation(n)
            if result == Sat_true:
                return result
    simp_sw = 1
    int_sw = 1
    reach_sw = 0
    cexf = 0
    reach_failed = 0
    init = 1
    run_command('write temptemp.aig')
    print '\nIterating BMC or BDD reachability'
    while True: # now try real hard to get the last cex.
        set_globals()
        if not init:
            set_size()
            result = generate_srm(1)
            if check_size() == True:
                print 'Failed to refine'
                return Error
            if result == 'failed':
                return Sat_true
            if simp_sw == 1:
                na = n_ands()
                simplify()
                if n_ands() > .7*na: #if not significant reduction, stop simplification
                    simp_sw = 0
            if n_latches() == 0:
                return check_sat()
        init = 0 # make it so that next time it is not the first time through
        time = max(1,G_T/(5*n_pos()))
        if int_sw ==1:
            npo = n_pos()
            if n_pos() > .5*npo:  # if not sufficient reduction, turn this off
                int_sw = 0
        if is_sat():        #if fast interpolation found a cex
            cexf = cex_frame()
            set_max_bmc(cexf - 1)
            if cex_po() < n_pos_before:
                print 'Int found true cex: Output = %d, Frame = %d'%(cex_po(),cex_frame())
                return Sat_true
            refine_with_cex()
            if ((n_pos_before == n_pos()) or (n_latches_before == n_latches())):            
                abc('r temp_spec.aig')
                return Undecided_no_reduction
            if is_sat():
                print '1. cex failed to refine abstraction'
                return Sat_true
            continue
        else:
            if n_latches() == 0:
                return check_sat()
            ri = n_real_inputs()  #seeing how many inputs would trm get rid of
            nlri = n_latches() + ri
            reach_allowed = ((nlri<75) or (((cexf>250)) and (nlri<300)))
            pdr_allowed = True
            bmc = False
            if (((reach_allowed  or pdr_allowed ) and not reach_failed)):
                t = max(1,1.2*G_T)
                f = max(3500, 2*max_bmc)
                #cmd = 'reachx -t %d'%max(10,int(t))
                cmd ='&get;,pdr -vt=%f'%t
            else:
                t = max(1,1.5*G_T)
                if max_bmc == -1:
                    f = 200
                else:
                    f = max_bmc
                f = int(1.5*f)
                #cmd = 'bmc3 -C %d -T %f -F %f'%(1.5*G_C,1.2*t,f)
                bmc = True
                cmd = '&get;,bmc -vt=%f'%(1.2*t)
            print '\n***Running %s'%cmd
            last_bmc = max_bmc
            abc(cmd)
            #run_command(cmd)
            if is_sat():
                cexf = cex_frame()
                #set_max_bmc(cexf  - 1)
                #This is a temporary fix since reachx always reports cex_ps = 0
                if ((cex_po() < n_pos_before) and (cmd[:4] == '&get')):
                    print 'BMC/PDR found true cex: Output = %d, Frame = %d'%(cex_po(),cex_frame())
                    return Sat_true
                #End of temporary fix
                refine_with_cex()#change the number of equivalences
                if n_pos_before == n_pos():            
                    return Undecided_no_reduction
                continue
            else:
                set_max_bmc(n_bmc_frames())
                if prob_status() == 1:
                        #print 'Convergence reached in %d frames'%n_bmc_frames()
                        return Unsat
                print 'No cex found in %d frames'%n_bmc_frames()
                if bmc:
                    break
                elif max_bmc > 1.2*last_bmc:
                    break
                else:
                    reach_failed = 1
                    init = 1
                    continue
    if n_pos_before == n_pos():
        return Undecided_no_reduction 
    else:
        return Undecided_reduction

def set_size():
    """Stores  the problem size of the current design. Size is defined as (PIs, POs, ANDS, FF, max_bmc)""" 
    global npi, npo, nands, nff, nmd
    npi = n_pis()
    npo = n_pos()
    nands = n_ands()
    nff = n_latches()
    nmd = max_bmc

def check_size():
    """Assumes the problem size has been set by set_size before some operation. This checks if the size was changed
    Size is defined as (PIs, POs, ANDS, FF, max_bmc)
    Returns TRUE is size is the same""" 
    global npi, npo, nands, nff, nmd
    result = ((npi == n_pis()) and (npo == n_pos()) and (nands == n_ands()) and (nff == n_latches()) and (nmd == max_bmc))
##    if result == 1:
##        print 'Size unchanged'
    return result

def inferior_size():
    """Assumes the problem size has been set by set_size beore some operation.
    This checks if the new size is inferior (larger) to the old one 
    Size is defined as (PIs, POs, ANDS, FF)""" 
    global npi, npo, nands, nff
    result = ((npi < n_pis()) or (npo < n_pos()) or (nands < n_ands()) )
    return result

def quick_verify(n):
    """Low resource version of final_verify n = 1 means to do an initial simplification first"""
    abc('trm')
    if n == 1:
        simplify()
        if n_latches == 0:
            return check_sat()
        abc('trm')
        if is_sat():
            return Sat_true
    print 'After trimming: ',
    print_circuit_stats()
    #try_rpm()
    set_globals()
    t = max(1,.4*G_T)
    print '    Running PDR for %d sec '%(t)
    abc('&get;,pdr -vt=%f'%(t*.8))
    status = get_status()
    if not status == Unsat:
        print 'PDR went to %d frames, '%n_bmc_frames(),
    print RESULT[status]
    return status #temporary
    if status <= Unsat:
        return status
    N = bmc_depth()
    c = max(G_C/10, 1000)
    t = max(1,.4*G_T)
    print '    RUNNING interpolation with %d conflicts, max %d sec and 100 frames'%(c,t)
    #abc('int -v -F 100 -C %d -T %f'%(c,t))
    abc(',imc -vt=%f '%t)
    status = get_status()
    if status <= Unsat:
        print 'Interpolation went to %d frames, '%n_bmc_frames(),
        print RESULT[status]
        return status
    L = n_latches()
    I = n_real_inputs()
    if ( ((I+L<200)&(N>100))  or  (I+L<125)  or  L < 51 ): #heuristic that if bmc went deep, then reachability might also
        t = max(1,.4*G_T)
        cmd = 'reachx -t %d'%max(10,int(t))
        print '    Running %s'%cmd
        abc(cmd)        
        status = get_status()
        if status <= Unsat:
            print 'Reachability went to %d frames, '%n_bmc_frames()
            print RESULT[status]
            return status
        print 'BDD reachability aborted'
    simplify() #why is this here
    if n_latches() == 0:
        print 'Simplified to 0 FF'
        return check_sat()
    set_max_bmc(bmc_depth()) # doesn't do anything
    print 'No success, max_depth = %d'%max_bmc
    return Undecided_reduction

def get_status():
    """this simply translates the problem status encoding done by ABC (-1,0,1)=(undecided,SAT,UNSAT) into the status code used by our python code."""
    status = prob_status() #interrogates ABC for the current status of the problem.
    # 0 = SAT
    if status == 1:
        status = Unsat
    if status == -1: #undecided
        status = Undecided_no_reduction
    return status

def try_rpm():
    """rpm is a cheap way of doing reparameterization and is an abstraction method, so may introduce false cex's.
    It finds a minimum cut between the PIs and the main sequential logic and replaces this cut by free inputs.
    A quick BMC is then done, and if no cex is found, we assume the abstraction is valid. Otherwise we revert back
    to the original problem before rpm was tried."""
    global x_factor
    if n_ands() > 30000:
        return
    set_globals()
    pis_before = n_pis()
    abc('w %s_savetemp.aig'%f_name)
    abc('rpm')
    result = 0
    if n_pis() < .5*pis_before:
        bmc_before = bmc_depth()
        #print 'running quick bmc to see if rpm is OK'
        t = max(1,.1*G_T)
        #abc('bmc3 -C %d, -T %f'%(.1*G_C, t))
        abc('&get;,bmc -vt=%f'%t)
        if is_sat(): #rpm made it sat by bmc test, so undo rpm
            abc('r %s_savetemp.aig'%f_name)
        else:
            abc('trm')
            print 'WARNING: rpm reduced PIs to %d. May make SAT.'%n_pis()
            result = 1
    else:
        abc('r %s_savetemp.aig'%f_name)
    return result
            
def final_verify():
    """This is the final method for verifying anything is nothing else has worked. It first tries BDD reachability
    if the problem is small enough. If this aborts or if the problem is too large, then interpolation is called."""
    global x_factor
    set_globals()
##    simplify()
##    if n_latches() == 0:
##        return check_sat()
##    abc('trm')
    #rpm_result = try_rpm()
    set_globals()
    N = bmc_depth()
    L = n_latches()
    I = n_real_inputs()
    #try_induction(G_C)
    c = max(G_C/5, 1000)
    t = max(1,G_T)
    print '\n***Running PDR for %d sec'%(t)
    abc('&get;,pdr -vt=%f'%(t*.8))
    status = get_status()
    if status <= Unsat:
        print 'PDR went to %d frames, '%n_bmc_frames(),
        print RESULT[status]
        return status
    if ( ((I+L<250)&(N>100))  or  (I+L<200) or (L<51) ): #heuristic that if bmc went deep, then reachability might also
        t = max(1,1.5*G_T)
        #cmd = 'reach -v -B 1000000 -F 10000 -T %f'%t
        #cmd = 'reachx -e %d'%int(long(t))
        #cmd = 'reachx -e %d -t %d'%(int(long(t)),max(10,int(t)))
        cmd = 'reachx -t %d'%max(10,int(t))
        print '\n***Running %s'%cmd
        abc(cmd)        
        status = get_status()
        if status <= Unsat:
            print 'Reachability went to %d frames, '%n_bmc_frames(),
            print RESULT[status]
            return status
        print 'BDD reachability aborted'          
    return status #temporary
    #f = max(100, bmc_depth())
    print '\n***RUNNING interpolation with %d conflicts, %d sec, max 100 frames'%(c,t)
    #abc('int -v -F 100 -C %d -T %f'%(c,t))
    abc(',imc -vt=%f '%t)
    status = get_status()
    if status <= Unsat:
        print 'Interpolation went to %d frames, '%n_bmc_frames(),
        print RESULT[status]
        return status
    t = max(1,G_T)
    simplify()
    if n_latches() == 0:
        return check_sat()
    print 'Undecided'
    return Undecided_reduction

def check_sat():
    """This is called if all the FF have disappeared, but there is still some logic left. In this case,
    the remaining logic may be UNSAT, which is usually the case, but this has to be proved. The ABC command 'dsat' is used fro combinational problems"""
##    if n_ands() == 0:
##        return Unsat
    abc('orpos;dsat -C %d'%G_C)
    if is_sat():
        return Sat_true
    elif is_unsat():
        return Unsat
    else:
        return Undecided_no_reduction

def try_era(s):
    """era is explicit state enumeration that ABC has. It only works if the number of PIs is small,
    but there are cases where it works and nothing else does"""
    if n_pis() > 12:
        return
    cmd = '&get;&era -mv -S %d;&put'%s
    print 'Running %s'%cmd
    run_command(cmd)

def try_induction(C):
    """Sometimes proving the property directly using induction works but not very often.
    For 'ind' to work, it must have only 1 output, so all outputs are or'ed together temporarily"""
    return Undecided_reduction
    print '\n***Running induction'
    abc('w %s_temp.aig'%f_name)
    abc('orpos; ind -uv -C %d -F 10'%C)
    abc('r %s_savetemp.aig'%f_name)
    status = prob_status()
    if not status == 1:
        return Undecided_reduction
    print 'Induction succeeded'
    return Unsat

def final_verify_recur(K):
    """During prove we make backups as we go. These backups have increasing abstractions done, which can cause
    non-verification by allowing false counterexamples. If an abstraction fails with a cex, we can back up to
    the previous design before the last abstraction and try to proceed from there. K is the backup number we
    start with and this decreases as the backups fails. For each backup, we just try final_verify.
    If ever we back up to 0, which is the backup just after simplify, we then try speculate on this. This often works
    well if the problem is a SEC problem where there are a lot of equivalences across the two designs."""
    for j in range(K):
        i = K-(j+1)
        if i == 0: #don't try final verify on original
            status = 3
            break
        print '\nVerifying backup number %d:'%i,
        abc('r %s_backup_%d.aig'%(initial_f_name,i))
        print_circuit_stats()
        status = final_verify()
        if status >= Unsat:
            return status
        if  i > 0:
            print 'SAT returned, Running less abstract backup'
            continue
        break
    if ((i == 0) and (status > Unsat) and (n_ands() > 0)):
        print '\n***Running speculate on initial backup number %d:'%i,
        abc('r %s_backup_%d.aig'%(initial_f_name,i))
        ps()
        if n_ands() < 20000:
            status = speculate()
            if ((status <= Unsat) or (status == Error)):
                return status
        status = final_verify()
    if status == Unsat:
        return status
    else:
        return Undecided_reduction
        

def smp():
    pre_simp()
    write_file('smp')

def pre_simp():
    """This uses a set of simplification algorithms which preprocesses a design.
    Includes forward retiming, quick simp, signal correspondence with constraints, trimming away
    PIs, and strong simplify"""
##    print "Trying BMC for 2 sec."
##    abc("&get; ,bmc -vt=2")
##    if is_sat():
##        return Sat_true
    set_globals()
    if n_latches == 0:
        return check_sat()
    #print '\n*** Running forward'
    try_forward()
    #print \n*** Running quick simp'
    quick_simp()
    #print 'Running_scorr_constr'
    status = try_scorr_constr()
    #status = 3
    #print 'Running trm'
    if ((n_ands() > 0) or (n_latches()>0)):
        abc('trm')
    print 'Forward, quick_simp, scorr_constr,: ',
    print_circuit_stats()
    if n_latches() == 0:
        return check_sat()
    status = process_status(status)
    if status <= Unsat:
        return status
    simplify()
    print 'Simplify: ',
    print_circuit_stats()
    #abc('w temp_simp.aig')
    if n_latches() == 0:
        return check_sat()
    try_phase()
    if n_latches() == 0:
        return check_sat()
    #abc('trm')
    if ((n_ands() > 0) or (n_latches()>0)):
        abc('trm')
    status = process_status(status)
    if status <= Unsat:
        return status
    status = try_scorr_constr()
    abc('trm')
    return process_status(status)

def try_scorr_constr():
    set_size()
    abc('w %s_savetemp.aig'%f_name)
    status = scorr_constr()
    if inferior_size():
        abc('r %s_savetemp.aig'%f_name)
    return status

def process(status):
    """Checks if there are no FF and if so checks if the remaining combinational
    problem is UNSAT"""
    if n_latches() == 0:
        return check_sat()
    return status

def try_phase():
    """Tries phase abstraction. ABC returns the maximum clock phase it found using n_phases.
    Then unnrolling is tried up to that phase and the unrolled model is quickly
    simplified (with retiming to see if there is a significant reduction.
    If not, then revert back to original""" 
    n = n_phases()
    if ((n == 1) or (n_ands() > 40000)):
        return
    print 'Number of possible phases = %d'%n
    abc('w %s_savetemp.aig'%f_name)
    na = n_ands()
    nl = n_latches()
    ni = n_pis()
    no = n_pos()
    cost_init = (1*n_pis())+(2*n_latches())+1*n_ands()
    cost_min = cost_init
    cost = cost_init
    abc('w %s_best.aig'%f_name)
    for j in range(4):
        abc('r %s_savetemp.aig'%f_name)
        p = 2**(j+1)
        if p > n:
            break
        abc('phase -F %d'%p)
        if na == n_ands():
            break
        abc('scl;rw')
        if n_latches() > nl: #why would this ever happen
            break
        #print_circuit_stats()
        abc('rw;lcorr;trm')
        #print_circuit_stats()
        cost = (1*n_pis())+(2*n_latches())+1*n_ands()
        if cost < cost_min:
            cost_min = cost
            abc('w %s_best.aig'%f_name)
        else:
            break
    if cost < cost_init:
        abc('r %s_best.aig'%f_name)
        simplify()
        abc('trm')
        print 'Phase abstraction obtained :',
        print_circuit_stats()
        return
    abc('r %s_savetemp.aig'%f_name)
    return       

def try_forward():
    """Attempts most forward retiming, and latch correspondence there. If attempt fails to help simplify, then we revert back to the original design
    This can be effective for equivalence checking problems where synthesis used retiming"""
    abc('w %s_savetemp.aig'%f_name)
    if n_ands() < 30000:
        abc('dr')
        abc('lcorr')
        nl = n_latches()
        na = n_ands()
        abc('w %s_savetemp0.aig'%f_name)
        abc('r %s_savetemp.aig'%f_name) 
        abc('dr -m')
        abc('lcorr')
        abc('dr')
        if ((n_latches() <= nl) and (n_ands() < na)):
            print 'Forward retiming reduced size to: ',
            print_circuit_stats()
            return
        else:
            abc('r %s_savetemp0.aig'%f_name)
            return
    return       

def quick_simp():
    """A few quick ways to simplify a problem before more expensive methods are applied.
    Uses & commands if problem is large. These commands use the new circuit based SAT solver"""
    na = n_ands()
    if na < 30000:
        abc('scl;rw')
    elif na < 80000:
        abc('&get;&scl;&put;rw')

def scorr_constr():
    """Extracts implicit constraints and uses them in signal correspondence
    Constraints that are found are folded back when done"""
    na = max(1,n_ands())
    if ((na > 40000) or n_pos()>1):
        return Undecided_no_reduction
    f = 40000/na
    f = min(f,16)
    n_pos_before = n_pos()
    f = 1 #temporary until bug fixed.
    abc('w %s_savetemp.aig'%f_name)
    if n_ands() < 3000:
        cmd = 'unfold -a -F 2'
    else:
        cmd = 'unfold'
    abc(cmd)
    if ((n_ands() > na) or (n_pos() == n_pos_before)):
        abc('r %s_savetemp.aig'%f_name)
        return Undecided_no_reduction
    print_circuit_stats()
    print 'Number of constraints = %d'%(n_pos() - n_pos_before)
    abc('scorr -c -F %d'%f)
    abc('fold')
    return Undecided_no_reduction

def process_status(status):
    """ if there are no FF, the problem is combinational and we still have to check if UNSAT"""
    if n_latches() == 0:
        return check_sat()
    return status

def input_x_factor():
    """Sets the global x_factor according to user input"""
    global x_factor, xfi
    print 'Type in x_factor:',
    xfi = x_factor = input()
    print 'x_factor set to %f'%x_factor

def prove(a):
    """Proves all the outputs together. If ever an abstraction was done then if SAT is returned,
        we make RESULT return "undecided".
        If a == 1 do not run speculate"""
    global x_factor,xfi,f_name
    x = time.clock()
    max_bmc = -1
    K = 0
    print 'Initial: ',
    print_circuit_stats()
    x_factor = xfi
    print 'x_factor = %f'%x_factor
    print '\n***Running pre_simp'
    set_globals()
    if n_latches() > 0:
        status = pre_simp()
    else:
        status = check_sat()
    if ((status <= Unsat) or (n_latches() == 0)):
        print 'Time for proof = %f sec.'%(time.clock() - x)
        return RESULT[status]
    if n_ands() == 0:
        #abc('bmc3 -T 2')
        abc('&get;,bmc -vt=2')
        if is_sat():
            return 'SAT'
    abc('trm')
    write_file('smp')
    abc('w %s_backup_%d.aig'%(initial_f_name,K))
    K = K +1
    set_globals()
##    if ((n_ands() < 30000) and (a == 1) and (n_latches() < 300)):
    if ((n_ands() < 30000) and (n_latches() < 300)):
        print '\n***Running quick_verify'
        status = quick_verify(0)
        if status <= Unsat:
            if not status == Unsat:
                print 'CEX in frame %d'%cex_frame()
            print 'Time for proof = %f sec.'%(time.clock() - x)
            return RESULT[status]
        if n_ands() == 0:
            #abc('bmc3 -T 2')
            abc('&get;,bmc -vt=2')
            if is_sat():
                return 'SAT'
    print'\n***Running abstract'
    nl_b = n_latches()
    status = abstract()
    abc('trm')
    write_file('abs')
    status = process_status(status)
    if ((status <= Unsat)  or  status == Error):
        if  status < Unsat:
            print 'CEX in frame %d'%cex_frame()
##            status = final_verify_recur(K)
##            write_file('final')
            print 'Time for proof = %f sec.'%(time.clock() - x)
            return RESULT[status]
        print 'Time for proof = %f sec.'%(time.clock() - x)
        return RESULT[status]
    abc('w %s_backup_%d.aig'%(initial_f_name,K))
    K = K +1
    if ((n_ands() > 20000) or (a == 1)):
        print 'Speculation skipped because either too large or already done'
        K = 2
    elif n_ands() == 0:
        print 'Speculation skipped because no AND nodes'
        K = 2
    else:
        print '\n***Running speculate'
        status = speculate()
        abc('trm')
        write_file('spec')
        status = process_status(status)
        if status == Unsat:
            print 'Time for proof = %f sec.'%(time.clock() - x)
            return RESULT[status]
        if ((status < Unsat) or (status == Error)):
            print 'CEX in frame %d'%cex_frame()
            K = K-1 #if spec found a true cex, then result of abstract was wrong
        else:
            abc('w %s_backup_%d.aig'%(initial_f_name,K))
            K = K +1
    status = final_verify_recur(K)
    abc('trm')
    write_file('final')
    print 'Time for proof = %f sec.'%(time.clock() - x)
    return RESULT[status]

def prove_g_pos(a):
    """Proves the outputs clustered by a parameter a. 
    a is the disallowed increase in latch support Clusters must be contiguous
    If a = 0 then outputs are proved individually. Clustering is done from last to first
    Output 0 is attempted to be proved inductively using other outputs as constraints.
    Proved outputs are removed if all the outputs have not been proved.
    If ever one of the proofs returns SAT, we stop and do not try any other outputs."""
    global f_name, max_bmc,x_factor
    x = time.clock()
    #input_x_factor()
    init_f_name = f_name
    #fast_int(1)
    print 'Beginning prove_g_pos'
    prove_all_ind()
    print 'Number of outputs reduced to %d by induction and fast interpolation'%n_pos()
    print '\n************Running second level prove****************\n'
    try_rpm()
    result = prove(1) # 1 here means do not try speculate.
    #result = prove_0_ind()
    if result == 'UNSAT':
        print 'Second prove returned UNSAT'
        return result
    if result == 'SAT':
        print 'CEX found'
        return result
    print '\n********** Proving each output separately ************'
    prove_all_ind()
    print 'Number of outputs reduced to %d by induction and fast interpolation'%n_pos()
    f_name = init_f_name
    abc('w %s_osavetemp.aig'%f_name)
    n = n_pos()
    print 'Number of outputs = %d'%n
    #count = 0
    pos_proved = []
    J = 0
    jnext = n-1
    while jnext >= 0:
        max_bmc = -1
        f_name = init_f_name
        abc('r %s_osavetemp.aig'%f_name)
        #Do in reverse order
        jnext_old = jnext
        if a == 0: # do not group
            extract(jnext,jnext)
            jnext = jnext -1 
        else:
            jnext = group(a,jnext)
        if jnext_old > jnext+1:
            print '\nProving outputs [%d-%d]'%(jnext + 1,jnext_old)
        else:
            print '\nProving output %d'%(jnext_old)
        #ps()
        #fast_int(1)
        f_name = f_name + '_%d'%jnext_old
        result = prove_1()
        if result == 'UNSAT':
            if jnext_old > jnext+1:
                print '\n********  PROVED OUTPUTS [%d-%d]  ******** \n\n'%(jnext+1,jnext_old)
            else:
                print '\n********  PROVED OUTPUT %d  ******** \n\n'%(jnext_old)
            pos_proved = pos_proved + range(jnext +1,jnext_old+1)
            continue
        if result == 'SAT':
            print 'One of output in (%d to %d) is SAT'%(jnext + 1,jnext_old)
            return result
        else:
            print '\n********  UNDECIDED on OUTPUTS %d thru %d  ******** \n\n'%(jnext+1,jnext_old)
    f_name = init_f_name
    abc('r %s_osavetemp.aig'%f_name)
    if not len(pos_proved) == n:
        print 'Eliminating %d proved outputs'%(len(pos_proved))
        remove(pos_proved)
        abc('trm')
        write_file('group')
        result = 'UNDECIDED'
    else:
        print 'Proved all outputs. The problem is proved UNSAT'
        result = 'UNSAT'
    print 'Total time for prove_g_pos = %f sec.'%(time.clock() - x)
    return result

def prove_pos():
    """
    Proved outputs are removed if all the outputs have not been proved.
    If ever one of the proofs returns SAT, we stop and do not try any other outputs."""
    global f_name, max_bmc,x_factor
    x = time.clock()
    #input_x_factor()
    init_f_name = f_name
    #fast_int(1)
    print 'Beginning prove_pos'
    prove_all_ind()
    print 'Number of outputs reduced to %d by induction and fast interpolation'%n_pos()
    print '\n********** Proving each output separately ************'
    f_name = init_f_name
    abc('w %s_osavetemp.aig'%f_name)
    n = n_pos()
    print 'Number of outputs = %d'%n
    #count = 0
    pos_proved = []
    pos_disproved = []
    J = 0
    jnext = n-1
    while jnext >= 0:
        max_bmc = -1
        f_name = init_f_name
        abc('r %s_osavetemp.aig'%f_name)
        #Do in reverse order
        jnext_old = jnext
        extract(jnext,jnext)
        jnext = jnext -1 
        print '\nProving output %d'%(jnext_old)
        f_name = f_name + '_%d'%jnext_old
        result = prove_1()
        if result == 'UNSAT':
            print '\n********  PROVED OUTPUT %d  ******** \n\n'%(jnext_old)
            pos_proved = pos_proved + range(jnext +1,jnext_old+1)
            continue
        if result == 'SAT':
            print '\n********  DISPROVED OUTPUT %d  ******** \n\n'%(jnext_old)
            pos_disproved = pos_disproved + range(jnext +1,jnext_old+1)
            continue
        else:
            print '\n********  UNDECIDED on OUTPUT %d  ******** \n\n'%(jnext_old)
    f_name = init_f_name
    abc('r %s_osavetemp.aig'%f_name)
    list = pos_proved + pos_disproved
    print 'Proved the following outputs: %s'%pos_proved
    print 'Disproved the following outputs: %s'%pos_disproved
    if not len(list) == n:
        print 'Eliminating %d resolved outputs'%(len(list))
        remove(list)
        abc('trm')
        write_file('group')
        result = 'UNRESOLVED'
    else:
        print 'Proved or disproved all outputs. The problem is proved RESOLVED'
        result = 'RESOLVED'
    print 'Total time for prove_pos = %f sec.'%(time.clock() - x)
    return result


def prove_g_pos_split():
    """like prove_g_pos but quits when any output is undecided"""
    global f_name, max_bmc,x_factor
    x = time.clock()
    #input_x_factor()
    init_f_name = f_name
    #fast_int(1)
    print 'Beginning prove_g_pos_split'
    prove_all_ind()
    print 'Number of outputs reduced to %d by induction and fast interpolation'%n_pos()
    try_rpm()
    print '\n********** Proving each output separately ************'  
    f_name = init_f_name
    abc('w %s_osavetemp.aig'%f_name)
    n = n_pos()
    print 'Number of outputs = %d'%n
    pos_proved = []
    J = 0
    jnext = n-1
    while jnext >= 0:
        max_bmc = -1
        f_name = init_f_name
        abc('r %s_osavetemp.aig'%f_name)
        jnext_old = jnext
        extract(jnext,jnext)
        jnext = jnext -1
        print '\nProving output %d'%(jnext_old)
        f_name = f_name + '_%d'%jnext_old
        result = prove_1()
        if result == 'UNSAT':
            if jnext_old > jnext+1:
                print '\n********  PROVED OUTPUTS [%d-%d]  ******** \n\n'%(jnext+1,jnext_old)
            else:
                print '\n********  PROVED OUTPUT %d  ******** \n\n'%(jnext_old)
            pos_proved = pos_proved + range(jnext +1,jnext_old+1)
            continue
        if result == 'SAT':
            print 'One of output in (%d to %d) is SAT'%(jnext + 1,jnext_old)
            return result
        else:
            print '\n********  UNDECIDED on OUTPUTS %d thru %d  ******** \n\n'%(jnext+1,jnext_old)
            print 'Eliminating %d proved outputs'%(len(pos_proved))
            # remove outputs proved and return
            f_name = init_f_name
            abc('r %s_osavetemp.aig'%f_name)
            remove(pos_proved)
            abc('trm')
            write_file('group')            
            return 'UNDECIDED'
    f_name = init_f_name
    abc('r %s_osavetemp.aig'%f_name)
    if not len(pos_proved) == n:
        print 'Eliminating %d proved outputs'%(len(pos_proved))
        remove(pos_proved)
        abc('trm')
        write_file('group')
        result = 'UNDECIDED'
    else:
        print 'Proved all outputs. The problem is proved UNSAT'
        result = 'UNSAT'
    print 'Total time = %f sec.'%(time.clock() - x)
    return result



def group(a,n):
    """Groups together outputs beginning at output n and any contiguous preceeding output
    that does not increase the latch support by a or more"""
    global f_name, max_bmc
    nlt = n_latches()
    extract(n,n)
    nli = n_latches()
    if n == 0:
        return n-1
    for J in range(1,n+1):
        abc('r %s_osavetemp.aig'%f_name)
        j = n-J
        #print 'Running %d to %d'%(j,n)
        extract(j,n)
        #print 'n_latches = %d'%n_latches()
        #if n_latches() >= nli + (nlt - nli)/2:
        if n_latches() == nli:
            continue
        if n_latches() > nli+a:
            break
    abc('r %s_osavetemp.aig'%f_name)
##    if j == 1:
##        j = j-1
    print 'extracting [%d-%d]'%(j,n)
    extract(j,n)
    ps()
    return j-1
        
def extract(n1,n2):
    """Extracts outputs n1 through n2"""
    no = n_pos()
    if n2 > no:
        return 'range exceeds number of POs'
    abc('cone -s -O %d -R %d'%(n1, 1+n2-n1))
    abc('scl')

def prove_0_ind():
    """Uses all other outputs as constraints to try to prove output 0 by induction"""
    abc('w %s_osavetemp.aig'%f_name)
    #ps()
    abc('constr -N %d'%(n_pos()-1))
    #ps()
    abc('fold')
    #ps()
    abc('ind -u -C 1000000 -F 20')
    status = get_status()
    abc('r %s_osavetemp.aig'%f_name)
    return status

def remove(list):
    """Removes outputs in list"""
    zero(list)
    abc('&get;&trim;&put')
    #fast_int(1)

def zero(list):
    """Zeros out POs in list"""
    for j in list:
        run_command('zeropo -N %d'%j)

def sp():
    """Alias for super_prove"""
    print 'Executing super_prove'
    result = super_prove()
    return result

def super_prove():
    """Main proof technique now. Does original prove and if after speculation there are multiple output left
    if will try to prove each output separately, in reverse order. It will quit at the first output that fails
    to be proved, or any output that is proved SAT"""
    global max_bmc, init_initial_f_name, initial_f_name
    init_initial_f_name = initial_f_name
    if x_factor > 1:
        print 'x_factor = %d'%x_factor
        input_x_factor()
    max_bmc = -1
    x = time.clock()
    print "Trying BMC for 2 sec."
    abc("&get; ,bmc -vt=2")
    if is_sat():
        print 'Total time taken by super_prove = %f sec.'%(time.clock() - x)
        return 'SAT'
    result = prove(0)
    if ((result[:3] == 'UND') and (n_latches() == 0)):
        return result
    k = 1
    print result
    if not result[:3] == 'UND':
        print 'Total time taken by super_prove = %f sec.'%(time.clock() - x)
        return result
    if n_pos() > 1:
        result = prove_g_pos(0)
        print result
        if result == 'UNSAT':
            print 'Total time taken by super_prove = %f sec.'%(time.clock() - x)
            return result
        if result == 'SAT':
            k = 0 #Don't try to prove UNSAT on an abstraction that had SAT
                    # should go back to backup 1 since probably spec was bad.
    y = time.clock()
    result = BMC_VER_result(k)
    print 'Total time taken by last gasp verification = %f sec.'%(time.clock() - y)
    print 'Total time for %s = %f sec.'%(init_initial_f_name,(time.clock() - x))
    return result

def reachm(t):
    x = time.clock()
    run_command('&get;&reach -vcs -T %d;&put'%t)
    print 'Time = %f'%(time.clock() - x)
    
def reachx(t):
    x = time.clock()
    run_command('reachx -t %d'%t)
    print 'Time = %f'%(time.clock() - x)

def BMC_VER_result(n):
    global init_initial_f_name
    #print init_initial_f_name
    xt = time.clock()
    result = 5
    T = 150
    if n == 0:
        abc('r %s_smp.aig'%init_initial_f_name)
        print '\n***Running proof on initial simplified circuit\n',
        ps()
    else:
        print '\n***Running proof on final unproved circuit'
        ps()
    print '    Running PDR for %d sec'%T
    abc('&get;,pdr -vt=%d'%(T*.8))
    result = get_status()
    if result == Unsat:
        return 'UNSAT'
    if result > Unsat: #still undefined
        if (n_pis()+n_latches() < 250):
            print '    Running Reachability for 150 sec.'
            abc('reachx -t 150')
            #run_command('&get;&reach -vcs -T %d'%T)
            result = get_status()
            if result == Unsat:
                return 'UNSAT'
        if ((result > Unsat) and n ==1):
            print '    Running interpolation for %f sec.'%T
            abc(',imc -vt=%f'%T)
            result = get_status()
            if result == Unsat:
                return 'UNSAT'
    # if n=1 we are trying to prove result on abstracted circuit. If still undefined, then probably does
    # not make sense to try pdr, reach, int on original simplified circuit, only BMC here.
    if n == 1:
        abc('r %s_smp.aig'%init_initial_f_name) #check if the initial circuit was SAT
        #print 'Reading %s_smp'%init_initial_f_name,
    #run_command('bmc3 -v -T %d -F 200000 -C 1000000'%T)
    print '***Running BMC on initial simplified circuit'
    ps()
    print '\n'
    abc('&get;,bmc -vt=%f'%T)
    result = get_status()
    if result < Unsat:
        result = 'SAT'
        print ' CEX found in frame %d'%cex_frame()
    else:
        result = 'UNDECIDED'
    print 'Additional time taken by BMC/PDR/Reach = %f sec.'%(time.clock() - xt)
    return result

def try_split():
    abc('w %s_savetemp.aig'%f_name)
    na = n_ands()
    split(3)
    if n_ands()> 2*na:
        abc('r %s_savetemp.aig'%f_name)
    

def time_diff():
    global last_time
    new_time = time.clock()
    diff = new_time - last_time
    last_time = new_time
    result = 'Lapsed time = %.2f sec.'%diff
    return result

def prove_all_ind():
    """Tries to prove output k by induction, using other outputs as constraints. If ever an output is proved
    it is set to 0 so it can't be used in proving another output to break circularity.
    Finally all zero'ed ooutputs are removed. """
    N = n_pos()
    remove_0_pos()
    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        #abc('r %s_osavetemp.aig'%f_name)
        abc('swappos -N %d'%j)
        remove_0_pos() #may not have to do this if constr works well with 0'ed outputs
        abc('constr -N %d'%(n_pos()-1))
        abc('fold')
        n = max(1,n_ands())
        f = max(1,min(40000/n,16))
        f = int(f)
        abc('ind -u -C 10000 -F %d'%f)
        status = get_status()
        abc('r %s_osavetemp.aig'%f_name)
        if status == Unsat:
            print '+',
            abc('zeropo -N %d'%j)
            abc('w %s_osavetemp.aig'%f_name) #if changed, store it permanently
        print '%d'%j,
    remove_0_pos()
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def prove_all_pdr(t):
    """Tries to prove output k by PDR. If ever an output is proved
    it is set to 0. Finally all zero'ed ooutputs are removed. """
    N = n_pos()
    remove_0_pos()
    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        #abc('r %s_osavetemp.aig'%f_name)
        abc('cone -O %d -s'%j)
        abc('scl')
        abc('&get;,pdr -vt=%d'%t)
        status = get_status()
        abc('r %s_osavetemp.aig'%f_name)
        if status == Unsat:
            print '+',
            abc('zeropo -N %d'%j)
            abc('w %s_osavetemp.aig'%f_name) #if changed, store it permanently
        print '%d'%j,
    remove_0_pos()
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status


def remove_0_pos():
    abc('&get; &trim; &put')

    
def prove_all_ind2():
    """Tries to prove output k by induction, using outputs > k as constraints. Removes proved outputs from POs."""
    abc('w %s_osavetemp.aig'%f_name)
    plist = []
    list = range(n_pos())
##    if r == 1:
##        list.reverse()
    for j in list:
        abc('r %s_osavetemp.aig'%f_name)
        extract(j,n_pos())
        abc('constr -N %d'%(n_pos()-1))
        abc('fold')
        n = max(1,n_ands())
        f = max(1,min(40000/n,16))
        f = int(f)
        abc('ind -u -C 10000 -F %d'%f)
        status = get_status()
        if status == Unsat:
            plist = plist + [j]
            print '-',
##        else:
##            status = pdr(1)
##            if status == Unsat:
##                print '+',
##                plist = plist + [j]
        print '%d'%j,
    print '\nOutputs proved = ',
    print plist
    abc('r %s_osavetemp.aig'%f_name)
    remove(plist) #remove the outputs proved
##    #the following did not work because abc command constr, allows only  last set of outputs to be constraints
##    abc('w %s_osavetemp.aig'%f_name)
##    plist = []
##    list = range(n_pos())
##    list.reverse()
##    for j in list:
##        abc('r %s_osavetemp.aig'%f_name)
##        extract(j,n_pos())
##        abc('constr -N %d'%(n_pos()-1))
##        abc('fold')
##        n = max(1,n_ands())
##        f = max(1,min(40000/n,16))
##        f = int(f)
##        abc('ind -u -C 10000 -F %d'%f)
##        status = get_status()
##        if status == Unsat:
##            plist = plist + [j]
##            print '-',
####        else:
####            status = pdr(1)
####            if status == Unsat:
####                print '+',
####                plist = plist + [j]
##        print '%d'%j,
##    print '\nOutputs proved = ',
##    print plist.reverse
##    abc('r %s_osavetemp.aig'%f_name)
##    remove(plist) #remove the outputs proved
##    return status

def pdr(t):
    abc('&get; ,pdr -vt=%f'%t)
    result = get_status()

def split(n):
    abc('orpos;&get')
    abc('&posplit -v -N %d;&put;dc2;trm'%n)

def keep_splitting():
    for j in range(5):
        split(5+j)
        no = n_pos()
        status = prove_g_pos_split(0)
        if status <= Unsat:
            return status
        if no == n_pos():
            return Undecided

def drill(n):
    run_command('&get; &reach -vcs -H 5 -S %d -T 50 -C 40'%n)

def prove_1():
    """Proves all the outputs together. If ever an abstraction was done then if SAT is returned,
        we make RESULT return "undecided".
        """
    a = 1
    global x_factor,xfi,f_name
    x = time.clock()
    max_bmc = -1
    K = 0
    print 'Initial: ',
    print_circuit_stats()
    x_factor = xfi
    print 'x_factor = %f'%x_factor
    print '\n***Running pre_simp'
    set_globals()
    status = pre_simp()
    if ((status <= Unsat) or (n_latches == 0)):
        print 'Time for proof = %f sec.'%(time.clock() - x)
        return RESULT[status]
    abc('trm')
    write_file('smp')
    abc('w %s_backup_%d.aig'%(initial_f_name,K))
    K = K +1
    set_globals()
    if ((n_ands() < 30000) and (a == 1) and (n_latches() < 300)):
        print '\n***Running quick_verify'
        status = quick_verify(0)
        if status <= Unsat:
            if not status == Unsat:
                print 'CEX in frame %d'%cex_frame()
            print 'Time for proof = %f sec.'%(time.clock() - x)
            return RESULT[status]
    print'\n***Running abstract'
    nl_b = n_latches()
    status = abstract()
    abc('trm')
    write_file('abs')
    status = process_status(status)
    if ((status <= Unsat)  or  status == Error):
        if  status < Unsat:
            print 'CEX in frame %d'%cex_frame()
            print 'Time for proof = %f sec.'%(time.clock() - x)
            return RESULT[status]
        print 'Time for proof = %f sec.'%(time.clock() - x)
        return RESULT[status]
    abc('w %s_backup_%d.aig'%(initial_f_name,K))
    status = final_verify_recur(2)
    abc('trm')
    write_file('final')
    print 'Time for proof = %f sec.'%(time.clock() - x)
    return RESULT[status]

def qprove():
    global x_factor
    x = time.clock()
    x_factor = 3
    print '\n*********pre_simp**********\n'
    pre_simp()
    print '\n*********absv**********\n'
    result = absv(3,1)
    x_factor = 2
    print '\n*********absv**********\n'
    result = absv(3,1)
    print '\n*********speculate**********\n'
    result = speculate()
    if result <= Unsat:
        return RESULT[result]
    print '\n*********absv**********\n'
    result = absv(3,1)
    print '\n*********prove_pos**********\n'
    result = prove_pos()
    if result == 'UNDECIDED':
        print '\n*********BMC_VER_result**********\n'
        result = BMC_VER_result(1)
    print 'Time for proof = %f sec.'%(time.clock() - x)
    return result
    
def pre_reduce():
    x = time.clock()
    pre_simp()
    write_file('smp')
    abstract()
    write_file('abs')
    print 'Time = %f'%(time.clock() - x)


#PARALLEL FUNCTIONS
"""  funcs should look like
funcs = [defer(abc)('&get;,bmc -vt=50;&put'),defer(super_prove)()]
After this is executed funcs becomes a special list of lambda functions
which are given to abc_split_all to be executed as in fork below.
It has been set up so that each of the functions works on the current aig and
possibly transforms it. The new aig and status is always read into the master when done

"""

def fork(funcs):
    """ runs funcs in parallel"""
    for i,res in pyabc_split.abc_split_all(funcs):
        status = prob_status()
        if not status == -1:
            print i,status
            ps()
            break
        else:
            print i,status
            ps()
            continue
    return status

def handler_s(res):
    """ This serial handler returns True if the problem is solved by the first returning function,
    in which case, the problem is replaced by the new aig and status.
    """
    if not res == -1:
        #replace_prob()
        print ('UNSAT','SAT')[res]
        return True
    else:
        return False
    
