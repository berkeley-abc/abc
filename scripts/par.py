from pyabc import *
import pyabc_split
import redirect
import sys
import os
import time
import math
import main

global G_C,G_T,latches_before_abs,latches_before_pba,n_pos_before,x_factor,methods,last_winner
global last_cex,JV,JP, cex_list,max_bmc, last_cx, pord_on

"""
The functions that are currently available from module _abc are:

int n_ands();
int n_pis();
int n_pos();
int n_latches();
int n_bmc_frames();
int prob_status(); 1 = unsat, 0 = sat, -1 = unsolved
int cex_get()
int cex_put()
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
#________________________________________________
stackno_gabs = stackno_gore = stackno_greg= 0
STATUS_UNKNOWN = -1
STATUS_SAT = 0
STATUS_UNSAT = 1
RESULT = ('SAT' , 'SAT', 'UNSAT', 'UNDECIDED', 'UNDECIDED,', 'UNDECIDED'  )
Sat = Sat_reg = 0
Sat_true = 1
Unsat = 2
Undecided = Undecided_reduction = 3
Undecided_no_reduction = 4
Error = 5
Restart = 6
xfi = x_factor = 1  #set this to higher for larger problems or if you want to try harder during abstraction
max_bmc = -1
last_time = 0
j_last = 0
seed = 113
init_simp = 1
K_backup = init_time = 0
last_verify_time = 20
last_cex = last_winner = 'None'
last_cx = 0
trim_allowed = True
pord_on = False
sec_sw = False
sec_options = ''
cex_list = []
TERM = 'USL'
t_init = 2 #initial time for poor man's concurrency.
methods = ['PDR', 'INTRP', 'BMC',
           'SIM', 'REACHX',
           'PRE_SIMP', 'SUPER_PROVE2', 'PDRM', 'REACHM', 'BMC3','Min_Retime',
           'For_Retime','REACHP','REACHN','PDRsd','prove_part_2',
           'prove_part_3','verify','sleep','PDRMm','prove_part_1',
           'run_parallel','INTRPb', 'INTRPm', 'REACHY', 'REACHYc','RareSim','simplify', 'speculate',
           'quick_sec', 'BMC_J']
#'0.PDR', '1.INTERPOLATION', '2.BMC', '3.SIMULATION',
#'4.REACHX', '5.PRE_SIMP', '6.SUPER_PROVE', '7.PDRM', '8.REACHM', 9.BMC3'
# 10. Min_ret, 11. For_ret, 12. REACHP, 13. REACHN 14. PDRseed 15.prove_part_2,
#16.prove_part_3, 17.verify, 18.sleep, 19.PDRMm, 20.prove_part_1,
#21.run_parallel, 22.INTRP_bwd, 23. Interp_m 24. REACHY 25. REACHYc 26. Rarity Sim 27. simplify
#28. speculate, 29. quick_sec, 30 bmc3 -S
win_list = [(0,.1),(1,.1),(2,.1),(3,.1),(4,.1),(5,-1),(6,-1),(7,.1)]
FUNCS = ["(pyabc_split.defer(abc)('&get;,pdr -vt=%f'%t))",
         "(pyabc_split.defer(abc)('&get;,imc -vt=%f'%(t)))",
         "(pyabc_split.defer(abc)('&get;,bmc -vt=%f'%t))",
         "(pyabc_split.defer(simulate)(t))",
         "(pyabc_split.defer(abc)('reachx -t %d'%t))",
         "(pyabc_split.defer(pre_simp)())",
         "(pyabc_split.defer(super_prove)(2))",
         "(pyabc_split.defer(pdrm)(t))",
         "(pyabc_split.defer(abc)('&get;&reachm -vcs -T %d'%t))",
         "(pyabc_split.defer(abc)('bmc3 -C 1000000 -T %f'%t))",
         "(pyabc_split.defer(abc)('dr;&get;&lcorr;&dc2;&scorr;&put;dr'))",
         "(pyabc_split.defer(abc)('dr -m;&get;&lcorr;&dc2;&scorr;&put;dr'))",
         "(pyabc_split.defer(abc)('&get;&reachp -vr -T %d'%t))",
         "(pyabc_split.defer(abc)('&get;&reachn -vr -T %d'%t))",
         "(pyabc_split.defer(abc)('&get;,pdr -vt=%f -seed=521'%t))",
         "(pyabc_split.defer(prove_part_2)(K))",
         "(pyabc_split.defer(prove_part_3)(K))",
         "(pyabc_split.defer(verify)(JV,t))",
         "(pyabc_split.defer(sleep)(t))",
         "(pyabc_split.defer(pdrmm)(t))",
         "(pyabc_split.defer(prove_part_1)'(%d)'%(K))",
         "(pyabc_split.defer(run_parallel)(JP,t,'TERM'))",
         "(pyabc_split.defer(abc)('&get;,imc -bwd -vt=%f'%t))",
         "(pyabc_split.defer(abc)('int -C 1000000 -F 10000 -K 2 -T %f'%t))",
         "(pyabc_split.defer(abc)('&get;&reachy -v -T %d'%t))",
         "(pyabc_split.defer(abc)('&get;&reachy -cv -T %d'%t))",
         "(pyabc_split.defer(simulate2)(t))",
         "(pyabc_split.defer(simplify)())",
         "(pyabc_split.defer(speculate)())",
         "(pyabc_split.defer(quick_sec)(t))",
         "(pyabc_split.defer(bmc_s)(t))"
         ]
##         "(pyabc_split.defer(abc)('bmc3 -C 1000000 -T %f -S %d'%(t,int(1.5*max_bmc))))"
#note: interp given 1/2 the time.
allreachs = [4,8,12,13,24,25]
reachs = [24]
allpdrs = [0,7,14,19]
pdrs = [0,7]
allbmcs = [2,9,30]
exbmcs = [2,9]
bmcs = [9,30]
allintrps = [1,22,23]
bestintrps = [23]
intrps = [23]
allsims = [3,26]
sims = [3]
allslps = [18]
slps = [18]

JVprove = [7,1,4,24]
JV = pdrs+intrps+bmcs+sims #sets what is run in parallel '17. verify' above
JP = JV + [27] # sets what is run in  '21. run_parallel' above 27 simplify should be last because it can't time out.
#_____________________________________________________________


# Function definitions:
# simple functions: ________________________________________________________________________
# set_globals, abc, q, x, has_any_model, is_sat, is_unsat, push, pop

# ALIASES

def initialize():
    global xfi, max_bmc, last_time,j_last, seed, init_simp, K_backup, last_verify_time
    global init_time, last_cex, last_winner, trim_allowed, t_init, sec_options, sec_sw
    global n_pos_before, n_pos_proved, last_cx, pord_on
    xfi = x_factor = 1  #set this to higher for larger problems or if you want to try harder during abstraction
    max_bmc = -1
    last_time = 0
    j_last = 0
    seed = 113
    init_simp = 1
    K_backup = init_time = 0
    last_verify_time = 20
    last_cex = last_winner = 'None'
    last_cx = 0
    trim_allowed = True
    pord_on = False
    t_init = 2 #this will start sweep time in find_cex_par to 2*t_init here
    sec_sw = False
    sec_options = ''
    cex_list = []
    n_pos_before = n_pos()
    n_pos_proved = 0

def ps():
    print_circuit_stats()

def n_real_inputs():
    """This gives the number of 'real' inputs. This is determined by trimming away inputs that
    have no connection to the logic. This is done by the ABC alias 'trm', which changes the current
    circuit. In some applications we do not want to change the circuit, but just to know how may inputs
    would go away if we did this. So the current circuit is saved and then restored afterwards."""
##    abc('w %s_savetempreal.aig; logic; trim; st ;addpi'%f_name)
    abc('w %s_savetempreal.aig'%f_name)
    with redirect.redirect( redirect.null_file, sys.stdout ):
##        with redirect.redirect( redirect.null_file, sys.stderr ):
        reparam()
    n = n_pis()
    abc('r %s_savetempreal.aig'%f_name)
    return n

def timer(t):
    btime = time.clock()
    time.sleep(t)
    print t
    return time.clock() - btime

def sleep(t):
    time.sleep(t)
    return Undecided
        
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

def convert(t):
    t = int(t*100)
    return str(float(t)/100)

def set_engines(N=0):
    """
    Sets the MC engines that are used in verification according to
    if there are 4 or 8 processors.
    """
    global reachs,pdrs,sims,intrps,bmcs
    if N == 0:
        N = os.sysconf(os.sysconf_names["SC_NPROCESSORS_ONLN"])
    if N == 1:
        reachs = [24]
        pdrs = [7]
##        bmcs = [30]
        bmcs = [9]
        intrps = []
        sims = []
        slps = [18]
    elif N == 2:
        reachs = [24]
        pdrs = [7]
        bmcs = [30]
        intrps = []
        sims = []
        slps = [18]
    elif N == 4:
        reachs = [24]
        pdrs = [7]
        bmcs = [9,30]
        intrps = [23]
        sims = []
        slps = [18]
    elif N == 8:
        reachs = [24]
        pdrs = [0,7]
        bmcs = [9,30]
        intrps = [23]
        sims = [3]
        slps = [18]

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

def remove_spaces(s):
    y = ''
    for t in s:
        if not t == ' ':
            y = y + t
    return y

def read_file_quiet(fname=None):
    """This is the main program used for reading in a new circuit. The global file name is stored (f_name)
    Sometimes we want to know the initial starting name. The file name can have the .aig extension left off
    and it will assume that the .aig extension is implied. This should not be used for .blif files.
    Any time we want to process a new circuit, we should use this since otherwise we would not have the
    correct f_name."""
    global max_bmc,  f_name, d_name, initial_f_name, x_factor, init_initial_f_name, win_list,seed, sec_options
    global win_list, init_simp, po_map
    set_engines(4) #temporary
    ps()
    init_simp = 1
    win_list = [(0,.1),(1,.1),(2,.1),(3,.1),(4,.1),(5,-1),(6,-1),(7,.1)] #initialize winning engine list
    po_map = range(n_pos())
    initialize()
##    x_factor = 1
##    seed = 223
##    max_bmc = -1
    if fname is None:
        print 'Type in the name of the aig file to be read in'
        s = raw_input()
        s = remove_spaces(s)
    else:
        s = fname
    if s[-4:] == '.aig':
        f_name = s[:-4]
    else:
        f_name = s
        s = s+'.aig'
##    run_command(s)
    run_command('&r %s;&put'%s)
    set_globals()
    initial_f_name = f_name
    init_initial_f_name = f_name
    abc('addpi')
    
def read_file():
    global win_list, init_simp, po_map
    read_file_quiet()
##    ps()
##    init_simp = 1
##    win_list = [(0,.1),(1,.1),(2,.1),(3,.1),(4,.1),(5,-1),(6,-1),(7,.1)] #initialize winning engine list
##    po_map = range(n_pos())

def rf():
##    set_engines(4) #temporary
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
    ps()
    abc('w '+ss)

def bmc_depth():
    """ Finds the number of BMC frames that the latest operation has used. The operation could be BMC, reachability
    interpolation, abstract, speculate. max_bmc is continually increased. It reflects the maximum depth of any version of the circuit
    including g ones, for which it is known that there is not cex out to that depth."""
    global max_bmc
    c = cex_frame()
    if c > 0:
        b = c-1
    else:
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
            print 'PIs=%d,POs=%d,FF=%d,ANDs=%d,max depth=%d,CEX depth=%d'%(i,o,l,a,b,c)
        elif is_unsat():
            print 'PIs=%d,POs=%d,FF=%d,ANDs=%d,max depth = infinity'%(i,o,l,a)
        else:
            print 'PIs=%d,POs=%d,FF=%d,ANDs=%d,max depth=%d'%(i,o,l,a,b)            
    else:
        if c>=0:
            print 'PIs=%d,POs=%d,FF=%d,ANDs=%d,CEX depth=%d'%(i,o,l,a,c)
        else:
            print 'PIs=%d,POs=%d,FF=%d,ANDs=%d'%(i,o,l,a)

def q():
    exit()

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

#more complex functions: ________________________________________________________
#, abstract, pba, speculate, final_verify, dprove3

def timer(s):
    btime = time.clock()
    abc(s)
    print 'time = %f'%(time.clock() - btime)

def med_simp():
    x = time.time()
    abc("&get;&scl;&dc2;&lcorr;&dc2;&scorr;&fraig;&dc2;&put;dr")
    #abc("dc2rs")
    ps()
    print 'time = %f'%(time.time() - x)

def simplify():
    """Our standard simplification of logic routine. What it does depende on the problem size.
    For large problems, we use the &methods which use a simple circuit based SAT solver. Also problem
    size dictates the level of k-step induction done in 'scorr' The stongest simplification is done if
    n_ands < 20000. Then it used the clause based solver and k-step induction where |k| depends
    on the problem size """
    set_globals()
    abc('&get;&scl;&lcorr;&put')
    n =n_ands()
    p_40 = False
    if (40000 < n and n < 100000):
        p_40 = True
        abc("&get;&dc2;&put;dr;&get;&lcorr;&dc2;&put;dr;&get;&scorr;&fraig;&dc2;&put;dr")
        n = n_ands()
        if n<60000:
            abc("&get;&scorr -F 2;&put;dc2rs")
        else: # n between 60K and 100K
            abc("dc2rs")
    n = n_ands()
    if (30000 < n  and n <= 40000):
        if not p_40:
            abc("&get;&dc2;&put;dr;&get;&lcorr;&dc2;&put;dr;&get;&scorr;&fraig;&dc2;&put;dr")
            abc("&get;&scorr -F 2;&put;dc2rs")
        else:
            abc("dc2rs")            
    n = n_ands()
    if n <= 30000:
        abc('scl -m;drw;dr;lcorr;drw;dr')
        nn = max(1,n)
        m = int(min( 60000/nn, 16))
        if m >= 1:
            j = 1
            while j <= m:
                set_size()
                if j<8:
                    abc('dc2')
                else:
                    abc('dc2rs')
                abc('scorr -C 5000 -F %d'%j)
                if check_size():
                    break
                j = 2*j
                continue
    return get_status()
            
def simulate2(t):
    """Does rarity simulation. Simulation is restricted by the amount
    of memory it might use. At first wide but shallow simulation is done, followed by
    successively more narrow but deeper simulation. 
    seed is globally initiallized to 113 when a new design is read in"""
    global x_factor, f_name, tme, seed
    btime = time.clock()
    diff = 0
    while True:
        f = 5
        w = 255
        for k in range(9): #this controls how deep we go
            f = min(f *2, 3500)
            w = max(((w+1)/2)-1,1)
            abc('sim3 -m -F %d -W %d -R %d'%(f,w,seed))
            seed = seed+23
            if is_sat():
                return 'SAT'
            if ((time.clock()-btime) > t):
                return 'UNDECIDED'


def simulate(t):
    abc('&get')
    result = eq_simulate(t)
    return result

def eq_simulate(t):
    """Simulation is restricted by the amount
    of memory it might use. At first wide but shallow simulation is done, followed by
    successively more narrow but deeper simulation. The aig to be simulated must be in the & space
    If there are equivalences, it will refine them. Otherwise it is a normal similation
    seed is globally initiallized to 113 when a new design is read in"""
    global x_factor, f_name, tme, seed
    btime = time.clock()
    diff = 0
    while True:
        f = 5
        w = 255
        for k in range(9):
            f = min(f *2, 3500)
            r = f/20
            w = max(((w+1)/2)-1,1)
##            abc('&sim3 -R %d -W %d -N %d'%(r,w,seed))
            abc('&sim -F %d -W %d -R %d'%(f,w,seed))
            seed = seed+23
            if is_sat():
                return 'SAT'
            if ((time.clock()-btime) > t):
                return 'UNDECIDED'

def generate_abs(n):
    """generates an abstracted  model (gabs) from the greg file. The gabs file is automatically
    generated in the & space by &abs_derive. We store it away using the f_name of the problem
    being solved at the moment. The f_name keeps changing with an extension given by the latest
    operation done - e.g. smp, abs, spec, final, group. """
    global f_name
    #we have a cex and we use this generate a new gabs file
    abc('&r %s_greg.aig; &abs_derive; &put; w %s_gabs.aig'%(f_name,f_name)) # do we still need the gabs file
    if n == 1:
        #print 'New abstraction: ',
        ps()
    return   

def refine_with_cex():
    """Refines the greg (which contains the original problem with the set of FF's that have been abstracted).
    This uses the current cex to modify the greg file to reflect which regs are in the
    new current abstraction"""
    global f_name
    #print 'CEX in frame %d for output %d'%(cex_frame(),cex_po())
    #abc('&r %s_greg.aig; &abs_refine -t; &w %s_greg.aig'%(f_name,f_name))
    abc('&r %s_greg.aig;&w %s_greg_before.aig'%(f_name,f_name))
##    run_command('&abs_refine -s -M 25; &w %s_greg.aig'%f_name)
    run_command('&abs_refine -s; &w %s_greg.aig'%f_name)
    #print ' %d FF'%n_latches()
    return

def abstraction_refinement(latches_before,NBF):
    """Subroutine of 'abstract' which does the refinement of the abstracted model,
    using counterexamples found by BMC or BDD reachability"""
    global x_factor, f_name, last_verify_time, x, win_list, last_winner, last_cex, t_init, j_last, sweep_time
    global cex_list, last_cx
    sweep_time = 2
    if NBF == -1:
        F = 2000
    else:
        F = 2*NBF
    print '\nIterating abstraction refinement'
    J = slps+intrps+pdrs+bmcs+sims
    print sublist(methods,J)
    last_verify_time = t = x_factor*max(50,max(1,2.5*G_T))
    initial_verify_time = last_verify_time = t
    reg_verify = True
    print 'Verify time set to %d'%last_verify_time
    while True: #cex based refinement
        generate_abs(1) #generate new gabs file from refined greg file
        set_globals()
        latches_after = n_latches()
        if rel_cost_t([pis_before_abs,latches_before_abs, ands_before_abs])> -.1:
            break
        if latches_after >= .90*latches_before:
            break
        t = last_verify_time
        yy = time.time()
        abc('w %s_beforerpm.aig'%f_name)
        rep_change = reparam() #new - must do reconcile after to make cex compatible
        abc('w %s_afterrpm.aig'%f_name)
        if reg_verify:
            status = verify(J,t)
        else:
            status = pord_1_2(t)
###############
        if status == Sat_true:
            print 'Found true cex'
            reconcile(rep_change)
            return Sat_true
        if status == Unsat:
            return status
        if status == Sat:
            reconcile(rep_change) # makes the cex compatible with original before reparam and puts original in work space
            abc('write_status %s_before.status'%f_name)
            refine_with_cex()
            if is_sat(): # if cex can't refine, status is set to Sat_true
                print 'Found true cex in output %d'%cex_po()
                return Sat_true
            else:
                continue
        else:
            break
    print '**** Latches reduced from %d to %d'%(latches_before, n_latches())
    return Undecided_reduction

def abstract():
    """ abstracts using N Een's method 3 - cex/proof based abstraction. The result is further refined using
    simulation, BMC or BDD reachability"""
    global G_C, G_T, latches_before_abs, x_factor, last_verify_time, x, win_list, j_last, sims
    global latches_before_abs, ands_before_abs, pis_before_abs
    j_last = 0
    set_globals()
    #win_list = []
    latches_before_abs = n_latches()
    ands_before_abs = n_ands()
    pis_before_abs = n_real_inputs()
    abc('w %s_before_abs.aig'%f_name)
    print 'Start: ',
    ps()
    funcs = [eval('(pyabc_split.defer(initial_abstract)())')]
    # fork off BMC3 and PDRm along with initial abstraction
    t = 10000 #want to run as long as initial abstract takes.
##    J = sims+pdrs+bmcs+intrps
    J = pdrs+bmcs+bestintrps
    if n_latches() < 80:
        J = J + [4]
    funcs = create_funcs(J,t) + funcs
    mtds = sublist(methods,J) + ['initial_abstract'] #important that initial_abstract goes last
    m,NBF = fork_last(funcs,mtds)
    if is_sat():
        print 'Found true counterexample in frame %d'%cex_frame()
        return Sat_true
    if is_unsat():
        return Unsat
    set_max_bmc(NBF)
    NBF = bmc_depth()
    print 'Abstraction good to %d frames'%max_bmc
    #note when things are done in parallel, the &aig is not restored!!!
    abc('&r %s_greg.aig; &w initial_greg.aig; &abs_derive; &put; w initial_gabs.aig; w %s_gabs.aig'%(f_name,f_name))
    set_max_bmc(NBF)
    print 'Initial abstraction: ',
    ps()
    abc('w %s_init_abs.aig'%f_name)
    latches_after = n_latches()
##    if latches_after >= .90*latches_before_abs:
    if ((rel_cost_t([pis_before_abs, latches_before_abs, ands_before_abs])> -.1) or (latches_after >= .90*latches_before_abs)):
        abc('r %s_before_abs.aig'%f_name)
        print "Little reduction!"
        return Undecided_no_reduction
    sims_old = sims
    sims=sims[:1] #make it so that rarity sim is not used since it can't find a cex
    result = abstraction_refinement(latches_before_abs, NBF)
    sims = sims_old
    if result <= Unsat:
        return result
##    if n_latches() >= .90*latches_before_abs:
    if ((rel_cost_t([pis_before_abs, latches_before_abs, ands_before_abs])> -.1) or (latches_after >= .90*latches_before_abs)):
##    if rel_cost_t([pis_before_abs,latches_before_abs, ands_before_abs])> -.1:
        abc('r %s_before_abs.aig'%f_name) #restore original file before abstract.
        print "Little reduction!"
        result = Undecided_no_reduction    
    return result

def initial_abstract_old():
    global G_C, G_T, latches_before_abs, x_factor, last_verify_time, x, win_list
    set_globals()
    time = max(1,.1*G_T)
    abc('&get;,bmc -vt=%f'%time)
    set_max_bmc(bmc_depth())
    c = 2*G_C
    f = max(2*max_bmc,20)
    b = min(max(10,max_bmc),200)
    t = x_factor*max(1,2*G_T)
    s = min(max(3,c/30000),10) # stability between 3 and 10 
    cmd = '&get;,abs -bob=%d -stable=%d -timeout=%d -vt=%d -depth=%d'%(b,s,t,t,f)
##    print cmd
    print 'Running initial_abstract with bob=%d,stable=%d,time=%d,depth=%d'%(b,s,t,f)
    abc(cmd)
    abc('&w %s_greg.aig'%f_name)
##    ps()

def initial_abstract():
    global G_C, G_T, latches_before_abs, x_factor, last_verify_time, x, win_list, max_bmc
    set_globals()
    time = max(1,.1*G_T)
    abc('&get;,bmc -vt=%f'%time)
    set_max_bmc(bmc_depth())
    c = 2*G_C
    f = max(2*max_bmc,20)
    b = min(max(10,max_bmc),200)
    t = x_factor*max(1,2*G_T)
    s = min(max(3,c/30000),10) # stability between 3 and 10 
    cmd = '&get;,abs -bob=%d -stable=%d -timeout=%d -vt=%d -depth=%d'%(b,s,t,t,f)
##    print cmd
    print 'Running initial_abstract with bob=%d,stable=%d,time=%d,depth=%d'%(b,s,t,f)
    abc(cmd)
    bmc_depth()
##    pba_loop(max_bmc+1)
    abc('&w %s_greg.aig'%f_name)
    return max_bmc

def abs_m():
    set_globals()
    y = time.time()
    nl = n_abs_latches() #initial set of latches
    c = 2*G_C
    t = x_factor*max(1,2*G_T) #total time
    bmd = bmc_depth()
    if bmd < 0:
        abc('bmc3 -T 2') #get initial depth estimate
        bmd = bmc_depth()
    f = bmd
    abc('&get')
    y = time.time()
    cmd = '&abs_cba -v -C %d -T %0.2f -F %d'%(c,.8*t,bmd) #initial absraction
##    print '\n%s'%cmd
    abc(cmd)
    b_old = b = n_bmc_frames()
    f = min(2*bmd,max(bmd,1.6*b))
    print 'cba: latches = %d, depth = %d'%(n_abs_latches(),b)
##    print n_bmc_frames()
    while True:
        if (time.time() - y) > .9*t:
            break
        nal = n_abs_latches()
        cmd = '&abs_cba -v -C %d -T %0.2f -F %d'%(c,.8*t,f) #f is 2*bmd and is the maximum number of frames allowed
##        print '\n%s'%cmd
        abc(cmd)
##        print n_bmc_frames()
        b_old = b
        b = n_bmc_frames() 
        nal_old = nal 
        nal = n_abs_latches() #nal - nal_old is the number of latches added by cba
        #b - b_old is the additional time frames added by cba
        f = min(2*bmd,max(bmd,1.6*b))   #may be this should just be bmd
        f = max(f,1.5*bmd)
        print 'cba: latches = %d, depth = %d'%(nal,b)
        if ((nal == nal_old) and (b >= 1.5*b_old) and b >= 1.5*bmd):
            """
            Went at least bmd depth and saw too many frames without a cex
            (ideally should know how many frames without a cex)
            """
            print 'Too many frames without cex'
            break
        if b > b_old: #if increased depth
            continue
        if nal > .9*nl: # try to minimize latches
##            cmd = '&abs_pba -v -S %d -F %d -T %0.2f'%(b,b+2,.2*t)
            cmd = '&abs_pba -v -F %d -T %0.2f'%(b+2,.2*t)
##            print '\n%s'%cmd
            abc(cmd)
            b = n_bmc_frames()
            nal_old = nal
            nal = n_abs_latches()
            print 'pba: latches = %d, depth = %d'%(nal,b)
##            print n_bmc_frames()
            if nal_old < nal: #if latches increased there was a cex
                continue
            if nal > .9*nl: # if still too big 
                return
        continue 
##    b = n_bmc_frames()
    cmd = '&abs_pba -v -F %d -T %0.2f'%(b+2,.2*t)
##    print '\n%s'%cmd
    abc(cmd)
    b = n_bmc_frames()
    print 'pba: latches = %d, depth = %d'%(n_abs_latches(),b)
##    print n_bmc_frames()
    print 'Total time = %0.2f'%(time.time()-y)

def n_abs_latches():
    abc('&w pba_temp.aig') #save the &space
    abc('&abs_derive;&put')
    abc('&r pba_temp.aig')
    return n_latches()
        
def pba_loop(F):
    n = n_abs_latches()
    while True:
        run_command('&abs_pba -v -C 100000 -F %d'%F)
        abc('&w pba_temp.aig')
        abc('&abs_derive;&put')
        abc('&r pba_temp.aig')
        N = n_latches()
##        if n == N or n == N+1:
##            break
##        elif N > n:
        if N > n:
            print 'cex found'
        break
##        else:
##            break
    
##def sec_m(options):
##    """
##    This assumes that a miter has been loaded into the workspace. The miter has been
##    constructed using &miter. Then we demiter it using command 'demiter'
##    This produces parts 0 and 1, renamed  A_name, and B_name.
##    We then do speculate immediately. Options are passed to &srm2 using the
##    options given by sec_options
##    """
##    global f_name,sec_sw, A_name, B_name, sec_options
##    A_name = f_name+'_part0'
##    B_name = f_name+'_part1'
##    run_command('demiter')
##    #simplify parts A and B here?
##    abc('r %s_part1.aig;scl;dc2;&get;&lcorr;&scorr;&put;dc2;dc2;w %s_part1.aig'%(f_name,f_name))
##    ps()
##    abc('r %s_part0.aig;scl;dc2;&get;&lcorr;&scorr;&put;dc2;dc2;w %s_part0.aig'%(f_name,f_name))
##    ps()
##    #simplify done
##    f_name = A_name
##    return sec(B_name,options)

def ss(options):
    """Alias for super_sec"""
    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time, sec_options
    sec_options = options
    print 'Executing speculate'
    result = speculate()
    return result


def quick_sec(t):
##    fb_name = f_name[:-3]+'New'
##    abc('&get;&miter -s %s.aig;&put'%fb_name)
##    abc('w %s.%s_miter.aig'%(f_name,fb_name))
    quick_simp()
    verify(slps+ pdrs+bmcs+intrps,t)
    if is_unsat():
        return 'UNSAT'
    if is_sat():
        return 'SAT'
    else:
        return'UNDECIDED'

def pp_sec():
    print 'First file: ',
    read_file_quiet()
    ps()
    abc('&w original_secOld.aig')
    print 'Second file: ',
    read_file_quiet()
    ps()
    abc('&w original_secNew.aig')


def sup_sec():
    global TERM
    """
    form miter of original_sec(Old,New), and then run in parallel quick_sec(28), speculate(29), and
    run_parallel(21) with JP set to 
    """
    global f_name,sec_sw, A_name, B_name, sec_options
    #preprocess files to get rid of dangling FF
    abc('&r original_secOld.aig;&scl -ce;&w Old.aig')
    abc('&r original_secNew.aig;&scl -ce;&w New.aig')
    #done preprocessing
    read_file_quiet('Old')
    abc('&get;&miter -s New.aig;&put')
    set_globals()
    yy = time.time()
    A_name = f_name # Just makes it so that we can refer to A_name later in &srm2
    B_name = 'New'
    f_name = 'miter'
    abc('w %s.aig'%f_name)
    sec_options = 'l'
    sec_sw = True
    JP = [18,27] # sleep and simplify. JP  sets the things run in parallel in method 21.
                    #TERM sets the stopping condition
    TERM = 'USL' #Sat, Unsat or Last
    print sublist(methods,[27,21,28,29]+JV)
    t = 100 #this is the amount of time to run
            #18 is controlled by t, 28(speculate) is not, 29(quick_sec) does quick_simp and then controlled by t
    run_parallel([21,28,29],t,'US') #21 is run_parallel with JP and TERM.
                                    #run simplify for t sec, speculate,
                                    #and quick_sec (quick_simp and then verify(JV) for t)
    if is_unsat():
        return 'UNSAT'
    if is_sat():
        return 'SAT'
    else:
        return 'UNDECIDED' # should do sp or something
        

def sec(B_part,options):
    """
    This assumes that the original aig (renamed A_name below) is already read into the working space.
    Then we form a miter using &miter between two circuits, A_name, and B_name.
    We then do speculate immediately. Optionally we could simplify A and B
    and then form the miter and start from there. The only difference in speculate
    is that &srm2 is used, which only looks at equivalences where one comes from A and
    one from B. Options are -a and -b which says use only flops in A or in B or both. The
    switch sec_sw controls what speculate does when it generates the SRM.
    """
    global f_name,sec_sw, A_name, B_name, sec_options
    yy = time.time()
    A_name = f_name # Just makes it so that we can refer to A_name later in &srm2
    B_name = B_part
    run_command('&get; &miter -s %s.aig; &put'%B_name)
##    abc('orpos')
    f_name = A_name+'.'+B_name+'_miter' # reflect that we are working on a miter.
    abc('w %s.aig'%f_name)
    print 'Miter = ',
    ps()
##    result = pre_simp()
##    write_file('smp')
##    if result <= Unsat:
##        return RESULT[result]
    sec_options = options
    if sec_options == 'ab':
        sec_options = 'l' #it will be changed to 'ab' after &equiv
    sec_sw = True 
    result = speculate() #should do super_sec here.
    sec_options = ''
    sec_sw = False
    if result <= Unsat:
        result = RESULT[result]
    else:
        result = sp()
    print 'Total time = %d'%(time.time() - yy)
    return result

def filter(opts):
    global A_name,B_name
    """ This is for filter which effectively only recognizes options -f -g"""
    if (opts == '' or opts == 'l'): #if 'l' this is used only for initial &equiv2 to get initial equiv creation
        return
    if opts == 'ab':
        run_command('&filter -f %s.aig %s.aig'%(A_name,B_name))
        return
    if not opts == 'f':
        opts = 'g'
    run_command('&filter -%s'%opts)

def check_if_spec_first():
    global sec_sw, A_name, B_name, sec_options, po_map
    set_globals()
    t = max(1,.5*G_T)
    r = max(1,int(t))
    abc('w check_save.aig')
    abc('&w check_and.aig')
    abc("&get; &equiv3 -v -F 20 -T %f -R %d"%(t,5*r))
    filter('g')
    abc("&srm; r gsrm.aig")
    print 'Estimated # POs = %d for initial speculation'%n_pos()
    result = n_pos() > max(50,.25*n_latches())
    abc('r check_save.aig')
    abc('&r check_and.aig')
    return result

def initial_speculate():
    global sec_sw, A_name, B_name, sec_options, po_map
    set_globals()
    t = max(1,.5*G_T)
    r = max(1,int(t))
##    print 'Running &equiv3'
##    abc('&w before3.aig')
    if sec_options == 'l':
        cmd = "&get; &equiv3 -lv -F 20 -T %f -R %d"%(3*t,15*r)
    else:
        cmd = "&get; &equiv3 -v -F 20 -T %f -R %d"%(3*t,15*r)
##    print cmd
    abc(cmd)
##    print 'AND space after &equiv3: ',
##    run_command('&ps')
    if (sec_options == 'l'):
        if sec_sw:
            sec_options = 'ab'
        else:
            sec_options = 'f'
            print sec_options
    filter(sec_options)
    abc('&w initial_gore.aig')
##    print 'Running &srm'
    if sec_sw:
        cmd = "&srm2 -%s %s.aig %s.aig; r gsrm.aig; w %s_gsrm.aig; &w %s_gore.aig"%(sec_options,A_name,B_name,f_name,f_name)
        abc(cmd)
        po_map = range(n_pos())
        return
    else:
        cmd = "&srm; r gsrm.aig; w %s_gsrm.aig; &w %s_gore.aig"%(f_name,f_name)
        abc(cmd)
        if (n_pos() > 100):
            sec_options = 'g'
            print 'sec_option changed to "g"'
            filter(sec_options)
            abc(cmd)
        po_map = range(n_pos())

def test_against_original():
    '''tests whether we have a cex hitting an original PO'''
    abc('&w %s_save.aig'%f_name) #we oreserve whatever was in the & space
    abc('&r %s_gore.aig'%f_name)
    abc('testcex')
    PO = cex_po()
    abc('&r %s_save.aig'%f_name)
    if PO > -1:
##        print 'cex fails an original PO'
        return True
    else:
        return False

def set_cex_po(n=0):
    """
    if cex falsifies a non-real PO return that PO first,
    else see if cex_po is one of the original, then take it next
    else return -1 which means that the cex is not valid and hence an error.
    parameter n = 1 means test the &-space
    """
    global n_pos_before, n_pos_proved #these refer to real POs
    if n == 0:
        abc('testcex -a -O %d'%(n_pos_before-n_pos_proved))
    else:
        abc('testcex -O %d'%(n_pos_before-n_pos_proved))
    PO = cex_po()
    if PO >= (n_pos_before - n_pos_proved): #cex_po is not an original
##        print 'cex PO = %d'%PO
        return PO # after original so take it.
    if n == 0:
        abc('testcex -a')
    else:
        abc('testcex')
    PO = cex_po()
    cx = cex_get()
    if PO > -1:
        if test_against_original(): #this double checks that it is really an original PO
            cex_put(cx)
            return PO
        else:
            return -1 #error
##    if PO < 0 or PO >= (n_pos_before - n_pos_proved): # not a valid cex because already tested outside original.
##        PO = -1 #error
    return PO
##    print 'cex PO = %d'%PO

def speculate():
    """Main speculative reduction routine. Finds candidate sequential equivalences and refines them by simulation, BMC, or reachability
    using any cex found. """    
    global G_C,G_T,n_pos_before, x_factor, n_latches_before, last_verify_time, trim_allowed, n_pos_before
    global t_init, j_last, sec_sw, A_name, B_name, sec_options, po_map, sweep_time, sims, cex_list, n_pos_proved,ifpord1
    global last_cx
    last_cx = 0
    ifpord1 = 1
    if sec_sw:
        print 'A_name = %s, B_name = %s, f_name = %s, sec_options = %s'%(A_name, B_name, f_name, sec_options)
    elif n_ands()> 6000 and sec_options == '':
        sec_options = 'g'
        print 'sec_options set to "g"'
        
    def refine_with_cex():
        """Refines the gore file to reflect equivalences that go away because of cex"""
        global f_name
##        print 'Refining',
##        abc('&r %s_gore.aig;&w %s_gore_before.aig'%(f_name,f_name))
        abc('write_status %s_before.status'%f_name)
        abc('&r %s_gore.aig; &resim -m'%f_name)
        filter(sec_options)
        run_command('&w %s_gore.aig'%f_name)
        return
    
##    def refine_with_cexs():
##        """Refines the gore file to reflect equivalences that go away because of cexs in cex_list"""
##        global f_name, cex_list
##        print 'Multiple refining'
##        abc('&r %s_gore.aig'%f_name)
####        run_command('&ps')
##        for j in range(len(cex_list)):
##            cx = cex_list[j]
##            if cx == None:
##                continue
##            cex_put(cx)
##            run_command('&resim -m') #put the jth cex into the cex space and use it to refine the equivs
##        filter(sec_options)
##        abc('&w %s_gore.aig'%f_name)
####        run_command('&ps')
##        cex_list = [] #done with this list.
##        return

    def set_cex(lst):
        """ assumes only one in lst """
        for j in range(len(lst)):
            cx = lst[j]
            if cx == None:
                continue
            else:
                cex_put(cx)
                break

##    def test_all_cexs(lst):
##        """tests all cex"s to see if any violate original POs
##        if it does, return the original PO number
##        if not return -1
##        """
##        global n_pos_before, cex_list
##        run_command('&r %s_gore.aig'%f_name)
##        for j in range(len(cex_list)):
##            cx = lst[j]
##            if cx == None:
##                continue
##            cex_put(cx)
##            PO = set_cex_po()   #if cex falsifies non-real PO it will set this first
##            if PO == -1:        # there is a problem with cex since it does not falsify any PO
##                continue        #we continue because there may be another valid cex in list
##            return PO           #we will only process one cex for now.
##        return -1               #a real PO is not falsified by any of the cexs

    def generate_srm():
        """generates a speculated reduced model (srm) from the gore file"""
        global f_name, po_map, sec_sw, A_name, B_name, sec_options, n_pos_proved
##        print 'Generating'
        pos = n_pos()
        ab = n_ands()
        if sec_sw:
            run_command('&r %s_gore.aig; &srm2 -%s %s.aig %s.aig; r gsrm.aig; w %s_gsrm.aig'%(f_name,sec_options,A_name,B_name,f_name))
        else:
            abc('&r %s_gore.aig; &srm ; r gsrm.aig; w %s_gsrm.aig'%(f_name,f_name)) #do we still need to write the gsrm file
##        ps()
        po_map = range(n_pos())
##        cmd = '&get;&lcorr;&scorr;&trim -i;&put;w %s_gsrm.aig'%f_name
##        cmd = 'lcorr;&get;&trim -i;&put;w %s_gsrm.aig'%f_name
##        print 'Executing %s'%cmd
##        abc(cmd)
        ps()
        n_pos_proved = 0
        return 'OK'
    
    n_pos_before = n_pos()
    n_pos_proved = 0
    n_latches_before = n_latches()    
    set_globals()
    t = max(1,.5*G_T)#irrelevant
    r = max(1,int(t))
    j_last = 0
    J = sims+pdrs+bmcs+intrps
    funcs = [eval('(pyabc_split.defer(initial_speculate)())')]
    funcs = create_funcs(J,10000)+funcs #want other functins to run until initial speculate stops
    mtds = sublist(methods,J) + ['initial_speculate'] #important that initial_speculate goes last
    fork_last(funcs,mtds)
##    ps()
    if is_unsat():
        return Unsat
    if is_sat():
        return Sat_true
    if n_pos_before == n_pos():
        print 'No new outputs. Quitting speculate'
        return Undecided_no_reduction # return result is unknown
##    cmd = 'lcorr;&get;&trim -i;&put;w %s_gsrm.aig'%f_name
    #print 'Executing %s'%cmd
    abc('w initial_gsrm.aig')
##    ps()
##    abc(cmd)
    print 'Initial speculation: ',
    ps()
    if n_latches() == 0:
        return check_sat()
    if sec_options == 'l' and sec_sw:
        sec_options = 'ab' #finished with initial speculate with the 'l' option
        print "sec_options set to 'ab'"
    elif sec_options == 'l':
        sec_options = 'f'
        print "sec_options set to 'f'"
    po_map = range(n_pos()) #we need this because the initial_speculate is done in parallel and po_map is not passed back.
    npi = n_pis()
    set_globals()
    if is_sat():
        return Sat_true
    simp_sw = init = True
    print '\nIterating speculation refinement'
    sims_old = sims
    sims = sims[:1] #make it so rarity simulation is not used since it can't find a cex.
    J = slps+sims+pdrs+intrps+bmcs
    print sublist(methods,J)
    t = max(50,max(1,2*G_T))
    last_verify_time = t
    print 'Verify time set to %d'%last_verify_time
    reg_verify = True
    ref_time = time.time()
    sweep_time = 2
    ifpord1=1
    while True: # refinement loop
        set_globals()
        yy = time.time()
        if not init:
            abc('r %s_gsrm.aig'%f_name) #this is done only to set the size of the previous gsrm.
            abc('w %s_gsrm_before.aig'%f_name)
            set_size()
            result = generate_srm()
            yy = time.time()
            # if the size of the gsrm did not change after generating a new gsrm
            # and if the cex is valid for the gsrm, then the only way this can happen is if
            # the cex_po is an original one.
            if check_size(): #same size before and after
                if check_cex(): #valid cex failed to refine possibly
                    if 0 <= cex_po() and cex_po() < (n_pos_before - n_pos_proved): #original PO
                        print 'Found cex in original output = %d'%cex_po()
                        print 'Refinement time = %s'%convert(time.time() - ref_time)
                        return Sat_true
                    elif check_same_gsrm(f_name): #if two gsrms are same, then failed to refine
                        print 'CEX failed to refine'
                        return Error
                else:
                    print 'not a valid cex'
                    return Error
            if n_latches() == 0:
                print 'Refinement time = %s'%convert(time.time() - ref_time)
                return check_sat()
        init = False # make it so that next time it is not the first time through
        if not t == last_verify_time: # heuristic that if increased last verify time,
                                      # then try pord_all 
            t = last_verify_time
            if reg_verify:
                t_init = (time.time() - yy)/2 #start poor man's concurrency at last cex fime found
                t_init = min(10,t_init)
                reg_verify = False #will cause pord_all to be used next
                print 'pord_all turned on'
                t = last_verify_time
                print 'Verify time set to %d'%t
        abc('w %s_beforerpm.aig'%f_name)
        rep_change = reparam() #must be paired with reconcile below if cex
        abc('w %s_afterrpm.aig'%f_name)
        if reg_verify:
            result = verify(J,t)
        else:
            result = pord_1_2(t)
        if result == Unsat:
            print 'UNSAT'
            print 'Refinement time = %s'%convert(time.time() - ref_time)
            return Unsat
        if result < Unsat:
            if not reg_verify:
                set_cex(cex_list)
##        if reg_verify: 
            reconcile(rep_change) #end of pairing with reparam()
            assert (npi == n_cex_pis()),'ERROR: #pi = %d, #cex_pi = %d'%(npi,n_cex_pis())
            abc('&r %s_gore.aig;&w %s_gore_before.aig'%(f_name,f_name)) #we are making sure that none of the original POs fail
            PO = set_cex_po() #testing the &space
            if (-1 < PO and PO < (n_pos_before-n_pos_proved)):
                print 'Found cex in original output = %d'%cex_po()
                print 'Refinement time = %s'%convert(time.time() - ref_time)
                return Sat_true
            if PO == -1:
                return Error
            refine_with_cex()    #change the number of equivalences
            continue
##            else: # we used pord_all()
##                cex_list = reconcile_all(cex_list, rep_change)  #end of pairing with reparam()
##                PO = test_all_cexs(cex_list) #we have to make sure that none of the cex's fail the original POs.
##                if 0 <= PO and PO < (n_pos_before - n_pos_proved):
##                    print 'PO = %d, n_pos_before = %d, n_pos_proved = %d'%(PO,n_pos_before, n_pos_proved)
##                    print 'Found one of cexs in original output = %d'%cex_po()
##                    print 'Refinement time = %0.2f'%(time.time() - ref_time)
##                    return Sat_true
##                if PO == -1:
##                    return Error
##                refine_with_cexs()
##                continue
        elif (is_unsat() or n_pos() == 0):
            print 'UNSAT'
            print 'Refinement time = %s'%convert(time.time() - ref_time)
            return Unsat
        else: #if undecided, record last verification time
            print 'Refinement returned undecided in %d sec.'%t
            last_verify_time = t
            #########################added
            if reg_verify: #try one last time with parallel POs cex detection (find_cex_par) if not already tried
                abc('r %s_beforerpm.aig'%f_name) # to continue refinement, need to restore original
                t_init = min(last_verify_time,(time.time() - yy)/2) #start poor man's concurrency at last cex fime found
                t_init = min(10,t_init)
                reg_verify = False
                t = last_verify_time # = 2*last_verify_time
                abc('w %s_beforerpm.aig'%f_name)
                rep_change = reparam() #must be paired with reconcile()below
                abc('w %s_afterrpm.aig'%f_name)
                result = pord_1_2(t) #main call to verification
                if result == Unsat:
                    print 'UNSAT'
                    print 'Refinement time = %s'%convert(time.time() - ref_time)
                    return Unsat
                if is_sat():
                    assert result == get_status(),'result: %d, status: %d'%(result,get_status())
                    set_cex(cex_list)
                    reconcile(rep_change)
                    PO = set_cex_po() #testing the &space
                    if (-1 < PO and PO < (n_pos_before-n_pos_proved)):
                        print 'Found cex in original output = %d'%cex_po()
                        print 'Refinement time = %s'%convert(time.time() - ref_time)
                        return Sat_true
                    if PO == -1:
                        return Error
                    refine_with_cex()    #change the number of equivalences
                    continue
##                    cex_list = reconcile_all(cex_list, rep_change)  #end of pairing with reparam()
##                    PO = test_all_cexs(cex_list) #we have to make sure that none of the cex's fail the original POs.
##                    if 0 <= PO and PO < (n_pos_before - n_pos_proved):
##                        print 'found SAT in true output = %d'%cex_po()
##                        print 'Refinement time = %s'%convert(time.time() - ref_time)
##                        return Sat_true
##                    if PO == -1:
##                        return Error
##                    refine_with_cexs()#change the number of equivalences
##                    continue
                elif is_unsat():
                    print 'UNSAT'
                    print 'Refinement time = %s'%convert(time.time() - ref_time)
                    return Unsat
                else: #if undecided, record last verification time
                    last_verify_time = t
                    print 'UNDECIDED'
                    break
            ################### added
            else:
                break
    sims = sims_old
    print 'UNDECIDED'
    print 'Refinement time = %s'%convert(time.time() - ref_time)
    write_file('spec')
    if n_pos_before == n_pos():
        return Undecided_no_reduction 
    else:
        return Undecided_reduction

def simple_bip(t=1000):
    y = time.time()
    J = [0,1,2,30,5] #5 is pre_simp
    funcs = create_funcs(J,t)
    mtds =sublist(methods,J)
    fork_last(funcs,mtds)
    result = get_status()
    if result > Unsat:
        write_file('smp')
        result = verify(slps+[0,1,2,30],t)
    print 'Time for simple_bip = %0.2f'%(time.time()-y)
    return RESULT[result] 

def simple_prove(t=1000):
    y = time.time()
    J = [7,9,23,30,5]
    funcs = create_funcs(J,t)
    mtds =sublist(methods,J)
    fork_last(funcs,mtds)
    result = get_status()
    if result > Unsat:
        write_file('smp')
        result = verify(slps+[7,9,23,30],t)
    print 'Time for simple_prove = %0.2f'%(time.time()-y)
    return RESULT[result] 

def check_same_gsrm(f):
##    return False #disable the temporarily until can figure out why this is there
    """checks gsrm miters before and after refinement and if equal there is an error"""
    global f_name
    abc('r %s_gsrm.aig'%f)
##    ps()
    run_command('miter -c %s_gsrm_before.aig'%f)
##    ps()
    abc('&get; ,bmc -timeout=5')
    result = True #if the same
    if is_sat(): #if different
        result = False
    abc('r %s_gsrm.aig'%f)
##    ps()
    return result

def check_cex():
    """ check if the last cex still asserts one of the outputs.
    If it does then we have an error"""
    global f_name
    abc('read_status %s_before.status'%f_name)
    abc('&r %s_gsrm_before.aig'%f_name)
##    abc('&r %s_gsrm.aig'%f_name)
    run_command('testcex')
    print 'cex po = %d'%cex_po()
    return cex_po() >=0
##    if cex_po() == -1: # means gsrm changes after refinement - no output is asserted.
##        return False
##    else:
##        return True

def set_size():
    """Stores  the problem size of the current design.
    Size is defined as (PIs, POs, ANDS, FF)""" 
    global npi, npo, nands, nff, nmd
    npi = n_pis()
    npo = n_pos()
    nands = n_ands()
    nff = n_latches()
    nmd = max_bmc
    #print npi,npo,nands,nff

def check_size():
    """Assumes the problem size has been set by set_size before some operation.
    This checks if the size was changed
    Size is defined as (PIs, POs, ANDS, FF, max_bmc)
    Returns TRUE is size is the same""" 
    global npi, npo, nands, nff, nmd
    #print n_pis(),n_pos(),n_ands(),n_latches()
    result = ((npi == n_pis()) and (npo == n_pos()) and (nands == n_ands()) and (nff == n_latches()) )
    return result

def inferior_size():
    """Assumes the problem size has been set by set_size beore some operation.
    This checks if the new size is inferior (larger) to the old one 
    Size is defined as (PIs, POs, ANDS, FF)""" 
    global npi, npo, nands, nff
    result = ((npi < n_pis()) or (npo < n_pos()) or (nands < n_ands()) )
    return result

def quick_verify(n):
    """Low resource version of final_verify n = 1 means to do an initial
    simplification first. Also more time is allocated if n =1"""
    global last_verify_time
    trim()
    if n == 1:
        simplify()
        if n_latches == 0:
            return check_sat()
        trim()
        if is_sat():
            return Sat_true
    #print 'After trimming: ',
    #ps()
    set_globals()
    last_verify_time = t = max(1,.4*G_T)
    if n == 1:
        last_verify_time = t = max(1,2*G_T)
    print 'Verify time set to %d '%last_verify_time
    J = [18] + intrps+bmcs+pdrs+sims
    status = verify(J,t)
    return status

##def process_status():
##    if n_latches() == 0:
##        status = check_sat()
##    else:
##        status = get_status()
##    return status

def process_status(status):
    """ if there are no FF, the problem is combinational and we still have to check if UNSAT"""
    if n_latches() == 0:
        return check_sat()
    return status

    
def get_status():
    """this simply translates the problem status encoding done by ABC
    (-1,0,1)=(undecided,SAT,UNSAT) into the status code used by our
    python code. -1,0,1 => 3,0,2
    """
    if n_latches() == 0:
        return check_sat()
    status = prob_status() #interrogates ABC for the current status of the problem.
    # 0 = SAT i.e. Sat_reg = 0 so does not have to be changed.
    if status == 1:
        status = Unsat
    if status == -1: #undecided
        status = Undecided
    return status

def reparam():
    """eliminates PIs which if used in abstraction or speculation must be restored by
    reconcile and the cex made compatible with file beforerpm"""
##    return
    rep_change = False
    n = n_pis()
##    abc('w t1.aig')
    abc('&get;,reparam -aig=%s_rpm.aig; r %s_rpm.aig'%(f_name,f_name))
##    abc('w t2.aig')
##    abc('testcex')
    if n_pis() == 0:
        print 'Number of PIs reduced to 0. Added a dummy PI'
        abc('addpi')
    nn = n_pis()
    if nn < n:
        print 'Reparam: PIs %d => %d'%(n,nn)
        rep_change = True
    return rep_change

def reconcile(rep_change):
    """used to make current cex compatible with file before reparam() was done.
    However, the cex may have come
    from extracting a single output and verifying this.
    Then the cex_po is 0 but the PO it fails could be anything.
    So testcex rectifies this."""
    global n_pos_before, n_pos_proved
##    print 'rep_change = %s'%rep_change
    if rep_change == False:
        return
    abc('&r %s_beforerpm.aig; &w tt_before.aig'%f_name)
    abc('write_status %s_after.status;write_status tt_after.status'%f_name)
    abc('&r %s_afterrpm.aig;&w tt_after.aig'%f_name)
    POa = set_cex_po(1)   #this should set cex_po() to correct PO. A 1 here means it uses &space to check
    abc('reconcile %s_beforerpm.aig %s_afterrpm.aig'%(f_name,f_name))
    # reconcile modifies cex and restores work AIG to beforerpm
    abc('write_status %s_before.status;write_status tt_before.status'%f_name)
    POb = set_cex_po()
##    assert POa == POb, 'cex PO afterrpm = %d, cex PO beforerpm = %d'%(POa,POb)
    if POa != POb:
        abc('&r %s_beforerpm.aig; &w tt_before.aig'%f_name)
        abc('&r %s_afterrpm.aig; &w tt_after.aig'%f_name)
        print 'cex PO afterrpm = %d, cex PO beforerpm = %d'%(POa,POb)
##        assert POa == POb, 'cex PO afterrpm = %d, cex PO beforerpm = %d'%(POa,POb)

def reconcile_all(lst, rep_change):
    """reconciles the list of cex's"""
    global f_name, n_pos_before, n_pos_proved
    if rep_change == False:
        return lst
    list = []
    for j in range(len(lst)):
        cx = lst[j]
        if cx == None:
            continue
        cex_put(cx)
        reconcile(rep_change)
        list = list + [cex_get()]
    return list
    

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
            trim()
            print 'WARNING: rpm reduced PIs to %d. May make SAT.'%n_pis()
            result = 1
    else:
        abc('r %s_savetemp.aig'%f_name)
    return result
            
def verify(J,t):
    """This method is used for finding a cex during refinement, but can also
    be used for proving the property. t is the maximum time to be used by
    each engine J is the list of methods to run in parallel. See FUNCS for list"""
    global x_factor, final_verify_time, last_verify_time, methods
    set_globals()
    t = int(max(1,t))
    N = bmc_depth()
    L = n_latches()
    I = n_real_inputs()
##    mtds = sublist(methods,J)
    #heuristic that if bmc went deep, then reachability might also
    if ( ((I+L<350)&(N>100))  or  (I+L<260) or (L<80) ):
        J = J+reachs
        J = remove_intrps(J)
        if L < 80:
            J=J+[4]
    mtds = sublist(methods,J)
    print mtds
    #print J,t
    F = create_funcs(J,t)
    (m,result) = fork(F,mtds) #FORK here
    assert result == get_status(),'result: %d, status: %d'%(result,get_status())
    return result

    
def check_sat():
    """This is called if all the FF have disappeared, but there is still some logic left. In this case,
    the remaining logic may be UNSAT, which is usually the case, but this has to be proved. The ABC command 'dsat' is used fro combinational problems"""
    if not n_latches() == 0:
        print 'circuit is not combinational'
        return Undecided
##    print 'Circuit is combinational - checking with dsat'
    abc('&get') #save the current circuit
    abc('orpos;dsat -C %d'%G_C)
    if is_sat():
        return Sat_true
    elif is_unsat():
        return Unsat
    else:
        abc('&put') #restore
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
    global last_verify_time
    #print 'Proving final_verify_recur(%d)'%K
    last_verify_time = 2*last_verify_time
    print 'Verify time increased to %d'%last_verify_time
    for j in range(K):
        i = K-(j+1)
        abc('r %s_backup_%d.aig'%(initial_f_name,i))
        if ((i == 0) or (i ==2)): #don't try final verify on original last one
            status = prob_status()
            break
        print '\nVerifying backup number %d:'%i,
        #abc('r %s_backup_%d.aig'%(initial_f_name,i))
        ps()
        #J = [18,0,1,2,3,7,14]
        J = slps+sims+intrps+bmcs+pdrs
        t = last_verify_time
        status = verify(J,t)
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
##            pre_simp()
            status = speculate()
            if ((status <= Unsat) or (status == Error)):
                return status
        #J = [18,0,1,2,3,7,14]
        J = slps+sims+intrps+bmcs+pdrs
        t = 2*last_verify_time
        print 'Verify time increased to %d'%last_verify_time
        status = verify(J,t)
    if status == Unsat:
        return status
    else:
        return Undecided_reduction
        
def smp():
    abc('smp')
    write_file('smp')

def dprove():
    abc('dprove -cbjupr')

def trim():
    global trim_allowed
    if not trim_allowed:
        return
##    abc('trm;addpi')
    reparam()
##    print 'exiting trim'

def prs():
    y = time.clock()
    pre_simp()
    print 'Time = %s'%convert(time.clock() - y)
    write_file('smp')

def pre_simp():
    """This uses a set of simplification algorithms which preprocesses a design.
    Includes forward retiming, quick simp, signal correspondence with constraints, trimming away
    PIs, and strong simplify"""
    global trim_allowed
    set_globals()
    abc('&get; &scl; &put')
    if (n_ands() > 200000 or n_latches() > 50000 or n_pis() > 40000):
        print 'Problem too large, simplification skipped'
        return 'Undecided'
    if ((n_ands() > 0) or (n_latches()>0)):
        trim()
##        ps()
    if n_latches() == 0:
        return check_sat()
    best_fwrd_min([10,11])
    ps()
    status = try_scorr_constr()
    if ((n_ands() > 0) or (n_latches()>0)):
        trim()
    if n_latches() == 0:
        return check_sat()
    status = process_status(status)
    if status <= Unsat:
        return status
    simplify()
    print 'Simplify: ',
    ps()
    if n_latches() == 0:
        return check_sat()
    if trim_allowed:
        t = min(15,.3*G_T)
##        try_tempor(t)
        try_temps(15)
        if n_latches() == 0:
            return check_sat()
        try_phase()
        if n_latches() == 0:
            return check_sat()
        if ((n_ands() > 0) or (n_latches()>0)):
            trim()
    status = process_status(status)
    if status <= Unsat:
        return status
    return process_status(status)

def try_scorr_constr():
    set_size()
    abc('w %s_savetemp.aig'%f_name)
    status = scorr_constr()
    if inferior_size():
        abc('r %s_savetemp.aig'%f_name)
    return status


def factors(n):
    l = [1,]
    nn = n
    while n > 1:
        for i in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53):
            if not i <nn:
                break
            if n%i == 0:
                l = l + [i,]
                n = n/i
        if not n == 1:
            l = l + [n,]
        break
    return sorted(l)

def select(x,y):
    z = []
    for i in range(len(x)):
        if x[i]:
            z = z + [y[i],]
    return z
    
def ok_phases(n):
    """ only try those where the resulting n_ands does not exceed 60000"""
    f = factors(n)
    sp = subproducts(f)
    s = map(lambda m:m*n_ands()< 90000,sp)
    z = select(s,sp)
    return z

def subproducts(ll):
    ss = (product(ll),)
    #print ll
    n = len(ll)
    if n == 1:
        return ss
    for i in range(n):
        kk = drop(i,ll)
        #print kk
        ss = ss+(product(kk),)
        #print ss
        ss = ss+subproducts(kk)
        #print ss
    result =tuple(set(ss))
    #result.sort()
    return tuple(sorted(result))

def product(ll):
    n = len(ll)
    p = 1
    if n == 1:
        return ll[0]
    for i in range(n):
        p = p*ll[i]
    return p

def drop(i,ll):
    return ll[:i]+ll[i+1:]

def try_phase():
    """Tries phase abstraction. ABC returns the maximum clock phase it found using n_phases.
    Then unnrolling is tried up to that phase and the unrolled model is quickly
    simplified (with retiming to see if there is a significant reduction.
    If not, then revert back to original"""
    global init_simp
    trim()
    n = n_phases()
##    if ((n == 1) or (n_ands() > 45000) or init_simp == 0):
    if ((n == 1) or (n_ands() > 45000)):
        return
##    init_simp = 0
    print 'Trying phase abstraction - Max phase = %d'%n,
    #ps()
##    trim()
    #ps()
    abc('w %s_phase_temp.aig'%f_name)
    na = n_ands()
    nl = n_latches()
    ni = n_pis()
    no = n_pos()
    z = ok_phases(n)
    print z,
    if len(z) == 1:
        return
    #p = choose_phase()
    p = z[1]
    abc('phase -F %d'%p)
##    ps()
    #print z
    if no == n_pos(): #nothing happened because p is not mod period
        print 'Phase %d is incompatible'%p
        abc('r %s_phase_temp.aig'%f_name)
        if len(z)< 3:
            return
        else:
            p = z[2]
            #print 'Trying phase = %d:  '%p,
            abc('phase -F %d'%p)
            if no == n_pos(): #nothing happened because p is not mod period
                print 'Phase %d is incompatible'%p
                abc('r %s_phase_temp.aig'%f_name)
                return
    #print 'Trying phase = %d:  '%p,
    print 'Simplifying with %d phases: => '%p,
    simplify()
    trim()
    ps()
    cost = rel_cost([ni,nl,na])
    print 'New relative cost = %f'%(cost)
    if cost <  -.01:
        abc('w %s_phase_temp.aig'%f_name)
        if ((n_latches() == 0) or (n_ands() == 0)):
            return
        if n_phases() == 1: #this bombs out if no latches
            return
        else:
            try_phase()
            return
    elif len(z)>2: #Try the next eligible phase.
        abc('r %s_phase_temp.aig'%f_name)
        if p == z[2]: #already tried this
            return
        p = z[2]
        print 'Trying phase = %d: => '%p,
        abc('phase -F %d'%p)
        if no == n_pos(): #nothing happened because p is not mod period
            print 'Phase = %d is not compatible'%p
            return
        ps()
        print 'Simplify with %d phases: '%p,
        simplify()
        trim()
        ps()
        cost = rel_cost([ni,nl,na])
        print 'New relative cost = %f'%(cost)
        if cost < -.01:
            print 'Phase abstraction with %d phases obtained:'%p,
            print_circuit_stats()
            abc('w %s_phase_temp.aig'%f_name)
            if ((n_latches() == 0) or (n_ands() == 0)):
                return
            if n_phases() == 1: # this bombs out if no latches
                return
            else:
                try_phase()
                return
    abc('r %s_phase_temp.aig'%f_name)
    #ps()
    return

def try_temp(t=15):
    btime = time.clock()
    trim()
    print'Trying temporal decomposition - for max %s sec. '%convert(t),
    abc('w %s_best.aig'%f_name)
    ni = n_pis()
    nl = n_latches()
    na = n_ands()
    best = [ni,nl,na]
    F = create_funcs([18],t) #create a timer function
    F = F + [eval('(pyabc_split.defer(abc)("tempor -s; trm; scr; trm; tempor; trm; scr; trm"))')]
    for i,res in pyabc_split.abc_split_all(F):
        break
    cost = rel_cost(best)
    print 'Cost = %0.2f'%cost
    if cost < .01:
        ps()
        return
    else:
        abc('r %s_best.aig'%f_name)

def try_temps(t=15):
    best = (n_pis(),n_latches(),n_ands())
    while True:
        try_temp(t)
        if ((best == (n_pis(),n_latches(),n_ands())) or n_ands() > .9 * best[2] ):
            break
        elif n_latches() == 0:
            break
        else:
            best = (n_pis(),n_latches(),n_ands())
        
def try_tempor(t):
    btime = time.clock()
    trim()
    print'Trying temporal decomposition - for max %s sec. '%convert(t),
    abc('w %s_best.aig'%f_name)
    ni = n_pis()
    nl = n_latches()
    na = n_ands()
    best = [ni,nl,na]
    F = create_funcs([18],t) #create a timer function
    #Caution: trm done in the following removes POs and PIs
##    F = F + [eval('(pyabc_split.defer(abc)("tempor -s -C %d; trm; lcr; scr; trm"))'%(2*na))]
##    F = F + [eval('(pyabc_split.defer(abc)("tempor -C %d; trm; lcr; scr; trm"))'%(2*na))]
    F = F + [eval('(pyabc_split.defer(abc)("tempor -s; trm; lcr; scr; trm"))')]
    F = F + [eval('(pyabc_split.defer(abc)("tempor -C; trm; lcr; scr; trm"))')]
    n_done = 0
    new_best = 0
##    debug_here()
    for i,res in pyabc_split.abc_split_all(F):
        if i == 0:
            break
        else:
            cost = rel_cost(best)
            print 'Cost = %0.2f'%cost
            if cost < .01:
                abc('w %s_best.aig'%f_name)
                best = [n_pis(),n_latches(),n_ands()]
                new_best = 1
            n_done = n_done+1
            if n_done == 2:
                break
            else:
                continue
    abc('r %s_best.aig'%f_name)
    ps()
    if new_best == 0: #nothing new
        print 'No reduction or timeout occurred'
        return
    if n_latches() == 0:
        return
    abc('scr;smp')
    trim()
    cost = rel_cost_t([ni,nl,na]) #see how much it improved
##    print 'rel_cost_t = %0.2f'%cost
    if (cost < -.01):
        print 'time = %f: '%(time.clock() - btime),
        if cost < -1:
            print 'Trying second tempor'
            try_tempor(t)
        print 'Reduction: time=%f'%(time.clock() - btime)
        return
    else:
        print 'No reduction'
        return    

def rel_cost_t(J):
    """ weighted relative costs versus previous stats."""
    if n_latches() == 0:
        return -10
    nli = J[0]+J[1]
    na = J[2]
    if ((nli == 0) or (na == 0)):
        return 100
    nri = n_real_inputs()
    #ri = (float(nri)-float(ni))/float(ni)
    rli = (float(n_latches()+nri)-float(nli))/float(nli)
    ra = (float(n_ands())-float(na))/float(na)
##    cost = 10*rli + .1*ra
    cost = 10*rli + .5*ra
##    print 'cost = %0.2f'%c
##    print 'cost = %0.2f'%cost
    return cost    

def rel_cost(J):
    """ weighted relative costs versus previous stats."""
    global f_name
    if n_latches() == 0:
        return -10
    nri = n_real_inputs()
    ni = J[0]
    nl = J[1]
    na = J[2]
    if (ni == 0 or na == 0 or nl == 0):
        return 100
    ri = (float(nri)-float(ni))/float(ni)
    rl = (float(n_latches())-float(nl))/float(nl)
    ra = (float(n_ands())-float(na))/float(na)
    cost = 1*ri + 10*rl + .1*ra
##    print 'Relative cost = %0.2f'%cost
    return cost

def best_fwrd_min(J):
    global f_name, methods
    mtds = sublist(methods,J)
    F = create_funcs(J,0)
    #print 'Trying forward retiming: running %s in parallel'%(mtds)
    (m,result) = fork_best(F,mtds) #FORK here
    print '%s: '%mtds[m],
    
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
        abc('scl -m;lcorr;drw')
    else:
        abc('&get;&scl;&lcorr;&put;drw')

def scorr_constr():
    """Extracts implicit constraints and uses them in signal correspondence
    Constraints that are found are folded back when done"""
##################### Temporary
#    return Undecided_no_reduction
#####################
    na = max(1,n_ands())
    n_pos_before = n_pos()
    if ((na > 40000) or n_pos()>1):
        return Undecided_no_reduction
    abc('w %s_savetemp.aig'%f_name)
    if n_ands() < 3000:
        cmd = 'unfold -a -F 2'
    else:
        cmd = 'unfold'
    abc(cmd)
    if n_pos() == n_pos_before:
        print 'No constraints found'
        return Undecided_no_reduction
    if (n_ands() > na): #no constraints found
        abc('r %s_savetemp.aig'%f_name)
        return Undecided_no_reduction
    #print_circuit_stats()
    na = max(1,n_ands())
##    f = 1
    f = 18000/na
    f = min(f,4)
    f = max(1,f)
    print 'Number of constraints = %d, frames = %d'%((n_pos() - n_pos_before),f)
    abc('scorr -c -F %d'%f)
    abc('fold')
    trim()
    ps()
    return Undecided_no_reduction

def try_scorr_c(f):
    """ Trying multiple frames because current version has a bug."""
    set_globals()
    abc('unfold -F %d'%f)
    abc('scorr -c -F %d'%f)
    abc('fold')
    t = max(1,.1*G_T)
    abc('&get;,bmc3 -vt=%f'%t)
    if is_sat(): 
        return 0
    else:
        trim()
        return 1
    

def input_x_factor():
    """Sets the global x_factor according to user input"""
    global x_factor, xfi
    print 'Type in x_factor:',
    xfi = x_factor = input()
    print 'x_factor set to %f'%x_factor

##def prove_sec():
##    """
##    Like 'prove' proves all the outputs together. Speculation is done first
##    If undecided, the do super_prove.
##    """
##    global x_factor,xfi,f_name, last_verify_time,K_backup, sec_options
##    max_bmc = -1
##    K_backup = K = 0
##    result = prove_part_1(K) #initial simplification here
##    if n_latches() == 0:
##        return 1,result
##    K = K_backup
##    if ((result == 'SAT') or (result == 'UNSAT')):
##        return 1,result
##    assert K==1, 'K = %d'%K
##    result = prove_part_3(K) #speculation done here
##    if ((result == 'SAT') or (result == 'UNSAT')):
##        return 1,result
##    else:
##        return 1,super_prove(0)
##
##    #################### End of ss
##    K = K_backup
##    #print 'after speculate'
##    status = get_status()
##    assert 0<K and K<4, 'K = %d'%K
##    if K > 1: # for K = 1, we will leave final verification for later
##        print 'Entering final_verify_recur(%d) from prove()'%K
##        status = final_verify_recur(K) # will start verifying with final verify
##                    #starting at backup number K-1 (either K = 2 or 3 here
##                    #1 if spec found true sat on abs, 2 can happen if abstraction
##                    #did not work but speculation worked,
##                    #3 if still undecided after spec)
##    else: #K=1 means that abstraction did not work and was proved wrong by speculation
##        if a == 0:
##            result = prove_spec_first()
##            if ((result == 'SAT') or (result == 'UNSAT')):
##                return 1,result
##    write_file('final')
##    return (not K == 1),RESULT[status]

def prove(a):
    """Proves all the outputs together. If ever an abstraction
        was done then if SAT is returned,
        we make RESULT return "undecided".
        If a == 1 skip speculate. K is the number of the next backup
        if a == 2 skip initial simplify and speculate"""
    global x_factor,xfi,f_name, last_verify_time,K_backup, t_init, sec_options
    spec_first = False
    max_bmc = -1
    K_backup = K = 0
    if a == 2: #skip initial simplification
        print 'Using quick simplification',
        abc('lcorr;drw')
        status = process_status(get_status())
        if status <= Unsat:
            result = RESULT[status]
        else:
            ps()
            write_file('smp')
            abc('w %s_backup_%d.aig'%(initial_f_name,K)) #writing backup 0
            K_backup = K = K+1
            result = 'UNDECIDED'
    else:
        result = prove_part_1(K) #initial simplification here
        if ((result == 'SAT') or (result == 'UNSAT')):
            return 1,result
        if n_latches() == 0:
            return 1,result
        if a == 0:
            spec_first = False
##            spec_first = check_if_spec_first()
            if spec_first:
                sec_options = 'g'
                print 'sec_options set to "g"'
    if n_latches() == 0:
        return 1,result
    K = K_backup
    if ((result == 'SAT') or (result == 'UNSAT')):
        return 1,result
    assert K==1, 'K = %d'%K
    t_init = 2
    if spec_first and a == 0:
        result = prove_part_3(K)
    else:
        result = prove_part_2(K) #abstraction done here
    K = K_backup
    if ((result == 'SAT') or (result == 'UNSAT')):
        return 1,result
    assert 0<K and K<3, 'K = %d'%K 
    if a == 0:
        t_init = 2
        if spec_first:
            result = prove_part_2(K) #speculation 2one here
        else:
            result = prove_part_3(K)
        if ((result == 'SAT') or (result == 'UNSAT')):
            return 1,result
    K = K_backup
    #print 'after speculate'
    status = get_status()
    assert 0<K and K<4, 'K = %d'%K
    if (((K > 2) and (n_pos()>1)) or ((K == 2) and  spec_first)): # for K = 1, we will leave final verification for later
        print 'Entering final_verify_recur(%d) from prove()'%K
        status = final_verify_recur(K) # will start verifying with final verify
                    #starting at backup number K-1 (either K = 2 or 3 here
                    #1 if spec found true sat on abs, 2 can happen if abstraction
                    #did not work but speculation worked,
                    #3 if still undecided after spec)
    #K=1 or 2 and not spec_first means that abstraction did not work and was proved wrong by speculation
    elif ((a == 0) and K == 1):
            t_init = 2
            result = prove_spec_first()
            if ((result == 'SAT') or (result == 'UNSAT')):
                return 1,result
    write_file('final')
    return (not K == 1),RESULT[status]

def psf():
    x = time.time()
    result = prove_spec_first()
    print 'Total clock time for %s = %f sec.'%(init_initial_f_name,(time.time() - x))
    return result

def prove_spec_first():
    """Proves all the outputs together. If ever an abstraction
        was done then if SAT is returned,
        we make RESULT return "undecided".
        """
    global x_factor,xfi,f_name, last_verify_time,K_backup
    max_bmc = -1
    K_backup = K = 1
##    result = prove_part_1(K) #initial simplification here
##    if n_latches() == 0:
##        return result
##    K = K_backup
##    if ((result == 'SAT') or (result == 'UNSAT')):
##        return result
##    assumes that initial simplification has been done already.
    assert K==1, 'K = %d'%K
    result = prove_part_3(K) #speculation done here
    K = K_backup
    if ((result == 'SAT') or (result == 'UNSAT')):
        return result
    assert 0<K and K<3, 'K = %d'%K
    K = K_backup #K = 1 => speculation did not do anything
    if K == 1: # so don't try abstraction because it did not work the first time
        return 'UNDECIDED'
    result = prove_part_2(K) #abstraction done here
    if result == 'UNSAT':
        return result
    if result == 'SAT': # abstraction proved speculation wrong.
        K = 2
    assert 0<K and K<4, 'K = %d'%K
    if K > 1: # for K = 1, we will leave final verification for later
        print 'Entering final_verify_recur(%d) from prove()'%K
        status = final_verify_recur(K) # will start verifying with final verify
                    #starting at backup number K-1 (either K = 2 or 3 here
                    #1 if spec found true sat on abs, 2 can happen if
                    #speculation worked but abstraction proved it wrong,
                    #3 if still undecided after spec and abstraction)
    write_file('final')
    return RESULT[status]


def prove_part_1(K):
    global x_factor,xfi,f_name, last_verify_time,K_backup
    #K=0
    print 'Initial: ',
    print_circuit_stats()
    x_factor = xfi
    print 'x_factor = %f'%x_factor
    print '\n***Running pre_simp'
    set_globals()
    if n_latches() > 0:
##        status = pre_simp()
        set_globals()
        t = 1000
        funcs = [eval('(pyabc_split.defer(pre_simp)())')]
##        J = sims+pdrs+bmcs+intrps
        J = pdrs+bmcs+bestintrps
        funcs = create_funcs(J,t)+ funcs #important that pre_simp goes last
        mtds =sublist(methods,J) + ['pre_simplify']
        fork_last(funcs,mtds)
##        funcs = [eval(FUNCS[3])] + [eval(FUNCS[0])] + [eval(FUNCS[1])] + [eval(FUNCS[2])] + [eval(FUNCS[9])] + [eval(FUNCS[7])] + funcs
##        fork_last(funcs,['SIM', 'PDR','INTRP','BMC', 'BMC3', 'PDRm','pre_simp'])
        status = get_status()
    else:
        status = check_sat()
    if ((status <= Unsat) or (n_latches() == 0)):
        return RESULT[status]
    if n_ands() == 0:
        abc('&get;,bmc -vt=2')
        if is_sat():
            return 'SAT'
    trim()
    write_file('smp')
    abc('w %s_backup_%d.aig'%(initial_f_name,K)) #writing backup 0
    K_backup = K = K+1
    #K=1 
    set_globals()
    return 'UNDECIDED'

def prove_part_2(K):
    """does the abstraction part of prove"""
    global x_factor,xfi,f_name, last_verify_time,K_backup, trim_allowed
    print'\n***Running abstract'
    nl_b = n_latches()
    status = abstract() #ABSTRACTION done here
##    write_file('abs')
##    print 'Abstract finished'
    if status == Undecided_no_reduction:
        K_backup = K = K-1 #K = 0
    if status == Unsat:
        write_file('abs')
        return RESULT[status]
##    trim()
    #just added in
    if status < Unsat:
        write_file('abs')
        print 'CEX in frame %d'%cex_frame()
        return RESULT[status]
    if  K > 0:
        t_old = trim_allowed
        if pord_on:
            trim_allowed = False
        pre_simp()
        trime_allowed = t_old
    #end of added in
    write_file('abs')
    status = process_status(status)
    if ((status <= Unsat)  or  status == Error):
        if  status < Unsat:
            print 'CEX in frame %d'%cex_frame()
            return RESULT[status]
        return RESULT[status]
    abc('w %s_backup_%d.aig'%(initial_f_name,K)) # writing backup 1 (or 0) after abstraction
    K_backup = K = K+1
    #K = 1 or 2 here
    return 'UNDECIDED'
    
def prove_part_3(K):
    """does the speculation part of prove"""
    global x_factor,xfi,f_name, last_verify_time,K_backup, init_initial_f_name
    global max_bmc, sec_options
    #K_backup = K = K +1 #K = 1 or 2 K =1 means that abstraction did not reduce
    assert 0 < K and K < 3, 'K = %d'%K
    if ((n_ands() > 10000) and sec_options == ''):
        sec_options = 'g'
        print 'sec_options set to "g"'
    if n_ands() == 0:
        print 'Speculation skipped because no AND nodes'
    else:
        print '\n***Running speculate'
##        pre_simp()
        status = speculate() #SPECULATION done here
        if status == Unsat:
            return RESULT[status]
        old_f_name = f_name
##        if not status < Unsat:
##            pre_simp()
##        write_file('spec1')
##        #we do not do the continuation of speculation right now so the following is not needed.
##        #abc('&r %s_gore.aig;&w %s_gore.aig'%(old_f_name,f_name)) #very subtle -needed for continuing spec refinement
        status = process_status(status)
        if status == Unsat:
            return RESULT[status]
        elif ((status < Unsat) or (status == Error)):
            print 'CEX in frame %d'%cex_frame()
            if K == 1: #if K = 1 then abstraction was not done.
                print 'speculate found cex on original'
                return RESULT[status] # speculate found cex on original
            K_backup = K = K-1 #since spec found a true cex, then result of abstract was wrong
            print 'cex means that abstraction was invalid'
            print 'Initial simplified AIG restored => ',
            abc('r %s_smp.aig'%init_initial_f_name)
            max_bmc = -1
            ps()
            assert K == 1, 'K = %d'%K
        else: 
            trim()
            print 'Problem still undecided'
            abc('w %s_backup_%d.aig'%(initial_f_name,K)) # writing backup 2 or 1
                                                        # 2 after speculation and abstraction
                                                        # 1 if abstraction did not reduce
            K_backup = K = K+1
            assert 1<K and K<4, 'K = %d'%K
##            write_file('spec2')
    trim()
    return 'UNDECIDED'

def prove_all(dir,t):
    """Prove all aig files in this directory using super_prove and record the results in results.txt"""
##    t = 1000 #This is the timeoout value
    xtime = time.time()
##    dir = main.list_aig('')
    results = []
    f =open('results_%d.txt'%len(dir), 'w')
    for name in dir:
        read_file_quiet(name)
        print '\n         **** %s:'%name,
        ps()
        F = create_funcs([18,6],t) #create timer function as i = 0 Here is the timer
        for i,res in pyabc_split.abc_split_all(F):
            break
        tt = time.time()
        if i == 0:
            res = 'Timeout'
        str = '%s: %s, time = %s'%(name,res,convert(tt-xtime))
        if res == 'SAT':
            str = str + ', cex_frame = %d'%cex_frame()
        str = str +'\n'
        f.write(str)
        f.flush()
        results = results + ['%s: %s, time = %s'%(name,res,convert(tt-xtime))]
        xtime = tt
##    print results
    f.close()
    return results

    
def prove_g_pos(a):
    """Proves the outputs clustered by a parameter a. 
    a is the disallowed increase in latch support Clusters must be contiguous
    If a = 0 then outputs are proved individually. Clustering is done from last to first
    Output 0 is attempted to be proved inductively using other outputs as constraints.
    Proved outputs are removed if all the outputs have not been proved.
    If ever one of the proofs returns SAT, we stop and do not try any other outputs."""
    global f_name, max_bmc,x_factor,x
    x = time.time()
    #input_x_factor()
    init_f_name = f_name
    print 'Beginning prove_g_pos'
    prove_all_ind()
    print 'Number of outputs reduced to %d by fast induction with constraints'%n_pos()
    print '\n****Running second level prove****************\n'
    reparam()
##    try_rpm()
##    k,result = prove(1) # 1 here means do not try speculate.
##    if result == 'UNSAT':
##        print 'Second prove returned UNSAT'
##        return result
##    if result == 'SAT':
##        print 'CEX found'
##        return result
    print '\n********** Proving each output separately ************'
    #prove_all_ind()
    #print 'Number of outputs reduced to %d by fast induction with constraints'%n_pos()
    f_name = init_f_name
    abc('w %s_osavetemp.aig'%f_name)
    n = n_pos()
    print 'Number of outputs = %d'%n
    #count = 0
    #Now prove each remaining output separately.
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
        f_name = f_name + '_%d'%jnext_old
        result = prove_1()
        if result == 'UNSAT':
            if jnext_old > jnext+1:
                print '********  PROVED OUTPUTS [%d-%d]  ******** '%(jnext+1,jnext_old)
            else:
                print '********  PROVED OUTPUT %d  ******** '%(jnext_old)
            pos_proved = pos_proved + range(jnext +1,jnext_old+1)
            continue
        if result == 'SAT':
            print 'One of output in (%d to %d) is SAT'%(jnext + 1,jnext_old)
            return result
        else:
            print '********  UNDECIDED on OUTPUTS %d thru %d  ******** '%(jnext+1,jnext_old)
    f_name = init_f_name
    abc('r %s_osavetemp.aig'%f_name)
    if not len(pos_proved) == n:
        print 'Eliminating %d proved outputs'%(len(pos_proved))
        remove(pos_proved)
        trim()
        write_file('group')
        result = 'UNDECIDED'
    else:
        print 'Proved all outputs. The problem is proved UNSAT'
        result = 'UNSAT'
    print 'Total clock time for prove_g_pos = %f sec.'%(time.time() - x)
    return result

def prove_pos(i):
    """
    i=1 means to execute prove_all_ind first
    Proved outputs are removed if all the outputs have not been proved.
    If ever one of the proofs returns SAT, we continue and try to resolve other outputs."""
    global f_name, max_bmc,x_factor,x
    x = time.time()
    #input_x_factor()
    init_f_name = f_name
    print 'Beginning prove_pos'
    remove_0_pos()
    if i:
        prove_all_ind()
    print 'Number of outputs reduced to %d by quick induction with constraints'%n_pos()
    print '********** Proving each output separately ************'
    f_name = init_f_name
    abc('w %s_osavetemp.aig'%f_name)
    n = n_pos()
    print 'Number of outputs = %d'%n
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
##        result = prove_1()    
        result = super_prove(2) #do not do initial simplification
        if result == 'UNSAT':
            print '********  PROVED OUTPUT %d  ******** '%(jnext_old)
            pos_proved = pos_proved + range(jnext +1,jnext_old+1)
            continue
        if result == 'SAT':
            print '********  DISPROVED OUTPUT %d  ******** '%(jnext_old)
            pos_disproved = pos_disproved + range(jnext +1,jnext_old+1)
            continue
        else:
            print '********  UNDECIDED on OUTPUT %d  ******** '%(jnext_old)
    f_name = init_f_name
    abc('r %s_osavetemp.aig'%f_name)
    list = pos_proved + pos_disproved
    print 'Proved the following outputs: %s'%pos_proved
    print 'Disproved the following outputs: %s'%pos_disproved
    if not len(list) == n:
        print 'Eliminating %d resolved outputs'%(len(list))
        remove(list)
        trim()
        write_file('group')
        result = 'UNRESOLVED'
    else:
        print 'Proved or disproved all outputs. The problem is proved RESOLVED'
        result = 'RESOLVED'
    print 'Total clock time for prove_pos = %f sec.'%(time.time() - x)
    return result

def remove_pos(lst):
    """Takes a list of pairs where the first part of a pair is the PO number and
    the second is the result 1 = disproved, 2 = proved, 3 = unresolved. Then removes
    the proved and disproved outputs and returns the aig with the unresolved
    outputs"""
    proved = disproved = unresolved = []
    for j in range(len(lst)):
        jj = lst[j]
        if jj[1] == 2:
            proved = proved + [jj[0]]
        if (jj[1] == 1 or (jj[1] == 0)):
            disproved = disproved +[jj[0]]
        if jj[1] > 2:
            unresolved = unresolved +[jj[0]]
    print '%d outputs proved'%len(proved)
##    print disproved
##    abc('w xxx__yyy.aig')
    if not proved == []:
        if ((max(proved)>n_pos()-1) or min(proved)< 0):
            print proved
        remove(proved)
            

#functions for proving multiple outputs in parallel
#__________________________________________________

def prove_only(j):
    """ extract the jth output and try to prove it"""
    global max_bmc, init_initial_f_name, initial_f_name, f_name,x
    #abc('w %s__xsavetemp.aig'%f_name)
    extract(j,j)
    set_globals()
    ps()
    print '\nProving output %d'%(j)
    f_name = f_name + '_%d'%j
    result = prove_1()
    #abc('r %s__xsavetemp.aig'%f_name)
    if result == 'UNSAT':
        print '********  PROVED OUTPUT %d  ******** '%(j)
        return Unsat
    if result == 'SAT':
        print '********  DISPROVED OUTPUT %d  ******** '%(j)
        return Sat
    else:
        print '********  UNDECIDED on OUTPUT %d  ******** '%(j)
        return Undecided

def verify_only(j,t):
    """ extract the jth output and try to prove it"""
    global max_bmc, init_initial_f_name, initial_f_name, f_name,x, reachs, last_cex, last_winner, methods
##    ps()
##    print 'Output = %d'%j
    extract(j,j)
##    ps()
    set_globals()
    if n_latches() == 0:
        result = check_sat()
    else:
        f_name = f_name + '_%d'%j
        # make it so that jabc is not used here
        reachs_old = reachs
        reachs = reachs[1:] #just remove jabc from this.
        res = verify(slps+sims+pdrs+bmcs+intrps,t) #keep the number running at the same time as small as possible.
##        res = verify(sims+pdrs+bmcs+intrps,t) #keep the number running at the same time as small as possible.
        reachs = reachs_old
        result = get_status()
        assert res == result,'result: %d, status: %d'%(res,get_status())
    if result > Unsat:
##        print result
##        print '******* %d is undecided ***********'%j
        return result
    elif result == Unsat:
##        print '******** PROVED OUTPUT %d  ******** '%(j)
        return result
    elif ((result < Unsat) and (not result == None)):
        print '******** %s DISPROVED OUTPUT %d  ******** '%(last_cex,j)
##        print ('writing %d.status'%j), result, get_status()
        abc('write_status %d.status'%j)
        last_winner = last_cex
        return result
    else:
        print '****** %d result is %d'%(j,result) 
        return result

def verify_range(j,k,t):
    """ extract the jth thru kth output and try to prove their OR"""
    global max_bmc, init_initial_f_name, initial_f_name, f_name,x, reachs, last_cex, last_winner, methods
    extract(j,k)
    abc('orpos')
    set_globals()
    if n_latches() == 0:
        result = check_sat()
    else:
        f_name = f_name + '_%d'%j
        # make it so that jabc is not used here
        reachs_old = reachs
        reachs = reachs[1:] #just remove jabc from this.
        res = verify(sims+pdrs+bmcs+intrps,t) #keep the number running at the sme time as small as possible.
        reachs = reachs_old
        result = get_status()
        assert res == result,'result: %d, status: %d'%(res,get_status())
    if result > Unsat:
##        print result
##        print '******* %d is undecided ***********'%j
        return result
    elif result == Unsat:
##        print '******** PROVED OUTPUT %d  ******** '%(j)
        return result
    elif ((result < Unsat) and (not result == None)):
        print '******** %s DISPROVED OUTPUT %d  ******** '%(last_cex,j)
##        print ('writing %d.status'%j), result, get_status()
        abc('write_status %d.status'%j)
        last_winner = last_cex
        return result
    else:
        print '****** %d result is %d'%(j,result) 
        return result

def prove_n_par(n,j):
    """prove n outputs in parallel starting at j"""
    F = []
    for i in range(n):
        F = F + [eval('(pyabc_split.defer(prove_only)(%s))'%(j+i))]
    #print S
    #F = eval(S)
    result = []
    print 'Proving outputs %d thru %d in parallel'%(j,j+n-1)
    for i,res in pyabc_split.abc_split_all(F):
        result = result +[(j+i,res)]
    #print result
    return result

def prove_pos_par(t,BREAK):
    """Prove all outputs in parallel and break on BREAK"""
    return run_parallel([],t,BREAK)

def prove_pos_par0(n):
    """ Group n POs grouped and prove in parallel until all outputs have been proved"""
    f_name = initial_f_name
    abc('w %s__xsavetemp.aig'%f_name)
    result = []
    j = 0
    N = n_pos()
    while j < N-n:
        abc('r %s__xsavetemp.aig'%f_name)
        result = result + prove_n_par(n,j)
        j = j+n
    if N > j:
        result = result + prove_n_par(N-j,j)
    abc('r %s__xsavetemp.aig'%initial_f_name)
    ps()
    print result
    remove_pos(result)
    write_file('group')
    return

def prop_decomp():
    """decompose a single property into multiple ones (only for initial single output),
    by finding single and double literal primes of the outputs."""
    if n_pos()>1:
        return
    run_command('outdec -v -L 2')
    if n_pos()>1:
        ps()


def distribute(N,div):
    """
    we are going to verify outputs in groups
    """
    n = N/div
    rem = N - (div * (N/div))
    result = []
    for j in range(div):
        if rem >0:
            result = result +[n+1]
            rem = rem -1
        else:
            result = result + [n]
    return result    

def find_cex_par(tt):
    """prove n outputs at once and quit at first cex. Otherwise if no cex found return aig
    with the unproved outputs"""
    global trim_allowed,last_winner, last_cex, n_pos_before, t_init, j_last, sweep_time
    b_time = time.time() #Wall clock time
    n = n_pos()
    remove_0_pos()
    N = n_pos()
    full_time = all_proc = False
    print 'Number of POs: %d => %d'%(n,N)
    if N == 0:
        return Unsat
##    inc = 5  #******* increment for grouping for sweep set here *************
##    inc = min(12,max(inc, int(.1*N)))
    inc = 1+N/100
##    if N <1.5*inc: # if near the increment for grouping try to get it below.
##        prove_all_ind()
##        N = n_pos()
    if inc == 1:
        prove_all_ind()
        N = n_pos()
    T = int(tt) #this is the total time to be taken in final verification run before quitting speculation
##    if inc == 10:
##        t_init = 10
##    t = max(t_init/2,T/20)
##    if N <= inc:
##        t = T
##    print "inc = %d, Sweep time = %s, j_group = %d"%(inc,convert(t),j_last)
    t = sweep_time/2 #start sweeping at last time where cex was found.
##    it used to be t = 1 here but it did not make sense although seemed to work.
##    inc = 2
    while True: #poor man's concurrency
        N = n_pos()
        if N == 0:
            return Unsat
        #sweep_time controls so that when sweep starts after a cex, it starts at the last sweep time
        t = max(2,2*t) #double sweep time
        if t > .75*T:
            t = T
            full_time = True
        if ((N <= inc) or (N < 13)):
            t = sweep_time = T
            full_time = True
            inc = 1
##            sweep_time = 2*sweep_time
        if not t == T:
            t= sweep_time = max(t,sweep_time)
##            t = sweep_time
##new heuristic
        if (all_proc and sweep_time > 8): #stop poor man's concurrency and jump to full time.
            t = sweep_time = T
            full_time - True #this might be used to stop speculation when t = T and the last sweep
##                           found no cex and we do not prove Unsat on an output
        abc('w %s__ysavetemp.aig'%f_name)
        ps()
        if N < 50:
            inc = 1
        print "inc = %d, Sweep time = %s, j_last = %d"%(inc,convert(t),j_last)
        F = []
##        G = []
        #make new lambda functions since after the last pass some of the functions may have been proved and eliminated.
        for i in range(N):
            F = F + [eval('(pyabc_split.defer(verify_only)(%d,%s))'%(i,convert(T)))] #make time large and let sleep timer control timeouts
##            G = G + [range(i,i+1)]
        ######
        result = []
        outcome = ''
        N = len(F)
        rng = range(1+(N-1)/inc)
        rng = rng[j_last:]+rng[:j_last] #pick up in range where last found cex.
##        print 'rng = ',
##        print rng
        k = -1
        bb_time = time.time()
        for j in rng:
            k = k+1 #keeps track of how many groups we have processed.
            j_last = j
            J = j*inc
            JJ = J+inc
            JJ = min(N,JJ)
            if J == JJ-1:
                print 'Function = %d '%J,
            else:
                print 'Functions = [%d,%d]'%(J,JJ-1)
            Fj = create_funcs([18],t+1) #create timer function as i = 0 Here is the timer
            Fj = Fj + F[J:JJ]
            count = 0
            fj_time = time.time()
            abc('r %s__ysavetemp.aig'%f_name) #important need to restore aig here so the F refers to right thing when doing verify_only.
##                                             # because verify_only changes the aig.
##            ps()
            for i,res in pyabc_split.abc_split_all(Fj):
                count = count+1
                Ji = J+i-1 #gives output number
                if ((res == 0) or (res == 1)):
                    abc('read_status %d.status'%Ji)
                    res = get_status()
                    outcome = 'CEX: Frame = %d, PO = %d, Time = %s'%(cex_frame(),Ji,convert((time.time() - fj_time)))
                    break
                if i == 0: #sleep timer expired
                    outcome = '*** Time expired in %s sec. Next group = %d to %d ***'%(convert(time.time() - fj_time),JJ,min(N,JJ+inc))
                    break
                elif res == None: #this should not happen
                    print res
                    print Ji,RESULT[res],
                else: # output Ji was proved
                    result = result + [[Ji,res]]
                    if count >= inc:
                        outcome = '--- all group processed without cex ---'
                        all_proc = True
                        break
                    continue #this can only happen if inc > 1
            # end of for i loop
            if ((res < Unsat) and (not res == None)): 
                break
            else:
                continue # continue j loop
        #end of for j loop
        if k < len(rng):      
            t_init = t/2 #next time start with this time.
        else:
            j_last = j_last+1 #this was last j and we did not find cex, so start at next group
        print outcome + ' => ' ,
        if ((res < Unsat) and (not res == None)):
            t_init = t/2
            abc('read_status %d.status'%Ji) #make sure we got the right status file.
            #actually if doing abstraction we could remove proved outputs now, but we do not. -**inefficiency**
            return res
        else: #This implies that no outputs were disproved. Thus can remove proved outputs.
            abc('r %s__ysavetemp.aig'%f_name) #restore original aig
            if not result == []:
                res = []
                for j in range(len(result)):
                    k = result[j]
                    if k[1] == 2:
                        res = res + [k[0]]
##                print res
##                result = mapp(res,G)
                result = res
##                print result
                remove(result) #remove the outputs that were proved UNSAT.
                #This is OK for both abstract and speculate
                print 'Number of POs reduced to %d'%n_pos()
                if n_pos() == 0:
                    return Unsat
            if t>=T:
                return Undecided
            else:
                continue
    return Undecided

def remap_pos():
    """ maintains a map of current outputs to original outputs"""
    global po_map
    k = j = 0
    new = []
    assert n_pos() == len(po_map), 'length of po_map, %d, and current # POs, %d, don"t agree'%(len(po_map),n_pos())
    for j in range(len(po_map)):
        N = n_pos()
        abc('removepo -N %d'%k) # this removes the output if it is 0 driven
        if n_pos() == N:
            new = new + [po_map[j]]
            k = k+1
    if len(new) < len(po_map):
##        print 'New map = ',
##        print new
        po_map = new

def prove_mapped():
    """
    assumes that srm is in workspace and takes the unsolved outputs and proves
    them by using proved outputs as constraints.
    """
    global po_map
##    print po_map
    po_map.sort() #make sure mapped outputs are in order
    for j in po_map: #put unsolved outputs first
        run_command('swappos -N %d'%j)
        print j
    N = n_pos()
    assert N > len(po_map), 'n_pos = %d, len(po_map) = %d'%(N, len(po_map))
    run_command('constr -N %d'%(N-len(po_map))) #make the other outputs constraints
    run_command('fold') #fold constraints into remaining outputs.
    ps()
    prove_all_mtds(100)
    
def mapp(R,G):
    result = []
    for j in range(len(R)):
        result = result + G[R[j]]
    return result
        
#_______________________________________        

    
def prove_g_pos_split():
    """like prove_g_pos but quits when any output is undecided"""
    global f_name, max_bmc,x_factor,x
    x = time.clock()
    #input_x_factor()
    init_f_name = f_name
    print 'Beginning prove_g_pos_split'
    prove_all_ind()
    print 'Number of outputs reduced to %d by fast induction with constraints'%n_pos()
    reparam()
##    try_rpm()
    print '********** Proving each output separately ************'  
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
                print '********  PROVED OUTPUTS [%d-%d]  ******** '%(jnext+1,jnext_old)
            else:
                print '********  PROVED OUTPUT %d  ******** '%(jnext_old)
            pos_proved = pos_proved + range(jnext +1,jnext_old+1)
            continue
        if result == 'SAT':
            print 'One of output in (%d to %d) is SAT'%(jnext + 1,jnext_old)
            return result
        else:
            print '********  UNDECIDED on OUTPUTS %d thru %d  ******** '%(jnext+1,jnext_old)
            print 'Eliminating %d proved outputs'%(len(pos_proved))
            # remove outputs proved and return
            f_name = init_f_name
            abc('r %s_osavetemp.aig'%f_name)
            remove(pos_proved)
            trim()
            write_file('group')            
            return 'UNDECIDED'
    f_name = init_f_name
    abc('r %s_osavetemp.aig'%f_name)
    if not len(pos_proved) == n:
        print 'Eliminating %d proved outputs'%(len(pos_proved))
        remove(pos_proved)
        trim()
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
    #abc('scl')   # eliminated because need to keep same number of inputs.

def remove_intrps(J):
    JJ = []
    for i in J:
        if i in allintrps:
            continue
        else:
            JJ = JJ +[i]
    return JJ
        
    

def remove(lst):
    """Removes outputs in list"""
    global po_map
    n_before = n_pos()
    zero(lst)
##    remap_pos()
    remove_0_pos()
    print 'list',
    lst
    print 'n_before = %d, n_list = %d, n_after = %d'%(n_before, len(lst), n_pos())
    

def zero(list):
    """Zeros out POs in list"""
    for j in list:
        run_command('zeropo -N %d'%j)

def remove_0_pos():
    global po_map
    """removes the 0 pos, but no pis because we might get cexs and need the correct number of pis
    Should keep tract of if original POs are 0 and are removed.
    Can this happen outside of prove_all_ind or
    pord_all which can set proved outputs to 0???
    """
    run_command('&get; &trim -i; &put; addpi') #adds a pi only if there are none
    po_map = range(n_pos())
##    # gone back to original method of removing pos. Thus po_map is irrelevant
##    remap_pos()
##    abc('addpi')

def psp():
    quick_simp()
    result = run_parallel([6,21],500,'US') #runs 'run_parallel' and sp() in parallel. run_parallel uses
                #JP and TERM to terminate.
    return result

def sp():
    """Alias for super_prove"""
    print 'Executing super_prove'
    result = super_prove(0)
    return result


##def super_sec(options):
##    """Main proof technique now for seq eq checking. Does original prove and if after speculation there are multiple output left
##    if will try to prove each output separately, in reverse order. It will quit at the first output that fails
##    to be proved, or any output that is proved SAT"""
##    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time, sec_options
##    sec_options = options
##    init_initial_f_name = initial_f_name
##    if x_factor > 1:
##        print 'x_factor = %f'%x_factor
##        input_x_factor()
##    max_bmc = -1
##    x = time.time()
##    k = 2
##    K,result = prove_sec()
##    if ((result == 'SAT') or (result == 'UNSAT')):
##        print '%s: total clock time taken by super_prove = %f sec.'%(result,(time.time() - x))
##        return
##    elif ((result[:3] == 'UND') and (n_latches() == 0)):
##        return result
##    print '%s: total clock time taken by super_prove = %f sec.'%(result,(time.time() - x))
##    if n_pos() > 1:
##        print 'Entering prove_g_pos'
##        result = prove_g_pos(0)
##        print result
##        if result == 'UNSAT':
##            print 'Total clock time taken by super_prove = %f sec.'%(time.time() - x)
##            return result
##        if result == 'SAT':
##            k = 1 #Don't try to prove UNSAT on an abstraction that had SAT
##                    # should go back to backup 1 since probably spec was bad.
##            if check_abs(): #if same as abstract version, check original simplified version
##                k = 0
##    y = time.time()
##    if K == 0: #K = 0 means that speculate found cex in abstraction.
##        k=0
##    print 'Entering BMC_VER_result(%d)'%k
##    result = BMC_VER_result(k)
##    #print 'win_list = ',win_list
##    print 'Total clock time taken by last gasp verification = %f sec.'%(time.time() - y)
##    print 'Total clock time for %s = %f sec.'%(init_initial_f_name,(time.time() - x))
##    return result

def super_prove(n=0):
    """Main proof technique now. Does original prove and if after speculation there are multiple output left
    if will try to prove each output separately, in reverse order. It will quit at the first output that fails
    to be proved, or any output that is proved SAT
    n controls call to prove(n)
    n = 2 means skip initial simplify and speculate,
    n=1 skip initial simp.
    """
    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time
    init_initial_f_name = initial_f_name
    if x_factor > 1:
        print 'x_factor = %f'%x_factor
        input_x_factor()
    max_bmc = -1
    x = time.time()
    k = 2
    if n == 2:
        K,result = prove(2)
    else:
        K,result = prove(0)
    if ((result == 'SAT') or (result == 'UNSAT')):
        print '%s: total clock time taken by super_prove = %f sec.'%(result,(time.time() - x))
        return result
    elif ((result[:3] == 'UND') and (n_latches() == 0)):
        return result
    print '%s: total clock time taken by super_prove = %f sec.'%(result,(time.time() - x))
    y = time.time()
    if K == 0: #K = 0 means that speculate found cex in abstraction.
        k=0
    if n == 2:
        print 'Entering BMC_VER()'
        result = BMC_VER() #typically called from a super_prove run in parallel.
        if result == 'SAT': #this is because we have done an abstraction and cex is invalid.
            result = 'UNDECIDED'
    else:
        print 'Entering BMC_VER_result(%d)'%k
        result = BMC_VER_result(k)
    #print 'win_list = ',win_list
    print result
    print 'Total clock time taken by last gasp verification = %f sec.'%(time.time() - y)
    print 'Total clock time for %s = %f sec.'%(init_initial_f_name,(time.time() - x))
    return result

def reachm(t):
    x = time.clock()
    #print 'trying reachm'
    abc('&get;&reachm -vcs -T %d'%t)
    print 'reachm done in time = %f'%(time.clock() - x)
    return get_status()

def reachp(t):
    x = time.clock()
    #print 'trying reachm2'
    abc('&get;&reachp -rv -T %d'%t)
    print 'reachm2 done in time = %f'%(time.clock() - x)
    return get_status()

def reachn(t):
    x = time.clock()
    #print 'trying reachm3'
    abc('&get;&reachn -rv -T %d'%t)
    print 'reachm3 done in time = %f'%(time.clock() - x)
    return get_status()
    
def reachx(t):
    x = time.time()
    #print 'trying reachx'
    abc('reachx -t %d'%t)
    print 'reachx  done in time = %f'%(time.time() - x)
    return get_status()

def reachy(t):
    x = time.clock()
    #print 'trying reachy'
    abc('&get;&reachy -v -T %d'%t)
    print 'reachy done in time = %f'%(time.clock() - x)
    return get_status()
    

def create_funcs(J,t):
    """evaluates strings indexed by J in methods given by FUNCS
    Returns a list of lambda functions for the strings in FUNCs
    If J = [], then create provers for all POs"""
    funcs = []
    for j in range(len(J)):
        k=J[j]
        funcs = funcs + [eval(FUNCS[k])]
    return funcs

def check_abs():
    global init_initial_f_name
    abc('w %s_save.aig'%init_initial_f_name)
    ni = n_pis()
    nl = n_latches()
    na = n_ands()
    abc('r %s_smp_abs.aig'%init_initial_f_name)
    if ((ni == n_pis()) and (nl == n_latches()) and (na == n_ands())):
        return True
    else:
        abc('r %s_save.aig'%init_initial_f_name)
        return False

"""make a special version of BMC_VER_result that just works on the current network"""
def BMC_VER():
    global init_initial_f_name, methods, last_verify_time
    #print init_initial_f_name
    xt = time.time()
    result = 5
    t = max(2*last_verify_time,100)
    print 'Verify time set to %d'%t
    N = bmc_depth()
    L = n_latches()
    I = n_real_inputs()
    X = pyabc_split.defer(abc)
    J = slps + pdrs + [23] + bmcs
    if ( ((I+L<350)&(N>100))  or  (I+L<260) or (L<80) ):
        J = J+reachs # add all reach methods
        if L < 80:
            J = J + [4]
    F = create_funcs(J,t)
    mtds = sublist(methods,J)
    print '%s'%mtds
    (m,result) = fork_break(F,mtds,'US')
    print '(m,result) = %d,%s'%(m,result)
    result = RESULT[result]
    print 'BMC_VER() result = %s'%result
    return result

        
def BMC_VER_result(n):
    global init_initial_f_name, methods, last_verify_time
    #print init_initial_f_name
    xt = time.time()
    result = 5
    if n == 0:
        abc('r %s_smp.aig'%init_initial_f_name)
        print '\n***Running proof on initial simplified circuit\n',
        ps()
    elif n == 1:
        abc('r %s_smp_abs.aig'%init_initial_f_name)        
        print '\n***Running proof on abstracted circuit',
        ps()
    else: # n was 2
        print '\n***Running proof on final unproved circuit',
        ps()
    t = max(2*last_verify_time,1000)
    print 'Verify time set to %d'%t
    #status = verify(J,t)
    N = bmc_depth()
    L = n_latches()
    I = n_real_inputs()
    X = pyabc_split.defer(abc)
    J = slps + pdrs + [23] +bmcs
##    [0,1,7,14] # try pdr, interpolation, and pdrm
##    if n == 0:
##        J = J+ bmcs #add BMC #eveen if n =1 or 2 we want to find a cex
    #heuristic that if bmc went deep, then reachability might also
    if ( ((I+L<350)&(N>100))  or  (I+L<260) or (L<80) ):
        #J = J+[4,13] #add reachx and reachn
        J = J+reachs # add all reach methods
        if L < 80:
            J = J + [4]
    #F = eval(S)
    F = create_funcs(J,t)
    mtds = sublist(methods,J)
    print '%s'%mtds
    (m,result) = fork(F,mtds)
    result = get_status()
    if result == Unsat:
        return 'UNSAT'
    if n == 0:
        if result < Unsat:
            return 'SAT'
        if result > Unsat: #still undefined
            return 'UNDECIDED'
    elif n == 1: #just tried abstract version - try initial simplified version
        if result < Unsat:
            return BMC_VER_result(0)
        else: #if undecided on good abstracted version, does not make sense to try initial one
            return 'UNDECIDED'
    else: # n was 2, just tried final unresolved version - now try abstract version
        if result < Unsat: 
            return BMC_VER_result(1) #try abstract version
        else: #undecided on final unproved circuit. Probably can't do better.
            return 'UNDECIDED'
            
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
    """Tries to prove output k by induction, using other outputs as constraints.
    If ever an output is proved
    it is set to 0 so it can't be used in proving another output to break circularity.
    Finally all zero'ed ooutputs are removed.
    Prints out unproved outputs Finally removes 0 outputs
    """
    global n_pos_proved, n_pos_before
    n_proved = 0
    N = n_pos()
##    remove_0_pos()
##    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    if n_pos() == 1:
        return
    abc('w %s_osavetemp.aig'%f_name)
    lst = range(n_pos())
##    list.reverse()
##    for j in list[1:]:
    for j in lst:
##        abc('zeropo -N 0')
        abc('swappos -N %d'%j)
##        remove_0_pos() #may not have to do this if constr works well with 0'ed outputs
        abc('constr -N %d'%(n_pos()-1))
        abc('fold')
        n = max(1,n_ands())
        f = max(1,min(40000/n,16))
        f = int(f)
        abc('ind -ux -C 10000 -F %d'%f)
##        run_command('print_status')
        status = get_status()
        abc('r %s_osavetemp.aig'%f_name)
        if status == Unsat:
##            print '+',
            abc('zeropo -N %d'%j)
            abc('w %s_osavetemp.aig'%f_name) #if changed, store it permanently
            if j < n_pos_before - n_pos_proved:
                n_proved = n_proved + 1 # keeps track of real POs proved.
        elif status < Unsat:
            print '-%d'%j,
        else:
            print '*%d'%j,
    remove_0_pos()
    n_pos_proved = n_pos_proved + n_proved 
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def prove_all_mtds(t):
    """
    Tries to prove output k  with multiple methods in parallel,
    using other outputs as constraints. If ever an output is proved
    it is set to 0 so it can't be used in proving another output to break circularity.
    Finally all zero'ed ooutputs are removed.
    """
    N = n_pos()
##    remove_0_pos()
##    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        run_command('swappos -N %d'%j)
##        remove_0_pos() #may not have to do this if constr works well with 0'ed outputs
        abc('constr -N %d'%(n_pos()-1))
        abc('fold')
##        cmd = '&get;,pdr -vt=%d'%t #put in parallel.
##        abc(cmd)
        verify(pdrs+bmcs+intrps+sims,t)
        status = get_status()
        abc('r %s_osavetemp.aig'%f_name)
        if status == Unsat:
            print '+',
            abc('zeropo -N %d'%j)
            abc('w %s_osavetemp.aig'%f_name) #if changed, store it permanently
        print '%d'%j,
    assert not is_sat(), 'one of the POs is SAT' #we can do better than this
    remove_0_pos()
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def prove_all_pdr(t):
    """Tries to prove output k by pdr, using other outputs as constraints. If ever an output is proved
    it is set to 0 so it can't be used in proving another output to break circularity.
    Finally all zero'ed ooutputs are removed. """
    N = n_pos()
##    remove_0_pos()
    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        abc('swappos -N %d'%j)
##        remove_0_pos() #may not have to do this if constr works well with 0'ed outputs
        abc('constr -N %d'%(n_pos()-1))
        abc('fold')
        cmd = '&get;,pdr -vt=%d'%t #put in parallel.
        abc(cmd)
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

def prove_each_ind():
    """Tries to prove output k by induction,  """
    N = n_pos()
    remove_0_pos()
    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        abc('cone -s -O %d'%j)
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

def prove_each_pdr(t):
    """Tries to prove output k by PDR. If ever an output is proved
    it is set to 0. Finally all zero'ed ooutputs are removed. """
    N = n_pos()
    remove_0_pos()
    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        abc('cone -O %d -s'%j)
        abc('scl -m')
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

def disprove_each_bmc(t):
    """Tries to prove output k by PDR. If ever an output is proved
    it is set to 0. Finally all zero'ed ooutputs are removed. """
    N = n_pos()
    remove_0_pos()
    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        abc('cone -O %d -s'%j)
        abc('scl -m')
        abc('bmc3 -T %d'%t)
        status = get_status()
        abc('r %s_osavetemp.aig'%f_name)
        if status == Sat:
            print '+',
            abc('zeropo -N %d'%j)
            abc('w %s_osavetemp.aig'%f_name) #if changed, store it permanently
        print '%d'%j,
    remove_0_pos()
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def pord_1_2(t):
    """ two phase pord. First one tries with 10% of the time. If not solved then try with full time"""
    global n_pos_proved, ifpord1, pord_on
    pord_on = True # make sure that we do not reparameterize after abstract in prove_2
    n_pos_proved = 0
    if ifpord1:
        print 'Trying each output for %0.2f sec'%(.1*t)
        result = pord_all(.1*t) #we want to make sure that there is no easy cex.
        if (result <= Unsat):
            return result
    ifpord1 = 0
    print 'Trying each output for %0.2f sec'%t
    result = pord_all(t+2*G_T) #make sure there is enough time to abstract
    pord_on = False #done with pord
    return result

def pord_all(t):
    """Tries to prove or disprove each output j by PDRM BMC3 or SIM. in time t"""
    global cex_list, n_pos_proved, last_cx, pord_on, ifpord1
    print 'last_cx = %d'%last_cx
    btime = time.time()
    N = n_pos()
##    remove_0_pos()
    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
##    bmc_ss(t)
##    if is_sat():
##        cex_list = cex_get_vector()
##        return Sat
    prove_all_ind() ############ change this to keep track of n_pos_proved
    nn = n_pos()
    abc('w %s_osavetemp.aig'%f_name)
    if nn < 4: #Just cut to the chase immediately.
        return Undecided
    lst = range(n_pos())
    proved = disproved = []
##    abc('&get') #using this space to save original file
##    with redirect.redirect( redirect.null_file, sys.stdout ):
##        with redirect.redirect( redirect.null_file, sys.stderr ):
    cx_list = []
    n_proved = 0
    lcx = last_cx + 1
    lst = lst[lcx:]+lst[:lcx]
    lst.reverse()
    n_und = 0
    for j in lst:
        print ''
        print j,
        abc('&put; cone -O %d -s'%j)
        abc('scl -m')
##                ps()
##        run_parallel(slps+sims+bmcs+pdrs+[6],t,'US')
        result = run_sp2_par(t)
        print 'run_sp2_par result is %s'%result
        if result == 'UNDECIDED':
            n_und = n_und + 1
            status = Undecided
            if ((n_und > 1) and not ifpord1):
                break
        elif result == 'SAT':
            status = Sat
            disproved = disproved + [j]
            last_cx = j
            cx = cex_get()
            cx_list = cx_list + [cx]
            assert len(cx_list) == len(disproved), cx_list
            if len(cx_list) > 0:
                break
        else: #is unsat here
            status = Unsat
            proved = proved + [j]
            if j < n_pos_before - n_pos_proved:
                n_proved = n_proved +1
    n_pos_proved = n_pos_proved + n_proved
    print '\nProved %d outputs'%len(proved)
    print 'Disproved %d outputs'%len(disproved)
    print 'Time for pord_all was %0.2f'%(time.time() - btime)
    NN = len(proved+disproved)
    cex_list = cx_list
    if len(disproved)>0:
        assert status == Sat, 'status = %d'%status
        return Sat
    else:
        abc('r %s_osavetemp.aig'%f_name)
##        abc('&put') # returning original to work spece
        remove(proved)
        print '\nThe number of unproved POs reduced from %d to %d'%(N,n_pos())
        if n_pos() > 0:
            return Undecided
        else:
            return Unsat

def bmc_ss(t):
    """
    finds a set cexs in t seconds starting at 2*N where N is depth of bmc -T 1
    The cexs are put in the global cex_list
    """
    global cex_list
    x = time.time()
    tt = min(10,max(1,.05*t))
    abc('bmc3 -T %0.2f'%tt)
    N = n_bmc_frames()
    if N <= max_bmc:
        return Undecided
##    print bmc_depth()
##    abc('bmc3 -C 1000000 -T %f -S %d'%(t,int(1.5*max(3,max_bmc))))
    run_command('bmc3 -vs -C 1000000 -T %f -S %d'%(t,2*N))
    if is_sat():
        cex_list = cex_get_vector() #does this get returned from a concurrent process?
        n = count_non_None(cex_list)
        print '%d cexs found in %0.2f sec at frame %d'%(n,(time.time()-x),cex_frame())
    return get_status()

def list_non_None(lst):
    """ return [i for i,s in enumerate(cex_list) if not s == None]"""
    L = []
    for i in range(len(lst)):
        if not lst[i] == None:
            L = L + [i]
    return L

def count_non_None(lst):
    #return len([i for i,s in enumerate(cex_list) if not s == None]
    count = 0
    for i in range(len(lst)):
        if not lst[i] == None:
            count = count + 1
    return count

def remove_disproved_pos(lst):
    for i in range(len(lst)):
        if not lst[i] == None:
            abc('zeropo -N %d'%i)
    remove_0_pos()
        
def bmc_s(t):
    """ finds a cex in t seconds starting at 2*N where N is depth of bmc -T 1"""
    x = time.time()
    tt = min(5,max(1,.05*t))
    abc('bmc3 -T %0.2f'%tt)
    if is_sat():
        print 'cex found in %0.2f sec at frame %d'%((time.time()-x),cex_frame())
        return get_status()
##    abc('bmc3 -T 1')
    N = n_bmc_frames()
##    print bmc_depth()
##    abc('bmc3 -C 1000000 -T %f -S %d'%(t,int(1.5*max(3,max_bmc))))
    cmd = 'bmc3 -J 2 -D 4000 -C 1000000 -T %f -S %d'%(t,2*N)
##    print cmd
    abc(cmd)
    if is_sat():
        print 'cex found in %0.2f sec at frame %d'%((time.time()-x),cex_frame())
    return get_status()


def pdr(t):
    abc('&get; ,pdr -vt=%f'%t)
    return RESULT[get_status()]

def pdrm(t):
    abc('pdr -v -C 0 -T %f'%t)
    return RESULT[get_status()]

def pdrmm(t):
    abc('pdr -mv -C 0 -T %f'%t)
    return RESULT[get_status()]

def split(n):
    abc('orpos;&get')
    abc('&posplit -v -N %d;&put;dc2'%n)
    trim()

def keep_splitting():
    for j in range(5):
        split(5+j)
        no = n_pos()
        status = prove_g_pos_split()
        if status <= Unsat:
            return status
        if no == n_pos():
            return Undecided

def drill(n):
    run_command('&get; &reachm -vcs -H 5 -S %d -T 50 -C 40'%n)

def prove_1():
    """
    A version of prove(). Called only during prove_pos or prove_g_pos or prove_only when we
    have speculated and produced multiple outputs. Does speculation only in final_verify_recur.
    Proves all the outputs together. If ever an abstraction was done then
    if SAT is returned,we make RESULT return "undecided".
    """
    global x_factor,xfi,f_name,x, initial_f_name
    x = time.time()
    max_bmc = -1
    K = 0
    print 'Initial: ',
    ps()
    x_factor = xfi
    print 'x_factor = %f'%x_factor
    write_file('smp')
    initial_f_name_save = initial_f_name #needed because we are making local backups here.
    initial_f_name = '%s_temp'%initial_f_name
    abc('w %s_backup_%d.aig'%(initial_f_name,K)) #backup 0
    K = K +1 #K = 1 is next backup
    set_globals()
    print'\n***Running abstract'
    nl_b = n_latches()
    status = abstract()
    trim()
    write_file('abs')
    status = process_status(status)
    if ((status <= Unsat)  or  status == Error):
        if  status < Unsat:
            print 'CEX in frame %d'%cex_frame(),
            print 'abstract found a cex in unabstacted circuit'
            print 'Time for proof = %f sec.'%(time.time() - x)
            initial_f_name = initial_f_name_save
            return RESULT[status]
        print 'Time for proof = %f sec.'%(time.time() - x)
        initial_f_name = initial_f_name_save
        return RESULT[status]
    abc('w %s_backup_%d.aig'%(initial_f_name,K)) #backup 1
    print 'Entering final_verify_recur(2) from prove_1()'
    status = final_verify_recur(2) 
    trim()
    write_file('final')
    print 'Time for proof = %f sec.'%(time.time() - x)
    initial_f_name = initial_f_name_save
    return RESULT[status]
    
def pre_reduce():
    x = time.clock()
    pre_simp()
    write_file('smp')
    abstract()
    write_file('abs')
    print 'Time = %f'%(time.clock() - x)

def sublist(L,I):
    # return [s for i,s in enumerate(L) if i in I]
    z = []
    for i in range(len(I)):
        s = L[I[i]],
        s = list(s)
        z = z + s
    return z

#PARALLEL FUNCTIONS
"""  funcs should look like
funcs = [pyabc_split.defer(abc)('&get;,bmc -vt=50;&put'),pyabc_split.defer(super_prove)()]
After this is executed funcs becomes a special list of lambda functions
which are given to abc_split_all to be executed as in below.
It has been set up so that each of the functions works on the current aig and
possibly transforms it. The new aig and status is always read into the master when done
"""


def tf():
    result = top_fork()
    return result

def top_fork(J,t):
    global x_factor, final_verify_time, last_verify_time, methods
    set_globals()
    mtds = sublist(methods,J)
    F = create_funcs(J,t)
    print 'Running %s in parallel for max %d sec.'%(mtds,t)
    (m,result) = fork_last(F,mtds) #FORK here
    return get_status()

def run_sp2_par(t):
    """ Runs the single method super_prove(2), timed for t seconds."""
    global cex_list,methods
    J = slps+[6]
    funcs = create_funcs(J,t) 
    y = time.time()
    for i,res in pyabc_split.abc_split_all(funcs):
        #print 'i,res = %d,%s'%(i,res)
        t = time.time()-y
        if i == 0:
            print 'sleep timer expired in %0.2f'%t
            return 'UNDECIDED'
        else:
            if res == 'UNSAT':
                print 'SUPER_PROVE2 proved UNSAT in %0.2f sec.'%t
                return 'UNSAT'
            elif res == 'UNDECIDED':
                print 'SUPER_PROVE2 proved UNDECIDED in %0.2f sec.'%t
                return 'UNDECIDED'
            else:
                print 'SUPER_PROVE2 found cex in %0.2f sec.'%t
                return 'SAT'
            

def run_parallel(J,t,BREAK):
    """ Runs the listed methods J, each for time = t, in parallel and
    breaks according to BREAK = subset of '?USLB'"""
    global cex_list,  methods
    mtds = sublist(methods,J)
    F = create_funcs(J,t) #if J = [] we are going to create functions that process each output separately.
                            #if 18, then these are run in parallel with sleep
    if ((J == []) ):
        result = fork_break(F,mtds,BREAK)
##        #redirect here to suppress printouts.
##        with redirect.redirect( redirect.null_file, sys.stdout ):
##            with redirect.redirect( redirect.null_file, sys.stderr ):
##                result = fork_break(F,mtds,BREAK)
    elif 'L' in BREAK:
        result = fork_last(F,mtds)
    elif 'B' in BREAK:
        result = fork_best(F,mtds)
    else:
        result = fork_break(F,mtds,BREAK)
    return result

def fork_all(funcs,mtds):
    """Runs funcs in parallel and continue running until all are done"""
    global methods
    y = time.time()
    for i,res in pyabc_split.abc_split_all(funcs):
        status = prob_status()
        t = time.time()-y
        if not status == -1: #solved here
            if status == 1: #unsat
                print '%s proved UNSAT in %f sec.'%(mtds[i],t)
            else:
                print '%s found cex in %f sec. - '%(mtds[i],t),
                if not mtds[i] == 'REACHM':
                    print 'cex depth at %d'%cex_frame()
                else:
                    print ' '
            continue
        else:
            print '%s was undecided in %f sec. '%(mtds[i],t)
    return i,res

def fork_break(funcs,mtds,BREAK):
    """
    Runs funcs in parallel and breaks according to BREAK <= '?US'
    If mtds = 'sleep' or [], we are proving outputs in parallel
    Saves cex's found in cex_list in case we are proving POs.
    """
    global methods,last_verify_time,seed,cex_list,last_winner,last_cex
    seed = seed + 3 # since parallel processes do not chenge the seed in the prime process, we need to change it here
    cex_list = lst = []
    y = time.time() #use wall clock time because parent fork process does not use up compute time.
    for i,res in pyabc_split.abc_split_all(funcs):
        status = get_status()
        t = time.time()-y
        lm = len(mtds)
        if ((lm < 2) and not i == 0): # the only single mtds case is where it is 'sleep'
            M = 'Output %d'%(i-lm)
        else:
            M = mtds[i]
            last_winner = M
        if M == 'sleep':
            print 'sleep: time expired in %s sec.'%convert(t)
            assert status >= Unsat,'status = %d'%status
            break
        if ((status > Unsat) and '?' in BREAK): #undecided
                break
        elif status == Unsat: #unsat
            print '%s: UNSAT in %s sec.'%(M,convert(t))
            if 'U' in BREAK:
                break
        elif status < Unsat: #status == 0 - cex found
            if M in methods:                
                if methods.index(M) in exbmcs+allreachs+allpdrs+[1]: #set the known best depth so far. [1] is interp
                    set_max_bmc(n_bmc_frames())
            last_cex = M
            print '%s: -- cex in %0.2f sec. at depth %d => '%(M,t,cex_frame()),
            cex_list = cex_list+[cex_get()] #accumulates multiple cex's and puts them on list.
            if len(cex_list)>1:
                print 'len(cex_list): %d'%len(cex_list)
            if 'S' in BREAK:
                break
        else:
            continue
    return i,status

def fork_best(funcs,mts):
    """ fork the functions, If not solved, take the best result in terms of AIG size"""
    global f_name
    n = len(mts)-1
    y = time.time()
    m_best = -1
    best_size = [n_pis(),n_latches(),n_ands()]
##    print best_size
    abc('w %s_best_aig.aig'%f_name)
    for i,res in pyabc_split.abc_split_all(funcs):
        status = prob_status()
##        print i,
##        ps()
##        print i,res,
        #ps()
        if not status == -1: #solved here
            m = i
            t = time.time()-y
            if status == 1: #unsat
                print '%s proved UNSAT in %f sec.'%(mtds[i],t)
            else:
                print '%s found cex in %f sec. - '%(mtds[i],t),
            break
        else:
            cost = rel_cost(best_size)
##            print i,cost
            if cost < 0:
                best_size = [n_pis(),n_latches(),n_ands()]
##                print best_size
                m_best = i
##                print m_best
                abc('w %s_best_aig.aig'%f_name)
    abc('r %s_best_aig.aig'%f_name)
    return m_best,res

def fork_last(funcs,mtds):
    """ fork the functions, and take first definitive answer, but
    if last method ends first, then kill others"""
    n = len(mtds)-1
    m = -1
    y = time.time()
    lst = ''
    print mtds
    for i,res in pyabc_split.abc_split_all(funcs):
        status = prob_status()
        if not status == -1: #solved here
            m = i
            t = int(time.time()-y)
            if status == 1: #unsat
                print '%s proved UNSAT in %d sec.'%(mtds[i],t)
            else:
                print '%s found cex in %s sec. - '%(mtds[i],convert(t)),
            break
        elif i == n:
            t = int(time.time()-y)
            m = i
            print '%s: %d sec.'%(mtds[i],t)
            ps()
            break
        elif mtds[i] == 'sleep':
            t = time.time()-y
            print 'sleep timer expired in %0.2f'%t
            break
        lst = lst + ', '+mtds[i]
    return m,res

def fork(funcs,mtds):
    """ runs funcs in parallel This keeps track of the verify time
    when a cex was found, and if the time to find
    the cex was > 1/2 allowed time, then last_verify_time is increased by 2"""
    global win_list, methods, last_verify_time,seed
    beg_time = time.time()
    i,res = fork_break(funcs,mtds,'US') #break on Unsat of Sat.
    t = time.time()-beg_time        #wall clock time because fork does not take any compute time.
    if t > .4*last_verify_time:
##    if t > .15*last_verify_time: ##### temp
        t = last_verify_time = last_verify_time + .1*t
        #print 'verify time increased to %s'%convert(t)
    assert res == get_status(),'res: %d, status: %d'%(res,get_status())
    return i,res


def save_time(M,t):
    global win_list,methods
    j = methods.index(M)
    win_list = win_list + [(j,t)]
    #print win_list

def summarize(lst):
    result = [0]*10
    for j in range(len(lst)):
        k = lst[j]
        result[k[0]]=result[k[0]]+k[1]
    return result

def top_n(lst,n):
    result = []
    ll = list(lst) #makes a copy
    m = min(n,len(ll))
    for i in range(m):
        mx_index = ll.index(max(ll))
        result = result + [mx_index]
        ll[mx_index] = -1
    return result

def super_pre_simp():
    while True:
        nff = n_latches()
        print 'Calling pre_simp'
        pre_simp()
        if n_latches() == nff:
            break

#______________________________
#new synthesis command

def synculate(t):
    """
    Finds candidate sequential equivalences and refines them by simulation, BMC, or reachability
    using any cex found. If any are proved, then they are used to reduce the circuit. The final aig
    is a new synthesized circuit where all the proved equivalences are merged.
    If we put this in a loop with increasing verify times, then each time we work with a simpler model
    and new equivalences. Should approach srm. If in a loop, we can remember the cex_list so that we don't
    have to deal with disproved equivalences. Then use refine_with_cexs to trim the initial equivalences.
    If used in synthesis, need to distinguish between
    original outputs and new ones. Things to take care of: 1. a PO should not go away until it has been processes by merged_proved_equivalences
    2. Note that &resim does not use the -m option where as in speculation - m is used. It means that if
    an original PO isfound to be SAT, the computation quits becasue one of the output
    miters has been disproved.
    """    
    global G_C,G_T,n_pos_before, x_factor, n_latches_before, last_verify_time, f_name,cex_list, max_verify_time
    
    
    def refine_with_cexs():
        """Refines the gores file to reflect equivalences that go away because of cexs in cex_list"""
        global f_name
        abc('&r %s_gores.aig'%f_name)
        for j in range(len(cex_list)):
            cex_put(cex_list[j])
            run_command('&resim') #put the jth cex into the cex space and use it to refine the equivs
        abc('&w %s_gores.aig'%f_name)
        return
    
    def generate_srms():
        """generates a synthesized reduced model (srms) from the gores file"""
        global f_name, po_map
        abc('&r %s_gores.aig; &srm -sf; r gsrms.aig; w %s_gsrms.aig'%(f_name,f_name))
        print 'New srms = ',ps()
        po_map = range(n_pos())
        return 'OK'

    def merge_proved_equivalences():
        #this only changes the gores file.
        run_command('&r %s_gores.aig; &equiv_mark -vf %s_gsrms.aig; &reduce -v; &w %s_gores.aig'%(f_name,f_name,f_name))
        return

    def generate_equivalences():
        set_globals()
        t = max(1,.5*G_T)
        r = max(1,int(t))
        cmd = "&get; &equiv2 -C %d -F 200 -T %f -S 1 -R %d"%((G_C),t,r)
        abc(cmd)
        #run_command('&ps')
        eq_simulate(.5*t)
        #run_command('&ps')
        cmd = '&semi -W 63 -S 5 -C 500 -F 20 -T %d'%(.5*t)
        abc(cmd)
        #run_command('&ps')
        run_command('&w %s_gores.aig'%f_name)

    remove_0_pos() #makes sure no 0 pos to start
    cex_list = []
    n_pos_before = n_pos()
    n_latches_before = n_latches()
##    print 'Generating equivalences'
    generate_equivalences()
##    print 'Generating srms file'
    generate_srms() #this should not create new 0 pos
##    if n_pos()>100:
##        removed
    remove_0_pos()
    n_pos_last = n_pos()
    if n_pos_before == n_pos():
        print 'No equivalences found. Quitting synculate'
        return Undecided_no_reduction
    print 'Initial synculation: ',ps()
##    ps()
    set_globals()
    simp_sw = init = True
    simp_sw = False #temporary
    print '\nIterating synculation refinement'
    abc('w initial_sync.aig')
    max_verify_time = t
    print 'max_verify_time = %d'%max_verify_time
    """
        in the following loop we increase max_verify_time by twice time spent to find last cexs or Unsat's
        We iterate only when we have proved cex + unsat > 1/2 n_pos. Then we update srms and repeat.        
    """
    while True:                 # refinement loop
        t = max_verify_time     #this may have been increased since the last loop
##        print 'max_verify_time = %d'%max_verify_time
        set_globals()
        if not init:
            generate_srms()     #generates a new gsrms file and leaves it in workspace
##            print 'generate_srms done'
            if n_pos() == n_pos_before:
                break
            if n_pos() == n_pos_last:   #if nothing new, then quit if max_verification time is reached.
                if t > max_verify_time:
                    break
            if simp_sw:                     #Warning: If this holds then simplify could create some 0 pos
                na = n_ands()
                simplify()
                while True:
                    npo = n_pos()
##                    print 'npos = %d'%npo
                    merge_proved_equivalences() #So we need to merge them here. Can merging create more???
                    generate_srms()
                    if npo == n_pos():
                        break
                if n_ands() > .7*na:            #if not significant reduction, stop simplification
                    simp_sw = False             #simplify only once.
            if n_latches() == 0:
                return check_sat()
        n_pos_last = n_pos()
        init = False                        # make it so that next time it is not the first time through
        syn_par(t)
        if (len(cex_list)+len(result)) == 0: #nothing happened aand ran out of time.
            break
        abc('w %s_gsrms.aig'%f_name)
        #print 'No. of cexs after syn_parallel = %d'%len(cex_list)
        merge_proved_equivalences()         #changes the underlying gores file by merging fanouts of proved eqs
        #print 'merge done'
        refine_with_cexs()                  #changes the gores file by refining the equivalences in it using cex_list.
        #print 'refine_with_cexs done'
        continue
    extract(0,n_pos_before) #get rid of unproved outputs
    return

def syn_par(t):
    """prove n outputs at once and quit at first cex. Otherwise if no cex found return aig
    with the unproved outputs"""
    global trim_allowed,max_verify_time, n_pos_before
    global cex_list, result
    b_time = time.time()
    n = n_pos()
    if n == n_pos_before:
        return
    mx = n_pos()
    if n_pos() - n_pos_before > 50:
        mx = n_pos_before + 50
    r = range(n_pos_before, mx)     
    N = max(1,(mx-n_pos_before)/2)
    abc('w %s__ysavetemp.aig'%f_name) 
    F = [eval(FUNCS[18])] #create a timer function
    #print r
    for i in r:
        F = F + [eval('(pyabc_split.defer(verify_only)(%d,%d))'%(i,t))]
    cex_list = result = []
    outcome = ''
    #redirect printout here
##    with redirect.redirect( redirect.null_file, sys.stdout ):
##        with redirect.redirect( redirect.null_file, sys.stderr ):
    for i,res in pyabc_split.abc_split_all(F):
        status = get_status()
##        print i
        if i == 0:          #timed out
            outcome = 'time expired after = %d'%(time.time() - b_time)
            break
        if status < Unsat:
            cex_list = cex_list + [cex_get()]                    
        if status == Unsat:
            result = result + [r[i-1]]
        if (len(result)+len(cex_list))>= N:
            T = time.time() - b_time
            if T > max_verify_time/2:
                max_verify_time = 2*T
            break
        continue
    if not outcome == '':
        print outcome
##    print 'cex_list,prove_list = ',cex_list,result
    abc('r %s__ysavetemp.aig'%f_name) #restore initial aig so that pos can be 0'ed out
    if not result == []: # found some unsat's
##        min_r = min(result)
##        max_r = max(result)
##        no = n_pos()
##        assert (0 <= min_r and max_r < no), 'min_r, max_r, length = %d, %d, %d'%(min_r,max_r,len(result))
        zero(result)
    return
    #print "Number PO's proved = %d"%len(result)

def absec(n):
    #abc('w t.aig')
    for j in range(n):
        print '\nFrame %d'%(j+1)
        run_command('absec -F %d'%(j+1))
        if is_unsat():
            print 'UNSAT'
            break
    

"""
    we might be proving some original pos as we go, and on the other hand we might have some equivalences that we
    can't prove. There are two uses, in verification
    verification - we want to remove the proved pos whether they are original or not. But if a cex for an original, then need to
                    remember this.
    synthesis - the original outputs need to be kept and ignored in terms of cex's - supposedly they can't be proved.
"""

""" Experimental"""

def csec():
    global f_name
    if os.path.exists('%s_part0.aig'%f_name):
        os.remove('%s_part0.aig'%f_name)
    run_command('demiter')
    if not os.path.exists('%s_part0.aig'%f_name):
        return
    run_command('r %s_part0.aig'%f_name)
    ps()
    run_command('comb')
    ps()
    abc('w %s_part0comb.aig'%f_name)
    run_command('r %s_part1.aig'%f_name)
    ps()
    run_command('comb')
    ps()
    abc('w %s_part1comb.aig'%f_name)
    run_command('&get; &cec %s_part0comb.aig'%(f_name))
    if is_sat():
        return 'SAT'
    if is_unsat():
        return 'UNSAT'
    else:
        return 'UNDECIDED'

    ###########################
####        we will verify outputs ORed in groups of g[i]
####        here we take div = N so no ORing
##        div = max(1,N/1)
##        g = distribute(N,div)
##        if len(g) <= 1:
##            t = tt
##        g.reverse()
####        print g
##        x = 0
##        G = []
##        for i in range(div):
##            y = x+g[i]
##            F = F + [eval('(pyabc_split.defer(verify_range)(%d,%d,%s))'%(x,y,convert(t)))]
##            G = G + [range(x,y)]
##            x = y
####        print G
###########################

def sop_balance(k):
    abc('st; if -K %d;ps'%k)
    for i in range(2):
        run_command('st; if -K %d;ps'%k)
    run_command('st; if  g -C %d -K %d;ps'%(k+4,k+4))
    for i in range(3):
        run_command('st;&get; &dch; &put; if -K %d;ps'%k)

def map_lut_dch(k):
    for i in range(5):
        run_command('st;if -a -K %d; ps; st; dch; ps; if -a -K %d; ps; mfs ;ps; lutpack; ps'%(k,k))
    
def map_lut(k):
    for i in range(5):
        run_command('st; if -e -K %d; ps;  mfs ;ps; lutpack -L 50; ps'%(k))
    
        
