from pyabc import *
import pyabc_split
import redirect
import sys
import os
import time
import math
import main
import filecmp


global G_C,G_T,latches_before_abs,latches_before_pba,n_pos_before,x_factor,methods,last_winner
global last_cex,JV,JP, cex_list,max_bmc, last_cx, pord_on, trim_allowed, temp_dec, abs_ratio, ifbip
global if_no_bip

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
int n_nodes();
int n_levels();

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
RESULT = ('SAT' , 'SAT', 'UNSAT', 'UNDECIDED', 'UNDECIDED,', 'ERROR'  )
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
temp_dec = True
ifpord1 = 1
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
ifbip = 0 # sets the abtraction method
if_no_bip = 0 #True sets it up so it can use bip and reachx commands.
abs_ratio = .5 #this controls when abstract stops
t_init = 2 #initial time for poor man's concurrency.
methods = ['PDR', 'INTRP', 'BMC',
           'SIM', 'REACHX',
           'PRE_SIMP', 'Simple_prove', 'PDRM', 'REACHM', 'BMC3','Min_Retime',
           'For_Retime','REACHP','REACHN','PDR_sd','prove_part_2',
           'prove_part_3','verify','sleep','PDRM_sd','prove_part_1',
           'run_parallel','INTRPb', 'INTRPm', 'REACHY', 'REACHYc','RareSim','simplify', 'speculate',
           'quick_sec', 'BMC_J', 'BMC2', 'extract -a', 'extract', 'PDRa']
#'0.PDR', '1.INTERPOLATION', '2.BMC', '3.SIMULATION',
#'4.REACHX', '5.PRE_SIMP', '6.SUPER_PROVE(2)', '7.PDRM', '8.REACHM', 9.BMC3'
# 10. Min_ret, 11. For_ret, 12. REACHP, 13. REACHN 14. PDRseed 15.prove_part_2,
#16.prove_part_3, 17.verify, 18.sleep, 19.PDRMm, 20.prove_part_1,
#21.run_parallel, 22.INTRP_bwd, 23. Interp_m 24. REACHY 25. REACHYc 26. Rarity Sim 27. simplify
#28. speculate, 29. quick_sec, 30 bmc3 -S, 31. BMC2 32. extract -a 33. extract 34. pdr_abstract
win_list = [(0,.1),(1,.1),(2,.1),(3,.1),(4,.1),(5,-1),(6,-1),(7,.1)]
FUNCS = ["(pyabc_split.defer(abc)('&get;,pdr -vt=%f'%t))",
         "(pyabc_split.defer(abc)('&get;,imc -vt=%f'%(t)))",
         "(pyabc_split.defer(abc)('&get;,bmc -vt=%f'%t))",
         "(pyabc_split.defer(simulate)(t))",
         "(pyabc_split.defer(abc)('reachx -t %d'%t))",
         "(pyabc_split.defer(pre_simp)())",
##         "(pyabc_split.defer(super_prove)(2))",
         "(pyabc_split.defer(simple)())",
         "(pyabc_split.defer(pdrm)(t))",
         "(pyabc_split.defer(abc)('&get;&reachm -vcs -T %d'%t))",
         "(pyabc_split.defer(abc)('bmc3 -C 1000000 -T %f'%t))",
         "(pyabc_split.defer(abc)('dr;&get;&lcorr;&dc2;&scorr;&put;dr'))",
         "(pyabc_split.defer(abc)('dr -m;&get;&lcorr;&dc2;&scorr;&put;dr'))",
         "(pyabc_split.defer(abc)('&get;&reachp -vr -T %d'%t))",
         "(pyabc_split.defer(abc)('&get;&reachn -vr -T %d'%t))",
##         "(pyabc_split.defer(abc)('&get;,pdr -vt=%f -seed=521'%t))",
         "(pyabc_split.defer(pdrseed)(t))",
         "(pyabc_split.defer(prove_part_2)())",
         "(pyabc_split.defer(prove_part_3)())",
         "(pyabc_split.defer(verify)(JV,t))",
         "(pyabc_split.defer(sleep)(t))",
         "(pyabc_split.defer(pdrmm)(t))",
         "(pyabc_split.defer(prove_part_1)())",
         "(pyabc_split.defer(run_parallel)(JP,t,'TERM'))",
         "(pyabc_split.defer(abc)('&get;,imc -bwd -vt=%f'%t))",
##         "(pyabc_split.defer(abc)('int -C 1000000 -F 10000 -K 2 -T %f'%t))",
         "(pyabc_split.defer(abc)('int -C 1000000 -F 10000 -K 1 -T %f'%t))",
         "(pyabc_split.defer(abc)('&get;&reachy -v -T %d'%t))",
         "(pyabc_split.defer(abc)('&get;&reachy -cv -T %d'%t))",
         "(pyabc_split.defer(simulate2)(t))",
         "(pyabc_split.defer(simplify)())",
         "(pyabc_split.defer(speculate)())",
         "(pyabc_split.defer(quick_sec)(t))",
         "(pyabc_split.defer(bmc_j)(t))",
         "(pyabc_split.defer(abc)('bmc2 -C 1000000 -T %f'%t))",
         "(pyabc_split.defer(extractax)('a'))",
         "(pyabc_split.defer(extractax)())",
         "(pyabc_split.defer(pdra)(t))",
         ]
##         "(pyabc_split.defer(abc)('bmc3 -C 1000000 -T %f -S %d'%(t,int(1.5*max_bmc))))"
#note: interp given 1/2 the time.
allreachs = [4,8,12,13,24,25]
reachs = [24]
##allpdrs = [14,7,34,19,0]
allpdrs = [14,7,34,19]
pdrs = [34,7,14]
allbmcs = [2,9,30,31]
exbmcs = [2,9]
bmcs = [9,30]
allintrps = [1,22,23]
bestintrps = [23]
intrps = [23]
allsims = [3,26]
sims = [26] 
allslps = [18]
slps = [18]
imc1 = [1]

JVprove = [7,23,4,24]
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
    global n_pos_before, n_pos_proved, last_cx, pord_on, temp_dec, abs_time
    xfi = x_factor = 1  #set this to higher for larger problems or if you want to try harder during abstraction
    max_bmc = -1
    last_time = 0
    j_last = 0
    seed = 113
    init_simp = 1
    temp_dec = True
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
    abs_time = 10000

def set_abs_method():
    """ controls the way we do abstraction, 0 = no bip, 1 = old way, 2 use new bip and -dwr
    see absab()
    """
    global ifbip
    print 'Set method of abstraction: \n0 = use vta and no bips, \n1 = old way, \nelse = use ,abs and -dwr'
    s = raw_input()
    s = remove_spaces(s)
    if s == '1':
        ifbip = 1 #old way
    elif s == '0':
        ifbip = 0 #use vta and no bip
    else:
        ifbip = 2 #use ,abc -dwr
    print 'ifbip set to %d. Note engines are set only when read_file is done'%ifbip
    
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
    Called only when read_file is called.
    Sets the MC engines that are used in verification according to
    if there are 4 or 8 processors. if if_no_bip = 1, we will not use any bip and reachx engines
    """
    global reachs,pdrs,sims,intrps,bmcs,n_proc,abs_ratio,ifbip
    if N == 0:
        N = n_proc = os.sysconf(os.sysconf_names["SC_NPROCESSORS_ONLN"])
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
        pdrs = [34,7]
        if if_no_bip:
            allpdrs = pdrs = [7,19]
        bmcs = [9,30]
        intrps = [23]
        sims = []
        slps = [18]
    elif N == 8:
        reachs = [24]
        pdrs = [34,7,14]
        intrps = [23,1]
        if if_no_bip:
            allpdrs = pdrs = [7,19]
            intrps = [23]
        bmcs = [9,30]
        sims = [26] #use default
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

def seq_name(f):
    names = []
    f = f + '_'
    names = []
    while len(f)>0:
        j = f.find('_')
        if j == -1:
            break
        names = names + [f[:j]]
##        print names
        f = f[j+1:]
##        print f
    return names

def revert(f,n):
    l = seq_name(f)
    for j in range(n):
        if len(l)>0:
            l.pop()
    name = construct(l)
    return name

def construct(l):
    ll = l
    name = ''
    while len(l)>0:
        name = '_'+ll.pop()+name
    return name[1:]

def process_sat():
    l = seq_name(f_name)

def read_file_quiet(fname=None):
    """This is the main program used for reading in a new circuit. The global file name is stored (f_name)
    Sometimes we want to know the initial starting name. The file name can have the .aig extension left off
    and it will assume that the .aig extension is implied. This should not be used for .blif files.
    Any time we want to process a new circuit, we should use this since otherwise we would not have the
    correct f_name."""
    global max_bmc,  f_name, d_name, initial_f_name, x_factor, init_initial_f_name, win_list,seed, sec_options
    global win_list, init_simp, po_map
    abc('fraig_restore') #clear out any residual fraig_store
    set_engines() #temporary
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
##        print s
    else:
        s = fname
    if s[-4:] == '.aig':
        f_name = s[:-4]
    elif s[-5:] == '.blif':
        f_name = s[:-5]
    else:
        f_name = s
        s = s+'.aig'
##    run_command(s)
##    print s
    if s[-4:] == '.aig':
        run_command('&r %s;&put'%s) #warning: changes names to generic ones.
    else: #this is a blif file
        run_command('r %s'%s)
        abc('st;&get;&put') #changes names to generic ones for doing cec later.
        run_command('zero;w %s.aig'%f_name)
    set_globals()
    init_initial_f_name = initial_f_name = f_name
    print 'Initial f_name = %s'%f_name
    abc('addpi')
    #check_pos() #this removes constant outputs with a warning -
    #needed when using iso. Need another fix for using iso.
    run_command('fold')
    ps()
    return
        
    
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

def null_status():
    """ resets the status to the default values but note that the &space is changed"""
    abc('&get;&put')

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
    s='ANDs'
    if a == -1:
        a = n_nodes()
        s = 'Nodes'
    b = max(max_bmc,bmc_depth())
    c = cex_frame()
    if b>= 0:
        if c>=0:
            print 'PIs=%d,POs=%d,FF=%d,%s=%d,max depth=%d,CEX depth=%d'%(i,o,l,s,a,b,c)
        elif is_unsat():
            print 'PIs=%d,POs=%d,FF=%d,%s=%d,max depth = infinity'%(i,o,l,s,a)
        else:
            print 'PIs=%d,POs=%d,FF=%d,%s=%d,max depth=%d'%(i,o,l,s,a,b)            
    else:
        if c>=0:
            print 'PIs=%d,POs=%d,FF=%d,%s=%d,CEX depth=%d'%(i,o,l,s,a,c)
        else:
            print 'PIs=%d,POs=%d,FF=%d,%s=%d'%(i,o,l,s,a)

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
    p_40 = False
    n =n_ands()
    if n >= 70000:
        abc('&get;&scorr -C 0;&put')
    n =n_ands()
    if n >= 100000:
        abc('&get;&scorr -k;&put')
    if (70000 < n and n < 100000):
        p_40 = True
        abc("&get;&dc2;&put;dr;&get;&lcorr;&dc2;&put;dr;&get;&scorr;&fraig;&dc2;&put;dr")
        n = n_ands()
##        if n<60000:
        if n < 80000:
            abc("&get;&scorr -F 2;&put;dc2rs")
        else: # n between 60K and 100K
            abc("dc2rs")
    n = n_ands()
##    if (30000 < n  and n <= 40000):
    if (60000 < n  and n <= 70000):
        if not p_40:
            abc("&get;&dc2;&put;dr;&get;&lcorr;&dc2;&put;dr;&get;&scorr;&fraig;&dc2;&put;dr")
            abc("&get;&scorr -F 2;&put;dc2rs")
        else:
            abc("dc2rs")            
    n = n_ands()
##    if n <= 60000:
    if n <= 70000:
        abc('scl -m;drw;dr;lcorr;drw;dr')
        nn = max(1,n)
        m = int(min( 70000/nn, 16))
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
                print 'ANDs=%d,'%n_ands(),
                if n_ands() >= .98 * nands:
                     break
                continue
            if not check_size():
                print '\n'
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
        f = 100
        w = 16
        b = 16
        r = 500
        for k in range(9): #this controls how deep we go
            f = min(f*2, 3500)
            w = max(((w+1)/2)-1,1)
            abc('sim3 -F %d -W %d -N %d -R %d -B %d'%(f,w,seed,r,b))
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

def iter_tempor():
    na = n_ands()
    while True:
        abc('w save.aig')
        npi = n_pis()
        print npi
        abc('tempor -T 5 -F 8')
        print 'tempor = ',
        ps()
        x = trim()
##        if n_pis() > 2*npi:
##            abc('r save.aig')
##            return 'UNDECIDED'  
        abc('dr')
        print 'retime = ',
        ps()
        simplify()
        trim()
        print 'simplify -> trim = ',
        ps()
        if n_ands() > na:
            abc('r save.aig')
            ps()
            print 'No improvement'
            return 'UNDECIDED'  
        na = n_ands()
        ps()
        if n_latches() == 0:
            return RESULT[check_sat()]


def abstraction_refinement(latches_before,NBF,ratio=.75):
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
    t = 1000 #temporary
    t = abs_time
    initial_verify_time = last_verify_time = t
    reg_verify = True
    print 'Verify time set to %d'%last_verify_time
    while True: #cex based refinement
        generate_abs(1) #generate new gabs file from refined greg file
        set_globals()
        latches_after = n_latches()
        if small_abs(ratio):
            break
        t = last_verify_time
        yy = time.time()
        abc('w %s_beforerpm.aig'%f_name)
        rep_change = reparam() #new - must do reconcile after to make cex compatible
        abc('w %s_afterrpm.aig'%f_name)
##        if reg_verify:
        status = verify(J,t)
##        else:
##            status = pord_1_2(t)
###############
        if status == Sat_true:
            print 'Found true cex'
            reconcile(rep_change)
            return Sat_true
        if status == Unsat:
            return status
        if status == Sat:
            abc('write_status %s_after.status'%f_name)
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

def small_abs(ratio=.75):
    """ tests is the abstraction is too large"""
    return ((rel_cost_t([pis_before_abs,latches_before_abs, ands_before_abs])> -.1)
           or (n_latches() >= ratio*latches_before_abs))

##def abstract(if_bip=True):
##    global ratio
##    if if_bip:
##        return abstractb(True) #old method using abstraction refinement
##    else:
##        return abstractb(False) #not using bip and reachx

def abstractb():
    """ abstracts using N Een's method 3 - cex/proof based abstraction. The result is further refined using
    simulation, BMC or BDD reachability. abs_ratio is the the limit for accepting an abstraction"""
    global G_C, G_T, latches_before_abs, x_factor, last_verify_time, x, win_list, j_last, sims
    global latches_before_abs, ands_before_abs, pis_before_abs, abs_ratio
    if ifbip < 1:
        print 'using ,abs in old way'
    tt = time.time()
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
    J = slps+pdrs+bmcs+intrps
    J = modify_methods(J,1)
##    if n_latches() < 80:
##        J = J + [4]
    funcs = create_funcs(J,t) + funcs
    mtds = sublist(methods,J) + ['initial_abstract'] #important that initial_abstract goes last
    m,result = fork_last(funcs,mtds)
    if is_sat():
        print 'Found true counterexample in frame %d'%cex_frame()
        return Sat_true
    if is_unsat():
        return Unsat
##    set_max_bmc(NBF)
    NBF = bmc_depth()
    print 'Abstraction good to %d frames'%max_bmc
    #note when things are done in parallel, the &aig is not restored!!!
    abc('&r %s_greg.aig; &w initial_greg.aig; &abs_derive; &put; w initial_gabs.aig; w %s_gabs.aig'%(f_name,f_name))
    set_max_bmc(NBF)
    print 'Initial abstraction: ',
    ps()
    abc('w %s_init_abs.aig'%f_name)
    latches_after = n_latches()
##    if latches_after >= .90*latches_before_abs: #the following should match similar statement
##    if ((rel_cost_t([pis_before_abs, latches_before_abs, ands_before_abs])> -.1) or
##        (latches_after >= .75*latches_before_abs)):
    if small_abs(abs_ratio):
        abc('r %s_before_abs.aig'%f_name)
        print "Little reduction!"
        print 'Abstract time wasted = %0.2f'%(time.time()-tt)
        return Undecided_no_reduction
    sims_old = sims
    sims=sims[:1] #make it so that rarity sim is not used since it can't find a cex
    result = abstraction_refinement(latches_before_abs, NBF,abs_ratio)
    sims = sims_old
    if result <= Unsat:
        return result
##    if n_latches() >= .90*latches_before_abs:
##    if ((rel_cost_t([pis_before_abs, latches_before_abs, ands_before_abs])> -.1) or (latches_after >= .90*latches_before_abs)):
##    if rel_cost_t([pis_before_abs,latches_before_abs, ands_before_abs])> -.1:
    if small_abs(abs_ratio): #r is ratio of final to initial latches in absstraction. If greater then True
        abc('r %s_before_abs.aig'%f_name) #restore original file before abstract.
        print "Little reduction!  ",
        print 'Abstract time wasted = %0.2f'%(time.time()-tt)
        result = Undecided_no_reduction
        return result
    #new
    else:
        write_file('abs') #this is only written if it was not solved and some change happened.
    print 'Abstract time = %0.2f'%(time.time()-tt)
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

def initial_abstract(t=100):
    global G_C, G_T, latches_before_abs, x_factor, last_verify_time, x, win_list, max_bmc, ifbip
    set_globals()
    time = max(1,.1*G_T)
    time = min(time,t)
    abc('&get;,bmc -vt=%f'%time)
    set_max_bmc(bmc_depth())
    c = 2*G_C
    f = max(2*max_bmc,20)
    b = min(max(10,max_bmc),200)
    t1 = x_factor*max(1,2*G_T)
    t = max(t1,t)
    s = min(max(3,c/30000),10) # stability between 3 and 10
    cmd = '&get;,abs -bob=%d -stable=%d -timeout=%d -vt=%d -depth=%d'%(b,s,t,t,f)
    if ifbip == 2:
        cmd = '&get;,abs -bob=%d -stable=%d -timeout=%d -vt=%d -depth=%d -dwr=%s_vabs'%(b,s,t,t,f,f_name)
        print 'Using -dwr=%s_vabs'%f_name
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
        run_command('&abs_pba -v -C 0 -F %d'%F)
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

def ssm(options=''):
    """ Now this should be the same as super_prove(1) """
    y = time.time()
    result = prove_part_1() # simplify first
    if result == 'UNDECIDED':
        result = ss(options)
    print 'Total time taken on file %s by function ssm(%s) = %d sec.'%(initial_f_name,options,(time.time() - y))
    return result

def ssmg():
    return ssm('g')
def ssmf():
    return ssm('f')


def ss(options=''):
    """
    Alias for super_sec
    This is the preferred command if the problem (miter) is suspected to be a SEC problem
    """
    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time, sec_options
    sec_options = options
    print '\n*************Executing speculate************'
    y = time.time()
    abc('scl')
    result = speculate()
    # if result is 1 then it is a real SAT since we did not do anything before
    if result > 2: #save the result and read in with /rf so that files are initialized correctly
        if not '_spec' in f_name:
            write_file('spec') #make sure we do not overwrite original file
        read_file_quiet('%s'%f_name) #this resets f_name and initial_f_name etc.
        print '\n*************Executing super_prove ************'
        print 'New f_name = %s'%f_name
        result = sp()
        if result == 'SAT':
            result = 'UNDECIDED' #because speculation was done initially.
    elif result == 1:
        result = 'SAT'
    else:
        result = RESULT[result]
    print 'Total time taken on file %s by function ss(%s) = %d sec.'%(initial_f_name,options,(time.time() - y))
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

def pre_sec():
    """ put files to be compared into Old and New aigs. Simplify, but
    turn off reparameterization so that PIs in Old and New match after simplification.
    """
    global trim_allowed
##    trim_allowed = False
##    print 'trim allowed = ',trim_allowed
    print 'First file: ',
    read_file_quiet() #note - reads into & space and then does &put
    ps()
    prs(False)
    ps()
    abc('&w Old.aig')
    print 'Second file: ',
    read_file_quiet()
    ps()
    prs(False)
    ps()
    abc('&w New.aig')
        
def cec():
    print 'Type in the name of the aig file to be compared against'
    s = raw_input()
    s = remove_spaces(s)
    if not 'aig' in s:
        s = s+'.aig'
    run_command("&get;&cec -v %s"%s)

def sec(B_part,options):
    """
    Use this for AB filtering and not sup_sec
    Use pp_sec to make easy names for A and B, namely Old and New.
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
    f_name = A_name+'_'+B_name+'_miter' # reflect that we are working on a miter.
    abc('w %s.aig'%f_name)
    print 'Miter = ',
    ps()
    sec_options = options
    if sec_options == 'ab':
        sec_options = 'l' #it will be changed to 'ab' after &equiv
    sec_sw = True 
    result = speculate() 
    sec_options = ''
    sec_sw = False
    if result <= Unsat:
        result = RESULT[result]
    else:
        result = sp()
        if result == 'SAT':
            result = 'UNDECIDED'
    print 'Total time = %d'%(time.time() - yy)
    return result

def filter(opts):
    global A_name,B_name
##    print 'Filtering with options = %s'%opts
    """ This is for filter which effectively only recognizes options -f -g"""
    if (opts == '' or opts == 'l'): #if 'l' this is used only for initial &equiv2 to get initial equiv creation
        return
    if opts == 'ab':
        print A_name ,
        print B_name
        run_command('&ps')
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

def initial_speculate(sec_opt=''):
    global sec_sw, A_name, B_name, sec_options, po_map
    set_globals()
    if sec_options == '':
        sec_options = sec_opt
    t = max(1,.5*G_T)
    r = max(1,int(t))
    print 'Initial sec_options = %s'%sec_options
    if sec_options == 'l':
        cmd = "&get; &equiv3 -lv -F 20 -T %f -R %d"%(3*t,15*r)
    else:
        cmd = "&get; &equiv3 -v -F 20 -T %f -R %d"%(3*t,15*r)
    print cmd
    abc(cmd)
##    print 'AND space after &equiv3: ',
    run_command('&ps')
    if (sec_options == 'l'):
        if sec_sw:
            sec_options = 'ab'
        else:
            sec_options = 'f'
##    print 'A_name: ',
##    run_command('r %s.aig;ps'%A_name)
##    print 'B_name: ',
##    run_command('r %s.aig;ps'%B_name)
    filter(sec_options)
    abc('&w initial_gore.aig')
##    print 'Running &srm'
    if sec_sw:
        print 'miter: ',
        run_command('&ps')
        print 'A_name: ',
        run_command('r %s.aig;ps'%A_name)
        print 'B_name: ',
        run_command('r %s.aig;ps'%B_name)
        cmd = "&srm2 -%s %s.aig %s.aig; r gsrm.aig; w %s_gsrm.aig; &w %s_gore.aig"%(sec_options,A_name,B_name,f_name,f_name)
        abc(cmd)
        po_map = range(n_pos())
        return
    else:
##        abc('&r %s_gore.aig; &srm ; r gsrm.aig; w %s_gsrm.aig'%(f_name,f_name))
        cmd = "&srm; r gsrm.aig; w %s_gsrm.aig; &w %s_gore.aig"%(f_name,f_name)
##        print 'Running %s'%cmd
        abc(cmd)
        print 'done with &srm'
        po_map = range(n_pos())
        if sec_options == '':
            if n_pos() > 200:
                sec_options = 'g'
                print 'sec_options set to %s'%'g'
                abc('&r %s_gore.aig'%f_name)
                filter(sec_options)
                print 'Running &srm'
                cmd = "&srm; r gsrm.aig; ps;w %s_gsrm.aig;&ps; &w %s_gore.aig"%(f_name,f_name)
                print 'Running %s'%cmd
                abc(cmd)
                po_map = range(n_pos())
        

def test_against_original():
    '''tests whether we have a cex hitting an original PO'''
    abc('&w %s_save.aig'%f_name) #we preserve whatever was in the & space
    abc('&r %s_gore.aig'%f_name) #This is the original
    abc('testcex')
    PO = cex_po()
##    print 'test_against original gives PO = %d'%PO 
    abc('&r %s_save.aig'%f_name)
    if PO > -1:
##        print 'cex fails an original PO'
        return True
    else:
        abc('write_status %s_status.status'%f_name)
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
        abc('testcex -a -O %d'%(n_pos_before-n_pos_proved)) #test regular AIG space
    else:
        abc('testcex -O %d'%(n_pos_before-n_pos_proved)) #test the &-AIG
    PO = cex_po()
##    print 'cex_po = %d, n_pos_before = %d, n_pos_proved = %d'%(PO, n_pos_before, n_pos_proved)
    if PO >= (n_pos_before - n_pos_proved): #cex_po is not an original
##        print '1. cex PO = %d'%PO
        return PO # after original so take it.
    if n == 0:
        abc('testcex -a') #test regular
    else:
        abc('testcex')  #test &space
    PO = cex_po()
##    print '2. cex PO = %d'%PO
    cx = cex_get()
    if PO > -1:
        if test_against_original(): #this double checks that it is really an original PO
            cex_put(cx)
##            print 'test_against_original was valid'
            return PO
        else:
            print '1. PO not valid'
            return -1 #error
    if PO < 0 or PO >= (n_pos_before - n_pos_proved): # not a valid cex because already tested outside original.
        print '2. PO is not valid'
        PO = -1 #error
##    print '3. cex PO = %d'%PO
    return PO

def speculate():
    """Main speculative reduction routine. Finds candidate sequential equivalences and refines them by simulation, BMC, or reachability
    using any cex found. """    
    global G_C,G_T,n_pos_before, x_factor, n_latches_before, last_verify_time, trim_allowed, n_pos_before
    global t_init, j_last, sec_sw, A_name, B_name, sec_options, po_map, sweep_time, sims, cex_list, n_pos_proved,ifpord1
    global last_cx
    last_cx = 0
    ifpord1 = 1
    initial_po_size = last_srm_po_size = n_pos()
    initial_sizes = [n_pis(),n_pos(),n_latches(),n_ands()]
    if sec_sw:
        print 'A_name = %s, B_name = %s, f_name = %s, sec_options = %s'%(A_name, B_name, f_name, sec_options)
    elif n_ands()> 36000 and sec_options == '':
        sec_options = 'g'
        print 'sec_options set to "g"'
        
    def refine_with_cex():
        """Refines the gore file to reflect equivalences that go away because of cex"""
        global f_name
        abc('write_status %s_before.status'%f_name)
        abc('&r %s_gore.aig; &resim -m'%f_name)
        filter(sec_options)
        run_command('&w %s_gore.aig'%f_name)
        return
    
    def set_cex(lst):
        """ assumes only one in lst """
        for j in range(len(lst)):
            cx = lst[j]
            if cx == None:
                continue
            else:
                cex_put(cx)
                break

    def generate_srm():
        """generates a speculated reduced model (srm) from the gore file"""
        global f_name, po_map, sec_sw, A_name, B_name, sec_options, n_pos_proved
##        print 'Generating'
        pos = n_pos()
        ab = n_ands()
        abc('w %s_oldsrm.aig'%f_name) #save for later purposes
        if sec_sw:
            run_command('&r %s_gore.aig; &srm2 -%s %s.aig %s.aig; r gsrm.aig; w %s_gsrm.aig'%(f_name,sec_options,A_name,B_name,f_name))
        else:
            abc('&r %s_gore.aig; &srm ; r gsrm.aig; w %s_gsrm.aig'%(f_name,f_name)) #do we still need to write the gsrm file
##        ps()
        po_map = range(n_pos())
        ps()
        n_pos_proved = 0
        return 'OK'
    
    n_pos_before = n_pos()
    n_pos_proved = 0
    n_latches_before = n_latches()    
    set_globals()
##    t = max(1,.5*G_T)#irrelevant
##    r = max(1,int(t))
    t = 1000
    j_last = 0
    J = slps+sims+pdrs+bmcs+intrps
    J = modify_methods(J,1)
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
    sims = sims[:1] 
    J = slps+sims+pdrs+intrps+bmcs
    J = modify_methods(J)
##    print sublist(methods,J)
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
            last_srm_po_size = n_pos()
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
##         temporary       reg_verify = False #will cause pord_all to be used next
##                print 'pord_all turned on'
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
            if reg_verify:
                PO = set_cex_po(0) #testing the regular space
            else:
                abc('&r %s_gsrm.aig'%f_name)
                PO = set_cex_po(1) # test against the &space.
            print 'cex_PO is %d'%PO
            if (-1 < PO and PO < (n_pos_before-n_pos_proved)):
                print 'Found cex in original output = %d'%cex_po()
                print 'Refinement time = %s'%convert(time.time() - ref_time)
                return Sat_true
            if PO == -1:
                return Error
            refine_with_cex()    #change the number of equivalences
            continue
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
                    abc('&r %s_gsrm.aig'%f_name)
                    PO = set_cex_po(1) #testing the & space
                    if (-1 < PO and PO < (n_pos_before-n_pos_proved)):
                        print 'Found cex in original output = %d'%cex_po()
                        print 'Refinement time = %s'%convert(time.time() - ref_time)
                        return Sat_true
                    if PO == -1:
                        return Error
                    refine_with_cex()    #change the number of equivalences
                    continue
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
##    if last_srm_po_size == initial_po_size: #essentially nothing happened. last_srm_po_size will be # POs in last srm.
    if initial_sizes == [n_pis(),n_pos(),n_latches(),n_ands()]:
        return Undecided_no_reduction #thus do not write spec file
    else: #file was changed, so some speculation happened. If we find a cex later, need to know this.
        write_file('spec')
        return Undecided_reduction

def simple_sat(t=10000):
    y = time.time()
    J = [14,2,7,9,30,31,26,5] #5 is pre_simp
    funcs = create_funcs(J,t)
    mtds =sublist(methods,J)
    fork_last(funcs,mtds)
    result = get_status()
    if result > Unsat:
        write_file('smp')
        result = verify(slps+[14,2,3,7,9,30,31,26],t)
    print 'Time for simple_sat = %0.2f'%(time.time()-y)
    return RESULT[result]     

def simple(t=10000):
    y = time.time()
##    J = [14,1,2,7,9,23,30,5] #5 is pre_simp
##    funcs = create_funcs(J,t)
##    mtds =sublist(methods,J)
##    fork_last(funcs,mtds)
##    result = get_status()
##    if result > Unsat:
##        write_file('smp')
##        J = slps+bmcs+pdrs+intrps
##        J = modify_methods(J)
##        result = verify(J,t)
    J = slps+bmcs+pdrs+intrps
    J = modify_methods(J)
    result = verify(J,t)
##    print 'Time for simple = %0.2f'%(time.time()-y)
    return RESULT[result] 


def simple_bip(t=1000):
    y = time.time()
    J = [14,1,2,30,5] #5 is pre_simp
    funcs = create_funcs(J,t)
    mtds =sublist(methods,J)
    fork_last(funcs,mtds)
    result = get_status()
    if result > Unsat:
        write_file('smp')
        result = verify(slps+[14,1,2,30],t)
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
    if POa != POb:
        abc('&r %s_beforerpm.aig; &w tt_before.aig'%f_name)
        abc('&r %s_afterrpm.aig; &w tt_after.aig'%f_name)
        print 'cex PO afterrpm = %d not = cex PO beforerpm = %d'%(POa,POb)
    assert POa > -1, 'cex did not assert any output'

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
    J = modify_methods(J)
    mtds = sublist(methods,J)
    print mtds
    #print J,t
    F = create_funcs(J,t)
    (m,result) = fork_break(F,mtds,'US') #FORK here
    assert result == get_status(),'result: %d, status: %d'%(result,get_status())
    return result

def dsat_all(t=100,c=100000):
    print 't=%d,c=%d'%(t,c)
    N = n_pos()
    abc('&get')
    J = range(N)
    ttt = time.time()
    J.reverse()
    abc('w %s_temp.aig'%f_name)
    for j in J:
        tt = time.time()
        abc('r %s_temp.aig'%f_name)
        run_command('cone -O %d; dc2; dsat -C %d'%(j,c))
        if is_unsat():
            print 'Output %d is %s'%(j,RESULT[2]),
        else:
            print 'Output %d is %s'%(j,RESULT[3]),
        T = time.time() -tt
        print 'time = %0.2f'%T
        if time.time() - tt > t:
            break
    print 'Total time = %0.2f'%(time.time() - ttt)
            
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
        abc('&put')
        if n_pos() == 1:
            return Sat_true
        else:
            return Undecided_no_reduction #some POs could be unsat.
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

##def final_verify_recur(K):
##    """During prove we make backups as we go. These backups have increasing abstractions done, which can cause
##    non-verification by allowing false counterexamples. If an abstraction fails with a cex, we can back up to
##    the previous design before the last abstraction and try to proceed from there. K is the backup number we
##    start with and this decreases as the backups fails. For each backup, we just try final_verify.
##    If ever we back up to 0, which is the backup just after simplify, we then try speculate on this. This often works
##    well if the problem is a SEC problem where there are a lot of equivalences across the two designs."""
##    global last_verify_time
##    #print 'Proving final_verify_recur(%d)'%K
##    last_verify_time = 2*last_verify_time
##    print 'Verify time increased to %d'%last_verify_time
##    for j in range(K):
##        i = K-(j+1)
##        abc('r %s_backup_%d.aig'%(initial_f_name,i))
##        if ((i == 0) or (i ==2)): #don't try final verify on original last one
##            status = prob_status()
##            break
##        print '\nVerifying backup number %d:'%i,
##        #abc('r %s_backup_%d.aig'%(initial_f_name,i))
##        ps()
##        #J = [18,0,1,2,3,7,14]
##        J = slps+sims+intrps+bmcs+pdrs
##        t = last_verify_time
##        status = verify(J,t)
##        if status >= Unsat:
##            return status
##        if  i > 0:
##            print 'SAT returned, Running less abstract backup'
##            continue
##        break
##    if ((i == 0) and (status > Unsat) and (n_ands() > 0)):
##        print '\n***Running speculate on initial backup number %d:'%i,
##        abc('r %s_backup_%d.aig'%(initial_f_name,i))
##        ps()
##        if n_ands() < 20000:
####            pre_simp()
##            status = speculate()
##            if ((status <= Unsat) or (status == Error)):
##                return status
##        #J = [18,0,1,2,3,7,14]
##        J = slps+sims+intrps+bmcs+pdrs
##        t = 2*last_verify_time
##        print 'Verify time increased to %d'%last_verify_time
##        status = verify(J,t)
##    if status == Unsat:
##        return status
##    else:
##        return Undecided_reduction
        
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

def prs(x=True):
    global trim_allowed
    """ If x is set to False, no reparameterization will be done in pre_simp"""
    trim_allowed = x
    print 'trim_allowed = ',trim_allowed
    y = time.clock()
    pre_simp()
    print 'Time = %s'%convert(time.clock() - y)
    write_file('smp')

def pre_simp():
    """This uses a set of simplification algorithms which preprocesses a design.
    Includes forward retiming, quick simp, signal correspondence with constraints, trimming away
    PIs, and strong simplify"""
    global trim_allowed, temp_dec
    tt = time.time()
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
##    if n_ands()<70000:
##        abs('scorr -C 5000')
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
        if not '_smp' in f_name: #try this only once on a design
            try_temps(15)
            if n_latches() == 0:
                return check_sat()
            try_phase()
            if n_latches() == 0:
                return check_sat()
        if ((n_ands() > 0) or (n_latches()>0)):
            trim()
    status = process_status(status)
    print 'Simplification time = %0.2f'%(time.time()-tt)
    return status

def pre_simp2():
    """This uses a set of simplification algorithms which preprocesses a design.
    Includes forward retiming, quick simp, signal correspondence with constraints, trimming away
    PIs, and strong simplify"""
    global trim_allowed, temp_dec
    tt = time.time()
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
    if n_ands()<70000:
        abc('scorr -C 5000')
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
        if not '_smp' in f_name: #try this only once on a design
            try_temps(15)
            if n_latches() == 0:
                return check_sat()
            try_phase()
            if n_latches() == 0:
                return check_sat()
        if ((n_ands() > 0) or (n_latches()>0)):
            trim()
    status = process_status(status)
    print 'Simplification time = %0.2f'%(time.time()-tt)
    return status


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
##    F = F + [eval('(pyabc_split.defer(abc)("tempor -s; trm; scr; trm; tempor; trm; scr; trm"))')]
    F = F + [eval('(pyabc_split.defer(abc)("tempor -s; &get; &trim -o; &put; scr; &get; &trim -o; &put; tempor; &get; &trim -o; &put; scr; &get; &trim -o; &put"))')]    
    for i,res in pyabc_split.abc_split_all(F):
        break
    cost = rel_cost(best)
    print 'cost = %0.2f'%cost
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
        

def rel_cost_t(J):
    """ weighted relative costs versus previous stats."""
    if (n_latches() == 0 and J[1]>0):
        return -10
    nli = J[0]+J[1]
    na = J[2]
    if ((nli == 0) or (na == 0)):
        return 100
    nri = n_real_inputs()
    #ri = (float(nri)-float(ni))/float(ni)
    rli = (float(n_latches()+nri)-float(nli))/float(nli)
    ra = (float(n_ands())-float(na))/float(na)
    cost = 10*rli + .5*ra
    return cost    

def rel_cost(J):
    """ weighted relative costs versus previous stats."""
    global f_name
    if (n_latches() == 0 and J[1]>0):
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
    cost = 1*ri + 5*rl + .2*ra
##    print 'Relative cost = %0.2f'%cost
    return cost

def best_fwrd_min(J):
    global f_name, methods
    mtds = sublist(methods,J)
    F = create_funcs(J,0)
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
    if na < 60000:
        abc('scl -m;lcorr;drw')
    else:
        abc('&get;&scl;&lcorr;&put;drw')
    print 'Using quick simplification',
    status = process_status(get_status())
    if status <= Unsat:
        result = RESULT[status]
    else:
        ps()
##        write_file('smp')
####            K_backup = K = K+1
        result = 'UNDECIDED'
    return result

def scorr_constr():
    """Extracts implicit constraints and uses them in signal correspondence
    Constraints that are found are folded back when done"""
    na = max(1,n_ands())
    n_pos_before = n_pos()
    if ((na > 40000) or n_pos()>1):
        return Undecided_no_reduction
    abc('w %s_savetemp.aig'%f_name)
    na = max(1,n_ands())
##    f = 1
    f = 18000/na  #**** THIS can create a bug 10/15/11
    f = min(f,4)
    f = max(1,f)
    if n_ands() > 18000:
        cmd = 'unfold -s -F 2'
    else:
        cmd = 'unfold -F %d -C 5000'%f
    abc(cmd)
    if n_pos() == n_pos_before:
        print 'No constraints found'
        return Undecided_no_reduction
    if (n_ands() > na): #no constraints found
        abc('r %s_savetemp.aig'%f_name)
        return Undecided_no_reduction
    na = max(1,n_ands())
    f = 1
    print 'Number of constraints = %d'%((n_pos() - n_pos_before))
    abc('scorr -c -F %d'%f)
    abc('fold')
    trim()
    print 'Constrained simplification: ',
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


def prove(a):
    """Proves all the outputs together. If ever an abstraction
        was done then if SAT is returned,
        we make RESULT return "undecided".
        is a == 0 do smp and abs first
        If a == 1 do smp and spec first 
        if a == 2 do quick simplification instead of full simplification, then abs first, spec second"""
    global x_factor,xfi,f_name, last_verify_time,K_backup, t_init, sec_options, spec_found_cex
    spec_first = False
    max_bmc = -1
    abs_found_cex_after_spec = spec_found_cex_after_abs = False
    if not '_smp' in f_name: #if already simplified, then don't do again
        if a == 2 : #do quick simplification
            result = quick_simp() #does not write 'smp' file
##            print result
        else :
            result = prove_part_1() #do full simplification here
        if ((result == 'SAT') or (result == 'UNSAT')):
            return result
    if a == 1:
        spec_first = True
    t_init = 2
    abs_found_cex_before_spec = spec_found_cex_before_abs = False
##    First phase
    if spec_first:
        result = prove_part_3() #speculation done here first
    else:
        result = prove_part_2() #abstraction done here first
    if ((result == 'SAT') or (result == 'UNSAT')):
        return result
##    Second phase
    if spec_first: #did spec already in first phase
        t_init = 2
        result = prove_part_2() #abstraction done here second
        if result == 'SAT':
            abs_found_cex_after_spec = True
    else:
        result = prove_part_3()  #speculation done here second
        if result == 'SAT':
            spec_found_cex_after_abs = True
    if result == 'UNSAT': 
        return result
    status = get_status()
    if result == 'ERROR':
        status = Error
    if ('_abs' in f_name and spec_found_cex_after_abs): #spec file should not have been written in speculate
        f_name = revert(f_name,1) #it should be as if we never did abstraction.
        print 'f_name = %s'%f_name
        abc('r %s.aig'%f_name) #restore previous
        t_init = 2
        if not '_rev' in f_name:
            print 'proving speculation first'
            write_file('rev') #maybe can get by with just changing f_name
            print 'f_name = %s'%f_name
            result = prove(1) #1 here means do smp and then spec 
            if ((result == 'SAT') or (result == 'UNSAT')):
                return result
    elif ('_spec' in f_name and abs_found_cex_after_spec): #abs file should not have been written in abstract
        f_name = revert(f_name,1) #it should be as if we never did speculation.
        abc('r %s.aig'%f_name) #restore previous 
        t_init = 2
        if not '_rev' in f_name:
            print 'proving abstraction first'
            write_file('rev') #maybe can get by with just changing f_name
            result = prove(0)
            if ((result == 'SAT') or (result == 'UNSAT')):
                return result
    else:
        return 'UNDECIDED'

def prove_part_1():
    global x_factor,xfi,f_name, last_verify_time,K_backup
    print 'Initial: ',
    ps()
    x_factor = xfi
    print '\n***Running pre_simp'
    set_globals()
    if n_latches() > 0:
        status = run_par_simplify()
    else:
        status = check_sat()
    if ((status <= Unsat) or (n_latches() == 0)):
        return RESULT[status]
    trim()
    write_file('smp') #need to check that this was not written in pre_simp
    set_globals()
    return RESULT[status]

def run_par_simplify():
    set_globals()
    t = 1000
    funcs = [eval('(pyabc_split.defer(pre_simp)())')]
    J = pdrs+bmcs+intrps
    J = modify_methods(J,1)
    funcs = create_funcs(J,t)+ funcs #important that pre_simp goes last
    mtds =sublist(methods,J) + ['pre_simp']
    fork_last(funcs,mtds)
    status = get_status()
    return status
    
def prove_part_2(ratio=.75):
    """does the abstraction part of prove"""
    global x_factor,xfi,f_name, last_verify_time,K_backup, trim_allowed,ifbip
    print'\n***Running abstract'
##    print 'ifbip = %d'%ifbip
    status = abstract(ifbip) #ABSTRACTION done here
    status = process_status(status)
    print 'abstract done, status is %d'%status
    result = RESULT[status]
    if status < Unsat:
        print 'CEX in frame %d'%cex_frame()
        return result #if we found a cex we do not want to trim.
    trim() 
    return result
    
def prove_part_3():
    """does the speculation part of prove"""
    global x_factor,xfi,f_name, last_verify_time,init_initial_f_name
    global max_bmc, sec_options
    if ((n_ands() > 36000) and sec_options == ''):
        sec_options = 'g'
        print 'sec_options set to "g"'
    print '\n***Running speculate'
    status = speculate() #SPECULATION done here
    status = process_status(status)
    print 'speculate done, status is %d'%status
    result = RESULT[status]
    if status < Unsat:
        print 'CEX in frame %d'%cex_frame()
        return result
    trim() #if cex is found we doo not want to trim.
    return result

def prove_all(dir,t):
    """Prove all aig files in this directory using super_prove and record the results in results.txt
    Not called from any subroutine
    """
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
##    print result
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

####def find_cex_par(tt):
####    """prove n outputs at once and quit at first cex. Otherwise if no cex found return aig
####    with the unproved outputs"""
####    global trim_allowed,last_winner, last_cex, n_pos_before, t_init, j_last, sweep_time
####    b_time = time.time() #Wall clock time
####    n = n_pos()
####    l=remove_const_pos()
####    N = n_pos()
####    full_time = all_proc = False
####    print 'Number of POs: %d => %d'%(n,N)
####    if N == 0:
####        return Unsat
######    inc = 5  #******* increment for grouping for sweep set here *************
######    inc = min(12,max(inc, int(.1*N)))
####    inc = 1+N/100
######    if N <1.5*inc: # if near the increment for grouping try to get it below.
######        prove_all_ind()
######        N = n_pos()
####    if inc == 1:
####        prove_all_ind()
####        N = n_pos()
####    T = int(tt) #this is the total time to be taken in final verification run before quitting speculation
######    if inc == 10:
######        t_init = 10
######    t = max(t_init/2,T/20)
######    if N <= inc:
######        t = T
######    print "inc = %d, Sweep time = %s, j_group = %d"%(inc,convert(t),j_last)
####    t = sweep_time/2 #start sweeping at last time where cex was found.
######    it used to be t = 1 here but it did not make sense although seemed to work.
######    inc = 2
####    while True: #poor man's concurrency
####        N = n_pos()
####        if N == 0:
####            return Unsat
####        #sweep_time controls so that when sweep starts after a cex, it starts at the last sweep time
####        t = max(2,2*t) #double sweep time
####        if t > .75*T:
####            t = T
####            full_time = True
####        if ((N <= inc) or (N < 13)):
####            t = sweep_time = T
####            full_time = True
####            inc = 1
######            sweep_time = 2*sweep_time
####        if not t == T:
####            t= sweep_time = max(t,sweep_time)
######            t = sweep_time
######new heuristic
####        if (all_proc and sweep_time > 8): #stop poor man's concurrency and jump to full time.
####            t = sweep_time = T
####            full_time - True #this might be used to stop speculation when t = T and the last sweep
######                           found no cex and we do not prove Unsat on an output
####        abc('w %s__ysavetemp.aig'%f_name)
####        ps()
####        if N < 50:
####            inc = 1
####        print "inc = %d, Sweep time = %s, j_last = %d"%(inc,convert(t),j_last)
####        F = []
######        G = []
####        #make new lambda functions since after the last pass some of the functions may have been proved and eliminated.
####        for i in range(N):
####            F = F + [eval('(pyabc_split.defer(verify_only)(%d,%s))'%(i,convert(T)))] #make time large and let sleep timer control timeouts
######            G = G + [range(i,i+1)]
####        ######
####        result = []
####        outcome = ''
####        N = len(F)
####        rng = range(1+(N-1)/inc)
####        rng = rng[j_last:]+rng[:j_last] #pick up in range where last found cex.
######        print 'rng = ',
######        print rng
####        k = -1
####        bb_time = time.time()
####        for j in rng:
####            k = k+1 #keeps track of how many groups we have processed.
####            j_last = j
####            J = j*inc
####            JJ = J+inc
####            JJ = min(N,JJ)
####            if J == JJ-1:
####                print 'Function = %d '%J,
####            else:
####                print 'Functions = [%d,%d]'%(J,JJ-1)
####            Fj = create_funcs([18],t+1) #create timer function as i = 0 Here is the timer
####            Fj = Fj + F[J:JJ]
####            count = 0
####            fj_time = time.time()
####            abc('r %s__ysavetemp.aig'%f_name) #important need to restore aig here so the F refers to right thing when doing verify_only.
######                                             # because verify_only changes the aig.
######            ps()
####            for i,res in pyabc_split.abc_split_all(Fj):
####                count = count+1
####                Ji = J+i-1 #gives output number
####                if ((res == 0) or (res == 1)):
####                    abc('read_status %d.status'%Ji)
####                    res = get_status()
####                    outcome = 'CEX: Frame = %d, PO = %d, Time = %s'%(cex_frame(),Ji,convert((time.time() - fj_time)))
####                    break
####                if i == 0: #sleep timer expired
####                    outcome = '*** Time expired in %s sec. Next group = %d to %d ***'%(convert(time.time() - fj_time),JJ,min(N,JJ+inc))
####                    break
####                elif res == None: #this should not happen
####                    print res
####                    print Ji,RESULT[res],
####                else: # output Ji was proved
####                    result = result + [[Ji,res]]
####                    if count >= inc:
####                        outcome = '--- all group processed without cex ---'
####                        all_proc = True
####                        break
####                    continue #this can only happen if inc > 1
####            # end of for i loop
####            if ((res < Unsat) and (not res == None)): 
####                break
####            else:
####                continue # continue j loop
####        #end of for j loop
####        if k < len(rng):      
####            t_init = t/2 #next time start with this time.
####        else:
####            j_last = j_last+1 #this was last j and we did not find cex, so start at next group
####        print outcome + ' => ' ,
####        if ((res < Unsat) and (not res == None)):
####            t_init = t/2
####            abc('read_status %d.status'%Ji) #make sure we got the right status file.
####            #actually if doing abstraction we could remove proved outputs now, but we do not. -**inefficiency**
####            return res
####        else: #This implies that no outputs were disproved. Thus can remove proved outputs.
####            abc('r %s__ysavetemp.aig'%f_name) #restore original aig
####            if not result == []:
####                res = []
####                for j in range(len(result)):
####                    k = result[j]
####                    if k[1] == 2:
####                        res = res + [k[0]]
######                print res
######                result = mapp(res,G)
####                result = res
######                print result
####                remove(result) #remove the outputs that were proved UNSAT.
####                #This is OK for both abstract and speculate
####                print 'Number of POs reduced to %d'%n_pos()
####                if n_pos() == 0:
####                    return Unsat
####            if t>=T:
####                return Undecided
####            else:
####                continue
####    return Undecided

####def remap_pos():
####    """ maintains a map of current outputs to original outputs"""
####    global po_map
####    k = j = 0
####    new = []
####    assert n_pos() == len(po_map), 'length of po_map, %d, and current # POs, %d, don"t agree'%(len(po_map),n_pos())
####    for j in range(len(po_map)):
####        N = n_pos()
####        abc('removepo -N %d'%k) # this removes the output if it is 0 driven
####        if n_pos() == N:
####            new = new + [po_map[j]]
####            k = k+1
####    if len(new) < len(po_map):
######        print 'New map = ',
######        print new
####        po_map = new

####def prove_mapped():
####    """
####    assumes that srm is in workspace and takes the unsolved outputs and proves
####    them by using proved outputs as constraints.
####    """
####    global po_map
######    print po_map
####    po_map.sort() #make sure mapped outputs are in order
####    for j in po_map: #put unsolved outputs first
####        run_command('swappos -N %d'%j)
####        print j
####    N = n_pos()
####    assert N > len(po_map), 'n_pos = %d, len(po_map) = %d'%(N, len(po_map))
####    run_command('constr -N %d'%(N-len(po_map))) #make the other outputs constraints
####    run_command('fold') #fold constraints into remaining outputs.
####    ps()
####    prove_all_mtds(100)
    
####def mapp(R,G):
####    result = []
####    for j in range(len(R)):
####        result = result + G[R[j]]
####    return result
        
#_______________________________________        

    
####def prove_g_pos_split():
####    """like prove_g_pos but quits when any output is undecided"""
####    global f_name, max_bmc,x_factor,x
####    x = time.clock()
####    #input_x_factor()
####    init_f_name = f_name
####    print 'Beginning prove_g_pos_split'
####    prove_all_ind()
####    print 'Number of outputs reduced to %d by fast induction with constraints'%n_pos()
####    reparam()
######    try_rpm()
####    print '********** Proving each output separately ************'  
####    f_name = init_f_name
####    abc('w %s_osavetemp.aig'%f_name)
####    n = n_pos()
####    print 'Number of outputs = %d'%n
####    pos_proved = []
####    J = 0
####    jnext = n-1
####    while jnext >= 0:
####        max_bmc = -1
####        f_name = init_f_name
####        abc('r %s_osavetemp.aig'%f_name)
####        jnext_old = jnext
####        extract(jnext,jnext)
####        jnext = jnext -1
####        print '\nProving output %d'%(jnext_old)
####        f_name = f_name + '_%d'%jnext_old
####        result = prove_1()
####        if result == 'UNSAT':
####            if jnext_old > jnext+1:
####                print '********  PROVED OUTPUTS [%d-%d]  ******** '%(jnext+1,jnext_old)
####            else:
####                print '********  PROVED OUTPUT %d  ******** '%(jnext_old)
####            pos_proved = pos_proved + range(jnext +1,jnext_old+1)
####            continue
####        if result == 'SAT':
####            print 'One of output in (%d to %d) is SAT'%(jnext + 1,jnext_old)
####            return result
####        else:
####            print '********  UNDECIDED on OUTPUTS %d thru %d  ******** '%(jnext+1,jnext_old)
####            print 'Eliminating %d proved outputs'%(len(pos_proved))
####            # remove outputs proved and return
####            f_name = init_f_name
####            abc('r %s_osavetemp.aig'%f_name)
####            remove(pos_proved)
####            trim()
####            write_file('group')            
####            return 'UNDECIDED'
####    f_name = init_f_name
####    abc('r %s_osavetemp.aig'%f_name)
####    if not len(pos_proved) == n:
####        print 'Eliminating %d proved outputs'%(len(pos_proved))
####        remove(pos_proved)
####        trim()
####        write_file('group')
####        result = 'UNDECIDED'
####    else:
####        print 'Proved all outputs. The problem is proved UNSAT'
####        result = 'UNSAT'
####    print 'Total time = %f sec.'%(time.clock() - x)
####    return result

####def group(a,n):
####    """Groups together outputs beginning at output n and any contiguous preceeding output
####    that does not increase the latch support by a or more"""
####    global f_name, max_bmc
####    nlt = n_latches()
####    extract(n,n)
####    nli = n_latches()
####    if n == 0:
####        return n-1
####    for J in range(1,n+1):
####        abc('r %s_osavetemp.aig'%f_name)
####        j = n-J
####        #print 'Running %d to %d'%(j,n)
####        extract(j,n)
####        #print 'n_latches = %d'%n_latches()
####        #if n_latches() >= nli + (nlt - nli)/2:
####        if n_latches() == nli:
####            continue
####        if n_latches() > nli+a:
####            break
####    abc('r %s_osavetemp.aig'%f_name)
######    if j == 1:
######        j = j-1
####    print 'extracting [%d-%d]'%(j,n)
####    extract(j,n)
####    ps()
####    return j-1
        
def extract(n1,n2):
    """Extracts outputs n1 through n2"""
    no = n_pos()
    if n2 > no:
        return 'range exceeds number of POs'
    abc('cone -s -O %d -R %d'%(n1, 1+n2-n1))

def remove_intrps(J):
    global n_proc,ifbip
    npr = n_proc
    if 18 in J:
        npr = npr+1
    if len(J) <= npr:
        return J
    JJ = []
    alli = [23,1,22] # if_no_bip, then this might need to be changed
    l = len(J)-npr
    alli = alli[:l]
    for i in J:
        if i in alli:
            continue
        else:
            JJ = JJ +[i]
    return JJ
        
def remove(lst):
    """Removes outputs in list"""
    global po_map
    n_before = n_pos()
    zero(lst)
    l=remove_const_pos()
    print 'n_before = %d, n_list = %d, n_after = %d'%(n_before, len(lst), n_pos())

def check_pos():
    """ checks if any POs are 0, and removes them with a warning"""
    N = n_pos()
    l=remove_const_pos()
    if not N == n_pos():
        print 'WARNING: some POs are 0 and are rremoved'
        print '%d POs removed'%(N - n_pos())

def zero(list):
    """Zeros out POs in list"""
    for j in list:
        run_command('zeropo -N %d'%j)

def mark_const_pos(ll=[]):
    """ creates an indicator of which PO are const-0 and which are const-1
        does not change number of POs
    """
    L = range(n_pos())
    L.reverse()
    if ll == []:
        ll = [-1]*n_pos()
    ind = ll
    abc('&get') #save original
    for j in L:
        n_before = n_pos()
        abc('removepo -N %d'%j) #removes const-0 output
        if n_pos() < n_before:
            ind[j]=0
##    print sumsize(ind)
##    ps()
    abc('&put')
    for j in L:
        n_before = n_pos()
        abc('removepo -z -N %d'%j) # -z removes const-1 output
        if n_pos() < n_before:
            ind[j]=1
##    ps()
    abc('&put') #put back original
##    remove_const_pos()
    print sumsize(ind)
    return ind

def remove_const_pos():
    global po_map
    """removes the 0 pos, but no pis because we might get cexs and need the correct number of pis
    Should keep tract of if original POs are 0 and are removed.
    Can this happen outside of prove_all_ind or
    pord_all which can set proved outputs to 0???
    WARNING: This can remove constant 1 nodes too???
    """
    run_command('&get; &trim -i; &put; addpi') #adds a pi only if there are none
    po_map = range(n_pos())

def psp():
    quick_simp()
    result = run_parallel([6,21],500,'US') #runs 'run_parallel' and sp() in parallel.
##                                          run_parallel uses JP and TERM to terminate.
    return result

def sp():
    global initial_f_name
    """Alias for super_prove"""
    print 'Executing super_prove'
    result = super_prove(0)
    print '%s is done'%initial_f_name
    return result


def sumsize(L):
    d = count_less(L,0)
    u = count_less(L,1)-d
    s = count_less(L,2) - (d+u)
    return 'SAT = %d, UNSAT = %d, UNDECIDED = %d'%(s,u,d)

def unmap(L,L2,map):
    mx = max(list(map))
    assert mx <= len(L2),'max of map = %d, length of L2 = %d'%(mx,len(L))
    for j in range(len(map)):
        L[j] = L2[map[j]] #expand results of L2 into L
    return L 

def create_map(L,N):
    map = [-1]*N
    for j in range(len(L)):
        lj = L[j]
        for k in range(len(lj)):
            map[lj[k]] = j
    return map

def mp(op='sp'):
    L = multi_prove(op,900)
    return sumsize(L)

def multi_prove(op='sp',tt=900):
    """two phase prove process for multiple output functions"""
    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time
    global f_name_save,name_save
    x_init = time.time()
    N = n_pos()
    L = [-1]*N
    print 'Mapping for isomorphism: '
    iso() #reduces number of POs
    map = create_map(iso_eq_classes(),N) #creates map into original
    N = n_pos()
    r = pre_simp() #pre_simp
    write_file('smp')
    NP = n_pos()/N #if NP > 1 then NP unrollings were done.
    if n_pos() > N:
        assert NP>=2, 'NP not 2, n_pos = %d, N = %d, NP = %d'%(n_pos(),N,NP)
    print 'pre_simp done. NP = %d\n\n'%NP
    #WARNING: if phase abstraction done, then number of POs changed.
    if r == Unsat:
        L = [0]*N #all outputs are UNSAT
        print sumsize(L)
        return L
    f_name_save = f_name
    name_save = '%s_initial_save.aig'%f_name
    abc('w %s'%name_save)
    L1 = [-1]*n_pos() # L1 has length after pre_simp
##    L1= mark_const_pos(L1) #puts const values in L1 
##    print sumsize(L1)
    #########do second iso here
    N = n_pos()
    print 'Mapping for isomorphism: '
    iso() #second iso - changes number of POs
    map2 = create_map(iso_eq_classes(),N) #creates map into previous
    L2 = [-1]*n_pos()
    L2 = mark_const_pos(L2) #populates L2 with constants
    print sumsize(L2)
    #########second iso done
    abc('r %s'%name_save)
    L2 = mprove(L2,op,10) #populates L2 with results
    print sumsize(L2)
    time_left = tt - (time.time()-x_init)
    print '\n\n\n*********time left = %d ********\n\n\n'%time_left
    N = count_less(L2,0)
    if N > 0:
        t = max(100,time_left/N)
        L2 = mprove(L2,op,t) #populates L2 with more results
    S = sumsize(L2)
    T = '%.2f'%(time.time() - x_init)
    print '%s in time = %s'%(S,T)
    ########undo second iso
    L1 = unmap(L1,L2,map2)
    print 'unmapping for iso: ',
    print sumsize(L1)
    #############
    if NP > 1: #an unrolling was done
        L1 = check_L(NP,L1) #map into reduced size before unrolling was done.
        print 'unmapping for unrolling.',
        print sumsize(L1)
    L = unmap(L,L1,map)
    print 'unmapping for iso',
    print sumsize(L)
    return L

def check_L(NP,L):
    """This happens when an unrolling creates additional POs
    We want to check that L[j] = L[j+N] etc to make sure the PO results agree
    in all phases, i.e. sat, unsat, or undecided
    """
    N = len(L)/NP #original number of POs
    for j in range(N):
        for k in range(NP)[1:]: #k = 1,2,...,NP-1
            if (L[j] == 1):
                break
            elif L[j+k*N] == 1:
                L[j] = 1
                break
            elif L[j] == -1:
                continue #we have to continue to look for a 1
            elif L[j] == 0:
                if L[j+k*N] == -1:
                    L[j] = -1
                    break
            continue #have to make sure that all phases are 0
    return L[:N]


def mprove(L,op='sp',tt=1000):
    """ 0 = unsat, 1 = sat, -1 = undecided"""
    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time
    global f_name_save,name_save,temp_dec
    N = len(L)
    t = tt #controls the amount of time spent on each cone
    funcs = [eval('(pyabc_split.defer(%s)())'%op)]
    funcs = create_funcs(slps,t)+funcs
    mtds =sublist(methods,slps) + [op]
    res = L
    for j in range(N):
        if L[j] > -1:
            continue #already solved
        abc('r %s'%name_save) #restore original function
        x = time.time()
        name = '%s_cone_%d'%(f_name_save,j)
        abc('cone -s -O %d'%j)
        abc('w %s.aig'%name)
        print '\n********************************************'
        read_file_quiet(name)
        print '________%s(%s)__________'%(op,name)
        temp_dec = False
        fork_last(funcs,mtds)
        T = '%.2f'%(time.time() - x)
        out = get_status()
        if out == Unsat:
            res[j] = 0
        if out < Unsat:
            res[j] = 1
        print '\n%s: %s in time = %s'%(name,RESULT[out],T)
    return res

def sp1(options = ''):
    global sec_options
    sec_options = options
    return super_prove(1)

def super_prove(n=0):
    """Main proof technique now. Does original prove and if after speculation there are multiple output left
    if will try to prove each output separately, in reverse order. It will quit at the first output that fails
    to be proved, or any output that is proved SAT
    n controls call to prove(n)
    is n == 0 do smp and abs first, then spec
    if n == 1 do smp and spec first then abs
    if n == 2 just do quick simplification instead of full simplification, then abs first, spec second
    """
    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time, f_name
    init_initial_f_name = initial_f_name
    if x_factor > 1:
        print 'x_factor = %f'%x_factor
        input_x_factor()
    max_bmc = -1
    x = time.time()
##    if n == 2:
##        result = prove(2)
##    else:
##        result = prove(0)
    result = prove(n)
    if ((result == 'SAT') or (result == 'UNSAT')):
        print '%s: total clock time taken by super_prove = %f sec.'%(result,(time.time() - x))
        return result
    elif ((result == 'UNDECIDED') and (n_latches() == 0)):
        return result
    print '%s: total clock time taken by super_prove so far = %f sec.'%(result,(time.time() - x))
    y = time.time()
    if n == 2:
        print 'Entering BMC_VER()'
        result = BMC_VER() #n=2 is only called from sp2, a super_prove run in parallel.
        if ((result == 'SAT') and (('_abs' in f_name)or '_spec' in f_name)): #this is because we have done an abstraction and cex is invalid.
            result = 'UNDECIDED'
    else:
        print 'Entering BMC_VER_result'
        result = BMC_VER_result() #this does backing up if cex is found
    print 'Total clock time taken by last gasp verification = %f sec.'%(time.time() - y)
    print 'Total clock time for %s = %f sec.'%(init_initial_f_name,(time.time() - x))
    return result

def reachm(t):
    x = time.clock()
    abc('&get;&reachm -vcs -T %d'%t)
    print 'reachm done in time = %f'%(time.clock() - x)
    return get_status()

def reachp(t):
    x = time.clock()
    abc('&get;&reachp -rv -T %d'%t)
    print 'reachm2 done in time = %f'%(time.clock() - x)
    return get_status()

def scorr():
    run_command('scorr')
    ps()

def select_undecided(L):
    res = []
    for j in range(len(L)):
        l = L[j]
        if l[1] == 'UNDECIDED':
            res = res + [l[0]]
    return res
        
####def execute(L,t):
####    """
####    run the files in the list L using ss, sp, ssm each for max time = t
####    """
####    funcs1 = [eval('(pyabc_split.defer(ss)())')]
####    funcs1 = create_funcs(slps,t)+funcs1
####    mtds1 =sublist(methods,slps) + ['ss']
####    funcs2 = [eval('(pyabc_split.defer(sp)())')]
####    funcs2 = create_funcs(slps,t)+funcs2
####    mtds2 =sublist(methods,slps) + ['sp']
####    funcs3 = [eval('(pyabc_split.defer(ssm)())')]
####    funcs3 = create_funcs(slps,t)+funcs3
####    mtds3 =sublist(methods,slps) + ['ssm']
####    for j in range(len(L)):
####        name = L[j]
####        print '\n\n\n\n________ss__________'
####        read_file_quiet(name)
####        print '****ss****'
####        fork_last(funcs1,mtds1)
####        print '***Done with ss on %s\n'%name
####        print '\n\n******ssm************'
####        read_file_quiet(name)
####        print '****ssm****'
####        fork_last(funcs3,mtds3)
####        print '***Done with ssm on %s \n'%name

def execute_op(op,L,t):
    """
    run the files in the list L using operation "op", each for max time = t
    """
    funcs = [eval('(pyabc_split.defer(%s)())'%op)]
    funcs = create_funcs(slps,t)+funcs
    mtds =sublist(methods,slps) + [op]
    res = []
    for j in range(len(L)):
        x = time.time()
        name = L[j]
        print '\n\n\n\n________%s__________'%op
        read_file_quiet(name)
        m,result = fork_last(funcs,mtds)
        if result == Undecided:
            result = RESULT[result]
        T = '%.2f'%(time.time() - x)
        new_res = [name,result,T]
        res = res + [new_res]
        print '\n%s'%new_res
    return res

def x_ops(ops,L,t):
    """ execute each op in the set of ops on each file in the set of files of L, each for time t"""
    result = []
    for j in range(len(ops)):
        op = ops[j]
        result.append('Result of %s'%op)
        result.append(execute_op(op,L,t))
    return result

def iso(n=0):
    if n == 0:
        run_command('&get;&iso;&put')
    else:
        run_command('&get;&iso;iso;&put')

def check_iso(N):
    ans = get_large_po()
    if ans == -1:
        return 'no output found'
    n_iso = count_iso(N)
    return n_iso

def count_iso(N):
    abc('&get;write_aiger -u file1.aig') #put this cone in & space and write file1
##    print 'PO %d is used'%i
    n_iso = 0 #start count
    for i in range(N):
        abc('permute;write_aiger -u file2.aig')
        n = filecmp.cmp('file1.aig','file2.aig')
        print n,
        n_iso = n_iso+n
    print 'the number of isomorphisms was %d out of %d'%(n_iso,N)
    return n_iso

def get_large_po():
##    remove_const_pos() #get rid of constant POs
    NL = n_latches()
    NO = n_pos()
    abc('&get') #put the in & space
    n_latches_max = 0
    nl = imax = -1
    for i in range(NO): #look for a big enough PO
        abc('&put;cone -s -O %d;scl'%i)
        nl = n_latches()
        if nl >.15*NL:
            imax = i
##            print 'cone %d has %d FF'%(i,nl)
            break
        if nl> n_latches_max:
            n_latches_max = nl
            imax = i
            print i,nl
        if i == NO-1:
            print 'no PO is big enough'
            return -1
    print 'PO_cone = %d, n_latches = %d'%(imax,nl)

def scorro():
    run_command('scorr -o')
    l = remove_const_pos()
    ps()

def drw():
    run_command('drw')
    ps()

def dc2rs():
    abc('dc2rs')
    ps()
    

def reachn(t):
    x = time.clock()
    abc('&get;&reachn -rv -T %d'%t)
    print 'reachm3 done in time = %f'%(time.clock() - x)
    return get_status()
    
def reachx(t):
    x = time.time()
    abc('reachx -t %d'%t)
    print 'reachx  done in time = %f'%(time.time() - x)
    return get_status()

def reachy(t):
    x = time.clock()
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

def modify_methods(J,dec=0):
    """ adjusts the engines to reflect number of processors"""
    N = bmc_depth()
    L = n_latches()
    I = n_real_inputs()
    npr = n_proc -dec
    if 18 in J: #if sleep in J add 1 more processor
        npr = npr+1
    if ( ((I+L<350)&(N>100))  or  (I+L<260) or (L<80) ):
        if not 24 in J: #24 is reachs
            J = J+[24] # add all reach methods
            if len(J)>npr:
                J = remove_intrps(J) #removes only if len(J)<n_processes
    if len(J)< npr: #if not using all processors, add in pdrs
        #modify allpdrs to reflect ifbip (see set_engines)
        for j in range(len(allpdrs)):
            if allpdrs[j] in J: #leave it in
                continue
            else: #add it in
                J = J + [allpdrs[j]]
                if len(J) == npr:
                    break            
##        if L < 80:
##            if ((not 4 in J) and len(J) < n_proc):
##                J = J + [4]
    return J

def BMC_VER():
    """ a special version of BMC_VER_result that just works on the current network
    Just runs engines in parallel - no backing up
    """
    global init_initial_f_name, methods, last_verify_time, n_proc
    xt = time.time()
    result = 5
    t = max(2*last_verify_time,10000)  ####
    print 'Verify time set to %d'%t
    J = slps + pdrs + bmcs + intrps
    J = modify_methods(J)
    F = create_funcs(J,t)
    mtds = sublist(methods,J)
    print mtds
    (m,result) = fork_break(F,mtds,'US')
    result = RESULT[result]
    print 'BMC_VER result = %s'%result
    return result

        
def BMC_VER_result():
    global init_initial_f_name, methods, last_verify_time,f_name
    xt = time.time()
    result = 5
    abc('r %s.aig'%f_name)
    print '\n***Running proof on %s :'%f_name,
    ps()
    t = max(2*last_verify_time,10000) #each time a new time-out is set t at least 1000 sec.
    print 'Verify time set to %d'%t
    X = pyabc_split.defer(abc)
    J = slps + pdrs + bmcs + intrps
    last_name = seq_name(f_name).pop()
    if 'smp' == last_name: # then we try harder to prove it.
        J = slps + intrps + allpdrs + [2]
    J = modify_methods(J) #if # processors is enough and problem is small enough then add in reachs
    F = create_funcs(J,t)
    mtds = sublist(methods,J)
    print '%s'%mtds
    (m,result) = fork(F,mtds)
    result = get_status()
    if result == Unsat:
        return 'UNSAT'
    if last_name == 'smp' :   # can't backup so just return result
        if result < Unsat:
            return 'SAT'
        if result > Unsat: #still undefined
            return 'UNDECIDED'
    else:    # (last_name == 'spec' or last_name == 'abs') - the last thing we did was an "abstraction"
        if result < Unsat:
            f_name = revert(f_name,1) # revert the f_name back to previous
            abc('r %s.aig'%f_name)
            return BMC_VER_result() #recursion here.
            
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
    Finally all zero'ed outputs are removed.
    Prints out unproved outputs Finally removes 0 outputs
    """
    global n_pos_proved, n_pos_before
    print 'n_pos_proved = %d'%n_pos_proved
    n_proved = 0
    N = n_pos()
##    l=remove_const_pos()
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
##        l=remove_const_pos() #may not have to do this if constr works well with 0'ed outputs
        abc('constr -N %d'%(n_pos()-1))
        abc('fold')
        n = max(1,n_ands())
        f = max(1,min(40000/n,16))
        f = int(f)
##        abc('ind -C 10000 -F %d'%f)
        abc('ind -C 1000 -F %d'%f)
##        run_command('print_status')
        status = get_status()
        abc('r %s_osavetemp.aig'%f_name) #have to restore original here
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
    l=remove_const_pos()
    n_pos_proved = n_pos_proved + n_proved 
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    print 'n_pos_proved = %d'%n_pos_proved
    #return status

def remove_iso(L):
    global n_pos_proved, n_pos_before
    lst = []
    for j in range(len(L)):
        ll = L[j][1:]
        if len(ll) == 0:
            continue
        else:
            lst = lst + ll
    zero(lst)
    n_pos_proved = n_pos_proved + count_less(lst,n_pos_before - n_pos_proved)
    print 'The number of POs removed by iso was %d'%len(lst)
    l=remove_const_pos() #can an original PO be zero?

def prove_all_iso():
    """Tries to prove output k by isomorphism. Gets number of iso-eq_classes as an array of lists.
    Updates n_pos_proved
    """
    global n_pos_proved, n_pos_before
    n_proved = 0
    N = n_pos()
    if n_pos() == 1:
        return
    print 'n_pos_proved = %d'%n_pos_proved
##    run_command('&get;&iso;&put')
    abc('&get;&iso')
    L = iso_eq_classes()
##    print L
    remove_iso(L)
##    lim = n_pos_before - n_pos_proved
##    for j in range(len(L)):
##        ll = L[j]
##        if len(ll) == 1:
##            continue
##        if not ll[0] < lim:
##            continue
##        else:
##            n = count_less(ll[1:], lim) #drop the first since it is the representative.
##            print n
##            n_proved = n_proved + n
##            print n, n_proved
##    n_pos_proved = n_pos_proved + n_proved 
    print '\nThe number of POs reduced by iso was from %d to %d'%(N,n_pos())

def count_less(L,n):
    count = 0
    for j in range(len(L)):
        if L[j] < n:
            count = count + 1
    return count

def prove_all_mtds(t):
    """
    Tries to prove output k  with multiple methods in parallel,
    using other outputs as constraints. If ever an output is proved
    it is set to 0 so it can't be used in proving another output to break circularity.
    Finally all zero'ed ooutputs are removed.
    """
    N = n_pos()
##    l=remove_const_pos()
##    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        run_command('swappos -N %d'%j)
##        l=remove_const_pos() #may not have to do this if constr works well with 0'ed outputs
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
    l=remove_const_pos()
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def prove_all_pdr(t):
    """Tries to prove output k by pdr, using other outputs as constraints. If ever an output is proved
    it is set to 0 so it can't be used in proving another output to break circularity.
    Finally all zero'ed ooutputs are removed. """
    N = n_pos()
##    l=remove_const_pos()
    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        abc('swappos -N %d'%j)
##        l=remove_const_pos() #may not have to do this if constr works well with 0'ed outputs
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
    l=remove_const_pos()
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def prove_each_ind():
    """Tries to prove output k by induction,  """
    N = n_pos()
    l=remove_const_pos()
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
    l=remove_const_pos()
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def prove_each_pdr(t):
    """Tries to prove output k by PDR. If ever an output is proved
    it is set to 0. Finally all zero'ed ooutputs are removed. """
    N = n_pos()
    l=remove_const_pos()
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
    l=remove_const_pos()
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def disprove_each_bmc(t):
    """Tries to prove output k by PDR. If ever an output is proved
    it is set to 0. Finally all zero'ed ooutputs are removed. """
    N = n_pos()
    l=remove_const_pos()
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
    l=remove_const_pos()
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def pord_1_2(t):
    """ two phase pord. First one tries with 10% of the time. If not solved then try with full time"""
    global n_pos_proved, ifpord1, pord_on
    pord_on = True # make sure that we do not reparameterize after abstract in prove_2
    n_pos_proved = 0
    if n_pos()<4:
        return Undecided
    if ifpord1:
        print 'Trying each output for %0.2f sec'%(.1*t)
        result = pord_all(.1*t) #we want to make sure that there is no easy cex.
        if (result <= Unsat):
            return result
    ifpord1 = 0
    print 'Trying each output for %0.2f sec'%t
    #might consider using iso before the second pass of pord_all
    result = pord_all(t+2*G_T) #make sure there is enough time to abstract
    pord_on = False #done with pord
    return result

def pord_all(t):
    """Tries to prove or disprove each output j by PDRM BMC3 or SIM. in time t"""
    global cex_list, n_pos_proved, last_cx, pord_on, ifpord1
    print 'last_cx = %d'%last_cx
    btime = time.time()
    N = n_pos()
    prove_all_ind() ############ change this to keep track of n_pos_proved
    nn = n_pos()
    abc('w %s_osavetemp.aig'%f_name)
    if nn < 4: #Just cut to the chase immediately.
        return Undecided
    lst = range(n_pos())
    proved = disproved = []
    abc('&get') #using this space to save original file.
    ### Be careful that & space is not changed.
##    with redirect.redirect( redirect.null_file, sys.stdout ):
##        with redirect.redirect( redirect.null_file, sys.stderr ):
    cx_list = []
    n_proved = 0
    lcx = last_cx + 1
    lst = lst[lcx:]+lst[:lcx]
    lst.reverse()
    n_und = 0
    for j in lst:
        print '\ncone %s. '%j,
        abc('&put; cone -s -O %d'%j) #puts the &space into reg-space and extracts cone j
        #requires that &space is not changed. &put resets status. Use &put -s to keep status
        abc('scl -m')
        ps()
##        print 'running sp2'
        ###
        result = run_sp2_par(t)
##        J = slps+JV
##        result = verify(J,t)
##        result = RESULT[result]
##        ###
##        print 'run_sp2_par result is %s'%result
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
##    n_pos_proved = n_pos_proved + n_proved. #this should not be here because we should start fresh
    print '\nProved %d outputs'%len(proved)
    print 'Disproved %d outputs'%len(disproved)
    print 'Time for pord_all was %0.2f'%(time.time() - btime)
    NN = len(proved+disproved)
    cex_list = cx_list
    if len(disproved)>0:
        assert status == Sat, 'status = %d'%status
        n_pos_proved = 0 #we want to reset this because of a bad speculation
        return Sat
    else:
        n_pos_proved = n_pos_proved + n_proved
        abc('r %s_osavetemp.aig'%f_name)
##        abc('&put') # returning original to work spece
        remove(proved)
        print '\nThe number of unproved POs reduced from %d to %d'%(N,n_pos()),
        ps()
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
    l=remove_const_pos()
        
def bmc_j(t):
    """ finds a cex in t seconds starting at 2*N where N is depth of bmc -T 1"""
    x = time.time()
    tt = min(5,max(1,.05*t))
    abc('bmc3 -T %0.2f'%tt)
    if is_sat():
        print 'cex found in %0.2f sec at frame %d'%((time.time()-x),cex_frame())
        return get_status()
##    abc('bmc3 -T 1')
    N = n_bmc_frames()
    N = max(1,N)
##    print bmc_depth()
##    abc('bmc3 -C 1000000 -T %f -S %d'%(t,int(1.5*max(3,max_bmc))))
    cmd = 'bmc3 -J 2 -D 4000 -C 1000000 -T %f -S %d'%(t,2*N)
##    print cmd
    abc(cmd)
    if is_sat():
        print 'cex found in %0.2f sec at frame %d'%((time.time()-x),cex_frame())
    return get_status()

def pdrseed(t):
    """uses the abstracted version now"""
##    abc('&get;,treb -rlim=60 -coi=3 -te=1 -vt=%f -seed=521'%t)
    abc('&get;,treb -rlim=100 -vt=%f -seed=521'%t)


def pdrold(t):
    abc('&get; ,pdr -vt=%f'%t)

def pdr(t):
    abc('&get; ,treb -vt=%f'%t)
    return RESULT[get_status()]

def pdra(t):
##    abc('&get; ,treb -rlim=100 -ssize -pre-cubes=3 -vt=%f'%t)
    abc('&get; ,treb -abs -rlim=100 -gen-cex -vt=%f'%t)
    return RESULT[get_status()]

def pdrm(t):
    abc('pdr -C 0 -T %f'%t)
    return RESULT[get_status()]

def pdrmm(t):
    abc('pdr -C 0 -M 298 -T %f'%t)
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

def prove_1(ratio=.75):
    """
    A version of prove called from prove_pos, prove_g_pos, prove_only, prove_g_pos_split when we
    have speculated and produced multiple outputs. 
    Proves all the outputs together. If ever an abstraction was done then
    if SAT is returned,we make RESULT return "undecided".
    """
    global x_factor,xfi,f_name,x, initial_f_name
    x = time.time()
    max_bmc = -1
    print 'Initial: ',
    ps()
    x_factor = xfi
    initial_f_name_save = initial_f_name #needed because we are making local backups here.
    initial_f_name = '%s_temp'%initial_f_name
    set_globals()
    print'\n***Running abstract'
    status = abstract(ifbip)
    trim()
    status = process_status(status)
    if ((status <= Unsat)  or  status == Error):
        if  status < Unsat:
            print 'CEX in frame %d'%cex_frame(),
            print 'abstract found a cex in initial circuit'
            print 'Time for proof = %f sec.'%(time.time() - x)
            initial_f_name = initial_f_name_save
            return RESULT[status]
        print 'Time for proof = %f sec.'%(time.time() - x)
        initial_f_name = initial_f_name_save
        return RESULT[status]
    #undecided here
    print 'Entering direct verificationb'
####    status = final_verify_recur(2)
    status = BMC_VER()
    return status
    
    trim()
####    write_file('final')
    print 'Time for proof = %f sec.'%(time.time() - x)
    initial_f_name = initial_f_name_save
    return RESULT[status]
    
def pre_reduce():
    x = time.clock()
    pre_simp()
    write_file('smp')
    abstract(ifbip)
####    write_file('abs')
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
    """ Runs the single method simple, timed for t seconds."""
    global cex_list,methods
    J = slps+[6]
    print sublist(methods,J)
    funcs = create_funcs(J,t) 
    y = time.time()
    for i,res in pyabc_split.abc_split_all(funcs):
##        print 'i,res = %d,%s'%(i,res)
        t = time.time()-y
        if i == 0:
            print 'sleep timer expired in %0.2f'%t
            return 'UNDECIDED'
        else:
##            print i,res
            if res == 'UNSAT':
                print 'Simple_prove proved UNSAT in %0.2f sec.'%t
                return 'UNSAT'
            elif res == 'UNDECIDED':
                print 'Simple_prove proved UNDECIDED in %0.2f sec.'%t
                return 'UNDECIDED'
            else:
                print 'Simple_prove found cex in %0.2f sec.'%t
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

def take_best(funcs,mts):
    """ fork the functions, If not solved, take the best result in terms of AIG size"""
    global f_name
    n = len(mts)-1
    y = time.time()
    m_best = -1
    best_size = 1000000
    abc('w %s_best_aig.aig'%f_name)
    for i,res in pyabc_split.abc_split_all(funcs):
        if n_ands() < best_size:
            best_size = n_ands()
            m_best = i
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
    #print 'starting fork_last'
    for i,res in pyabc_split.abc_split_all(funcs):
        #print i,res
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
            res = Undecided
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

####def synculate(t):
####    """
####    Finds candidate sequential equivalences and refines them by simulation, BMC, or reachability
####    using any cex found. If any are proved, then they are used to reduce the circuit. The final aig
####    is a new synthesized circuit where all the proved equivalences are merged.
####    If we put this in a loop with increasing verify times, then each time we work with a simpler model
####    and new equivalences. Should approach srm. If in a loop, we can remember the cex_list so that we don't
####    have to deal with disproved equivalences. Then use refine_with_cexs to trim the initial equivalences.
####    If used in synthesis, need to distinguish between
####    original outputs and new ones. Things to take care of: 1. a PO should not go away until it has been processes by merged_proved_equivalences
####    2. Note that &resim does not use the -m option where as in speculation - m is used. It means that if
####    an original PO isfound to be SAT, the computation quits becasue one of the output
####    miters has been disproved.
####    """    
####    global G_C,G_T,n_pos_before, x_factor, n_latches_before, last_verify_time, f_name,cex_list, max_verify_time
####    
####    
####    def refine_with_cexs():
####        """Refines the gores file to reflect equivalences that go away because of cexs in cex_list"""
####        global f_name
####        abc('&r %s_gores.aig'%f_name)
####        for j in range(len(cex_list)):
####            cex_put(cex_list[j])
####            run_command('&resim') #put the jth cex into the cex space and use it to refine the equivs
####        abc('&w %s_gores.aig'%f_name)
####        return
####    
####    def generate_srms():
####        """generates a synthesized reduced model (srms) from the gores file"""
####        global f_name, po_map
####        abc('&r %s_gores.aig; &srm -sf; r gsrms.aig; w %s_gsrms.aig'%(f_name,f_name))
####        print 'New srms = ',ps()
####        po_map = range(n_pos())
####        return 'OK'
####
####    def merge_proved_equivalences():
####        #this only changes the gores file.
####        run_command('&r %s_gores.aig; &equiv_mark -vf %s_gsrms.aig; &reduce -v; &w %s_gores.aig'%(f_name,f_name,f_name))
####        return
####
####    def generate_equivalences():
####        set_globals()
####        t = max(1,.5*G_T)
####        r = max(1,int(t))
####        cmd = "&get; &equiv2 -C %d -F 200 -T %f -S 1 -R %d"%((G_C),t,r)
####        abc(cmd)
####        #run_command('&ps')
####        eq_simulate(.5*t)
####        #run_command('&ps')
####        cmd = '&semi -W 63 -S 5 -C 500 -F 20 -T %d'%(.5*t)
####        abc(cmd)
####        #run_command('&ps')
####        run_command('&w %s_gores.aig'%f_name)
####
####    l=remove_const_pos() #makes sure no 0 pos to start
####    cex_list = []
####    n_pos_before = n_pos()
####    n_latches_before = n_latches()
######    print 'Generating equivalences'
####    generate_equivalences()
######    print 'Generating srms file'
####    generate_srms() #this should not create new 0 pos
######    if n_pos()>100:
######        removed
####    l=remove_const_pos()
####    n_pos_last = n_pos()
####    if n_pos_before == n_pos():
####        print 'No equivalences found. Quitting synculate'
####        return Undecided_no_reduction
####    print 'Initial synculation: ',ps()
######    ps()
####    set_globals()
####    simp_sw = init = True
####    simp_sw = False #temporary
####    print '\nIterating synculation refinement'
####    abc('w initial_sync.aig')
####    max_verify_time = t
####    print 'max_verify_time = %d'%max_verify_time
####    """
####        in the following loop we increase max_verify_time by twice time spent to find last cexs or Unsat's
####        We iterate only when we have proved cex + unsat > 1/2 n_pos. Then we update srms and repeat.        
####    """
####    while True:                 # refinement loop
####        t = max_verify_time     #this may have been increased since the last loop
######        print 'max_verify_time = %d'%max_verify_time
####        set_globals()
####        if not init:
####            generate_srms()     #generates a new gsrms file and leaves it in workspace
######            print 'generate_srms done'
####            if n_pos() == n_pos_before:
####                break
####            if n_pos() == n_pos_last:   #if nothing new, then quit if max_verification time is reached.
####                if t > max_verify_time:
####                    break
####            if simp_sw:                     #Warning: If this holds then simplify could create some 0 pos
####                na = n_ands()
####                simplify()
####                while True:
####                    npo = n_pos()
######                    print 'npos = %d'%npo
####                    merge_proved_equivalences() #So we need to merge them here. Can merging create more???
####                    generate_srms()
####                    if npo == n_pos():
####                        break
####                if n_ands() > .7*na:            #if not significant reduction, stop simplification
####                    simp_sw = False             #simplify only once.
####            if n_latches() == 0:
####                return check_sat()
####        n_pos_last = n_pos()
####        init = False                        # make it so that next time it is not the first time through
####        syn_par(t)
####        if (len(cex_list)+len(result)) == 0: #nothing happened aand ran out of time.
####            break
####        abc('w %s_gsrms.aig'%f_name)
####        #print 'No. of cexs after syn_parallel = %d'%len(cex_list)
####        merge_proved_equivalences()         #changes the underlying gores file by merging fanouts of proved eqs
####        #print 'merge done'
####        refine_with_cexs()                  #changes the gores file by refining the equivalences in it using cex_list.
####        #print 'refine_with_cexs done'
####        continue
####    extract(0,n_pos_before) #get rid of unproved outputs
####    return
####
####def syn_par(t):
####    """prove n outputs at once and quit at first cex. Otherwise if no cex found return aig
####    with the unproved outputs"""
####    global trim_allowed,max_verify_time, n_pos_before
####    global cex_list, result
####    b_time = time.time()
####    n = n_pos()
####    if n == n_pos_before:
####        return
####    mx = n_pos()
####    if n_pos() - n_pos_before > 50:
####        mx = n_pos_before + 50
####    r = range(n_pos_before, mx)     
####    N = max(1,(mx-n_pos_before)/2)
####    abc('w %s__ysavetemp.aig'%f_name) 
####    F = [eval(FUNCS[18])] #create a timer function
####    #print r
####    for i in r:
####        F = F + [eval('(pyabc_split.defer(verify_only)(%d,%d))'%(i,t))]
####    cex_list = result = []
####    outcome = ''
####    #redirect printout here
######    with redirect.redirect( redirect.null_file, sys.stdout ):
######        with redirect.redirect( redirect.null_file, sys.stderr ):
####    for i,res in pyabc_split.abc_split_all(F):
####        status = get_status()
######        print i
####        if i == 0:          #timed out
####            outcome = 'time expired after = %d'%(time.time() - b_time)
####            break
####        if status < Unsat:
####            cex_list = cex_list + [cex_get()]                    
####        if status == Unsat:
####            result = result + [r[i-1]]
####        if (len(result)+len(cex_list))>= N:
####            T = time.time() - b_time
####            if T > max_verify_time/2:
####                max_verify_time = 2*T
####            break
####        continue
####    if not outcome == '':
####        print outcome
######    print 'cex_list,prove_list = ',cex_list,result
####    abc('r %s__ysavetemp.aig'%f_name) #restore initial aig so that pos can be 0'ed out
####    if not result == []: # found some unsat's
######        min_r = min(result)
######        max_r = max(result)
######        no = n_pos()
######        assert (0 <= min_r and max_r < no), 'min_r, max_r, length = %d, %d, %d'%(min_r,max_r,len(result))
####        zero(result)
####    return
####    #print "Number PO's proved = %d"%len(result)
####
####def absec(n):
####    #abc('w t.aig')
####    for j in range(n):
####        print '\nFrame %d'%(j+1)
####        run_command('absec -F %d'%(j+1))
####        if is_unsat():
####            print 'UNSAT'
####            break
####    
####
####"""
####    we might be proving some original pos as we go, and on the other hand we might have some equivalences that we
####    can't prove. There are two uses, in verification
####    verification - we want to remove the proved pos whether they are original or not. But if a cex for an original, then need to
####                    remember this.
####    synthesis - the original outputs need to be kept and ignored in terms of cex's - supposedly they can't be proved.
####"""
####
####""" Experimental"""
####
####def csec():
####    global f_name
####    if os.path.exists('%s_part0.aig'%f_name):
####        os.remove('%s_part0.aig'%f_name)
####    run_command('demiter')
####    if not os.path.exists('%s_part0.aig'%f_name):
####        return
####    run_command('r %s_part0.aig'%f_name)
####    ps()
####    run_command('comb')
####    ps()
####    abc('w %s_part0comb.aig'%f_name)
####    run_command('r %s_part1.aig'%f_name)
####    ps()
####    run_command('comb')
####    ps()
####    abc('w %s_part1comb.aig'%f_name)
####    run_command('&get; &cec %s_part0comb.aig'%(f_name))
####    if is_sat():
####        return 'SAT'
####    if is_unsat():
####        return 'UNSAT'
####    else:
####        return 'UNDECIDED'

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


""" These commands map into luts and leave the result in mapped format. To return to aig format, you
have to do 'st'
"""
def sop_balance(k=4):
    '''minimizes LUT logic levels '''
##    kmax = k
    kmax=min(k+2,15)
    abc('st; if -K %d;ps'%kmax)
    print nl(),
##    for i in range(1):
##        abc('st; if -K %d;ps'%kmax)
##        run_command('ps')
    kmax=min(k+2,15)
    abc('st; if  -g -C %d -K %d -F 2;ps'%(10,kmax)) #balance
    print nl(),
    for i in range(1):
        abc('st;dch; if -C %d -K %d;ps'%(10,kmax))
        print nl(),

def speedup(k=4):
    run_command('speedup;if -K %d'%k)
    print nl()

def speed_tradeoff(k=4):
    print nl(),
    best = n_nodes()
    abc('write_blif %s_bestsp.blif'%f_name)
    L_init = n_levels()
    while True:
        L_old = n_levels()
        L = L_old -1
        abc('speedup;if -D %d -F 2 -K %d -C 11'%(L,k))
        if n_nodes() < best:
            best = n_nodes()
            abc('write_blif %s_bestsp.blif'%f_name)
        if n_levels() == L_old:
            break
        print nl(),
        continue
    abc('r %s_bestsp.blif'%f_name)
    return

def map_lut_dch(k=4):
    '''minimizes area '''
    abc('st; dch; if -a  -F 2 -K %d -C 11; mfs -a -L 50 ; lutpack -L 50'%k)
    
def map_lut_dch_iter(k=8):
##    print 'entering map_lut_dch_iter with k = %d'%k
    best = n_nodes()
    abc('write_blif %s_best.blif'%f_name)
##    abc('st;dch;if -a -K %d -F 2 -C 11; mfs -a -L 1000; lutpack -L 1000'%k)
##    if n_nodes() < best:
##        abc('write_blif %s_best.blif'%f_name)
##        best = n_nodes()
##        print nl(),
##    else:
##        abc('r %s_best.blif'%f_name)
##    best = n_nodes()
##    abc('write_blif %s_best.blif'%f_name)
##    print 'best = %d'%best
    n=0
    while True:
        map_lut_dch(k)
        if n_nodes()< best:
            best = n_nodes()
##            print 'best=%d'%best
            n = 0
            abc('write_blif %s_best.blif'%f_name)
            print nl(),
            continue
        else:
            n = n+1
            if n>2:
                break    
    abc('r %s_best.blif'%f_name)

def dmitri_iter(k=8):
    best = 100000
    n=0
    while True:
        dmitri(k)
        if n_nodes()< best:
            best = n_nodes()
##            print '\nbest=%d'%best
            n = 0
            abc('write_blif %s_best.blif'%f_name)
            continue
        else:
            n = n+1
        if n>2:
            break
    abc('r %s_best.blif'%f_name)
##    run_command('cec -n %s.aig'%f_name)
    print nl()


def map_lut(k=4):
    '''minimizes edge count'''
    for i in range(5):
        abc('st; if -e -K %d; ps;  mfs ;ps; lutpack -L 50; ps'%(k))
        print nl(),

def extractax(o=''):
    abc('extract -%s'%o)

def nl():
    return [n_nodes(),n_levels()]

def dc2_iter(th=.999):
    abc('st')
    while True:
        na=n_ands()
        abc('dc2')
        print n_ands(),
##        print nl(),
        if n_ands() > th*na:
            break
##    print n_ands()

def adc2_iter(th=.999):
    abc('st;&get')
    while True:  
        na=n_ands()
        abc('&dc2;&put')
##        print n_ands(),
        if n_ands() > th*na:
            break
    print n_ands()
        
def try_extract():
##    abc('dc2;dc2')
    print 'Initial: ',
    ps()
    na = n_ands()
##    abc('w %s_savetemp.aig'%f_name)
    #no need to save initial aig since fork_best will return initial if best.
    J = [32,33]
    mtds = sublist(methods,J)
    F = create_funcs(J,0)
    (m,result) = take_best(F,mtds) #FORK here
    if not m == -1:
        print 'Best extract is %s: '%mtds[m],
        ps()
##    if (n_ands() < na):
##        return
##    else:
##        abc('r %s_savetemp.aig'%f_name)

def speedup_iter(k=8):
    abc('st;if -K %d'%k)
    run_command('ps')
    abc('write_blif %s_bests.blif'%f_name)
    run_command('ps')
    best = n_levels()
    print 'n_levels before speedup = %d'%n_levels()
    n=0
    while True:
        nl()
        abc('speedup;if -K %d'%k)
        if n_levels() < best:
            best = n_levels()
            abc('write_blif %s_bests.blif'%f_name)
            n=0
        else:
            n = n+1
        if n>2:
            break
    abc('r %s_bests.blif'%f_name)
    print 'n_levels = %d'%n_levels()

def jog(n=16):
    """ applies to a mapped blif file"""
    run_command('eliminate -N %d;fx'%n)
    run_command('if -K %d'%(n/2))
    run_command('fx')

def perturb_f(k=4):
    abc('st;dch;if -g -K %d'%(k))
##    snap()
    abc('speedup;if -K %d -C 10'%(k))
    jog(5*k)
##    snap()
##    abc('if -a -K %d -C 11 -F 2;mfs -a -L 50;lutpack -L 50'%k

def perturb(k=4):
    abc('st;dch;if -g -K %d'%k)
##    snap()
    abc('speedup;if -K %d -C 10'%(k))
    
def preprocess(k=4):
    n_initial = n_nodes()
    abc('write_blif %s_temp_initial.blif'%f_name)
##    abc('st;dc2')
    abc('w %s_temp_initial.aig'%f_name)
    ni = n_pis() + n_latches()
    res = 1
    if ni >= 101:
        abc('st;if -a -F 2 -K %d'%k)
        return res
##    dc2_iter()
    abc('st;if -a -K %d'%k) # to get plain direct map
    if n_nodes() > n_initial:
        abc('r %s_temp_initial.blif'%f_name)
        res = 1
    #plain
    n_plain = n_nodes()
##    print nl()
    abc('write_blif %s_temp_plain.blif'%f_name)
    #clp
    abc('st;clp; if -a -K %d'%k)
##    print nl()
    abc('write_blif %s_temp_clp.blif'%f_name)
    n_clp = n_nodes()
    #clp_lutmin
    abc('r %s_temp_initial.blif'%f_name)
    abc('st;clp;lutmin -K %d;'%k)
    abc('write_blif %s_temp_clp_lut.blif'%f_name)
    n_clp_lut = n_nodes()
##    print nl()
    if n_plain <= min(n_clp,n_clp_lut):
        abc('r %s_temp_plain.blif'%f_name)
        res = 1
    elif n_clp < n_clp_lut:
        abc('r %s_temp_clp.blif'%f_name)
        res = 1
    else:
        abc('r %s_temp_clp_lut.blif'%f_name)
        res = 1
##    print nl()
    return res

def snap():
##    abc('fraig;fraig_store')
    abc('fraig_store')

def snap_bestk(k):
    abc('write_blif %s_temp.blif'%f_name)
    unsave_bestk(k)
    snap()
    abc('r %s_temp.blif'%f_name)

def cec_it():
    """ done because &r changes the names. Can't use -n because rfraig_store reorders pis and pos."""
    abc('write_blif %s_temp.blif'%f_name)
    abc('&r %s.aig;&put'%f_name)
    run_command('cec %s_temp.blif'%f_name)
    abc('r %s_temp.blif'%f_name)

def save_bestk(b,k):
##    if os.access('%s_best%d.blif'%(f_name,k),os.R_OK):
##        res = get_bestk(k)
##    else:
    """ saves the best, returns bestk and if not best, leaves blif unchanged""" 
    res = b
    if n_nodes() < res:
        res = n_nodes()
        abc('write_blif %s_best%d.blif'%(f_name,k))
        print 'best%d = %d'%(k,res)
    return res
##    unsave_bestk(k)

def unsave_bestk(k):
    abc('r %s_best%d.blif'%(f_name,k))
        
def unsnap(k=4):
##    snap()
    abc('fraig_restore')
    map_lut_dch(k)
##    abc('fraig_restore;if -a -F 2 -C 11 -K %d'%k)

def map_until_conv(k=4):
    kk = 2*k
    # make sure that no residual results are left over.
    if os.access('%s_best%d.blif'%(f_name,k),os.R_OK):
        os.remove('%s_best%d.blif'%(f_name,k))
    if os.access('%s_best%d.blif'%(f_name,kk),os.R_OK):
        os.remove('%s_best%d.blif'%(f_name,kk))
    tt = time.time()
    #get initial map and save
    map_lut_dch(k)
    bestk = save_bestk(100000,k)
    print nl()
##    snap()
    res = preprocess() #get best of initial, clp, and lutmin versions
    print nl()
##    map_lut_dch(k)
##    ###
##    bestk = save_bestk(bestk,k)
##    map_iter(k)
##    bestk = save_bestk(bestk,k)
##    ###
    map_lut_dch_iter(kk) #initialize with mapping with 2k input LUTs
    bestkk = save_bestk(100000,kk)
    snap()
    unsnap(k) #have to do snap first if want current result snapped in.
        # unsnap fraigs snapshots and does map_lut_dch at end
    print nl()
    bestk = save_bestk(bestk,k)
    abc('r %s_bestk%d.blif'%(f_name,k))
    map_iter(k) #1
    bestk = save_bestk(bestk,k)
    while True:
        print 'Perturbing with %d-Lut'%kk
##        snap()
        map_lut_dch_iter(kk)
##        snap()
        bestkk_old = bestkk
        bestkk = save_bestk(bestkk,kk)
        if bestkk >= bestkk_old:
            break
##        snap()
##        jog(kk)
##        perturb_f(k)
##        snap()
##        perturb_f(k)
##        snap()
##        unsave_bestk(k)
##        map_lut_dch(k+1)
##        snap()
##        snap_bestk(k)
        snap()
        unsnap(k) #fraig restore and map
##        bestk = save_bestk(bestk,k)
##        snap()
        bestk_old = bestk
        map_iter(k)
        bestk = save_bestk(bestk,k)
        if bestk >= bestk_old:
            break
        continue
    abc('fraig_restore') #dump what is left in fraig_store
    unsave_bestk(k)
    print '\nFinal size = ',
    print nl()
    print 'time for %s = %.02f'%(f_name,(time.time()-tt))
##    cec_it()

def get_bestk(k=4):
    abc('write_blif %s_temp.blif'%f_name)
    unsave_bestk(k)
    res = n_nodes()
    abc('r %s_temp.blif'%f_name)
    return res

def map_iter(k=4):
    tt = time.time()
    bestk = get_bestk(k)
##    bestk = n_nodes()
##    bestk = save_bestk(bestk,k)
##    abc('st;dch;if -a -F 2 -K %d -C 11; mfs -a -L 1000; lutpack -L 1000'%k)#should be same as Initial
##    map_lut_dch_iter(k) ####
    map_lut_dch(k)
    bestk = save_bestk(bestk,k)
    n=0
    unsave_bestk(k)
    while True:
##        snap()
        perturb(k) #
##        snap()
        perturb(k)
##        snap_bestk(k)
##        unsnap(k)
##        bestk = save_bestk(bestk,k)
##        snap()
##        map_lut_dch(k+1)
##        abc('if -K %d'%(k+1))
##        snap()
##        unsnap(k)
        old_bestk = bestk
##        print old_bestk
        map_lut_dch_iter(k)
        bestk = save_bestk(bestk,k)
        print bestk
        if bestk < old_bestk:
            n=0 # keep it up
            continue
        elif n == 2: #perturb 
            break
        else:
            n = n+1
            print '%d-perturb'%n
##            snap()
##            unsave_bestk(k)
    unsave_bestk(k)

def map_star(k=4):
    tt = time.time()
    map_until_conv(k)
    abc('write_blif %s_best_star.blif'%f_name)
    best = n_nodes()
    while True:
        jog(2*k)
        map_until_conv(k)
        if n_nodes() >= best:
            break
        else:
            best = n_nodes()
            abc('write_blif %s_best_star.blif'%f_name)
    abc('r %s_best_star.blif'%f_name)
    print 'SIZE = %d, TIME = %.2f for %s'%(n_nodes(),(time.time() - tt),f_name)

def decomp_444():
    abc('st; dch; if -K 10 -S 444')
    abc('write_blif -S 444 %s_temp.blif; r %s_temp.blif'%(f_name,f_name)) 

def dmitri(k=8):
##    abc('w t.aig')
##    dc2_iter()
##    print 'first iter done:  %d'%n_ands()
##    abc('dc2rs')
####    dc2_iter()
##    print 'second iter done:  %d'%n_ands()
##    sop_balance(k)
##    abc('w t_before.aig')
##    run_command('cec -n t.aig')
##    speedup_iter(k)
##    print 'n_levels after speedup = %d'%n_levels()
##    abc('write_blif %s_save.blif'%f_name)
##    nn=n_levels()
    abc('st;dch; if -g -K %d'%(k))
##    print 'n_levels after sop balance = %d'%n_levels()
##    if n_levels() > nn:
##        run_command('r %s_save.blif'%f_name)
##        print 'n_levels = %d'%n_levels()
##    print 'final n_levels = %d'%n_levels()
##    print 'sop_balance done:  ',
##    print nl()
##    run_command('st;w t_after.aig')
##    run_command('cec -n t.aig')
    abc('if -G %d '%k)
##    print 'after if -G %d:  '%k,
##    print nl()
##    run_command('cec -n t.aig')
    abc('cubes')
##    print 'after cubes:  ',
##    print nl()
##    run_command('cec -n t.aig')
    abc('addbuffs -v')
##    print 'after addbuffs:  ',
    print nl(),
##    run_command('cec -n t.aig')

def lut():
    dc2_iter()
    abc('extract -a')
    print nl()
    dc2_iter()
##    ps()
    sop_balance(6)
    map_lut_dch()
    map_lut()
    print nl()
##    run_command('ps')

################################## gate level abstraction
    """
    Code for using
    for abstraction
    """

def bip_abs(t=100):
    """ t is ignored here"""
    set_globals()
    time = max(1,.1*G_T)
    abc('&get;,bmc -vt=%f'%time)
    set_max_bmc(bmc_depth())
    c = 2*G_C
    f = max(2*max_bmc,20)
    b = min(max(10,max_bmc),200)
    t1 = x_factor*max(1,2*G_T)
    t = max(t1,t)
    s = min(max(3,c/30000),10) # stability between 3 and 10 
##    cmd = '&get;,abs -bob=%d -stable=%d -timeout=%d -vt=%d -depth=%d -dwr=vabs'%(b,s,t,t,f)
    cmd = '&get;,abs -timeout=%d -vt=%d -dwr=%s_vabs'%(t,t,f_name)
    print 'Running %s'%cmd
##    abc(cmd)
    run_command(cmd)
    bmc_depth()
    abc('&w %s_greg.aig'%f_name)
    return max_bmc

def check_frames():
    abc('read_status vta.status')
    return n_bmc_frames()

def gate_abs(t):
    """ Do gate-level abstraction for F frames """
    r = 100 *(1 - abs_ratio)
    run_command('orpos; &get;&vta -dv -A %s_vabs.aig -P 2 -T %d -R %d; &vta_gla;&gla_derive; &put'%(f_name,t,r))
##    write_file('abs')

def gla_abs(t):
    """ Do gate-level abstraction for F frames """
    r = 100 *(1 - abs_ratio)
    run_command('orpos; &get;&gla_cba -C 0 -T %d -F 0 -R %d;  &gla_derive; &put'%(t,r))

def sizeof():
    return [n_pis(),n_pos(),n_latches(),n_ands()]

def abstract(ifb=2):
    global abs_ratio
##    print 'ifb = %d'%ifb
    if ifb == 0: #new way using gate_abs and no bip
        return abstracta(False)
    elif ifb == 1: #old way using ,abs
        assert ifb == ifbip, 'call to abstract has ifb not = global ifbip'
        return abstractb()
    else:
        #new way using ,abs -dwr -- (bip_abs)
        return abstracta(True)

def abstracta(if_bip=True):
    """
    if_bip = 0 it uses a new abstraction based on &vta (gate level abstraction) and no bip operations
    Right now, if we do not prove it with abstraction in the time allowed,
    we abandon abstraction and go on with speculation
    if_bip = 1, we use ,abs -dwr
    """
    global G_C, G_T, latches_before_abs, x_factor, last_verify_time, x, win_list, j_last, sims
    global latches_before_abs, ands_before_abs, pis_before_abs, abs_ratio
##    n_vabs = 0
    latches_before_abs = n_latches()
    ands_before_abs = n_ands()
    pis_before_abs = n_real_inputs()
    tt = time.time()
    print 'using abstracta, ',
##    print 'if_bip = %d'%if_bip
##    latch_ratio = abs_ratio
##    t = 100
    t = 1000 #temporary
    t = abs_time
    if if_bip == 0:
        t = 1000 #timeout on vta
        t = abs_time
    tt = time.time()
    if n_pos() > 1 and if_bip == 0:
        abc('orpos')
        print 'POs ORed together, ',
    initial_size = sizeof()
    abc('w %s_before_abs.aig'%f_name)
    # 25 below means that it will quit if #FF+#ANDS > 75% of original
##    funcs = [eval("(pyabc_split.defer(abc)('orpos;&get;&vta -d -R 25'))")] #right now we need orpos
    if if_bip:
        print 'using bip_abs'
        mtds = ['bip_abs']
        funcs = [eval('(pyabc_split.defer(bip_abs)(t))')]
    else:
        print 'using gate_abs'
        mtds = ['gate_abs']
        funcs = [eval('(pyabc_split.defer(gate_abs)(t))')]
    funcs = funcs + [eval('(pyabc_split.defer(monitor_and_prove)())')]
    J = [34,30]
    if n_ands()> 500000: #if greater than this, bmc_j may take too much memory.
        J = [34]
##    J=[]
    funcs = funcs + create_funcs(J,1000)
    mtds = mtds + ['monitor_and_prove'] + sublist(methods,J)
    print 'methods = ',
    print mtds
    vta_term_by_time=0
    for i,res in pyabc_split.abc_split_all(funcs):
##        print i,res
        if i == 0: #vta ended first
            print 'time taken = %0.2f'%(time.time() - tt)
            if is_sat():
                print 'vta abstraction found cex in frame %d'%cex_frame()
                return Sat
            if is_unsat():
                print 'vta abstraction proved UNSAT'
                return Unsat
            else: #undecided
                if time.time() - tt < .95*t:
                    print 'abstraction terminated but not by timeout'
                    vta_term_by_time = 0
                    break
                else:
                    print 'abstraction terminated by a timeout of %d'%t
##                    print 'final abstraction: ',
##                    ps()
                    vta_term_by_time=1
                    break
        if i == 1: #monitor and prove ended first (sleep timed out)
##            print i,res
            if res > Unsat: #we abandon abstraction
##                print 'final abstraction: ',
##                ps()
##                print 'Trying to verify final abstraction'
##                result = verify([7,9,19,23,24,30],100) #do this if if_bip==0
##                if result == Unsat:
##                    print 'Abstraction proved valid'
##                    return result
##                else:
##                    print 'Abstract time wasted = %0.2f'%(time.time()-tt)
##                    abc('r %s_before_abs.aig'%f_name)
##                    result = Undecided_no_reduction
##                    return result
##            elif res == Undecided_no_reduction:
                print 'monitor and prove timed out or little reduction'
                abc('r %s_before_abs.aig'%f_name)
                return Undecided_no_reduction
            else: 
                if not initial_size == sizeof(): #monitor and prove should not return SAT in this case'
                    assert not is_sat(), 'monitor_and_prove returned SAT on abstraction!' 
                print 'time taken = %0.2f'%(time.time() - tt)
                if is_unsat():
                    return Unsat
                elif is_sat():
                    return Sat
                else:
                    abc('r %s_before_abs.aig'%f_name)
                    return Undecided_no_reduction
        else: #one of the engines got an answer
            print 'time taken = %0.2f'%(time.time() - tt)
            if is_unsat():
                print 'Initial %s proved UNSAT'%mtds[i]
                return Unsat
            if is_sat():
                print 'Initial %s proved SAT'%mtds[i]
                return Sat
            else: # an engine failed here
                print 'Initial %s terminated without result'%mtds[i]
##                return Undecided
                continue
    if  vta_term_by_time == 0 and if_bip == 0: #vta timed out itself
        print 'Trying to verify final abstraction',
        ps()
        result = verify([7,9,19,23,24,30],100)
        if result == Unsat:
            print 'Abstraction proved valid'
            return result
    # should do abstraction refinement here if if_bip==1
    if if_bip == 0:
        print 'abstraction no good - restoring initial simplified AIG'
        abc('r %s_before_abs.aig'%f_name)
        return Undecided_no_reduction
    else:
        if is_sat():
            print 'Found true counterexample in frame %d'%cex_frame()
            return Sat_true
        if is_unsat():
            return Unsat
    ##    set_max_bmc(NBF)
        NBF = bmc_depth()
        print 'Abstraction good to %d frames'%max_bmc
        #note when things are done in parallel, the &aig is not restored!!!
        abc('&r %s_greg.aig; &w initial_greg.aig; &abs_derive; &put; w initial_gabs.aig; w %s_gabs.aig'%(f_name,f_name))
        set_max_bmc(NBF)
        print 'Initial abstraction: ',
        ps()
        abc('w %s_init_abs.aig'%f_name)
        latches_after = n_latches()
    ##    if latches_after >= .90*latches_before_abs: #the following should match similar statement
    ##    if ((rel_cost_t([pis_before_abs, latches_before_abs, ands_before_abs])> -.1) or
    ##        (latches_after >= .75*latches_before_abs)):
        if small_abs(abs_ratio):
            abc('r %s_before_abs.aig'%f_name)
            print "Little reduction!"
            print 'Abstract time wasted = %0.2f'%(time.time()-tt)
            return Undecided_no_reduction
        sims_old = sims
        sims=sims[:1] #make it so that rarity sim is not used since it can't find a cex
        result = abstraction_refinement(latches_before_abs, NBF,abs_ratio)
        sims = sims_old
        if result <= Unsat:
            return result
    ##    if n_latches() >= .90*latches_before_abs:
    ##    if ((rel_cost_t([pis_before_abs, latches_before_abs, ands_before_abs])> -.1) or (latches_after >= .90*latches_before_abs)):
    ##    if rel_cost_t([pis_before_abs,latches_before_abs, ands_before_abs])> -.1:
        if small_abs(abs_ratio): #r is ratio of final to initial latches in absstraction. If greater then True
            abc('r %s_before_abs.aig'%f_name) #restore original file before abstract.
            print "Little reduction!  ",
            print 'Abstract time wasted = %0.2f'%(time.time()-tt)
            result = Undecided_no_reduction
            return result
        #new
        else:
            write_file('abs') #this is only written if it was not solved and some change happened.
        print 'Abstract time = %0.2f'%(time.time()-tt)
    return result

        
def monitor_and_prove():
    """
    monitor and prove. whenever a new vabs is found, try to verify it
    """
    global ifbip
    #write the current aig as vabs.aig so it will be regularly verified at the beginning.
##    print 'Entering monitora_and_prove'
    print ifbip
    run_command('w %s_vabs.aig'%f_name)
    if ifbip == 0:
        run_command('w vabs.aig')
    initial_size = sizeof()
    print 'initial size = ',
    print initial_size
    funcs = [eval('(pyabc_split.defer(read_and_sleep)())')]
    t = 1000 # do not want to timeout verification engines.
    t = abs_time
    J = [9,19,23,24,34] #engines BMC3,PDRMsd,INTRPm,REACHY - engines for first time through when no abstraction
    funcs = funcs + create_funcs(J,t)
    mtds = ['read_and_sleep'] + sublist(methods,J)
    print 'methods = %s'%mtds
    #a return of Undecided means that abstraction might be good and calling routine will check this
    while True:
        time_done = abs_bad = 0
        for i,res in pyabc_split.abc_split_all(funcs):
##            print i,res
            if i == 0: # read and sleep terminated
                if res == False: #found new abstraction
                    abs_bad = 0 #new abs starts out good.
                    if not initial_size == sizeof() and n_latches() > abs_ratio * initial_size[2]:
                        return Undecided_no_reduction
                    else:
                        break
                elif res == True: # read and sleep timed out
                    time_done = 1
##                    print 'read_and_sleep timed out'
                    if abs_bad:
                        return Undecided_no_reduction
                    else: #abs is still good. Let other engines continue
                        return Undecided #calling routine handles >Unsat all the same right now.
                else:
                    assert False, 'something wrong. read and sleep did not return right thing'
            if i > 0: #got result from one of the verify engines
##                print 'method %s found SAT in frame %d'%(mtds[i],cex_frame())
                if is_unsat():
                    print 'Parallel method %s proved UNSAT on current abstraction'%mtds[i]
                    return Unsat
                if is_sat(): #abstraction is not good yet.
                    print 'Parallel method %s found SAT on current abstraction in frame %d'%(mtds[i],cex_frame())
##                    print 'n_vabs = %d'%n_vabs
                    if initial_size == sizeof():# the first time we were working on an aig before abstraction
                        return Sat
##                    print 'current abstraction invalid'
                    abs_bad = 1 
                    break #this kills off other verification engines working on bad abstraction
                else: #one of the engines undecided for some reason - failed?
                    print 'Parallel %s terminated without result on current abstraction'%mtds[i]
                    continue
        if abs_bad and not time_done: #here we wait until have a new vabs.
            print 'current abstraction bad, waiting for new one'
##            print 'waiting for new abstraction'
            abc('r %s_abs.aig'%f_name) #read in the abstraction to destroy is_sat.
            res = read_and_sleep(5) #this will check every 5 sec, until abs_time sec has passed without new abs
            if res == False: #found new vabs. Now continue if vabs small enough
##                print 'n_vabs = %d'%n_vabs
                if (not initial_size == sizeof()) and n_latches() > abs_ratio * initial_size[2]:
                    return Undecided_no_reduction
                else:
                    continue
            elif res ==True: #read_and_sleep timed out
##                print 'read_and_sleep timed out'
                return Undecided_no_reduction
            else:
                break #this should not happen
        elif abs_bad and time_done:
            print 'current abstraction bad, time has run out'
            return Undecided_no_reduction
        elif time_done: #abs is good here
            print 'current abstraction still good, time has run out'
            return Undecided #this will cause calling routine to try to verify the final abstraction
                            #right now handles the same as Undecided_no_reduction-if time runs out we quit abstraction
        else: #abs good and time not done
            print 'current abstraction still good, time has not run out'
            #we want to continue but after first time, we use expanded set of engines.
            funcs = [eval('(pyabc_split.defer(read_and_sleep)())')]
            funcs = funcs + create_funcs(J,t) #use old J first time
            mtds = ['read_and_sleep'] + sublist(methods,J)
            if initial_size == sizeof():
                print 'methods = %s'%mtds
            J = [7,9,19,23,24,30] #first time reflects that 7 and 30 are already being done
            continue #will try with new vabs

def read_and_sleep(t=5):
    """
    keep looking for a new vabs every 5 seconds. This is usually run in parallel with
    &vta -d
    """
    #t is not used at present
    tt = time.time()
    T = 1000 #if after the last abstraction, no answer, then terminate
    T = abs_time
    set_size()
    name = '%s_vabs.aig'%f_name
##    if ifbip > 0:
##        name = '%s_vabs.aig'%f_name
####    print 'name = %s'%name
    while True:
        if time.time() - tt > T: #too much time between abstractions
            print 'read_and_sleep timed out in %d sec.'%T
            return True
        if os.access('%s'%name,os.R_OK):
            abc('r %s'%name)
            abc('w %s_vabs_old.aig'%f_name)
            os.remove('%s'%name)
            if not check_size():
                print '\nNew abstraction: ',
                ps()
                set_size()
                abc('w %s_abs.aig'%f_name)
                return False
            #if same size, keep going.
        print '.',
        sleep(5)
####################################################
