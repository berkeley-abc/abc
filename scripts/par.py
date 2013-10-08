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
global if_no_bip, gabs, gla, sec_options,last_gasp_time, abs_ref_time, bmcs1, total_spec_refine_time
global last_gap

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
RESULT = ('SAT', 'SAT', 'UNSAT', 'UNDECIDED', 'UNDECIDED', 'ERROR')
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
last_gasp_time = 10000
last_gasp_time = 500
last_gasp_time = 900 #set to conform to hwmcc12
use_pms = True

#gabs = False #use the gate refinement method after vta
#abs_time = 100

####################################
#default abstraction methods
gabs = False #False = use gla refinement, True = use reg refinement.
gla = True #use gla_abs instead of vta_abs
##abs_time = 10000 #number of sec before initial abstraction terminates.
abs_time = 150
abs_time = 5000
abs_time = 500
abs_time = 100
abs_ref_time = 50 #number of sec. allowed for abstraction refinement.
total_spec_refine_time = 150
ifbip = 0 # sets the abtraction method to vta or gla, If = 1 then uses ,abs
if_no_bip = False #True sets it up so it can't use bip and reachx commands.
abs_ratio = .5 #this controls when abstraction is too big and gives up
#####################################

def abstr_a(t1=200,t2=200,absr=0):
    global abs_time, abs_ref_time, abs_ratio
    if not absr == 0:
        abs_ratio_old = abs_ratio
        abs_ratio = absr
    abs_time = t1
    abs_ref_time = t2
    abstracta(False)
    if not absr == 0:
        abs_ratio = abs_ratio_old

t_init = 2 #initial time for poor man's concurrency.

def set_global(s=''):
    global G_C,G_T,latches_before_abs,latches_before_pba,n_pos_before,x_factor,methods,last_winner
    global last_cex,JV,JP, cex_list,max_bmc, last_cx, pord_on, trim_allowed, temp_dec, abs_ratio, ifbip
    global if_no_bip, gabs, gla, sec_options,last_gasp_time,abs_ref_time, abs_time,use_pms
    exec(s)


methods = ['PDR', 'INTRP', 'BMC', 'SIM', 'REACHX',
           'PRE_SIMP', 'simple', 'PDRM', 'REACHM', 'BMC3','Min_Retime',
           'For_Retime','REACHP','REACHN','PDR_sd','prove_part_2',
           'prove_part_3','verify','sleep','PDRM_sd','prove_part_1',
           'run_parallel','INTRPb', 'INTRPm', 'REACHY', 'REACHYc','RareSim','simplify', 'speculate',
           'quick_sec', 'BMC_J', 'BMC2', 'extract -a', 'extract', 'PDRa', 'par_scorr', 'dsat', 'iprove']
#'0.PDR', '1.INTERPOLATION', '2.BMC', '3.SIMULATION',
#'4.REACHX', '5.PRE_SIMP', '6.simple', '7.PDRM', '8.REACHM', 9.BMC3'
# 10. Min_ret, 11. For_ret, 12. REACHP, 13. REACHN 14. PDRseed 15.prove_part_2,
#16.prove_part_3, 17.verify, 18.sleep, 19.PDRMm, 20.prove_part_1,
#21.run_parallel, 22.INTRP_bwd, 23. Interp_m 24. REACHY 25. REACHYc 26. Rarity Sim 27. simplify
#28. speculate, 29. quick_sec, 30 bmc3 -S, 31. BMC2 32. extract -a 33. extract 34. pdr_abstract
#35 par_scorr, 36. dsat, 37. iprove
win_list = [(0,.1),(1,.1),(2,.1),(3,.1),(4,.1),(5,-1),(6,-1),(7,.1)]
FUNCS = ["(pyabc_split.defer(pdr)(t))",
##         "(pyabc_split.defer(abc)('&get;,pdr -vt=%f'%t))",
         "(pyabc_split.defer(intrp)(t))",
##         "(pyabc_split.defer(abc)('&get;,imc -vt=%f'%(t)))",
##         "(pyabc_split.defer(abc)('&get;,imc-sofa -vt=%f'%(t)))",
         "(pyabc_split.defer(bmc)(t))",
##         "(pyabc_split.defer(abc)('&get;,bmc -vt=%f'%t))",
         "(pyabc_split.defer(simulate)(t))",
         "(pyabc_split.defer(reachx)(t))",
##         "(pyabc_split.defer(abc)('reachx -t %d'%t))",
         "(pyabc_split.defer(pre_simp)())",
##         "(pyabc_split.defer(super_prove)(2))",
         "(pyabc_split.defer(simple)(t))",
         "(pyabc_split.defer(pdrm)(t))",
         "(pyabc_split.defer(abc)('&get;&reachm -vcs -T %d'%t))",
         "(pyabc_split.defer(bmc3)(t))",
##         "(pyabc_split.defer(abc)('bmc3 -C 1000000 -T %f'%t))",
         "(pyabc_split.defer(abc)('dretime;&get;&lcorr;&dc2;&scorr;&put;dretime'))",
         "(pyabc_split.defer(abc)('dretime -m;&get;&lcorr;&dc2;&scorr;&put;dretime'))",
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
         "(pyabc_split.defer(intrpm)(t))",
##         "(pyabc_split.defer(abc)('int -C 1000000 -F 10000 -K 1 -T %f'%t))",
         "(pyabc_split.defer(reachy)(t))",
##         "(pyabc_split.defer(abc)('&get;&reachy -v -T %d'%t))",
         "(pyabc_split.defer(abc)('&get;&reachy -cv -T %d'%t))",
         "(pyabc_split.defer(simulate2)(t))",
         "(pyabc_split.defer(simplify)())",
         "(pyabc_split.defer(speculate)())",
         "(pyabc_split.defer(quick_sec)(t))",
         "(pyabc_split.defer(bmc_j)(t))",
##         "(pyabc_split.defer(abc)('bmc2 -C 1000000 -T %f'%t))",
         "(pyabc_split.defer(bmc2)(t))",
         "(pyabc_split.defer(extractax)('a'))",
         "(pyabc_split.defer(extractax)())",
         "(pyabc_split.defer(pdra)(t))",
         "(pyabc_split.defer(pscorr)(t))",
         "(pyabc_split.defer(dsat)(t))",
         "(pyabc_split.defer(iprove)(t))"
         ]
##         "(pyabc_split.defer(abc)('bmc3 -C 1000000 -T %f -S %d'%(t,int(1.5*max_bmc))))"
#note: interp given 1/2 the time.

## Similar engines below listed in the order of priority, high to low.
allreachs = [4,8,12,13,24,25]
allreachs = [24,4]
reachs = [24]
##allpdrs = [14,7,34,19,0]
allpdrs = [34,7,14,19,0]
allpdrs2 = [34,7,14,19,0]
pdrs = [34,7,14,0]
allbmcs = [9,30,2,31]
exbmcs = [2,9,31]
bmcs = [9,30]
bmcs1 = [9]
allintrps = [23,1,22]
bestintrps = [23]
##intrps = [23,1]
intrps = [23,1] #putting ,imc-sofa first for now to test
allsims = [26,3]
sims = [26] 
allslps = [18]
slps = [18]
imc1 = [1]
pre = [5]
combs = [36,37]

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
    global n_pos_before, n_pos_proved, last_cx, pord_on, temp_dec, abs_time, gabs, gla,m_trace
    global smp_trace,hist,init_initial_f_name, skip_spec, t_iter_start,last_simp, final_all, scorr_T_done
    global last_gap
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
    smp_trace = m_trace = []
    cex_list = []
    n_pos_before = n_pos()
    n_pos_proved = 0
    abs_time = 150
    abs_ref_time = 50 #number of sec. allowed for abstraction refinement.
    total_spec_refine_time = 150
    abs_ratio = .5
    hist = []
    skip_spec = False
    t_iter_start = 0
    inf = 10000000
    last_simp = [inf,inf,inf,inf]
    final_all = 1
    scorr_T_done = 0
    last_gap = 0
##    abs_time = 100
##    gabs = False
##    abs_time = 500
##    gabs = True

    

def set_abs_method():
    """ controls the way we do abstraction, 0 = no bip, 1 = old way, 2 use new bip and -dwr
    see absab()
    """
    global ifbip, abs_time,gabs,gla,if_no_bip
    print 'current values ifbip = %d, abs_time = %d'%(ifbip,abs_time)
    print 'Set method of abstraction: \n0 = vta for 500 and gla refin., \n1 = old way, \n2 = ,abs and -dwr, \n3 = vta for 100 followed by gla refine.,\n4 = vta for 500 then gla refine. but no bip methods gla refine., \n5 = gla and gla refine.'
    s = raw_input()
    s = remove_spaces(s)
    if s == '1': #use the old way with ,abs but no dwr
        ifbip = 1 #old way
        abs_time = 100
        if_no_bip = False
        gabs = True
        gla = False
    elif s == '0':#use vta and gla refinement
        ifbip = 0 
        abs_time = 500
        if_no_bip = False
        gabs = False
        gla = False
    elif s == '2':  #use ,abc -dwr
        ifbip = 2 
        abs_time = 100
        if_no_bip = False
        gabs = True #use register refinement
        gla = False
    elif s == '3': #use vta and gla refinement
        ifbip = 0
        abs_time = 100
        if_no_bip = False
        gabs = False
        gla = False
    elif s == '4': #use vta, gla refine. and no bip
        ifbip = 0
        abs_time = 100
        if_no_bip = True
        gabs = True
        gla = False
    elif s == '5': #use gla and gla_refinement
        ifbip = 0
        abs_time = 100
        if_no_bip = False
        gabs = False
        gla = True
    #should make any of the methods able to us no bip
    print 'ifbip = %d, abs_time = %d, gabs = %d, if_no_bip = %d, gla = %d'%(ifbip,abs_time,gabs,if_no_bip,gla)
    
def ps():
    print_circuit_stats()

def iprove(t=100):
    abc('iprove')

def dsat(t=100):
    abc('dsat')

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
##    print 'Sleep time = %d'%t
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

##def convert(t):
##    t = int(t*100)
##    return str(float(t)/100)

def set_engines(N=0):
    """
    Called only when read_file is called.
    Sets the MC engines that are used in verification according to
    if there are 4 or 8 processors. if if_no_bip = 1, we will not use any bip and reachx engines
    """
    global reachs,pdrs,sims,intrps,bmcs,n_proc,abs_ratio,ifbip,bmcs1, if_no_bip, allpdrs,allbmcs
    bmcs1 = [9] #BMC3
    #for HWMCC we want to set N = 8
    N = 8
    if N == 0:
        N = n_proc = 1+os.sysconf(os.sysconf_names["SC_NPROCESSORS_ONLN"])
##        N = n_proc = 8 ### simulate 4 processors for HWMCC - turn this off a hwmcc.
    else:
        n_proc = N
##    print 'n_proc = %d'%n_proc
    if N <= 1:
        reachs = [24]
        pdrs = [7]
##        bmcs = [30]
        bmcs = [9]
        intrps = []
        sims = []
        slps = [18]
    elif N <= 2:
        reachs = [24]
        pdrs = [7]
        bmcs = [30]
        intrps = []
        sims = []
        slps = [18]
    elif N <= 4:
        reachs = [24] #reachy
        pdrs = [7,34] #prdm pdr_abstract
        if if_no_bip:
            allpdrs = pdrs = [7,19] #pdrm pdrmm
        bmcs = [9,30] #bmc3 bmc3 -S
        intrps = [23] #unterp_m
        sims = [26] #Rarity_sim
        slps = [18] #sleep
# 0.PDR, 1.INTERPOLATION, 2.BMC, 3.SIMULATION,
# 4.REACHX, 5.PRE_SIMP, 6.simple, 7.PDRM, 8.REACHM, 9.BMC3
# 10.Min_ret, 11.For_ret, 12.REACHP, 13.REACHN 14.PDRseed 15.prove_part_2,
# 16.prove_part_3, 17.verify, 18.sleep, 19.PDRMm, 20.prove_part_1,
# 21.run_parallel, 22.INTRP_bwd, 23.Interp_m 24.REACHY 25.REACHYc 26.Rarity Sim 27.simplify
# 28.speculate, 29.quick_sec, 30.bmc3 -S, 31.BMC2 32.extract -a 33.extract 34.pdr_abstract
# 35.par_scorr, 36.dsat, 37.iprove

# BIPS = 0.PDR, 1.INTERPOLATION, 2.BMC, 14.PDRseed, 22.INTRP_bwd, 34.pdr_abstract
#       also  reparam which uses ,reparam 

    elif N <= 8: #used for HWMCC
        reachs = [24] #REACHY
        allpdrs = pdrs = [7,34,14] #PDRM pdr_abstract PDR_seed
        intrps = [23,1] #Interp_m
        allbmcs = bmcs = [9,30,31] #BMC3 bmc3 -S 
        if if_no_bip:
            allpdrs = pdrs = [7,19] #PDRM PDRMm
            intrps = allintrps = [23] #Interp_m
            bmcs = allbmcs = [2]
        sims = [26] #Rarity_Sim
        slps = [18] #sleep
    else:
        reachs = [24,4] #REACHY REACHX
        pdrs = [7,34,14,19,0] #PDRM pdr_abstract PDR_seed PDRMm PDR
        intrps = [23,1] #Interp_m INTERPOLATION
        bmcs = allbmcs
        if if_no_bip:
            allpdrs = pdrs = [7,19] #PDRM PDRMm
            intrps = allintrps = [23] #Interp_m
            reachs = [24] #REACHY
            bmcs = [9,30] #BMC3 bmc3 -S 
        sims = [26] #Rarity_Sim
        slps = [18] #sleep
        
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

def n_eff_pos():
    N=n_pos()
    l=len(list_0_pos())
    return N-l

def construct(l):
    ll = l
    name = ''
    while len(l)>0:
        name = '_'+ll.pop()+name
    return name[1:]

def process_sat():
    l = seq_name(f_name)

def add_trace(s):
    global m_trace
    m_trace = m_trace + [s] 

def read_file_quiet_i(fname=None):
    """ this preserves t_inter_start and is called internally by some functons."""
    global t_iter_start
    ts = t_iter_start
    read_file_quiet(fname)
    t_iter_start = ts

def read_file_quiet(fname=None):
    """This is the main program used for reading in a new circuit. The global file name is stored (f_name)
    Sometimes we want to know the initial starting name. The file name can have the .aig extension left off
    and it will assume that the .aig extension is implied. This should not be used for .blif files.
    Any time we want to process a new circuit, we should use this since otherwise we would not have the
    correct f_name."""
    global max_bmc,  f_name, d_name, initial_f_name, x_factor, init_initial_f_name, win_list,seed, sec_options
    global win_list, init_simp, po_map, aigs, hist, init_initial_f_name
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
##        run_command('&r %s;&put'%s) #warning: changes names to generic ones.
        run_command('r %s'%s)
        run_command('zero')
    else: #this is a blif file
        run_command('r %s'%s)
        abc('st;&get;&put') #changes names to generic ones for doing cec later.
        run_command('zero;w %s.aig'%f_name)
    set_globals()
    hist = []
    init_initial_f_name = initial_f_name = f_name
    run_command('fold') #only does something if some of the outputs are constraints.
    aigs_pp('push','initial')
    #aigs = create push/pop history of aigs
    #aigs.push() put the initial aig on the aig list.
    print 'Initial f_name = %s'%f_name
    abc('addpi') #only does something if there are no PIs
    #check_pos() #this removes constant outputs with a warning -
    #needed when using iso. Need another fix for using iso.
    ps()
    return

def aigs_pp(op='push', typ='reparam'):
    global hist,init_initial_f_name
##    print hist
    if op == 'push':
        hist.append(typ)
        abc('w %s_aigs_%d.aig'%(init_initial_f_name,len(hist)))
    if op == 'pop':
        abc('cexsave') #protect current cex from a read
        abc('r %s_aigs_%d.aig'%(init_initial_f_name,len(hist)))
        abc('cexload')
        typ = hist.pop()
##    print hist
    return typ

def scl():
    abc('&get;&scl;&put')
    ps()

def cex_trim_g(F_init=0,tail=0,m=''):
    abc('w %s_cex.aig'%f_name)
    N=cex_frame()
    G = N - tail
    F = F_init
    abc('cexsave')
    while True:
        print 'F = %d, G = %d'%(F,G)
        abc('r %s_cex.aig'%f_name)
        abc('cexload')
        if m == '':
            abc('cexcut -F %d -G %d'%(F,G))
        else:
            abc('cexcut -m -F %d -G %d'%(F,G))
##        abc('drw')
##        ps()
        res = run_parallel(slps+bmcs,20)
##        run_command('bmc2 -v -T 20')
##        if is_sat(): #got a shortening of cex
        if not res == Undecided:
            Nb = cex_frame() #size of shortcut
            abc('cexmerge -F %d -G %d'%(F,G))
            abc('r %s_cex.aig'%f_name)
            abc('cexload')
            abc('testcex -a')
            if cex_po() <0:
                return 'ERROR2'
            Nt=cex_frame() #current cex length
            print 'Cex length reduced from %d to %d'%(N,Nt)
            return
        F = F + (G-F)/2
##        G = N - i*delta
        if F >= G:
           return

def cex_trim(factor=1):
    t_begin = time.time()
    abc('w %s_cex.aig'%f_name)
    N=cex_frame()
    inc = min(N/10,100)
    F = 0
    G = inc
    abc('cexsave')
    abc('cexcut -n -F %d -G %d'%(F,G))
    run_command('bmc2 -v -F %d -T 5'%(.9*inc))
    inc = max(int(factor*n_bmc_frames()),2)
    F = N - inc
    G = N
    print 'inc = %d'%inc
    while True:
        abc('r %s_cex.aig'%f_name)
        abc('cexload')
        abc('cexcut -n -F %d -G %d'%(F,G))
##        abc('drw')
##        ps()
##        run_command('bmc2 -v -F %d -T 20'%(.9*inc))
        run_parallel(slps+bmcs,10)
        if not is_sat():
            abc('cex_load') #leave current cex in buffer
            Nb = inc
        else:
            Nb = cex_frame() #size of shortcut
            abc('cexmerge -F %d -G %d'%(F,G))
        abc('r %s_cex.aig'%f_name)
        abc('cexload')
        abc('testcex -a')
        if cex_po() <0:
            return 'ERROR2'
##        abc('cexload')
        Nt=cex_frame() #current cex length
        print 'Cex length = %d'%Nt
        G=F
        F = max(0,F - inc)
        print 'F = %d, G = %d'%(F,G)
        if G <= 2:
            abc('cexload')
            print 'Time: %0.2f'%(time.time() - t_begin) 
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
    abc('zero')

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
    if b > max_bmc:
        max_bmc = b
        report_bmc_depth(max_bmc)
    return max_bmc

def null_status():
    """ resets the status to the default values but note that the &space is changed"""
    abc('&get;&put')

def set_max_bmc(b):
    """ Keeps increasing max_bmc which is the maximum number of time frames for
    which the current circuit is known to be UNSAT for"""
    global max_bmc
    if b > max_bmc:
        max_bmc = b
        report_bmc_depth(max_bmc)

def report_bmc_depth(m):
    print 'u%d'%m

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
##    b = max(max_bmc,bmc_depth()) # don't want to do this because bmc_depth can change max_bmc
    b = max_bmc
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
    abc('&r -s %s;&put'%file)                         

#more complex functions: ________________________________________________________
#, abstract, pba, speculate, final_verify, dprove3

def timer(s):
    btime = time.clock()
    abc(s)
    print 'time = %0.2f'%(time.clock() - btime)

def med_simp():
    x = time.time()
    abc("&get;&scl;&dc2;&lcorr;&dc2;&scorr;&fraig;&dc2;&put;dretime")
    #abc("dc2rs")
    ps()
    print 'time = %0.2f'%(time.time() - x)

def simplify_old(M=0):
    """Our standard simplification of logic routine. What it does depende on the problem size.
    For large problems, we use the &methods which use a simple circuit based SAT solver. Also problem
    size dictates the level of k-step induction done in 'scorr' The stongest simplification is done if
    n_ands < 20000. Then it used the clause based solver and k-step induction where |k| depends
    on the problem size """
    set_globals()
    abc('&get;&scl;&lcorr;&put')
    p_40 = False
    n =n_ands()
    if n >= 70000 and not '_smp' in f_name:
##        abc('&get;&scorr -C 0;&put')
        scorr_T(30)
        ps()
    n =n_ands()
    if n >= 100000:
        abc('&get;&scorr -k;&put')
        ps()
    if (70000 < n and n < 150000):
##        print '1'
        p_40 = True
        abc("&get;&dc2;&put;dretime;&get;&lcorr;&dc2;&put;dretime;&get;&scorr;&fraig;&dc2;&put;dretime")
##        print 2'
        ps()
        n = n_ands()
##        if n<60000:
        if n < 80000:
            abc("&get;&scorr -F 2;&put;dc2rs")
            ps()
        else: # n between 60K and 100K
            abc("dc2rs")
            ps()
    n = n_ands()
##    if (30000 < n  and n <= 40000):
    if (60000 < n  and n <= 70000):
        if not p_40:
            abc("&get;&dc2;&put;dretime;&get;&lcorr;&dc2;&put;dretime;&get;&scorr;&fraig;&dc2;&put;dretime")
            abc("&get;&scorr -F 2;&put;dc2rs")
            ps()
        else:
            abc("dc2rs")
            ps()
    n = n_ands()
##    if n <= 60000:
    if n <= 70000:
        abc('scl -m;drw;dretime;lcorr;drw;dretime')
        ps()
        nn = max(1,n)
        m = int(min( 70000/nn, 16))
        if M > 0:
            m = M
        if m >= 1:
            j = 1
            while j <= m:
                set_size()
                if j<8:
                    abc('dc2')
                else:
                    abc('dc2rs')
                abc('scorr -C 1000 -F %d'%j) #was 5000 temporarily 1000
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

def simplify(M=0,N=0):
    """Our standard simplification of logic routine. What it does depende on the problem size.
    For large problems, we use the &methods which use a simple circuit based SAT solver. Also problem
    size dictates the level of k-step induction done in 'scorr' The stongest simplification is done if
    n_ands < 20000. Then it used the clause based solver and k-step induction where |k| depends
    on the problem size
    Does not change #PIs.
    """
    global smp_trace
    set_globals()
    smp_trace = smp_trace + ['&scl;&lcorr']
    abc('&get;&scl;&lcorr;&put')
    p_40 = False
    n =n_ands()
    if N == 0 and n >= 70000 and not '_smp' in f_name:
##        abc('&get;&scorr -C 0;&put')
##        print 'Trying scorr_T'
        scorr_T(30)
        ps()
    n =n_ands()
    if n >= 100000:
        smp_trace = smp_trace + ['&scorr']
        abc('&get;&scorr -k;&put')
        ps()
    if (70000 < n and n < 150000):
        p_40 = True
        smp_trace = smp_trace + ['&dc2;dretime;&lcorr;&dc2;dretime;&scorr;&fraig;&dc2;dretime']
        abc("&get;&dc2;&put;dretime;&get;&lcorr;&dc2;&put;dretime;&get;&scorr;&fraig;&dc2;&put;dretime")
        ps()
    n = n_ands()
##    if (30000 < n  and n <= 40000):
    if (60000 < n  and n <= 70000):
        if not p_40:
            smp_trace = smp_trace + ['&dc2;dretime;&lcorr;&dc2;dretime;&scorr;&fraig;&dc2;dretime']
            abc("&get;&dc2;&put;dretime;&get;&lcorr;&dc2;&put;dretime;&get;&scorr;&fraig;&dc2;&put;dretime")
            smp_trace = smp_trace + ['&scorr -F 2;dc2rs']
            abc("&get;&scorr -F 2;&put;dc2rs")
            ps()
        else:
            abc("dc2rs")
            smp_trace = smp_trace + ['dc2rs']
            ps()
    n = n_ands()
##    if n <= 60000:
    if n <= 70000:
        smp_trace = smp_trace + ['scl -m;drw;dretime;lcorr;drw;dretime']
        abc('scl -m;drw;dretime;lcorr;drw;dretime')
        ps()
        nn = max(1,n)
        m = int(min( 70000/nn, 16))
        if M > 0:
            m = M
        if N == 0 and m >= 1:
            j = 1
            while j <= m:
                set_size()
                if j<8:
                    abc('dc2')
                else:
                    abc('dc2rs')
                smp_trace = smp_trace + ['scorr -F %d'%j]
                abc('scorr -C 1000 -F %d'%j) #was 5000 temporarily 1000
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
            
def simulate2(t=900):
    """Does rarity simulation. Simulation is restricted by the amount
    of memory it might use. At first wide but shallow simulation is done, followed by
    successively more narrow but deeper simulation. 
    seed is globally initiallized to 113 when a new design is read in"""
    global x_factor, f_name, tme, seed
    btime = time.clock()
    tt = time.time()
    diff = 0
    while True:
        f = 20
        w = 64
        b = 16
        r = 700
        for k in range(9): #this controls how deep we go
            f = min(f*2, 3500)
            w = max(((w+1)/2)-1,1)
            abc('sim3 -F %d -W %d -N %d -R %d -B %d'%(f,w,seed,r,b))
            seed = seed+23
            if is_sat():
##                print 'RareSim time = %0.2f at frame %d'%((time.time() - tt),cex_frame())
                return 'SAT'
            if ((time.clock()-btime) > t):
                return 'UNDECIDED'

def simulate(t=900):
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
            abc('&sim -F %d -W %d -N %d'%(f,w,seed))
            seed = seed+23
            if is_sat():
                return 'SAT'
            if ((time.clock()-btime) > t):
                return 'UNDECIDED'

def generate_abs(n):
    """generates an abstracted  model (gabs) from the greg file or gla. The gabs file is automatically
    generated in the & space by &abs_derive or gla_derive. We store it away using the f_name of the problem
    being solved at the moment. The f_name keeps changing with an extension given by the latest
    operation done - e.g. smp, abs, spec, final, group. """
    global f_name
    #we have a cex and we use this generate a new gabs (gla) file
    if gabs: #use the register refinement method
        abc('&r -s %s_greg.aig; &abs_derive; &put; w %s_gabs.aig'%(f_name,f_name)) # do we still need the gabs file
    else: #use the gate refinement method
        run_command('&r -s %s_gla.aig; &gla_derive; &put'%f_name)
        if n_ands() < 2000:
            run_command('scl;scorr;dretime')
        run_command('w %s_gabs.aig'%f_name)
    if n == 1:
        #print 'New abstraction: ',
        ps()
    return   

def refine_with_cex():
    """Refines the greg or gla file (which contains the original problem with the set of FF's or gates
    that have been abstracted).
    This uses the current cex to modify the greg or gla file to reflect which regs(gates) are in the
    new current abstraction"""
    global f_name
    if gabs:
        abc('&r -s %s_greg.aig;&w %s_greg_before.aig'%(f_name,f_name))
        run_command('&abs_refine -s; &w %s_greg.aig'%f_name)
    else:
        run_command('&r -s %s_gla.aig;&w %s_gla_before.aig'%(f_name,f_name))
        run_command('&gla_refine; &w %s_gla.aig'%f_name)
    return

def refine_with_cex_suffix():
    """Refines the greg or gla file (which contains the original problem with the set of FF's or gates
    that have been abstracted).
    This uses the current cex to modify the greg or gla file to reflect which regs(gates) are in the
    new current abstraction"""
    global f_name
    return Undecided_no_reduction
    t = 5
    cexf = cex_frame()
    suf = .9*cexf
    run_command('write_status %s_temp.status'%f_name)
    ub = int(cexf -min(10, .02*cexf))
    lb = int(min(10,.02*cexf))
    suf = int(.5*(ub-lb))
    if_last = 0
    N = 0
    while True:
        N = N+1
        tt = time.time()
        run_command('read_status %s_temp.status'%f_name)
        print 'Refining using suffix %d with time = %d'%(suf,t)
        run_command('&r -s %s_gla.aig;&w %s_gla_before.aig'%(f_name,f_name))
        F = create_funcs([18],t) #create a timer function with timeout = t
        F = F + [eval('(pyabc_split.defer(abc)("&gla_refine -F %d; &w %s_gla.aig"))'%(suf,f_name))]
        for i,res in pyabc_split.abc_split_all(F): #need to do a binary search
            if i == 0:  #timeout
                lb = int(suf)
                dec = 'increasing'
                break
            elif same_abs(): #suffix did not refine - need to decrease suf
                ub = int(suf)
                dec = 'decreasing'
                break
            else: #refinement happened
                print 'refinement happened.'
                return
        print 'ub = %.2f, lb = %.2f, suf = %.2f'%(ub,lb,suf)
        suf = int(lb+.5*(ub-lb))
        if (ub-lb)< (max(1.1,min(10,.02*cexf))) or if_last or N >=4: # not refining in time allowed, give up
            print '(ub-lb) = %0.2f'%(ub-lb)
            print 'could not refine in resources allowed'
            return Undecided_no_reduction
    
def same_abs():
    run_command('r %s_gabs.aig'%f_name)
    set_size()
##    ps()
    run_command('&r -s %s_gla.aig; &gla_derive; &put'%f_name)
    if n_ands() < 2000:
        run_command('scl;scorr;dretime')
##    ps()
    return check_size()

def abstraction_refinement(latches_before,NBF,ratio=.75):
    """Subroutine of 'abstract' which does the refinement of the abstracted model,
    using counterexamples found by BMC, BDD reachability, etc"""
    global x_factor, f_name, last_verify_time, x, win_list, last_winner, last_cex, t_init, j_last, sweep_time
    global cex_list, last_cx, abs_ref_time
    sweep_time = 2
    T1 = time.time()
    if NBF == -1:
        F = 2000
    else:
        F = 2*NBF
    print '\nIterating abstraction refinement'
    add_trace('abstraction refinement')
    J = slps+intrps+pdrs+bmcs+sims
    J=modify_methods(J)
    print sublist(methods,J)
    last_verify_time = t = x_factor*max(50,max(1,2.5*G_T))
##    t = 1000 #temporary
    t = abs_time
    initial_verify_time = last_verify_time = t
    reg_verify = True
    print 'Verify time set to %d'%last_verify_time
    while True: #cex based refinement
        generate_abs(1) #generate new gabs file from refined greg or gla file
        set_globals()
        latches_after = n_latches()
        if small_abs(ratio):
            print 'abstraction too large'
            return Undecided_no_reduction
        if (time.time() - T1)> abs_ref_time:
            print 'abstraction time ran out'
            break
        t = last_verify_time
        yy = time.time()
        abc('w %s_beforerpm.aig'%f_name)
        rep_change = reparam() #new - must do reconcile after to make cex compatible
##        if rep_change:
##            add_trace('reparam')
        abc('w %s_afterrpm.aig'%f_name)
##        if reg_verify:
        status = verify(J,t)
        print 'status = ',
        print status
##        else:
##            status = pord_1_2(t)
###############
        if status[0] == Sat_true:
            print 'Found true cex'
            reconcile_a(rep_change)
##            add_trace('SAT by %s'%status[1])
            return Sat_true
        if status[0] == Unsat:
##            add_trace('UNSAT by %s'%status[1])      
            return Unsat
        if status[0] == Sat:
##            add_trace('SAT by %s'%status[1])
            abc('write_status %s_after.status'%f_name)
            reconcile_a(rep_change) # makes the cex compatible with original before reparam and puts original in work space
            abc('write_status %s_before.status'%f_name)
            if gabs: #global variable
                refine_with_cex()
            else:
                result = refine_with_cex_suffix()
                if result == Sat:
                    return Sat
##                result = refine_with_cex()
                if result == Undecided_no_reduction:
                    return result
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
##    return ((rel_cost_t([pis_before_abs,latches_before_abs, ands_before_abs])> -.1)
##           or (n_latches() >= ratio*latches_before_abs))
    return (n_latches() >= ratio*latches_before_abs)

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
    abc('&r -s %s_greg.aig; &w initial_greg.aig; &abs_derive; &put; w initial_gabs.aig; w %s_gabs.aig'%(f_name,f_name))
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
        print "Too little reduction!"
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
    if small_abs(abs_ratio) or result == Undecided_no_reduction: #r is ratio of final to initial latches in abstraction. If greater then True
        abc('r %s_before_abs.aig'%f_name) #restore original file before abstract.
        print "Too little reduction!  ",
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
    abc('&r -s pba_temp.aig')
    return n_latches()
        
def pba_loop(F):
    n = n_abs_latches()
    while True:
        run_command('&abs_pba -v -C 0 -F %d'%F)
        abc('&w pba_temp.aig')
        abc('&abs_derive;&put')
        abc('&r -s pba_temp.aig')
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
        read_file_quiet_i('%s'%f_name) #this resets f_name and initial_f_name etc.
        print '\n*************Executing super_prove ************'
        print 'New f_name = %s'%f_name
        result = sp()
        if result[0] == 'SAT':
            result = 'UNDECIDED' #because speculation was done initially.
    elif result[0] == 1:
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
    read_file_quiet_i() #note - reads into & space and then does &put
    ps()
    prs(False)
    ps()
    abc('&w Old.aig')
    print 'Second file: ',
    read_file_quiet_i()
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
        if result[0] == 'SAT':
            result = 'UNDECIDED'
    print 'Total time = %d'%(time.time() - yy)
    return result

def filter(opts):
    global A_name,B_name
##    print 'Filtering with options = %s'%opts
    """ This is for filter which effectively only recognizes options -f -g"""
    if (opts == '' or opts == 'l'): #if 'l' this is used only for initial &equiv2 to get initial equiv creation
        return
    print 'filter = %s  '%opts,
    if opts == 'ab':
        print A_name ,
        print B_name
##        run_command('&ps')
        run_command('&filter -f %s.aig %s.aig'%(A_name,B_name))
        return
####    if not opts == 'f':
####        opts = 'g'
##    print 'filter = %
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
    abc("&srm -A %s_gsrm.aig; r %s_gsrm.aig"%(f_name,f_name))
    print 'Estimated # POs = %d for initial speculation'%n_pos()
    result = n_pos() > max(50,.25*n_latches())
    abc('r check_save.aig')
    abc('&r -s check_and.aig')
    return result

def initial_speculate(sec_opt=''):
    global sec_sw, A_name, B_name, sec_options, po_map
    set_globals()
    if sec_options == '':
        sec_options = sec_opt
    # 1000 - 15, 5000 - 25, 10000 - 30, 50000 - 50
    na = n_ands()
##    t = max(1,G_T)
    if na < 1000:
        t =20
    elif na < 5000:
        t = 20 + ((na-1000)/4000)*20
    elif na < 10000:
        t = 40 + ((na-5000)/5000)*20
    elif na < 50000:
        t = 60 + ((na-40000)/40000)*15
    else:
        t = 75
    r = max(1,int(t))
    rounds = 30*r
    print 'Initial sec_options = %s'%sec_options
##    if sec_options == 'l':
##        cmd = "&get; &equiv3 -lv -F 20 -T %f -R %d -S %d"%(3*t,rounds,rounds/20)
##    else:
##        cmd = "&get; &equiv3 -v -F 20 -T %f -R %d -S %d"%(3*t,rounds,rounds/20)
    cmd = "&get; &equiv3 -v -F 20 -T %d -R %d -S %d"%(int(t),0,0) #####XXX
    print cmd
    abc(cmd)
##    print 'AND space after &equiv3: ',
##    run_command('&ps')
    if (sec_options == 'l'):
        if sec_sw:
            sec_options = 'ab'
        else:
            sec_options = 'f'
##    print 'A_name: ',
##    run_command('r %s.aig;ps'%A_name)
##    print 'B_name: ',
##    run_command('r %s.aig;ps'%B_name)
    print 'filtering'
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
        return sec_options
    else:
##        abc('&r %s_gore.aig; &srm ; r gsrm.aig; w %s_gsrm.aig'%(f_name,f_name))
        cmd = "&srm -A %s_gsrm.aig; r %s_gsrm.aig; &w %s_gore.aig"%(f_name,f_name,f_name)
        print 'Running %s'%cmd
        abc(cmd)
        print 'done with &srm'
        po_map = range(n_pos())
        if sec_options == '' or sec_options == 'g':
##            if n_pos() > 10000:###temp
            if n_eff_pos() > 1000: ##### Temporary
                sec_options = 'g'
                print 'sec_options set to %s'%'g'
                abc('&r -s %s_gore.aig'%f_name)
                filter(sec_options)
##                print 'Running &srm'
                cmd = "&srm -A %s_gsrm.aig; r %s_gsrm.aig; &w %s_gore.aig"%(f_name,f_name,f_name)
##                print 'Running %s'%cmd
                abc(cmd)
                po_map = range(n_pos())
                if n_eff_pos() > 500:
##                if n_pos() > 20000:####temp
                    sec_options = 'f'
                    print 'sec_options set to %s'%'f'
                    abc('&r -s %s_gore.aig'%f_name)
                    filter(sec_options)
                    print 'Running &srm'
                    cmd = "&srm -A %s_gsrm.aig; r %s_gsrm.aig; &w %s_gore.aig"%(f_name,f_name,f_name)
                    print 'Running %s'%cmd
                    abc(cmd)
                    po_map = range(n_pos())
    return sec_options
                
##                    if n_pos() > 2000:
##                        return sec_options
                        
        
def test_against_original():
    '''tests whether we have a cex hitting an original PO'''
    abc('&w %s_save.aig'%f_name) #we preserve whatever was in the & space
    abc('&r -s %s_gore.aig'%f_name) #This is the original
    abc('testcex') #test the cex against the &space
    PO = cex_po()
##    print 'test_against original gives PO = %d'%PO 
    abc('&r -s %s_save.aig'%f_name)
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
    print '2. cex PO = %d'%PO
    cx = cex_get()
    if PO > -1:
        if test_against_original(): #this double checks that it is really an original PO
            cex_put(cx)
            print 'test_against_original was valid'
            return PO
        else:
            print '1. PO is not valid'
            return -1 #error
    if PO < 0 or PO >= (n_pos_before - n_pos_proved): # not a valid cex because already tested outside original.
##        print 'cex_po = %d, n_pos_before = %d, n_pos_proved = %d'%(PO, n_pos_before, n_pos_proved)
        print '2. PO is not valid'
        PO = -1 #error
##    print '3. cex PO = %d'%PO
    return PO

def cex_stats():
    print 'cex_pis = %d, cex_regs = %d, cex_po = %d, cex_frame = %d'%(n_cex_pis(),n_cex_regs(),cex_po(),cex_frame())

def speculate(t=0):
    """Main speculative reduction routine. Finds candidate sequential equivalences and refines them by simulation, BMC, or reachability
    using any cex found. """    
    global G_C,G_T,n_pos_before, x_factor, n_latches_before, last_verify_time, trim_allowed, n_pos_before
    global t_init, j_last, sec_sw, A_name, B_name, sec_options, po_map, sweep_time, sims, cex_list, n_pos_proved,ifpord1
    global last_cx, total_spec_refine_time, skip_spec
##    print 'sec_options = %s'%sec_options
    if skip_spec:
        return Undecided_no_reduction
    add_trace('speculate')
    if t > 0:
        total_spec_refine_time = t
    abc('scl') #make sure no dangling flops
    abc('orpos')
    last_cx = 0
    ifpord1 = 1
    initial_po_size = last_srm_po_size = n_pos()
    initial_sizes = [n_pis(),n_pos(),n_latches(),n_ands()]
    if sec_sw:
        print 'A_name = %s, B_name = %s, f_name = %s, sec_options = %s'%(A_name, B_name, f_name, sec_options)
    elif n_ands()> 36000 and sec_options == '':
##        add_trace('sec options g')
        sec_options = 'g'
        print 'sec_options set to "g"'
##        add_trace('sec_options ="g"')
        
    def refine_with_cex():
        """Refines the gore file to reflect equivalences that go away because of cex"""
        global f_name
        abc('write_status %s_before_refine.status'%f_name)
        abc('&r -s %s_gore.aig; &resim -m'%f_name)
##        run_command('&ps')
##        cex_stats()
        filter(sec_options)
        run_command('&w %s_gore.aig'%f_name)
        return

    def refine_without_cex(L=[]):
        """removes the POs in the current SRM in the list L. Alters the equivalence classes in the
            gore file accordingly.
        """
        global f_name
        if L == []:
            return
        print 'Entered refine_without_cex'
        abc('write_status %s_before_refine.status'%f_name)
        create_abc_array(L)
        print 'wrote array'
        abc('&r -s %s_gore.aig; &equiv_filter'%f_name)
        print 'filtered gore using L'
        filter(sec_options)
        print 'filtered with %s'%sec_options
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
    def retry(t):
        add_trace('retrying')
        print 'retrying winner cex which did not refine'
        abc('r %s_gsrm_before.aig'%f_name) #restore previous gsrm
        abc('w %s_beforerpm.aig'%f_name)
        rep_change = reparam() #must be paired with reconcile below if cex
        if rep_change:
            add_trace('reparam')
        abc('w %s_afterrpm.aig'%f_name)
        if last_winner == 'RareSim':
            simulate2(t)
        elif last_winner == 'PDR':
            pdr(t)
        elif last_winner == 'BMC':
            bmc(t)
        elif last_winner == 'INTRP':
            intrp(t)
        elif last_winner == 'PDRM':
            pdrm(t)
        elif last_winner == 'BMC3':
            bmc3(t)
        elif last_winner == 'PDR_sd':
            pdrseed(t)
        elif last_winner == 'PDRM_sd':
            pdrmm(t)
        elif last_winner == 'INTRPm':
            intrpm(t)
        elif last_winner == 'REACHY':
            reachy(t)
        elif last_winner == 'BMC_J':
            bmc_j(t)
        elif last_winner == 'PDRa':
            pdra(t)
        else:
            reconcile(rep_change)
            return False
        reconcile(rep_change)
        if not is_sat():
            return False
        abc('&r -s %s_gore_before.aig ;&w %s_gore.aig'%(f_name,f_name)) #restore old gore file
        return True
    
    def generate_srm():
        """generates a speculated reduced model (srm) from the gore file"""
        global f_name, po_map, sec_sw, A_name, B_name, sec_options, n_pos_proved
##        print 'Generating'
        pos = n_pos()
        ab = n_ands()
        abc('w %s_oldsrm.aig'%f_name) #save for later purposes
        if sec_sw:
            run_command('&r -s %s_gore.aig; &srm2 -%s %s.aig %s.aig; r gsrm.aig; w %s_gsrm.aig'%(f_name,sec_options,A_name,B_name,f_name))
        else:
            abc('&r -s %s_gore.aig; &srm -A %s_gsrm.aig ; r %s_gsrm.aig'%(f_name,f_name,f_name)) #do we still need to write the gsrm file
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
    print 'sec_options = %s'%sec_options 
    funcs = [eval('(pyabc_split.defer(initial_speculate)("%s"))'%sec_options)]
    funcs = create_funcs(J,10000)+funcs #want other functins to run until initial speculate stops
    mtds = sublist(methods,J) + ['initial_speculate'] #important that initial_speculate goes last
    print mtds
    res = fork_last(funcs,mtds)
    print 'init_spec return = ',
    print res
    if res[1] in ['f','g','']:
        sec_options = res[1]
    add_trace('sec_options = %s'%sec_options)
    add_trace('Number of POs: %d'%n_pos())
##    ps()
    if is_unsat():
        return Unsat
    if is_sat():
        return Sat_true
    if n_pos_before == n_pos():
        print 'No new outputs. Quitting speculate'
        add_trace('de_speculate')
        return Undecided_no_reduction # return result is unknown
    if n_eff_pos() > 1999000:
        print 'Too many POs'
        add_trace('de_speculate')
        return Undecided_no_reduction
    print 'Initial speculation: ',
    ps()
    abc('w %s_initial_gsrm.aig'%f_name)
    if n_pos() > 1000:
        print 'Too many new outputs. Quitting speculate'
        add_trace('de_speculate')
        return Undecided_no_reduction # return result is unknown
    if n_pos() <= n_pos_before + 2:
        print 'Too few new outputs. Quitting speculate'
        add_trace('de_speculate')
        return Undecided_no_reduction # return result is unknown
    if n_latches() == 0:
        return check_sat()
    if use_pms:
        p,q,r=par_multi_sat(0)
        q = indices(r,1)
        print sumsize(r)
        if count_less(r,1) < .25*len(r):
            print 'too many POs are already SAT'
            add_trace('de_speculate')
            return Undecided_no_reduction
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
    add_trace('speculative refinement')
    print '\nIterating speculation refinement'
    sims_old = sims
    sims = sims[:1] 
    J = slps+sims+pdrs+intrps+bmcs
    J = modify_methods(J)
##    print sublist(methods,J)
    t = max(50,max(1,2*G_T))
    last_verify_time = t
    ### temp
    last_verify_time = total_spec_refine_time
    ###
    print 'Verify time set to %d'%last_verify_time
    reg_verify = True
    ref_time = time.time()
    sweep_time = 2
    ifpord1=1
    par_verify = re_try = False
##    total_spec_refine_time = 150
    while True: ##################### refinement loop
        set_globals()
        yy = time.time()
        time_used = (yy-ref_time)
        print 'Time_used = %0.2f'%time_used
        if time_used > total_spec_refine_time:
            print 'Allotted speculation refinement time is exceeded'
            add_trace('de_speculate')
            return Undecided_no_reduction
        if not init:
            abc('r %s_gsrm.aig'%f_name) #this is done only to set the size of the previous gsrm.
            abc('w %s_gsrm_before.aig'%f_name)
            set_size()
            result = generate_srm()
            if n_pos() <= n_pos_before + 1: #heuristic that if only have one equivalence, then not worth it
                abc('r %s.aig'%f_name) #revert to previous aig
                sims = sims_old
                print 'UNDECIDED'
                print 'Refinement time = %0.2f'%(time.time() - ref_time)
                add_trace('de_speculate')
                return Undecided_no_reduction 
            last_srm_po_size = n_pos()
            yy = time.time()
            # if the size of the gsrm did not change after generating a new gsrm
            # and if the cex is valid for the gsrm, then the only way this can happen is if
            # the cex_po is an original one.
            if check_size(): #same size before and after
                if check_cex(): #valid cex failed to refine possibly
                    if 0 <= cex_po() and cex_po() < (n_pos_before - n_pos_proved): #original PO
                        print 'Found cex in original output number = %d'%cex_po()
                        print 'Refinement time = %0.2f'%(time.time() - ref_time)
                        return Sat_true
                    elif check_same_gsrm(f_name): #if two gsrms are same, then failed to refine
                        print 'CEX failed to refine'
                        add_trace('de_speculate')
                        return Error
                else:
                    print 'not a valid cex'
                    print 'Last winner = %s'%last_winner
                    print 're_try = %d'%re_try
                    if re_try:
                        add_trace('de_speculate')
                        return Error #abort speculation
                    re_try = True
            else:
                re_try = False # just got a valid refinement so reset.
            if n_latches() == 0:
                print 'Number of latches reduced to 0'
                print 'CEX refined incorrectly'
                abc('r %s.aig'%f_name) #revert to previous aig
                sims = sims_old
                add_trace('de_speculate')
                return Error
        init = False # make it so that next time it is not the first time through
        if not t == last_verify_time: # heuristic that if increased last verify time,
                                      # then try pord_all 
            t = last_verify_time
            if reg_verify:
                t_init = (time.time() - yy)/2 #start poor man's concurrency at last cex fime found
                t_init = min(10,t_init)
                t = last_verify_time
                print 'Verify time set to %d'%t
        if not re_try:
##            abc('w %s_beforerpm.aig'%f_name)
##            rep_change = reparam() #must be paired with reconcile below if cex
####            if rep_change:
####                add_trace('reparam')
##            abc('w %s_afterrpm.aig'%f_name)
            rep_change = False #TEMP
            if reg_verify:
                if par_verify:
                    S,L_sat_POs,s = par_multi_sat(120)
                    L_sat_POs = indices(s,1)
##                    L_sat_POs = L[1]
                    L=[]
                    for j in range(len(L_sat_POs)): #eliminate any of the original POs
                        if L_sat_POs[j] >= (n_pos_before-n_pos_proved):
                            L=L+[L_sat_POs[j]]
                    L_sat_POs = L
                    print L
                    if not L_sat_POs == []:
                        ress = [1,[['multi_sat']]]
                        add_trace(['multi_sat'])
                    else:
                        reg_verify = False
                        ress = pord_1_2(t)
                        add_trace(ress[1])
                else:
                    ttt = time.time() #find time it takes to find a cex
                    ress = verify(J,t)
                    t_last_verify = time.time() - ttt
            else:
                ress = pord_1_2(t)
##                print ress
                add_trace(ress[1])
            result = ress[0]
##            add_trace(ress[1])
        else:
            if not retry(100):
                add_trace('de_speculate')
                return Error
            result = get_status()
##        print result
        if result == Unsat:
            add_trace('UNSAT by %s'%ress[1])
            print 'UNSAT'
            print 'Refinement time = %0.2f'%(time.time() - ref_time)
            return Unsat
        if result < Unsat:
            abc('&r -s %s_gore.aig;&w %s_gore_before.aig'%(f_name,f_name)) #we are making sure that none of the original POs fail
            if par_verify:
                refine_without_cex(L_sat_POs)
                print 'refining without cex done'
                continue
            if not reg_verify:
                set_cex(cex_list)
##            if not re_try:
####                rec = reconcile(rep_change) #end of pairing with reparam()TEMP
####                if rec == 'error':
####                    add_trace('de_speculate')
####                    return Error
##                assert (npi == n_cex_pis()),'ERROR: #pi = %d, #cex_pi = %d'%(npi,n_cex_pis())
            abc('&r -s %s_gore.aig;&w %s_gore_before.aig'%(f_name,f_name)) #we are making sure that none of the original POs fail
            if reg_verify:
                PO = set_cex_po(0) #testing the regular space
            else:
                abc('&r -s %s_gsrm.aig'%f_name)
                PO = set_cex_po(1) # test against the &space.
            print 'cex_PO is %d,  '%PO,
            if (-1 < PO and PO < (n_pos_before-n_pos_proved)):
                print 'Found cex in original output = %d'%cex_po()
                print 'Refinement time = %0.2f'%(time.time() - ref_time)
                return Sat_true
            if PO == -1:
                add_trace('de_speculate')
                return Error
            refine_with_cex()    #change the number of equivalences
            if not par_verify and t_last_verify > 2500:
                par_verify = True #switch to finding many POs at a time
            continue
        elif (is_unsat() or n_pos() == 0):
            print 'UNSAT'
            print 'Refinement time = %0.2f'%(time.time() - ref_time)
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
                ress = pord_1_2(t) #main call to verification
                print ress
                result = ress[0]
                add_trace(ress[1])
                if result == Unsat:
                    print 'UNSAT'
                    print 'Refinement time = %0.2f'%(time.time() - ref_time)
                    return Unsat
                if is_sat() or result == Sat:
##                    assert result == get_status(),'result: %d, status: %d'%(result,get_status())
                    print 'result: %d, status: %d'%(result,get_status())
                    set_cex(cex_list)
                    rec = reconcile(rep_change)
                    if rec == 'error':
                        add_trace('de_speculate')
                        return Error
                    abc('&r -s %s_gsrm.aig'%f_name)
                    PO = set_cex_po(1) #testing the & space
                    if (-1 < PO and PO < (n_pos_before-n_pos_proved)):
                        print 'Found cex in original output = %d'%cex_po()
                        print 'Refinement time = %0.2f'%(time.time() - ref_time)
                        return Sat_true
                    if PO == -1:
                        add_trace('de_speculate')
                        return Error
                    refine_with_cex()    #change the number of equivalences
                    continue
                else: #if undecided, record last verification time
                    last_verify_time = t
                    print 'UNDECIDED'
                    break
            ################### added
            else:
                break
    sims = sims_old
    print 'UNDECIDED'
    print 'Refinement time = %0.2f'%(time.time() - ref_time)
##    if last_srm_po_size == initial_po_size: #essentially nothing happened. last_srm_po_size will be # POs in last srm.
    if initial_sizes == [n_pis(),n_pos(),n_latches(),n_ands()]:
        abc('r %s.aig'%f_name)
        add_trace('de_speculate')
        return Undecided_no_reduction #thus do not write spec file
    else: #file was changed, so some speculation happened. If we find a cex later, need to know this.
        write_file('spec')
        return Undecided_reduction

def simple_sat(t=900):
    """
    aimed at trying harder to prove SAT
    """
    y = time.time()
    bmcs2 = [9,31]
    bmcs2 = [9,30]
    J = allbmcs+pdrs+sims+[5]
##    J = modify_methods(J)
##    J = [14,2,7,9,30,31,26,5] #5 is pre_simp
    funcs = create_funcs(J,t)
    mtds =sublist(methods,J)
    print mtds
    fork_last(funcs,mtds)
    result = get_status()
    if result > Unsat:
        write_file('smp')
        result = verify(slps+allbmcs+pdrs+sims,t)
    print 'Time for simple_sat = %0.2f'%(time.time()-y)
    report_bmc_depth(max(max_bmc,n_bmc_frames()))
    return [RESULT[result[0]]] + [result[1]]

def simple(t=10000,no_simp=0):
    y = time.time()
##    pre_simp()
    if not no_simp:
        prove_part_1()
        if is_sat():
            return ['SAT']+['pre_simp']
        if is_unsat():
            return ['UNSAT']+['pre_simp']
        if n_latches() == 0:
            return [RESULT[check_sat()]]+['pre_simp']
##    J = slps+sims+bmcs+pdrs+intrps+pre
    J = slps+sims+allbmcs+allpdrs+intrps
    J = modify_methods(J)
    result = verify(J,t)
##    add_pord('%s by %s'%(result[0],result[1])
    return [RESULT[result[0]]] + [result[1]]

def simple_bip(t=1000):
    y = time.time()
    J = [0,14,1,2,30,5] #5 is pre_simp
    funcs = create_funcs(J,t)
    mtds =sublist(methods,J)
    fork_last(funcs,mtds)
    result = get_status()
    if result > Unsat:
        write_file('smp')
        result = verify(slps+[0,14,1,2,30],t)
    print 'Time for simple_bip = %0.2f'%(time.time()-y)
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
    abc('read_status %s_before_refine.status'%f_name)
    abc('&r -s %s_gsrm_before.aig'%f_name)
##    abc('&r %s_gsrm.aig'%f_name)
    run_command('testcex') #test the cex against the &-space aig.
##    print 'cex po = %d'%cex_po()
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

##def quick_verify(n):
##    """Low resource version of final_verify n = 1 means to do an initial
##    simplification first. Also more time is allocated if n =1"""
##    global last_verify_time
##    trim()
##    if n == 1:
##        simplify()
##        if n_latches == 0:
##            return check_sat()
##        trim()
##        if is_sat():
##            return Sat_true
##    #print 'After trimming: ',
##    #ps()
##    set_globals()
##    last_verify_time = t = max(1,.4*G_T)
##    if n == 1:
##        last_verify_time = t = max(1,2*G_T)
##    print 'Verify time set to %d '%last_verify_time
##    J = [18] + intrps+bmcs+pdrs+sims
##    status = verify(J,t)
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

def two_temp(t=20):
    tt = time.time()
    abc('tempor;scl;drw;&get;&rpm;&put;tempor;scl;drw;&get;&rpm;&put;scorr')
    print 'Time for two_temp = %.2f'%(time.time()-tt)
    return get_status()

def reparam_m():
    """eliminates PIs which if used in abstraction or speculation must be restored by
    reconcile and the cex made compatible with file beforerpm
    Uses the &-space
    """
    abc('w %s_temp.aig'%f_name)
    n = n_pis()
    t1 = time.time()
##    abc('&get;,reparam -aig=%s_rpm.aig; r %s_rpm.aig'%(f_name,f_name))
    abc('&get;&rpm;&put')
    tm = (time.time() - t1)
    if n_pis() == 0:
        print 'Number of PIs reduced to 0. Added a dummy PI'
        abc('addpi')
    nn = n_pis()
    if nn < n:
        print 'Reparam_m: PIs %d => %d, time = %.2f'%(n,nn,tm)
        rep_change = True
    else:
        abc('r %s_temp.aig'%f_name)
        rep_change = False
    return rep_change

def reparam_e():
    """eliminates PIs which if used in abstraction or speculation must be restored by
    reconcile and the cex made compatible with file beforerpm
    Uses the &-space
    """
    abc('w %s_temp.aig'%f_name)
    n = n_pis()
    t1 = time.time()
    abc('&get;,reparam -aig=%s_rpm.aig; r %s_rpm.aig'%(f_name,f_name))
##    abc('&get;&rpm;&put')
    tm =(time.time() - t1)
    if n_pis() == 0:
        print 'Number of PIs reduced to 0. Added a dummy PI'
        abc('addpi')
    nn = n_pis()
    if nn < n:
        print 'Reparam_e: PIs %d => %d, time = %.2f'%(n,nn,tm)
        rep_change = True
    else:
        abc('r %s_temp.aig'%f_name)
        rep_change = False
    return rep_change

def reparam():
##    abc('w %s_temp.aig'%f_name)
##    res = reparam_e()
##    res = reparam_m()
    res = reparam_e()
    return res

##def try_and_rpm():
##    abc('w %s_temp.aig'%f_name)
##    n = n_pis()
##    t1 = time.time()
##    abc('&get;&rpm;&put')
##    print 'time &rpm = %.2f'%(time.time() - t1)
##    if n_pis() == 0:
##        print '&rpm: Number of PIs reduced to 0. Added a dummy PI'
##        abc('addpi')
##    nn = n_pis()
##    if nn < n:
##        print '&rpm: Reparam: PIs %d => %d'%(n,nn)
####        rep_change = True
##    abc('r %s_temp.aig'%f_name)
####    else:
####        abc('r %s_temp.aig'%f_name)
####        return False

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
    abc('&r -s %s_beforerpm.aig; &w tt_before.aig'%f_name)
    abc('write_status %s_after.status;write_status tt_after.status'%f_name)
    abc('&r -s %s_afterrpm.aig;&w tt_after.aig'%f_name)
    POa = set_cex_po(1)   #this should set cex_po() to correct PO. A 1 here means it uses &space to check
    abc('reconcile %s_beforerpm.aig %s_afterrpm.aig'%(f_name,f_name))
    # reconcile modifies cex and restores work AIG to beforerpm
    abc('write_status %s_before.status;write_status tt_before.status'%f_name)
    POb = set_cex_po()#does not make sense if we are in absstraction refinement
    if POa != POb:
        abc('&r -s %s_beforerpm.aig; &w tt_before.aig'%f_name)
        abc('&r -s %s_afterrpm.aig; &w tt_after.aig'%f_name)
        print 'cex PO afterrpm = %d not = cex PO beforerpm = %d'%(POa,POb)
    if POa < 0: #'cex did not assert any output'
        return 'error'

def reconcile_a(rep_change):
    """ This is the reconcile used in abstraction refinement
    used to make current cex compatible with file before reparam() was done.
    However, the cex may have come
    from extracting a single output and verifying this.
    Then the cex_po is 0 but the PO it fails could be anything.
    So testcex rectifies this."""
    global n_pos_before, n_pos_proved
##    print 'rep_change = %s'%rep_change
    if rep_change == False:
        return
    abc('&r -s %s_beforerpm.aig; &w tt_before.aig'%f_name)
    abc('write_status %s_after.status;write_status tt_after.status'%f_name)
    abc('&r -s %s_afterrpm.aig;&w tt_after.aig'%f_name)
    POa = set_cex_po(1)   #this should set cex_po() to correct PO. A 1 here means it uses &space to check
    abc('reconcile %s_beforerpm.aig %s_afterrpm.aig'%(f_name,f_name))
    # reconcile modifies cex and restores work AIG to beforerpm
    abc('write_status %s_before.status;write_status tt_before.status'%f_name)
    if POa < 0: #'cex did not assert any output'
        return 'error'

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
    

##def try_rpm():
##    """rpm is a cheap way of doing reparameterization and is an abstraction method, so may introduce false cex's.
##    It finds a minimum cut between the PIs and the main sequential logic and replaces this cut by free inputs.
##    A quick BMC is then done, and if no cex is found, we assume the abstraction is valid. Otherwise we revert back
##    to the original problem before rpm was tried."""
##    global x_factor
##    if n_ands() > 30000:
##        return
##    set_globals()
##    pis_before = n_pis()
##    abc('w %s_savetemp.aig'%f_name)
##    abc('rpm')
##    result = 0
##    if n_pis() < .5*pis_before:
##        bmc_before = bmc_depth()
##        #print 'running quick bmc to see if rpm is OK'
##        t = max(1,.1*G_T)
##        #abc('bmc3 -C %d, -T %f'%(.1*G_C, t))
##        abc('&get;,bmc -vt=%f'%t)
##        if is_sat(): #rpm made it sat by bmc test, so undo rpm
##            abc('r %s_savetemp.aig'%f_name)
##        else:
##            trim()
##            print 'WARNING: rpm reduced PIs to %d. May make SAT.'%n_pis()
##            result = 1
##    else:
##        abc('r %s_savetemp.aig'%f_name)
##    return result
            
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
##    result = fork_break(F,mtds,'US') #FORK here
    print result
##    assert result[0] == get_status(),'result: %d, status: %d'%(result[0],get_status())
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
        abc('r %s.aig'%f_name)
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
            
def check_sat(t=900):
    """This is called if all the FF have disappeared, but there is still some logic left. In this case,
    the remaining logic may be UNSAT, which is usually the case, but this has to be proved. The ABC command 'dsat' is used fro combinational problems"""
    global smp_trace
    if not n_latches() == 0:
        print 'circuit is not combinational'
        return Undecided
##    print 'Circuit is combinational - checking with dsat'
    abc('&get') #save the current circuit
    abc('orpos')
    J = combs+slps
    mtds = sublist(methods,J)
##    print mtds
    F = create_funcs(J,t)
    (m,result) = fork_last(F,mtds) #FORK here
##    print '%s: '%mtds[m],
##    smp_trace = smp_trace + ['%s'%mtds[m]]
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
        
def smp():
    abc('smp')
    write_file('smp')

def dprove():
    abc('dprove -cbjupr')

def trim():
    global trim_allowed,smp_trace
    if not trim_allowed:
        return False
    result = reparam()
    return result

def prs(x=True):
    global trim_allowed, smp_trace
    """ If x is set to False, no reparameterization will be done in pre_simp"""
    global smp_trace
    smp_trace = []
    trim_allowed = x
    print 'trim_allowed = ',trim_allowed
    y = time.time()
    result = pre_simp()
    print 'Time = %0.2f'%(time.time() - y)
    write_file('smp')
    return RESULT[result[0]]

def check_push():
    """save the current aig if it has a different number of latches from last aig on lst"""
    result = False
    n = n_latches()
##    ps()
    abc('&get;cexsave') #save the current aig
##    typ = hist[-1:]
##    print hist
    run_command('r %s_aigs_%d.aig'%(init_initial_f_name,len(hist)))
##    typ = aigs_pp('pop')
##    aigs.pop() #check latches in last aig.
    nn = n_latches()
##    ps()
##    aigs.push() # put back last aig.
##    aigs_pp('push',typ)
    abc('&put;cexload') # restore current aig
##    print 'check_push: current n=%d, previous nn=%d'%(n,nn)
    if not n == nn: #if number of latches changes need to push the current aig so that reconcile can work.
##        aigs.push()
##        print 'n /= nn'
        aigs_pp('push','reparam0') #default is push,reparam
        result = True
    return result

def dump():
    """ get rid of the last aig on the list"""
    abc('&get')
##    aigs.pop()
    aigs_pp('pop')
    abc('&put')

def test_no_simp():
    global last_simp
    ri = float(n_pis())/float(last_simp[0])
    ro = float(n_pos())/float(last_simp[1])
    rl = float(n_latches())/float(last_simp[2])
    ra = float(n_ands())/float(last_simp[3])
    val = min(ri,ro,rl,ra)
    if val < .95:
        print 'simplification worthwhile'
        return False
    print 'simplification not worthwhile'
    return True
        
def pre_simp(n=0,N=0):
    """This uses a set of simplification algorithms which preprocesses a design.
    Includes forward retiming, quick simp, signal correspondence with constraints, trimming away
    PIs, and strong simplify. If n not 0, then do not do phase abs"""
    global trim_allowed, temp_dec
    global smp_trace, aigs, last_simp
    chk_sat = 0
    smp_trace = []
    while True:
        if n_latches() == 0:
            print 'Circuit is combinational'
            chk_sat = 1
            break
        if test_no_simp():
            break
        ttime = time.time()
        set_globals()
        smp_trace = smp_trace + ['&scl']
        abc('&get; &scl; &put')
        if (n_ands() > 200000 or n_latches() > 50000 or n_pis() > 40000):
            smp_trace = smp_trace + ['scorr_T']
            scorr_T(50)
            ps()
        if ((n_ands() > 0) or (n_latches()>0)):
            res =a_trim()
        if n_latches() == 0:
            break
        status = get_status()
        if (n == 0 and (not '_smp' in f_name) or '_cone' in f_name):
            best_fwrd_min([10,11])
            ps()
            status = try_scorr_constr()
        if ((n_ands() > 0) or (n_latches()>0)):
            res = a_trim()
        if n_latches() == 0:
            break
        status = process_status(status)
        if status <= Unsat:
            last_simp = [n_pis(),n_pos(),n_latches(),n_ands()]
            return [status,smp_trace,hist]
        print 'Starting simplify ',
        simplify(n,N)
        print 'Simplify: ',
        ps()
        if n_latches() == 0:
            break
        if trim_allowed and n == 0:
            t = min(15,.3*G_T)
            if (not '_smp' in f_name) or '_cone' in f_name: #try this only once on a design
                tt = 25
                if n_ands() > 500000:
                    tt = 30
                res,F = try_temps(tt) 
                if res:
                    aigs_pp('push','tempor')
                if n_latches() == 0:
                    break
                if n == 0: 
                    res,N = try_phases()
                    if res:
                        aigs_pp('push','phase')
                if n_latches() == 0:
                    break
            if ((n_ands() > 0) or (n_latches()>0)):
                res = a_trim()
        status = process_status(status)
        print 'Simplification time = %0.2f'%(time.time()-ttime)
        last_simp = [n_pis(),n_pos(),n_latches(),n_ands()]
        return [status, smp_trace,hist]
    last_simp = [n_pis(),n_pos(),n_latches(),n_ands()]
    return [check_sat(),smp_trace,hist]


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
    s = map(lambda m:m*n_ands()< 120000,sp)
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

def try_phases():
####    print 'entered try_phases ',
##    ps()
    no = n_pos()
    res = try_phase()
##    print 'after try_phase ',
##    ps()
    N = n_pos()/no
    if N > 1:
        res = True
    else:
        res = False
    return res,N

def try_phase():
    """Tries phase abstraction. ABC returns the maximum clock phase it found using n_phases.
    Then unnrolling is tried up to that phase and the unrolled model is quickly
    simplified (with retiming to see if there is a significant reduction.
    If not, then revert back to original"""
    global init_simp, smp_trace,aigs
    n = n_phases()
##    if ((n == 1) or (n_ands() > 45000) or init_simp == 0):
    if ((n == 1) or (n_ands() > 60000)):
        return False
##    init_simp = 0
    res = a_trim()
    print 'Trying phase abstraction - Max phase = %d'%n,
    abc('w %s_phase_temp.aig'%f_name)
    na = n_ands()
    nl = n_latches()
    ni = n_pis()
    no = n_pos()
    z = ok_phases(n)
    print z,
    if len(z) == 1:
        return False
    #p = choose_phase()
    p = z[1]
    abc('phase -F %d'%p)
    if no == n_pos(): #nothing happened because p is not mod period
        print 'Phase %d is incompatible'%p
        abc('r %s_phase_temp.aig'%f_name)
        if len(z)< 3:
            return False
        else:
            p = z[2]
            #print 'Trying phase = %d:  '%p,
            abc('phase -F %d'%p)
            if no == n_pos(): #nothing happened because p is not mod period
                print 'Phase %d is incompatible'%p
                abc('r %s_phase_temp.aig'%f_name)
                return False
            else:
                smp_trace = smp_trace + ['phase -F %d'%p]
                abc('r %s_phase_temp.aig'%f_name)
                abc('&get;&frames -o -F %d;&scl;&put'%p)
    else:
        abc('r %s_phase_temp.aig'%f_name)
        abc('&get;&frames -o -F %d;&scl;&put'%p)
        smp_trace = smp_trace + ['phase -F %d'%p]
    print 'Simplifying with %d phases: => '%p,
    smp_trace = smp_trace + ['simplify(1)']
    simplify(1)
##    res = a_trim() #maybe we don't need this because rel_cost uses n_real_inputs
    ps()
    cost = rel_cost([ni,nl,na])
    print 'New relative cost = %f'%(cost)
    if cost <  -.01:
        abc('w %s_phase_temp.aig'%f_name)
        if ((n_latches() == 0) or (n_ands() == 0)):
            return True
        if n_phases() == 1: #this bombs out if no latches
            return False
        else:
            result = try_phase()
            return result
    elif len(z)>2: #Try the next eligible phase.
        abc('r %s_phase_temp.aig'%f_name)
        if p == z[2]: #already tried this
            return False
        p = z[2]
        print 'Trying phase = %d: => '%p,
        abc('phase -F %d'%p)
        if no == n_pos(): #nothing happened because p is not mod period
            print 'Phase = %d is not compatible'%p
            return False
        abc('r %s_phase_temp.aig'%f_name)
        abc('&get;&frames -o -F %d;&scl;&put'%p)
        smp_trace = smp_trace + ['phase -F %d'%p]
        print 'Simplify with %d phases: '%p,
        simplify(1)
##        res =a_trim() #maybe we don't need this because rel_cost uses n_real_inputs
        cost = rel_cost([ni,nl,na])
        print 'New relative cost = %f'%(cost)
        if cost < -.01:
            print 'Phase abstraction with %d phases obtained:'%p,
            print_circuit_stats()
            abc('w %s_phase_temp.aig'%f_name)
            if ((n_latches() == 0) or (n_ands() == 0)):
                return True
            if n_phases() == 1: # this bombs out if no latches
                return True
            else:
                result = try_phase()
                return result
        else:
            smp_trace = smp_trace + ['de_phase']
    abc('r %s_phase_temp.aig'%f_name)
    return False

def try_temp(t=15):
    global smp_trace,aigs
    btime = time.clock()
##    res = a_trim() #maybe we don't want this here.
    print'Trying temporal decomposition - for max %0.2f sec. '%(t),
    abc('w %s_best_temp.aig'%f_name)
##    ni = n_pis()
    ni = n_real_inputs()
    nl = n_latches()
    na = n_ands()
    best = [ni,nl,na]
    cost_best = 0
    i_best = 0
    n_done = 0
    print 'best = ',
    print best
    F = create_funcs([18],t) #create a timer function
    F = F + [eval('(pyabc_split.defer(struc_temp)())')]
    F = F + [eval('(pyabc_split.defer(full_temp)())')]
    F = F + [eval('(pyabc_split.defer(two_temp)())')]
    for i,res in pyabc_split.abc_split_all(F):
##        print i,res
        if i == 0:
            break
        if n_latches() == 0:
            return True
        n_done = n_done+1
        cost = rel_cost(best)
        if cost<0:
            nri=n_real_inputs()
            best = (nri,n_latches(),n_ands())
            abc('w %s_best_temp.aig'%f_name)
            i_best = i
            cost_best = cost
            print 'cost = %.2f, best = '%cost,
            print best
##            if i == 1:
##                smp_trace = smp_trace + ['tempor -s']
##            if i == 2:
##                smp_trace = smp_trace + ['tempor']
##        if n_latches == 0:
##            break
        if n_done > 2:
            break
##    cost = rel_cost(best)
    cost = cost_best
    print 'cost = %0.2f'%cost
    abc('r %s_best_temp.aig'%f_name)
##    if cost < -.01:
    if cost<0:
        ps()
        return True
    else:
##        smp_trace = smp_trace + ['de_tempor']
##        abc('r %s_best_temp.aig'%f_name)
        return False

def struc_temp():
    abc('tempor -s;scr')
    result = quick_simp()
    if result == 'UNSAT':
        return Unsat
    elif result == 'SAT':
        return Sat
    return Undecided

def full_temp():
    abc('tempor')
    return simplify()

def try_temps(t=20):
    """ need to modify something to be able to update cex"""
    global smp_trace
    abc('w %s_try_temps.aig'%f_name)
    best = (n_pis(),n_latches(),n_ands())
    npi = n_pis()
    F = 1
    while True:
        res = try_temp(t)
        ps()
        if n_latches() == 0:
            break
        if res == False:
            return False,F
        if ((best == (n_pis(),n_latches(),n_ands())) or n_ands() > .9 * best[2] ):
            break
        else:
            smp_trace = smp_trace + ['tempor']
            best = (n_pis(),n_latches(),n_ands())
    return True,n_pis()/npi
        
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
    cost = 10*rli + 1*ra #changed from .5 to 1 on ra
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
    cost = 1*ri + 5*rl + .25*ra
##    print 'Relative cost = %0.2f'%cost
    return cost

def best_fwrd_min(J,t=30):
    global f_name, methods,smp_trace
    J=[18]+J
    mtds = sublist(methods,J)
    F = create_funcs(J,t)
    (m,result) = fork_best(F,mtds) #FORK here
    print '%s: '%mtds[m],
    smp_trace = smp_trace + ['%s'%mtds[m]]
    
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
        abc('dretime -m')
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

def qqsimp():
    abc('&get;&scl;,reparam;&scorr -C 0;&scl;,reparam;&put')
    shrink()
    abc('w %ssimp.aig'%f_name)
    ps()


def quick_simp():
    """A few quick ways to simplify a problem before more expensive methods are applied.
    Uses & commands if problem is large. These commands use the new circuit based SAT solver"""
    na = n_ands()
    if na < 60000:
        abc('scl -m;lcorr;drw')
    else:
        abc('&get;&scl;&lcorr;&put')
    if n_ands() < 500000:
        abc('drw')
    print 'Using quick simplification',
    status = process_status(get_status())
    if status <= Unsat:
        result = RESULT[status]
    else:
        ps()
        result = 'UNDECIDED'
    return result

def scorr_constr():
    """Extracts implicit constraints and uses them in signal correspondence
    Constraints that are found are folded back when done"""
    global aigs
    na = max(1,n_ands())
    n_pos_before = n_pos()
    if ((na > 40000) or n_pos()>1):
        return Undecided_no_reduction
    abc('w %s_savetemp.aig'%f_name)
    na = max(1,n_ands())
##    f = 1
    f = 18000/na  #**** THIS can create a bug 10/15/11. see below
    f = min(f,4)
    f = max(1,f)
    print 'Looking for constraints - ',
    if n_ands() > 18000:
        cmd = 'unfold -s -F 2'
    else:
        cmd = 'unfold -F %d -C 5000'%f
    abc(cmd)
    if n_pos() == n_pos_before:
        print 'none found'
        return Undecided_no_reduction
    if (n_ands() > na): #no constraints found
        abc('r %s_savetemp.aig'%f_name)
        return Undecided_no_reduction
    na = max(1,n_ands())
    f = 1 #put here until bug is fixed.
    print 'found %d constraints'%((n_pos() - n_pos_before))
    abc('scorr -c -F %d'%f)
    abc('fold')
    res = a_trim()
    print 'Constrained simplification: ',
    ps()
    return Undecided_no_reduction

def a_trim():
    """ this is set up to put the aig on the aigs list if trim was successful"""
##    print 'trimming'
##    print 5.1
    pushed = check_push() #checking if a push is needed and if so do it.
                        #It is not needed if flops match previous aig
##    print 5.2
    res = trim()
##    print 5.3
    if res:
        aigs_pp()
##        aigs.push() #store the aig after rpm if it did something
    elif pushed: #since trim did not do anything, we don't need the last push done by check push
        dump() #dump the last aig on the list
##    print 5.4
    return res

def try_scorr_c(f):
    """ Trying multiple frames because current version has a bug."""
    global aigs
    set_globals()
    abc('unfold -F %d'%f)
    abc('scorr -c -F %d'%f)
    abc('fold')
    t = max(1,.1*G_T)
    abc('&get;,bmc3 -vt=%f'%t)
    if is_sat(): 
        return 0
    else:
        res = a_trim()
        return 1
    

def input_x_factor():
    """Sets the global x_factor according to user input"""
    global x_factor, xfi
    print 'Type in x_factor:',
    xfi = x_factor = input()
    print 'x_factor set to %f'%x_factor


def prove(a=0,abs_tried = False):
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
    if n_latches() == 0:
        return 'UNDECIDED'
    if a == 1:
        spec_first = True
    t_init = 2
    abs_found_cex_before_spec = spec_found_cex_before_abs = False
##    First phase
    if spec_first:
        result = prove_part_3() #speculation done here first
        if result == 'UNDECIDED' and abs_tried and n_pos() <= 2:
            add_trace('de_speculate')
            return result
    else:
        abs_tried = True
        result = prove_part_2() #abstraction done here first
    if ((result == 'SAT') or (result == 'UNSAT')):
        return result
##    Second phase
    if spec_first: #did spec already in first phase
        t_init = 2
        abs_tried = True
        result = prove_part_2() #abstraction done here second
        if result == 'SAT':
            abs_found_cex_after_spec = True
    else:
        result = prove_part_3()  #speculation done here second
        if result == 'SAT':
            if '_abs' in f_name:
                spec_found_cex_after_abs = True
            else:
                return result
    if result == 'UNSAT': 
        return result
    status = get_status()
    if result == 'ERROR':
        status = Error
    if ('_abs' in f_name and spec_found_cex_after_abs): #spec file should not have been written in speculate
        f_name = revert(f_name,1) #it should be as if we never did abstraction.
        add_trace('de_abstract')
        print 'f_name = %s'%f_name
        abc('r %s.aig'%f_name) #restore previous
        t_init = 2
        if not '_rev' in f_name:
            print 'proving speculation first'
            write_file('rev') #maybe can get by with just changing f_name
            print 'f_name = %s'%f_name
            result = prove(1,True) #1 here means do smp and then spec 
            if ((result == 'SAT') or (result == 'UNSAT')):
                return result
    elif ('_spec' in f_name and abs_found_cex_after_spec): #abs file should not have been written in abstract
        f_name = revert(f_name,1) #it should be as if we never did speculation.
        add_trace('de_speculate')
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
    global x_factor,xfi,f_name, last_verify_time,K_backup,aigs
    print 'Initial: ',
    ps()
    x_factor = xfi
    set_globals()
    if n_latches() > 0:
##        ps()
        res = try_frames_2()
        if res:
            print 'frames_2: ',
            ps()
            aigs_pp('push','phase')
        print '\n***Running pre_simp'
        add_trace('pre_simp')
        result = run_par_simplify()
        status = result[0]
        method = result[1]
        if 'scorr' in method:
            add_trace(method)
    else:
        print '\n***Circuit is combinational, running check_sat'
        add_trace('comb_check')
        status = check_sat()
    if ((status <= Unsat) or (n_latches() == 0)):
        return RESULT[status]
    res =a_trim()
    if not '_smp' in f_name:
        write_file('smp') #need to check that this was not written in pre_simp
    set_globals()
    return RESULT[status]

def run_par_simplify():
    set_globals()
    t = 1000
    funcs = [eval('(pyabc_split.defer(pre_simp)())')]
    J = [35]+pdrs[:3]+bmcs[:3]+intrps[:1]+sims  # 35 is par_scorr
    J = modify_methods(J,1)
##    J = J + bestintrps
    funcs = create_funcs(J,t)+ funcs #important that pre_simp goes last
    mtds =sublist(methods,J) + ['pre_simp']
    print mtds
    result = fork_last(funcs,mtds)
    status = get_status()
    return [status] + [result]

def try_frames_2():
    abc('scl')
    nl = n_latches()
    if n_ands()> 35000:
        return
    abc('w %s_temp.aig'%f_name)
    abc('&get;&frames -o -F 2;&scl;&put')
    if n_latches() < .75*nl:
        print 'frames_2: Number of latches reduced to %d'%n_latches()
        add_trace('frames_2')
##        res = reparam()
##        xxxxx handle this
##        if res:
##            aigs.push()
        return True
    abc('r %s_temp.aig'%f_name)
    return False
    
def prove_part_2(ratio=.75):
    """does the abstraction part of prove"""
    global x_factor,xfi,f_name, last_verify_time,K_backup, trim_allowed,ifbip
    print'\n***Running abstract'
##    print 'ifbip = %d'%ifbip
    status = abstract(ifbip) #ABSTRACTION done here
    status = process_status(status)
    print 'abstract done, status is %s'%str(status)
    result = RESULT[status]
    if status < Unsat:
        print 'CEX in frame %d'%cex_frame()
        return result #if we found a cex we do not want to trim.
    return result
    
def prove_part_3():
    """does the speculation part of prove"""
    global x_factor,xfi,f_name, last_verify_time,init_initial_f_name
    global max_bmc, sec_options
##    if ((n_ands() > 36000) and sec_options == ''):
##        sec_options = 'g'
##        print 'sec_options set to "g"'
    print '\n***Running speculate on %s: '%f_name,
    ps()
##    add_trace('speculate')
    status = speculate() #SPECULATION done here
    status = process_status(status)
##    print 'speculate done, status is %d'%status
    result = RESULT[status]
    if status < Unsat:
        print 'CEX in frame %d'%cex_frame()
        return result
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
        read_file_quiet_i(name)
        print '\n         **** %s:'%name,
        ps()
        F = create_funcs([18,6],t) #create timer function as i = 0 Here is the timer
        for i,res in pyabc_split.abc_split_all(F):
            break
        tt = time.time()
        if i == 0:
            res = 'Timeout'
        str = '%s: %s, time = %0.2f'%(name,res,(tt-xtime))
        if res == 'SAT':
            str = str + ', cex_frame = %d'%cex_frame()
        str = str +'\n'
        f.write(str)
        f.flush()
        results = results + ['%s: %s, time = %0.2f'%(name,res,(tt-xtime))]
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
        remove(proved,0)
            

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

        
def extract(n1,n2):
    """Extracts outputs n1 through n2"""
    no = n_pos()
    if n2 > no:
        return 'range exceeds number of POs'
    abc('cone -s -O %d -R %d'%(n1, 1+n2-n1))

def remove_intrps(J):
    global n_proc,ifbip
##    print J
    npr = n_proc
    if 18 in J:
        npr = npr+1
    if len(J) <= npr:
##        print J
        return J
    JJ = []
    alli = [23,1,22] # if_no_bip, then this might need to be changed
    l = len(J)-npr
    alli = alli[l:]
##    J.reverse() #strip off in reverse order.
    for i in J:
        if i in alli: 
            continue
        else:
            JJ = JJ+[i]
##    print JJ
    return JJ

def restrict(lst,v=0):
    '''restricts the aig to the POs in the list'''
    #this assumes that there are no const-1 POs. Warning, this will not remove any const-0 POs
    N = n_pos()
    lst1 = lst + [N]
    r_lst = gaps(lst1) #finds POs not in lst
    if len(r_lst) == N:
        return
    remove(r_lst,v)
        
def remove(lst,v=0):
    """Removes outputs in list
    WARNING will not remove all POs even if in lst
    """
    global po_map
    n_before = n_pos()
    zero(lst,v)
    l=remove_const_pos(v)
    assert len(lst) == (n_before - n_pos()),'Inadvertantly removed some const-0 POs.\nPO_before = %d, n_removed = %d, PO_after = %d'%(n_before, len(lst), n_pos())
    print 'PO_before = %d, n_removed = %d, PO_after = %d'%(n_before, len(lst), n_pos())


def zero(list,v=0):
    """Zeros out POs in list"""
    if v == 0:
        cmd = 'zeropo -s -N ' #puts const-0 in PO
    else:
        cmd = 'zeropo -so -N ' #puts const-1 in PO
    for j in list:
        run_command('%s%d'%(cmd,j)) #-s prevents the strash after every zeropo
    abc('st')

def listr_0_pos():
    """ returns a list of const-0 pos and removes them
    """  
    L = range(n_pos())
    L.reverse()
    ll = []
    for j in L:
        i = is_const_po(j)
        if i == 0:
            abc('removepo -N %d'%j) #removes const-0 output
##            print 'removed PO %d'%j
            ll = [j] + ll
    return ll

def list_0_pos():
    """ returns a list of const-0 pos and removes them
    """
    abc('w %s_savetemp.aig'%f_name)
    L = range(n_pos())
    L.reverse()
    ll = []
    for j in L:
        i = is_const_po(j)
        if i == 0:
            abc('removepo -N %d'%j) #removes const-0 output
##            print 'removed PO %d'%j
            ll = [j] + ll
    abc('r %s_savetemp.aig'%f_name)
    return ll

def listr_1_pos():
    """ returns a list of const-1 pos and removes them
    """  
    L = range(n_pos())
    L.reverse()
    ll = []
    for j in L:
        i = is_const_po(j)
        if i == 1:
            abc('removepo -z -N %d'%j) #removes const-1 output
##            print n_pos()
            ll = [j] + ll
    return ll


def mark_const_pos(ll=[]):
    """ creates an indicator of which PO are const-0 and which are const-1
        does not change number of POs
    """
    n=n_pos()
    L = range(n)
    ll = [-1]*n
    for j in L:
        ll[j] = is_const_po(j)
    print sumsize(ind)
    return ind

def remove_const_pos(n=-1):
    global po_map
    """removes the const 0  or 1 pos according to n, but no pis because we might
    get cexs and need the correct number of pis
    """
    if n > -1:
        run_command('&get; &trim -i -V %d; &put'%n) #V is 0 or 1
    else:
        run_command('&get; &trim -i; &put') #removes both constants

def unmap_cex():
    """ aig before trim is put in reg-space and after trim in the &space
        Before and after need to have same number of flops in order o reconcile
        aigs list should be such that if before and after don't match in number of latches,
        then some operation changed the flops and we just update the aig with the new number
        reconcile leaves before aig in reg-space after cex has been updated so cex and aig
        always match
    """
    global aigs,hist
    print hist
##    while not aigs == []:
    while not len(hist) == 0:
        n = n_latches()
        abc('&get') #save the current aig in &-space
        print 'Number of PIs in cex = %d'%n_cex_pis()
        typ = aigs_pp('pop')
        print typ,
        ps()
        if typ == 'phase':
            typ2 =aigs_pp('pop') #gets the aig before phase
            abc('phase -c')
            print 'Number of PIs in cex = %d, Number of frames = %d'%(n_cex_pis(),cex_frame())
            run_command('testcex -a')
            hist = hist + [typ2]
            continue
        if typ == 'tempor':
            typ2 = aigs_pp('pop') #gets the aig before tempor
            abc('tempor -c')
            print 'Number of PIs in cex = %d, Number of frames = %d'%(n_cex_pis(),cex_frame())
            run_command('testcex -a')
            hist = hist + [typ2]
            continue
        if typ == 'reparam':
            nn = n_latches()
            abc('&get') #put 'after' in &space
            typ2 = aigs_pp('pop') #get previous to put before in reg-space
            run_command('reconcile')
            print 'Number of PIs in cex = %d'%n_cex_pis()
##                reconcile(True) #maps the cex from &-space aig to current aig
            run_command('testcex -a')
            if not typ2 == 'reparam0':
                hist = hist + [typ2] #put back (aig iss still there so just have to restore hist
            continue
            #else we just leave the aig updated
        else:
            assert typ == 'initial','type is not initial'
            size = str([n_pis(),n_pos(),n_latches(),n_ands()])
            print 'cex length = %d'%cex_frame()
            tr = ['cex length = %d'%cex_frame()] + ['cex matches original aig = %s'%size]
            print 'cex matches original aig'
            return tr
##    print 'cex matches original aig'
    
                                  
def sp(n=0,t=900,check_trace=False):
    """Alias for super_prove, but also resolves cex to initial aig"""
    global initial_f_name
    print 'Executing super_prove'
    result = super_prove(n,t)
    print '%s is done and is %s'%(initial_f_name,result[0])
    print 'sp: ',
    print result
    if result[0] == 'SAT' and check_trace:
        res = unmap_cex()
        result1 = result[1]+ res
        result = ['SAT'] + result1
        report_cex()
    report_bmc_depth(max(max_bmc,n_bmc_frames()))
    return result

def mp():
    multi_prove_iter()

def report_cex():
    abc('write_status %s_cex.status'%init_initial_f_name)

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

def unmap2(L2,map):
    mx = max(list(map))
    assert mx <= len(L2),'max of map = %d, length of L2 = %d'%(mx,len(L))
    L=[-1]*len(map)
    for j in range(len(map)):
        L[j] = L2[map[j]] #expand results of L2 into L
    return L 

def create_map(L,N):
    """ map equivalence classes into their representative."""
##    print L
    mapp = [-1]*N
    m = -1
    error = False
    for j in range(len(L)):
        lj = L[j]
        for k in range(len(lj)):
            mapp[lj[k]] = j
##        print lj
        mm = min(lj)
##        print mm
        if not mm == lj[0]: #check if rep is not first on list
            print 'ERROR: rep is not first, mm = %d, lj[0] = %d'%(mm,lj[0])
            error = True
        if mm <= m: #check if iso_classes are in increasing order of representatives.
            print 'ERROR: in iso map mm < m, mm = %d, m = %d'%(mm,m)
            error = True
        m = mm
    assert not error,'ERROR'
    return mapp


def weave(L1,lst0,lst1):
    """ interleave values of L1 and with 1's in positions given in lst1,
        and 0's in lst0. It is assumed that these lists are in num order..
        Final list has len = len(L1)+len(lst0)+len(lst1)"""
    L = [-1]*(len(L1)+len(lst0)+len(lst1))
##    print len(L)
    if lst0 == []:
        if lst1 == []:
            return L1
        lst = lst1
        v = 1
    if lst1 == []:
        lst = lst0
        v = 0
    l = k = 0
    for j in range(len(L)):
##        print L
        if j == lst[l]:
            L[j] = v
            if l+1 < len(lst):
                l = l+1
        else: #put in value in L1
            L[j] = L1[k]
            if k+1 < len(L1):
                k = k+1
    return L

def quick_mp(t):
    t1 =time.time()
    l1 = list_0_pos()
    S,l2,s = par_multi_sat(t)
    l2 = indices(s,1)
    remove(l2,1)
    abc('scl')
    simple()
    ps()
    print'time = %0.2f'%(time.time() - t1)

def indices(s,v):
    """return in indices of s that have value v"""
    L = []
    for i in range(len(s)):
        if s[i]== v:
            L = L+[i]
    return L

def expand(s,ind,v):
    """expand s by inserting value v at indices ind"""
    N = len(s)+len(ind)
    ind1 = ind+[N]
    g = gaps(ind1)
    ss = [-1]*N
    for i in ind:
        ss[i] = v
    j = 0
    for i in g: #put original values in ss
        ss[i] = s[j]
        j = j+1
    for j in ind:
        assert ss[j] == v, 'ss = %s, ind = %s'%(str(ss),str(ind))
    return ss

def remove_v(ss,v):
    s = []
    for i in range(len(ss)):
        if ss[i] == v:
            continue
        else:
            s = s + [ss[i]]
    return s
                 
def multi_prove(op='simple',tt=900,n_fast=0, final_map=[]):
    """two phase prove process for multiple output functions"""
    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time
    global f_name_save,nam_save,_L_last,file_out
    x_init = time.time()
    abc('&get;&scl;,reparam -aig=%s_rpm.aig; r %s_rpm.aig')
    print 'Initial after &scl and reparam = ',
    ps()
    abc('w %s_initial_save.aig'%init_initial_f_name)
    #handle single output case differently
    _L_last = [-1]*n_pos()
    if n_pos() == 1:
        result = sp(2000)
##        abc('w %s_unsolved.aig'%init_initial_f_name)
        rs=result[0]
        if rs == 'SAT':
            report_result(0,1)
            L = [1]
        elif rs == 'UNSAT':
            report_result(0,0)
            L = [0]
        elif rs == 'UNDECIDED':
            report_result(0,-1)
            L = [-1]
        else: #error
            L = [2]
        res = sumsize(L)
        rr = '\n@@@@ Time =  %d '%(time.time() - t_iter_start) + res
        print rr
        file_out.write(rr+ '\n')
        file_out.flush()
        return L
##    print 'Removing const-0 POs'
    NNN = n_pos()
    lst0 = listr_0_pos() #remove const-0 POs and record
##    print lst0
    lst0.sort()
    N = n_pos()
    L = [-1]*N
    print 'Removed %d const-0 POs'%len(lst0)
    res = 'SAT = 0, UNSAT = %d, UNDECIDED = %d'%(len(lst0),N)
    rr = '\n@@@@ Time =  %.2f: '%(time.time() - t_iter_start)
    report_L(lst0,0) ##########
    rr = rr + res
    print rr
    file_out.write(rr + '\n')
    file_out.flush()
    ttt = n_ands()/1000
    if ttt < 10:
        ttt=10
    elif ttt<20:
        ttt = 20
    elif ttt< 30:
        ttt = 30
    else:
        ttt = 50
    S,lst1,s = par_multi_sat(ttt,1,1,1) #run engines in parallel looking for SAT outputs
    lst1 = indices(s,1)
##    print S,lst1
    #put 0 values into lst0
    lst10 = indices(s,0) #new unsat POs in local indices (with lst0 removed)
    if not lst10 == []:
        print 'lst10 = %s'%str(lst10)
    lst11 = indices(s,1) #local variables
    ss = expand(s,lst0,0) #ss will reflect original indices
    report_s(ss)
    lst0_old = lst0
    lst0 = indices(ss,0) #additional unsat POs added to initial lst0 (in original indices)
    print 'lst0 = %s'%str(lst0)
    assert len(lst0) == len(lst0_old)+len(lst10), 'lst0 = %s, lst0_old = %s, lst10 = %s'%(str(lst0),str(lst0_old),str(lst10))
    sss = remove_v(ss,0) #remove the 0's from ss
    assert len(sss) == len(ss)-len(lst0), 'len(sss) = %d, len(ss) = %d, len(lst0) = %d'%(len(sss),len(ss),len(lst0))
    lst1_1 = indices(sss,1) #The sats now reflect the new local indices.
                #It makes it as if the newly found unsat POs were removed initially
                #done with new code
    assert len(lst1_1) == len(lst1), 'mismatch, lst1 = %d, lst1_1 = %d'%(len(lst1),len(lst1_1))
    lst1 = lst1_1 #lst1 should be in original minus lst0
    print 'Found %d SAT POs'%len(lst1)
    print 'Found %d UNSAT POs'%len(lst10)
    res = 'SAT = %d, UNSAT = %d, UNDECIDED = %d'%(len(lst1),len(lst0),NNN-(len(lst1)+len(lst0)))
    rr = '\n@@@@ Time =  %.2f: '%(time.time() - t_iter_start)
    rr = rr + res
    print rr
    file_out.write(rr + '\n')
    file_out.flush()
    N = n_pos()
    print len(lst10),n_pos()
    if not len(lst10) == n_pos() and len(lst10) > 0:
        remove(lst10,1) #remove 0 POs
        print 'Removed %d UNSAT POs'%len(lst10)
        N = n_pos()
    elif len(lst10) == n_pos():
        N = 0 #can't remove all POs. Must proceed as if there are no POs. But all POs are UNSAT.
    print len(lst1),N,S #note: have not removed the lst1 POs.
    if len(lst1) == N or S == 'UNSAT' or N == 0: #all POs are SAT
        L = [0]*N #could just put L as all 1's. If N = 0, all POs are UNSAT and lst1 = []
        for i in range(len(lst1)): #put 1's in SAT POs
            L[lst1[i]]=1
        L = weave(L,lst0,[]) #expand L, and put back 0 in L. 
        report_results(L)
        print sumsize(L)
        print 'Time = %.2f'%(time.time() - x_init) 
        return L
##    print 'removing them'
    if not len(lst1)== n_pos():
        remove(lst1,1) #here we removed all POs in lst1 (local indices)
        abc('&get;&scl;&put')
    ##    lst1 = bmcj_ss_r(2) #find easy cex outputs
    ##    write_file('bmc1')
        print 'Removed %d SAT POs'%len(lst1)
        N = n_pos()
    else:
        N = 0
    if N == 1: #this was wrong. Need to report in original indices???
        result = sp(2000)
        rs=result[0]
        #need to find out original index of remaining PO
        if rs == 'SAT':
            v = 1
        elif rs == 'UNSAT':
            v = 0
        elif rs == 'UNDECIDED':
            v = -1
        else: #error should not happen, but be conservative
            v = -1
        L = [v]*N
        L = weave(list(L),[],lst1) #put back 1 in L
        L = weave(list(L),lst0,[]) #put back 0 in L
        report_results(L)
        res = sumsize(L)
        rr = '\n@@@@ Time =  %d '%(time.time() - t_iter_start) + res
        print rr
        file_out.write(rr+ '\n')
        file_out.flush()
        return L
    L1 =L = [-1]*N
    if N > 1 and N < 10000 and n_ands() < 500000: #keeps iso in
##    if N > 1 and N < 10000 and False: #temporarily disable iso
        print 'Mapping for first isomorphism: '
        res = iso() #reduces number of POs
        if res == True:
            abc('&get;&scl;&put')
            write_file('iso1')
            leq = eq_classes()
##        print leq
            map1 = create_map(leq,N) #creates map into original
##        print map1
            if not count_less(L,0) == N:
                print L
            L1 = [-1]*n_pos()
##        L1 = pass_down(L,list(L1),map1) # no need to pass down because L will have no values at this point.
        else:
            map1 =range(N)
    else:
        map1 = range(N)
    N = n_pos()
##    print 4
    r = pre_simp() #pre_simp
    write_file('smp1')
    NP = n_pos()/N #if NP > 1 then NP unrollings were done in pre_simp.
    if NP > 1:
        L1 = duplicate_values(L1,NP) # L1 has only -1s here. Put in same valuess for iso POs
    if n_pos() > N:
        assert NP>=2, 'NP not 2, n_pos = %d, N = %d, NP = %d'%(n_pos(),N,NP)
    print 'pre_simp done. NP = %d\n\n'%NP
    #WARNING: if phase abstraction done, then number of POs changed.
    if r[0] == Unsat:
        print 'example is UNSAT'
        L1 = [0]*N #all outputs are UNSAT
        print sumsize(L1)
        print 'unmapping for iso'
        L = unmap(list(L),L1,map1)
        print "putting in easy cex's and easy unsat's"
        L = weave(list(L),[],lst1) #put back 1 in L
        L = weave(list(L),lst0,[]) #put back 0 in L
        print sumsize(L)
        print 'Time = %.2f'%(time.time() - x_init)
        report_results(L)
        return L
    f_name_save = f_name
    nam_save = '%s_initial_save.aig'%f_name
    #########do second iso here
    N = n_pos()
    if N == 1:
        map2 = [0]
        L2=[-1]
##        write_file('1')
##        L = output(list(L),list(L1),L2,map1,map2,lst0,lst1,NP)
        L = output2(list(L2),map1,map2,lst0,lst1,NP)
        result = simple(2000,1)
        Ss = rs = result[0]
        if rs == 'SAT':
            L2 = [1]
        if rs == 'UNSAT':
            L2 = [0]
    else:
##        if False and N < 10000: #temp disable iso
        if N < 10000 and n_ands() < 500000: 
            print 'Mapping for second isomorphism: '
            res = iso() #second iso - changes number of POs
            if res == True:
                abc('&get;&scl;&put')
                map2 = create_map(eq_classes(),N) #creates map into previous
            else:
                map2 = range(n_pos())
        else:
            map2 = range(n_pos())
        write_file('iso2')
        print 'entering par_multi_sat'
        S,lbmc,s = par_multi_sat(2*ttt,1,1,1) #look for SAT POs
        lmbc = indices(s,1)
        print 'par_multi_sat ended'
        if len(lmbc)>0:
            print 'found %d SAT POs'%len(lmbc)
        L2 = s
##        #first mprove for 10-20 sec.
        ps()
        print 'Before first mprove2, L2 = %s'%sumsize(L2)
        DL = output2(list(L2),map1,map2,lst0,lst1,NP) #reporting intermediate results
##        DDL = output3(range(len(L2)),map1,map2,lst0,lst1,NP)
##        print 'DDL = %s'%str(DDL)
        if n_fast == 1:
            abc('w %s_unsolved.aig'%init_initial_f_name)
            return DL
        NN=n_ands()
        #create timeout time for first mprove2
        ttt = 10
        if NN >30000:
            ttt = 15
        if NN > 50000:
            ttt = 20
        abc('w %s_before_mprove2.aig'%f_name)
        print '%s_before_mprove2.aig written'%f_name
        print 'L2 = %s'%str(L2)
        print 'Entering first mprove2 for %d sec.'%ttt,
        Ss,L2 = mprove2(list(L2),op,ttt,1) #populates L2 with results
##        print Ss,L2
        if Ss == 'SAT':
            print 'At least one PO is SAT'
        if Ss == 'ALL_SOLVED':
            if count_less(L2,0)>0:
                print 'ERROR'
##            L = output(list(L),list(L1),L2,map1,map2,lst0,lst1,NP) # final report of results.
            L = output2(list(L2),map1,map2,lst0,lst1,NP)
            return L
        print 'After first mprove2: %s'%sumsize(L2)
    time_left = tt - (time.time()-x_init)
    N = count_less(L2,0)
    if N > 0 and n_fast == 0:
##        output(list(L),list(L1),L2,map1,map2,lst0,lst1,NP) #reporting new intermediate results
        L = output2(list(L2),map1,map2,lst0,lst1,NP)
        t = max(100,time_left/N)
        t_all = 100
    S = sumsize(L2)
    T = '%.2f'%(time.time() - x_init)
    print '%s in time = %s'%(S,T)
    abc('w %s_unsolved.aig'%init_initial_f_name)
    N = n_pos()
    ttime = 100
    J = slps+intrps+pdrs+bmcs+sims
    #do each output for ttime sec.
    Nn = count_less(L2,0)
##    assert N == len(L2),'n_pos() = %d, len(L2) = %d'%(N,len(L2))
    if Nn > 0:
        found_sat = 0
        print 'final_all = %d, Ss = %s'%(final_all,str(Ss))
        if final_all and not Ss == 'SAT':
            print 'Trying to prove all %d remaining POs at once with super_prove'%Nn
            remove_proved_pos(L2)
            result = super_prove()
            if result[0] == 'UNSAT': #all remaining POs are UNSAT
                for i in range(len(L2)):
                    if L2[i] < 0:
                        L2[i] = 0
##                L = output(list(L),list(L1),L2,map1,map2,lst0,lst1,NP) # final report of results. 
                L = output2(list(L2),map1,map2,lst0,lst1,NP)
                return L
            if result == 'SAT':
                found_sat = 1
        if found_sat or not final_all or Ss == 'SAT':
            print 'Trying each remaining PO for %d sec.'%ttime
            found_sat = 0
##            ttime = 10
            for i in range(N):
                if L2[i] > -1:
                    continue
                print '\n**** cone %d ****'%i
                abc('r %s_unsolved.aig'%init_initial_f_name)
                abc('cone -s -O %d'%i)
                abc('&get;&scl;&lcorr;&put')
                result = verify(J,ttime)
                r = result[0]
                if r > 2:
                    continue
                elif r == 2:
                    L2[i] = 0
                else:
                    L2[i] = 1
                    found_sat = 1
##                output(list(L),list(L1),L2,map1,map2,lst0,lst1,NP)
                L = output2(list(L2),map1,map2,lst0,lst1,NP)
            if Ss == 'SAT' and found_sat: #previous solve_all was SAT and found at least 1 PO SAT
                abc('r %s_unsolved.aig'%init_initial_f_name)
                if not count_less(L2,0) == 0:
                    remove_proved_pos(L2)
                    simplify()
                    write_file('save')
                    result = simple(2000,1)
                    if_found = False
                    if result[0] == 'UNSAT':
                        for i in range(N):
                            if L2[i] == -1:
                                L2[i] = 0
                    elif result[0] == 'SAT' and n_pos() == 1:
                        for i in range(N):
                            if L2[i] == -1:
                                if if_found == True:
                                    print 'Error: more that 1 UNDECIDED remained in L2'
                                    break
                                L2[i] = 1
                                if_found = True
                    else:
                        if result[0] == 'SAT':
                            print 'at least 1 unsolved PO is SAT'
##    L = output(list(L),list(L1),L2,map1,map2,lst0,lst1,NP) # final report of results.
    L = output2(list(L2),map1,map2,lst0,lst1,NP)
    return L

def create_unsolved(L):
    abc('r %s_initial_save.aig'%init_initial_f_name) 
    lst = []
    assert len(L) == n_pos(),'lengths of L and n_pos = %d,%d'%(len(L),n_pos())
    for i in range(len(L)):
        if L[i] > -1: #solved PO
            lst = lst + [i]
    assert max(lst) < n_pos(), 'error in lengths'
    assert count_less(L,0) == n_pos() - len(lst),'mismatch'
    remove(lst,-1) # remove solved
    
def multi_prove_iter():
    global t_iter_start,file_out,ff_name
    ff_name = init_initial_f_name
    file_out = open('%s_time_results.txt'%init_initial_f_name, 'w') #
    t_iter_start = time.time()
    L = multi_prove()
    d = count_less(L,0)
    u = count_less(L,1)-d
    s = count_less(L,2) - (d+u)
    rr =  '\n@@@@@ %s: Final time =  %.2f '%(init_initial_f_name,(time.time() - t_iter_start))
    rr = rr + 'SAT = %d, UNSAT = %d, UNDECIDED = %d '%(s,u,d)
    print rr
    file_out.write(rr)
    res = PO_results(L)
    file_out.write(res)
##    print res
    file_out.flush()
    file_out.close()
    #at this point could restrict to SAT(UNSAT) POs and invoke solver to verify all POs are SAT(UNSAT)
    return

def restrict_v(L,v):
    """ L is a list of 0,1,-1"""
    lst = []
    for j in range(len(L)):
        if L[j] == v:
            lst = lst + [j]
    restrict(lst)
    return lst

def PO_results(L):
    global ff_name
    S=U=UD=[]
    for j in range(len(L)):
        ll = L[j]
        if ll == -1:
            UD = UD + [j]
        elif ll == 0:
            U = U + [j]
        elif ll == 1:
            S = S + [j]
        else:
            print 'error, L contains a non -1,0,1'
    res = "[[SAT = %s], [UNSAT = %s], [UNDECIDED = %s]"%(str(S),str(U),str(UD))
    #restore initial unsolved POs
    abc('r %s.aig'%ff_name)
    if not UD == []:
        restrict(UD,0)
        abc('w %s_UNSOLVED.aig'%ff_name)
        print 'Unsolved POs restored as %s_UNSOLVED.aig'%ff_name
    else:
        print 'All POs were solved'
    abc('r %s.aig'%ff_name) #what if original had constraints.
    abc('fold')
    if not U == []: 
        restrict(U,1) #we use 1 here because do not want to remove const-0 POs which should be in U
        abc('w %s_UNSAT.aig'%ff_name)
        print 'Unsat POs restored as %s_UNSAT.aig'%ff_name
    abc('r %s.aig'%ff_name)
    abc('fold')
    if not S == []:
        restrict(S,0)
        abc('w %s_SAT.aig'%ff_name)
        print 'Sat POs restored as %s_SAT.aig'%ff_name
    return res

def syn3():
    t = time.clock()
    run_command('&get;&b; &jf -K 6; &b; &jf -K 4; &b;&put')
    ps()
    print 'time = %.2f'%(time.clock() - t)

def syn4():
    t = time.clock()
    abc('&get;&b; &jf -K 7; &fx; &b; &jf -K 5; &fx; &b;&put')
    ps()
    print 'time = %.2f'%(time.clock() - t)


def solve_parts(n):
    global t_iter_start,file_out
    r=range(n)
    r.reverse()
    name = init_initial_f_name
    results = []
    for i in r:
        file_out.write('\n@@@@ Starting part%d: \n'%i)
        file_out.flush()
        abc('r %s_part%d.aig'%(name,i))
        print '\nPart%d: '%i
        L = multi_prove()
        rr =  '\n@@@@ Time =  %.2f '%(time.time() - t_iter_start)
        rr = rr + 'Part%d: '%i
        ssl = sumsize(L)
        rr = rr + ssl
        results = results + [[ssl]]
        print rr
        file_out.write(rr + '\n')
        file_out.flush()
    return results

def cp(n=10):
    return chop_prove(n)

def chop_prove(n=10,t=100):
    global t_iter_start,file_out
    tm = time.time()
    abc('w %s_chop_temp.aig'%f_name)
    N = max(5,n_pos()/n)
    J = 0
    total = []
    np = n_pos()
    while J < np:
        abc('r %s_chop_temp.aig'%f_name)
        E = J+N-1
        R = N
        if E > np-1:
            R = N - (E - (np -1))
        abc('cone -s -O %d -R %d'%(J,R))
        npp = n_pos()
        print '\n\n*****     solving outputs %d to %d     *****'%(J,(J+R-1))
        f_map = str([J]*R + range(R))
        funcs = create_funcs(slps,t)
        funcs = funcs + [eval('(pyabc_split.defer(mp)(simple,%s,1,%s))'%(t,f_map))] #1 means do fast mp
##        funcs = funcs + [eval('(pyabc_split.defer(sp)())')]
        for i,res in pyabc_split.abc_split_all(funcs):
            print 'Method %d returned first with result = %s'%(i,res)
            if i == 0:
                res = 'SAT = 0, UNSAT = 0, UNDECIDED = %d'%npp
                rr = '\n@@@@ Time =  %.2f: '%(time.time() - t_iter_start)
                rr = rr + 'chop%d: '%i
                rr = rr + res
                print rr
                file_out.write(rr + '\n')
                file_out.flush()
                break
            if i == 1:
                rr = '\n@@@@ Time =  %.2f: '%(time.time() - t_iter_start)
                rr = rr + 'chop%d: '%i
                rr = rr + res
                file_out.write(rr + '\n')
                file_out.flush()
##                print res
                break
            else:
                if res == 'UNSAT':
                    res = 'SAT = 0, UNSAT = %d, UNDECIDED = 0'%npp
                    rr = '\n@@@@ Time =  %.2f: '%(time.time() - t_iter_start)
                    rr = rr + 'chop%d: '%i
                    rr = rr + res
                    print rr
                    file_out.write(rr + '\n')
                    file_out.flush()
                    break
                else:
                    res = 'SAT = 0, UNSAT = 0, UNDECIDED = %d'%npp
                    rr = '\n@@@@ Time =  %.2f: '%(time.time() - t_iter_start)
                    rr = rr + 'chop%d: '%i
                    rr = rr + res
                    print rr
                    file_out.write(rr + '\n')
                    file_out.flush()
                    break
##        print res
        total = total + [[res]]
        print total
        J = J + R
    c = get_counts(total)
    tm = time.time() - tm
    rr = '\n@@@@ Total time for chop = %.2f, SAT = %d, UNSAT = %d, UNDECIDED = %d'%(tm,c[0],c[1],c[2])
    file_out.write(rr + '\n')
    file_out.flush()
    print rr
    return total

def get_counts(L):
    s=u=d=0
    for i in range(len(L)):
        li = L[i][0]
##        print li
        j1=li.find('=')
        j2 = li.find(',')
        num = int(li[j1+1:j2])
        s = s+num
        li = li[j2+1:]
        j1=li.find('=')
        j2 = li.find(',')
        num = int(li[j1+1:j2])
        u = u+num
        li = li[j2+1:]
        j1=li.find('=')
        j2 = li.find(',')
        num = int(li[j1+1:])
        d = d+num
    return [s,u,d]
        

def output(L,L1,L2,map1,map2,lst0,lst1,NP,final_map=[]):
    global t_iter_start
    print_all(L,L1,L2,map1,map2,lst0,lst1,NP,final_map=[])
    #print 'L = %s, L1 = %s, L2 = %s'%(sumsize(L),sumsize(L1),sumsize(L2))
    L1 = unmap(list(L1),L2,map2)
    print 'L1 after map2 = %s'%sumsize(L1)
    if NP > 1: #an unrolling was done
        L1 = check_and_trim_L(NP,list(L1))#map into reduced size before unrolling was done by phase.
        print 'L1 = %s'%sumsize(L1)
    L = unmap(list(L),L1,map1)
    print 'L after map1 = %s'%sumsize(L)
    L = weave(list(L),[],lst1) #put back 1 in L
    print 'L after lst1 = %s'%sumsize(L)
    L = weave(list(L),lst0,[]) #put back 0 in L
    print 'L after lst0= %s'%sumsize(L) 
    report_results(list(L),final_map)
    return L

def output2(L2,map1,map2,lst0,lst1,NP,final_map=[]):
    global t_iter_start
##    print_all(L,L1,L2,map1,map2,lst0,lst1,NP,final_map=[])
    #print 'L = %s, L1 = %s, L2 = %s'%(sumsize(L),sumsize(L1),sumsize(L2))
    L1 = unmap2(L2,map2)
    print 'L1 after map2 = %s'%sumsize(L1)
##    if NP > 1: #an unrolling was done
##        L1 = check_and_trim_L(NP,list(L1))#map into reduced size before unrolling was done by phase.
##        print 'L1 = %s'%sumsize(L1)
    L = unmap2(L1,map1)
    print 'L after map1 = %s'%sumsize(L)
    L = weave(list(L),[],lst1) #put back 1 in L
    print 'L after lst1 = %s'%sumsize(L)
    L = weave(list(L),lst0,[]) #put back 0 in L
    print 'L after lst0= %s'%sumsize(L) 
    report_results(list(L),final_map)
    return L

def output3(L2,map1,map2,lst0,lst1,NP,final_map=[]):
    """ find out where results came from"""
    global t_iter_start
    L1 = unmap2(L2,map2)
    L = unmap2(L1,map1)
    L = weave(list(L),[],lst1) #put back 1 in L
    L = weave(list(L),lst0,[]) #put back 0 in L
    return L

def print_all(L,L1,L2,map1,map2,lst0,lst1,NP,final_map=[]):
##    return
    print 'L = ',
    print L
    print 'L1 = ',
    print L1
    print 'L2 = ',
    print L2
    print 'map1 = ',
    print map1
    print 'map2 = ',
    print map2
    print 'lst0 = ',
    print lst0
    print 'lst1 = ',
    print lst1


def rnge(n,m):
    """ return interval n+range(m)"""
    N = []
    for j in range(m):
        N = N + [n + j]
    return N

def create_cluster(n=0,p=1,L=100):
    """n is the start node and p is the multiplier on the # of POs to extract
        ll is the limit on the number of latches to include"""
    clstr=rem = [] #make a list of nodes to remove because not compatible
    N = 0 #number of end skips
    init = False
    skip=0 #number of initial skips
    abc('w temp.aig')
    np = n_pos()
    for i in range(np):
        if n + p*(i+1-skip) > np:
            if n_latches() > L:
                bp = n_pos()-p 
                remove(rnge(bp,p),1) #remove last p
                abc('scl')
            return clstr
        abc('r temp.aig')
        abc('cone -s -O %d -R %d;scl'%(n,p*(i+1-skip)))
        xx = n_pos()
        if n_latches() > L:
            if not init: #have not found start point yet
                n=n+p #increase start point
                print 'n,FF = %d,%d'%(n,n_latches())
                skip = skip + 1
                continue
        else:
            if not init:
##                nn=p*(i-skip)
##                clstr = clstr + rnge(nn,p*(i+1-skip))
##                print clstr #initial cluster
                init = True
##        abc('w old.aig')
        remove(rem,1)
        abc('scl')
        ps()
        if n_latches() > L:
            x = xx - p #remove last p POs
            rem = rem + rnge(x,p)
##            print len(rem)
            print 'x,len(rem) = %d,%d,%d'%(x,len(rem))
            N = N+1
        else:
            bn=p*(i-skip)
            nr=rnge(bn,p)
            clstr = clstr + nr
        if N > 100: #don't do more than 10 end-skips
            bp = n_pos()-p 
            remove(rnge(bp,p),1) #put last p on remove list
            abc('scl')
            return clstr

def generate_clusters(b=0,inc=10,end=100):
    abc('w temp_gen_clstr.aig')
    abc('w t_gen_cl.aig')
    clusters = []
    while True:
        abc('r t_gen_cl.aig')
        clstr = create_cluster(b,inc,end)
        clusters = clusters + [clstr]
        abc('r t_gen_cl.aig')
        if clstr == []:
            return clusters
        remove(clstr,1)
        abc('w t_gen_cl.aig')

def map_clusters_to_original(cl):
    L = range(n_pos())
    Clstrs = []
    k = 0
    for j in range(len(cl)):
        c = cl[j]
        cc = pick(L,c)
        Clstrs = Clstrs + [cc]
        L = pick_not(L,cc)
    return Clstrs

def pick(L,c):
    """ computes L(c) """
    x=[]
    for i in range(len(c)):
        x = x + [L[c[i]]]
    return x

def pick_not(L,c):
    """ computes L(~c)"""
    x = []
    for i in range(len(L)):
        if not i in c:
            x = x + [L[i]]
    return x

def report_L(lst=[],v=0):
    """lst must refer to original PO numbering"""
    global _L_last
    if lst == []:
        return
    for j in lst:
        if _L_last[j] == -1: #means not reported yet
            _L_last[j] = v
            report_result(j,v)

def report_s(s):
    """s must refer to original PO numbering
    Differs from above """
    global _L_last
    assert len(s) == len(_L_last), 'two lengths are not equal'
    if s == []:
        return
    for j in range(len(s)):
        if not _L_last[j] == s[j]: #means not reported yet
            assert _L_last[j] == -1, 'j = %d, _L_last[j] = %d, s[j] = %d'%(j,_L_last[j],s[j])
            if _L_last[j] == -1:
                _L_last[j] = s[j]
                report_result(j,s[j])
    

def report_results(L,final_map=[],if_final=False):
    global _L_last,t_iter_start,file_out
    out = '\n@@@@ Time = %.2f: results = %s'%((time.time()- t_iter_start),sumsize(L))
    print out
    file_out.write(out + '\n')
    file_out.flush()
    for j in range(len(L)):
        if not L[j] == _L_last [j]:
            assert _L_last[j] == -1, '_L_last[j] = %d, L[j] = %d'%(_L_last[j],L[j])
            report_result(j,L[j])
    _L_last = list(L) #update _L_last
##    print 'report: _L_last = %s'%sumsize(_L_last)
    print '\n'

def report_result(POn, REn, final_map=[]):
    if final_map == []:
        print 'PO = %d, Result = %d:  '%(POn, REn),
    else:
        print 'PO = %d, Result = %d:  '%(final_map[POn], REn),


def scorr_T(t=10000):
    global smp_trace, scorr_T_done
    if scorr_T_done:
        return
    scorr_T_done = 1
    print 'Trying scorr_T (scorr -C 2, &scorr, &scorr -C 0)'
    funcs = [eval('(pyabc_split.defer(abc)("scorr -C 2"))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("&get;&scorr;&put"))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("&get;&scorr -C 0;&put"))')]
    funcs = create_funcs(slps,t)+funcs
    mtds = sublist(methods,slps) + ['scorr2','&scorr','&scorr0']
    best = n_ands()
    abc('w %s_best_T.aig'%f_name)
    name1 = '%s_sc1.aig'%f_name
    if os.access(name1,os.R_OK):
        os.remove(name1)
    name2 = '%s_sc2.aig'%f_name
    if os.access(name2,os.R_OK):
        os.remove(name2)
    name3 = '%s_sc3.aig'%f_name
    if os.access(name3,os.R_OK):
        os.remove(name3)
    N=m_best = 0
    for i,res in pyabc_split.abc_split_all(funcs):
        if i == 0:
            break
        if i == 1:
            abc('w %s_sc1.aig'%f_name)
            print 'scorr: ',
            ps()
            N=N+1
        if N == 3 or n_latches() == 0:
                break
        if i == 2 or n_latches() == 0:
            abc('w %s_sc2.aig'%f_name)
            print '&scorr: ',
            ps()
            N=N+1
            if N == 3:
                break
        if i == 3 or n_latches() == 0:
            abc('w %s_sc3.aig'%f_name)
            print '&scorr0: ',
            ps()
            N=N+1
            if N == 3:
                break
    if os.access(name1,os.R_OK):
        abc('r %s'%name1)
        if n_ands() < best:
            best = n_ands()
            m_best = 1
            abc('w %s_best_T.aig'%f_name)
    if os.access(name2,os.R_OK):
        abc('r %s'%name2)
        if n_ands() < best:
            m_best = 2
            best = n_ands()
            abc('w %s_best_T.aig'%f_name)
    if os.access(name3,os.R_OK):
        abc('r %s'%name3)
        if n_ands() < best:
            m_best = 3
            best = n_ands()
            abc('w %s_best_T.aig'%f_name)
    smp_trace = smp_trace + ['%s'%mtds[m_best]]
    abc('r %s_best_T.aig'%f_name)

def pscorr(t=900):
    result = par_scorr(t)
    if n_ands() == 0:
        return result
    else:
        return 'UNDECIDED'

def par_scorr(t=30,ratio = 1):
    t_init = time.time()
##    abc('dr -m;drw')
    abc('dretime;dc2')
    funcs = [eval('(pyabc_split.defer(abc)("scorr -vq -F 1"))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("scorr -vq -F 2"))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("scorr -vq -F 4"))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("scorr -vq -F 8"))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("scorr -vq -F 16"))')]
    funcs = create_funcs(slps,t)+funcs
    mtds = sublist(methods,slps) + ['scorr1','scorr2', 'scorr4', 'scorr8', 'scorr16']
    best = n_ands()
    print 'par_scorr: best = %d'%best
    abc('w %s_best.aig'%f_name)
    idone = []
    for i,res in pyabc_split.abc_split_all(funcs):
##        print i,res
        if i == 0: #timeout
            break
        else:
            idone = idone + [i]
            if n_ands() <= ratio * best:
                best = n_ands()
##                print 'par_scorr: best = %d, method = %s'%(best, mtds[i])
                abc('w %s_best.aig'%f_name)
                if best == 0 or len(idone) >= 5:
                    mtd = mtds[i]
                    break
            else:
                break
##    print 'Time: %.2f'%(time.time() - t_init)
    abc('r %s_best.aig'%f_name)
##    if best == 0:
##        print mtd
    return mtd

def par_scorr_q(t=10000,ratio = 1):
    abc('dretime;dc2')
    abc('bmc2 -T 5')
    depth = n_bmc_frames()
    mtds = funcs = []
    n=1
    while True:
        funcs = funcs + [eval('(pyabc_split.defer(abc)("scorr -vq -F %d"))'%n)]
        mtds = mtds + ['scorr%d'%n]
        n = 2* n
        if n > max(1,min(depth,16)):
            break
    funcs = create_funcs(slps,t)+funcs
    mtds = sublist(methods,slps) + mtds
    best = n_ands()
    print 'best = %d'%best
    abc('w %s_best.aig'%f_name)
    idone = []
    for i,res in pyabc_split.abc_split_all(funcs):
##        print i,res
        if i == 0:
            break
        else:
            idone = idone + [i]
            if n_ands() <= ratio * best:
                best = n_ands()
                print 'best = %d, method = %s'%(best, mtds[i])
                abc('w %s_best.aig'%f_name)
                if best == 0 or len(idone) >= len(mtds)-1:
                    break
            else:
                break
    abc('r %s_best.aig'%f_name)


def indicate_0_pos(L2):
    """
    puts 0's in L2 where the corresponding output is driven by a const-0
    """
##    assert n_pos() == len(L2), 'list L2=%d and n_pos=%d in current AIG dont match'%(len(L2),n_pos())
    for j in range(n_pos()):
        i=is_const_po(j)
        if i == 0:
            L2[j]=0
    return L2

def list_0_pos():
    """
    returns indices of outputs driven by  const-0
    """
    L = []
    for j in range(n_pos()):
        i=is_const_po(j) #returns const value of PO if const. Else -1
        if i == 0:
            L = L + [j]
    return L

def mprove2(L=0,op='simple',t=100,nn=0):
    global _L_last, f_name, skip_spec
    print 'mprove2 entered' ,
    if L == 0:
        L = [-1]*n_pos()
    ps()
    print 'mprove2 entered with L = ',
    print sumsize(L)
    abc('w %s_mp2.aig'%f_name) #save aig before pos removed
    old_f_name = f_name #we may call sp() which can change f_name
    n = count_less(L,0)
    ind = []
    for j in range(len(L)):
        if L[j] > -1:
            ind = ind +[j]
    if len(ind) == n_pos(): #all POs already solved
        return 'ALL_SOLVED',L
    remove(ind,-1) #remove solved POs
    if len(ind)>0:
        print 'Removed %d proved POs'%len(ind)
    if n_pos() == 0:
        f_name = old_f_name
        abc('r %s_mp2.aig'%f_name)
        return 'ALL_SOLVED',L
    ps()
    N = n_pos()
    if N == 1: #only one PO left
        v = -1
        skip_spec_old = skip_spec
        skip_spec = True
        result = simple(2000,1)
        ff_name == f_name
        result = sp(0,2000) #warning sp() can change f_name. 0 means simplify
        f_name = ff_name
        skip_spec = skip_spec_old
        res = result[0]
        print 'result of sp = ',
        print res
####        print result
        if res == 'SAT':
            v = 1
        if res == 'UNSAT':
            v = 0
        i = L.index(-1)
##        print 'i=%d,v=%d,L=%s'%(i,v,str(L))
        L[i] = v
        f_name = old_f_name #if sp() changed f_name need to revert to old f_name
        abc('r %s_mp2.aig'%f_name)
        print 'reverting %s_mp2.aig'%f_name,
        ps()
        print sumsize(L)
        if v > -1:
            res = 'ALL_SOLVED'
        return res,L
    r = pre_simp()
    NP = n_pos()/N
    L1 = [-1]*n_pos()
    Llst0 = []
    if r[0] == Unsat:
        L1 = [0]*N
    else:
        Llst0 = list_0_pos()
        Llst0.sort()
        print 'Llst0 = %s'%str(Llst0)
        n_0 = len(Llst0)
        if n_0 > 0:
##            print 'Found %d const-0 POs'%n_0
            remove(Llst0,0)
            print 'Removed %d const-0 POs'%len(Llst0)
        if NP > 1: # we want to do iso here because more than one phase was found.
            iso()  # additional iso - changes number of POs
            map3 = create_map(eq_classes(),N) #creates map into previous
##        tb = min(n_pos(),20)
        N = n_pos()
        tb = min(N,50)
##        print 'Trying par_multi_sat for %d sec.'%tb
        S,lst1,s = par_multi_sat(tb,1,1,0) #this gives a list of SAT POs
        L2 = s10 = s
        n_solved = n_pos() - count_less(s10,0)
        if 1 in s10 or 0 in s10: #something solved 
            if n_solved < N: #not all solved
                rem = indices(s,0)+indices(s,1)
                rem.sort()
                remove(rem,1)
                """ if lst1 > 1 element, simplify and run par_multi_sat again to get lst2
                      then merge lst1 and lst2 appropriately to create new lst1 for below.
                """
                tb = tb+25
                gap = max(15,.2*tb)
                if len(rem) > 0:
                    s210 = s10
                    #iterate here as long as more than 1 PO is found SAT
                    n_solved = n_pos() - count_less(s210,0) 
                    while n_solved > 0:
                        gap = int(1+1.2*gap)
                        print 'gap = %.2f'%gap
                        pre_simp(1) #warning this may create const-0 pos
                        S,lst2,s = par_multi_sat(tb,gap,1,0) #this can find UNSAT POs
                        s210 = s
                        n_solved = n_pos() - count_less(s210,0)
                        s10 = put(s210,list(s10)) #put the new values found into s10
                        if count_less(s10,0) == 0 or n_solved == 0: #all solved or nothing solved
                            break #s10 has the results
                        else:
                            out = '\n@@@@ Time = %.2f: additional POs found SAT = %d'%((time.time()- t_iter_start),len(lst2))
                            print out
                            file_out.write(out + '\n')
                            file_out.flush()
                            rem = indices(s210,0)+indices(s210,1)
                            rem.sort()
                            remove(rem,1) #this zeros the l210 and then removes ALL const-1 POs.
                                            #If there are more than lst2 removed, it fires an assertion.
                            continue
                    L2 = s10 #put results in s10
                else: #lst1 is empty or S == SAT'
                    print 'no cex found or S = UNSAT'
            else: #all solved
                print 'all POs solved'
            print 'Removed %d solved POs'%(len(s10) - count_less(s10,0))
        else:
            print 'nothing solved'
        write_file('bmc2')
        if -1 in s10:
            print 'Entering solve_all ',
            ps()
            S,s210 = solve_all([-1]*n_pos(),900) #solve_all calls sp() or simple but preserves the aig and f_name
##            else: zzz
            if -1 in s210: #then no POs were solved by solve_all
##                abc('r %s_smp2_2.aig'%f_name)
                if n_pos() < 50:
                    print 'Entering mprove with %d sec. for each cone'%t,
                    ps()
                    print 'L2 before mprove: %s'%sumsize(L2)
                    s210 = mprove([-1]*n_pos(),op,t) #proving each output separately
                else:
                    s210 = [-1]*n_pos()
            print 's210 after mprove and before inject 1 %s:'%sumsize(s210)
            L2 = put(s210,s10) 
            print 'L2 after inject 1 %s:'%sumsize(L2)
        else: #all POs solved
            L2 = s10
        assert NP == 1, 'NP > 1: ERROR'
        if NP>1: 
            print 'NP = %d'%NP
            print 'L1 before unmap3: %s'%sumsize(L1)  #L1 should be all -1's of length before iso 
            L1 = unmap(list(L1),L2,map3)
            print 'L1 after unmap of map3: ',
            print sumsize(L1)
        else:
            print 'L2 = %s'%str(L2)
            L1 = L2
        L1 = inject(list(L1),Llst0,0)
        print 'L1 after inject of Llst0 0s: %s:'%sumsize(L1)
    if NP >1:
        L1 = check_and_trim_L(NP,L1)
    assert len(L1)<=len(L),"L1 = %d larger than L = %d"%(len(L1),len(L))
##    print 'L = %s'%str(L)
    L = insert(L1,list(L)) # replace -1s in L with values in L1. Size of L1<=L L is really L2
    print sumsize(L)
    f_name = old_f_name
    abc('r %s_mp2.aig'%f_name) #restore aig
    if 1 in L:
        S = 'SAT'
    if not -1 in L:
        S = 'ALL_PROVED'
    return S,L

def merge(L1,L2,n=0):
    """L2 refers to POs that were solved after POs in L1 were removed
    modifies L2 to refer to the original POs.
    if n=0 adds in L1 and sorts
    """
    if L1 == []:
        return L2
    if L2 == []:
        if n == 0:
            return L1
        else:
            return [] 
    m = max(L1)
    LL1 = L1 + [3+m+max(L2)] #this makes sure that there are enough gaps
    g = gaps(LL1)
##    print g
    L = []
    for i in range(len(L2)):
        l2i=L2[i]
        assert  l2i < len(g),'ERROR, L2 = %s,g = %s'%(str(L2),str(g))
        L = L + [g[l2i]]
##        print L
    if n == 0:
        L = L + L1
        L.sort()        
    return L            #L is already sorted

def put(s2,s11):
    """ put in the values of s2 into where there are -1's in s1 into s1
    return s2 """
    s1 = list(s11)
    k = 0
    assert len(s2) == count_less(s1,0),'mismatch in put'
    for j in range(len(s1)):
        if s1[j] == -1:
            s1[j] = s2[k]
            k=k+1
    return s1

def gaps(L1):
    """L2 refers to POs that were solved after POs in L1 were removed
    modifies L2 to refer to the original POs.
    if n=0 adds in L1 and sorts
    """
    if L1 == [] or max(L1)+1 == len(L1):
        return []
    L1_gaps = []
    i=0
    for j in range(len(L1)):
        lj=L1[j]
##        print lj,i
        if lj == i:
            i = i+1
            continue
        assert lj > i,'Error'
        while  lj > i:
            L1_gaps = L1_gaps + [i]
            i = i+1
##            print L1_gaps
        i=i+1
    return L1_gaps

##    j=i=0
##    L = []
##    L1.sort()
##    L2.sort()
##    LL1 = L1 + [10000000] #make sure list L2 is processed to the end
####    print 'L1 and L2 is sorted %d, %d: '%(len(L1),len(L2))
##    if not L2 == []:
##        while True:
##    ##        print i,j
##            if LL1[i] <= L2[j]:
##                i = i+1
##            else:
##                L= L + [L2[j] + i]
##    ##            print L
##                j = j+1
##                if j == len(L2):
##                    break
##    if n == 0:
##        L = L + L1
##        L.sort()        
##    return L            #L is already sorted
    

def solve_all(L2,t):
    global f_name, skip_spec
    abc('w %s_solve_all.aig'%f_name)
    old_f_name = f_name
##    abc('orpos')
##    print 'solve_all for %.2f sec.: '%t,
##    ps()
    skip_spec_old = skip_spec
    skip_spec = True
    tt = max(t,900)
    print 'Entering simple for %d sec.'%tt
    result = simple(tt,1) #### temporary 1 means do not simplify
##    result = sp(0,t) #warning sp() may change f_name
    skip_spec = skip_spec_old
##    print 'solve_all: result = %s'%result
    if result[0] == 'UNSAT':
        L2 = [0]*len(L2)
    f_name = old_f_name
    abc('r %s_solve_all.aig'%f_name)
    return result[0],L2

def inject(L,lst,v):
    """
    expends the len(L) by len(lst). puts value v in expanded position
    Preserves values in L
    """
    k = i = j = 0 #i indexes L, j indexes lst, and k is total length of LL
    if lst == []:
        return L
    LL = []
    N = len(L) + len(lst)
    while True:
        if lst[j] == k:
            LL= LL + [v]
            if j < len(lst)-1:
                j = j+1
        else:
            LL = LL + [L[i]]
            if i < len(L)-1:
                i = i+1
        k = k+1
        if k >= N:
            break
    return LL

def insert(L1,L):
    """ insert L1 in L and return L"""
    k=0
    for j in range(len(L)):
        if L[j] > -1:
            continue
        else:
            L[j] = L1[k]
            k = k+1
            if k >= len(L1):
                break
    return L
                   
    

def duplicate_values(L1,NP):
    """ append values """
##    L=L1*NP
    L = L1
    for j in range(NP-1):
        L = L+[-1]*len(L1)
    return L

##def duplicate_values2(L1,NP):
##    """ interleave values """
##    L = []
##    for j in range(len(L1)):
##        v = L1[j]
##        L = L + [v]*NP
##    return L

def check_and_trim_L(NP,L):
    """This happens when an unrolling creates additional POs
    We want to check that L[j] = L[j+kN] etc to make sure the PO results agree
    in all phases, i.e. sat, unsat, or undecided. if one is sat then make all L[j+kN] sat,
    If one is unsat, then all L[j+kN] must be unsat. If not then make L[j]=-1.
    Return first N of L.
    """
    N = len(L)/NP #original number of POs
    for j in range(N):
        if L[j] == 1:
            continue
        for k in range(NP)[1:]: #k = 1,2,...,NP-1
            if L[j+k*N] == 1:
                L[j] = 1
                break
            elif L[j] == -1:
                continue #we have to continue to look for a 1
            elif L[j] == 0:
                if L[j+k*N] == -1:
                    print 'some copies of PO unsat and some undecided'
                    L[j] = -1
                    break
            continue #have to make sure that all phases are 0
    return L[:N]

def pass_down(L,L1,map):
    """map maps L into L1.Populate L1 with values in L"""
##    print len(L),len(L1),len(map),max(map)
##    print sumsize(L)
##    print sumsize(L1)              
    for j in range(len(map)):
        if L[j] == -1:
            continue
        assert L1[map[j]] == -1 or L1[map[j]] == L[j], 'L1=%d, L = %d'%(L1[map[j]],L[j]) 
        L1[map[j]] = max(L[j],L1[map[j]])
    return L1

def mpr():
    tt = time.time()
    N=n_pos()
    r = pre_simp()
    if r == Unsat:
        L = [0]*N
    else:
        L = mprove([-1]*n_pos(),'simple',100)
    L = L[:N]
    print sumsize(L)
    print 'Time = %.2f'%(time.time() - tt)
    return L
                

def mprove(L,op='simple',tt=1000):
    """ 0 = unsat, 1 = sat, -1 = undecided"""
    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time
    global f_name_save, nam_save, temp_dec, f_name
    f_name_save = f_name
    nam_save = '%s_mp_save.aig'%f_name
    abc('w %s'%nam_save)
    N = len(L)
    print 'Length L = %d, n_pos() = %d'%(len(L),n_pos())
    t = tt #controls the amount of time spent on each cone
    funcs = [eval('(pyabc_split.defer(%s)())'%op)]
    funcs = create_funcs(slps,t)+funcs
    mtds = sublist(methods,slps) + [op]
    res = L
    NN = count_less(L,0)
    rr = range(N)
    rr.reverse()
    init_name = init_initial_f_name
    for j in rr:
        if L[j] > -1:
            continue #already solved
        print '\n************** No. Outputs = %d ******************************'%NN
        abc('r %s'%nam_save) #restore original function
##        ps()
        x = time.time()
        name = '%s_cone_%d.aig'%(f_name,j)
        print '________%s(%s)__________'%(op,name)
        abc('cone -s -O %d;scl'%j)
        abc('w %s_cone.aig'%f_name)
##        ps()
        read_file_quiet_i('%s_cone.aig'%f_name) #needed to reset initial settings
##        ps()
        temp_dec = False
        i,result = fork_last(funcs,mtds)
##        print '\ni = %d, result = %s'%(i,str(result))
        f_name = f_name_save #restore original f_name
        T = '%.2f'%(time.time() - x)
        out = get_status()
##        print '\nout= %d, result = %s'%(out,str(result))
        rslt = Undecided
        if not out == result:
            print 'out = %d, result = %d'%(out,result)
##        assert out == result,'out = %d, result = %d'%(out,result)
        if out == Unsat or result == 'UNSAT' or result == Unsat:
            res[j] = 0
            rslt = Unsat
        if out < Unsat:
            res[j] = 1
            rslt = Sat
        print '\n%s: %s in time = %s'%(name,RESULT[rslt],T)
    abc('r %s'%nam_save) #final restore of original function for second mprove if necessary.
    init_initial_f_name = init_name
##    print res
    return res

##def sp1(options = ''):
##    global sec_options
##    sec_options = options
##    return super_prove(1)

def super_prove(n=0,t=900):
    """Main proof technique now. Does original prove and if after speculation there are multiple output left
    if will try to prove each output separately, in reverse order. It will quit at the first output that fails
    to be proved, or any output that is proved SAT
    n controls call to prove(n)
    is n == 0 do smp and abs first, then spec
    if n == 1 do smp and spec first then abs
    if n == 2 just do quick simplification instead of full simplification, then abs first, spec second
    """
    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time, f_name
##    print 'sec_options = %s'%sec_options
##    init_initial_f_name = initial_f_name
    size = str([n_pis(),n_pos(),n_latches(),n_ands()])
    add_trace('[%s: size = %s ]'%(f_name,size))
    if x_factor > 1:
        print 'x_factor = %f'%x_factor
        input_x_factor()
    max_bmc = -1
    x = time.time()
    add_trace('prove')
    result = prove(n)
    print 'prove result = ',
    print result
    tt = time.time() - x
    if ((result == 'SAT') or (result == 'UNSAT')):
        print '%s: total clock time taken by super_prove = %0.2f sec.'%(result,tt)
        add_trace('%s'%result)
        add_trace('Total time = %.2f'%tt)
        print m_trace
        return [result]+[m_trace]
    elif ((result == 'UNDECIDED') and (n_latches() == 0)):
        add_trace('%s'%result)
        add_trace('Total time = %.2f'%tt)
        print m_trace
        return [result]+[m_trace]
    print '%s: total clock time taken by super_prove so far = %0.2f sec.'%(result,(time.time() - x))
    y = time.time()
    print 'Entering BMC_VER_result'
    add_trace('BMC_VER_result')
    result = BMC_VER_result() #this does backing up if cex is found
    print 'Total clock time taken by last gasp verification = %0.2f sec.'%(time.time() - y)
    tt = time.time() - x
    print 'Total clock time for %s = %0.2f sec.'%(init_initial_f_name,tt)
    add_trace('%s'%result)
    add_trace('Total time for %s = %.2f'%(init_initial_f_name,tt))
##    print m_trace
    return [result]+[m_trace]

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
    global res
    funcs = [eval('(pyabc_split.defer(%s)())'%op)]
    funcs = create_funcs(slps,t)+funcs
    mtds =sublist(methods,slps) + [op]
    res = []
    for j in range(len(L)):
        x = time.time()
        name = L[j]
        print '\n\n\n\n________%s__________'%op
        read_file_quiet_i(name)
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
    if n_ands() > 500000:
        return False
    if n_pos() < 2:
        print 'no more than 1 output'
        return False
    npos=n_pos()
    if n == 0:
        abc('&get;&iso -q;&put')
        if n_pos() == npos:
            print 'no reduction'
            return False
    else:
        run_command('&get;&iso;iso;&put')
        if n_pos() == npos:
            print 'no reduction'
            return False
    print 'Reduced n_pos from %d to %d'%(npos,n_pos())
    return True

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
    l = remove_const_pos(0)
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
    
def reachx(t=900):
    x = time.time()
    abc('reachx -t %d'%t)
    print 'reachx  done in time = %f'%(time.time() - x)
    return get_status()

def reachy(t=900):
    x = time.clock()
    abc('&get;&reachy -v -T %d'%t)
##    print 'reachy done in time = %f'%(time.clock() - x)
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
    npr = n_proc - dec
    reachi = reachs
    if 18 in J: #if sleep in J add 1 more processor
        npr = npr+1
    if ( ((I+L<550)&(N>100))  or  (I+L<400) or (L<80) ):
        if not 24 in J: #24 is reachy
            if L < 70 and not 4 in reachs:
                reachi = [4]+reachs #[4] = reachx
            J = reachi+J # add all reach methods
            if len(J)>npr:
                J = remove_intrps(J) #removes only if len(J)<n_processes
    if len(J)< npr: #if not using all processors, add in pdrs
        for j in range(len(allpdrs)):
            if allpdrs[j] in J: #leave it in
                continue
            else: #add it in
                J = J + [allpdrs[j]]
                if len(J) == npr:
                    break            
    if len(J)>npr:
        J = remove_intrps(J)
    return J

def BMC_VER():
    """ a special version of BMC_VER_result that just works on the current network
    Just runs engines in parallel - no backing up
    """
    global init_initial_f_name, methods, last_verify_time, n_proc,last_gasp_time
    xt = time.time()
    result = 5
    t = max(2*last_verify_time,last_gasp_time)  ####
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

def BMC_VER_result(t=0):
##    return 'UNDECIDED'   #TEMP
    global init_initial_f_name, methods, last_verify_time,f_name,last_gasp_time
    xt = time.time()
    result = 5
    abc('r %s.aig'%f_name)
    abc('scl')
    print '\n***Running proof on %s after scl:'%f_name,
    ps()
    if t == 0:
        t = max(2*last_verify_time,last_gasp_time) #each time a new time-out is set t at least 1000 sec.
    print 'Verify time set to %d'%t
    J = slps + allpdrs2 + bmcs + intrps + sims
    last_name = seq_name(f_name).pop()
    if not last_name in ['abs','spec']:
        J = slps +allpdrs2 +bmcs + intrps + sims
##    if 'smp' == last_name or last_name == f_name: # then we try harder to prove it.
    J = modify_methods(J) #if # processors is enough and problem is small enough then add in reachs
    F = create_funcs(J,t)
    mtds = sublist(methods,J)
    print '%s'%mtds
    (m,result) = fork(F,mtds)
    result = get_status()
    if result == Unsat:
        return 'UNSAT'
##    if last_name == 'smp' or last_name == f_name:   # can't backup so just return result
    if not last_name in ['abs','spec']:
        if result < Unsat:
            return 'SAT'
        if result > Unsat: #still undecided
            return 'UNDECIDED'
    else:    # (last_name == 'spec' or last_name == 'abs') - the last thing we did was an "abstraction"
        if result < Unsat:
            if last_name == 'abs':
                add_trace('de_abstract')
            if last_name == 'spec':
                add_trace('de_speculate')
            f_name = revert(f_name,1) # revert the f_name back to previous
            abc('r %s.aig'%f_name)
            abc('scl')
            return BMC_VER_result() #recursion here.
        else:
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
##    lst.reverse()
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
    l=remove_const_pos(0)
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
    l=remove_const_pos(0) #can an original PO be zero?

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
    L = eq_classes()
##    print L
    remove_iso(L)
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
    l=remove_const_pos(0)
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def prove_all_pdr(t):
    """Tries to prove output k by pdr, using other outputs as constraints. If ever an output is proved
    it is set to 0 so it can't be used in proving another output to break circularity.
    Finally all zero'ed outputs are removed. """
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
    l=remove_const_pos(0)
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def prove_each_ind():
    """Tries to prove output k by induction,  """
    N = n_pos()
    l=remove_const_pos(0)
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
    l=remove_const_pos(0)
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def prove_each_pdr(t):
    """Tries to prove output k by PDR. If ever an output is proved
    it is set to 0. Finally all zero'ed ooutputs are removed. """
    N = n_pos()
    l=remove_const_pos(0)
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
    l=remove_const_pos(0)
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def disprove_each_bmc(t):
    """Tries to prove output k by PDR. If ever an output is proved
    it is set to 0. Finally all zero'ed ooutputs are removed. """
    N = n_pos()
    l=remove_const_pos(0)
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
    l=remove_const_pos(0)
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def add_pord(s):
    global pord_trace
    pord_trace = pord_trace + [s]

def pord_1_2(t):
    """ two phase pord. First one tries with 10% of the time. If not solved then try with full time"""
    global n_pos_proved, ifpord1, pord_on, pord_trace
    #first eliminate easy POs
    ttt = n_ands()/1000
    if ttt < 100:
        ttt=100
    elif ttt<200:
        ttt = 200
    elif ttt< 300:
        ttt = 300
    else:
        ttt = 500
    S,lst,L = par_multi_sat(ttt,1,1,1)
    lst = indices(L,1)
    if 1 in L:
        return [Sat]+[['par_multi_sat: SAT']]
    if -1 in L:
        restrict_v(L,-1)
    else: return [Unsat] + [['par_multi_sat: UNSAT']]
    pord_trace = []
    pord_on = True # make sure that we do not reparameterize after abstract in prove_2
    n_pos_proved = 0
    if n_pos()<4:
        return [Undecided] +[pord_trace]
    if ifpord1:
        add_pord('pord1')
        t_time = .1*t
        print 'Trying each output for %0.2f sec'%(.1*t)
        result = pord_all(.1*t) #we want to make sure that there is no easy cex.
        if (result <= Unsat):
            return [result] + [pord_trace]
    return [Undecided] + [pord_trace]
        
def pord_all(t,n=4):
    """Tries to prove or disprove each output j by PDRM BMC3 or SIM. in time t"""
    global cex_list, n_pos_proved, last_cx, pord_on, ifpord1,pord_trace
    print 'last_cx = %d, time = %0.2f'%(last_cx,t)
    btime = time.time()
    N = n_pos()
    prove_all_ind() ############ change this to keep track of n_pos_proved
    nn = n_pos()
    abc('w %s_osavetemp.aig'%f_name)    
    if nn < n or nn*t > 300: #Just cut to the chase immediately.
        return Undecided
    lst = range(n_pos())
    proved = disproved = []
    abc('&get') #using this space to save original file.
    ### Be careful that & space is not changed.
    cx_list = []
    n_proved = 0
    lcx = last_cx + 1
    lst = lst[lcx:]+lst[:lcx]
    lst.reverse()
    n_und = 0
    for j in lst:
        print '\ncone %s. '%j,
        abc('&r -s %s_osavetemp.aig'%f_name) #for safety
        abc('&put; cone -s -O %d'%j) #puts the &space into reg-space and extracts cone j
        #requires that &space is not changed. &put resets status. Use &put -s to keep status
        abc('scl -m')
        ps()
##        print 'running sp2'
        ###
        result = run_sp2_par(t)
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
        if nn == n_pos_proved:
            return Unsat
        abc('r %s_osavetemp.aig'%f_name)
##        abc('&put') # returning original to work spece
        remove(proved,0)
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
    abc('bmc3 -a -C 1000000 -T %f'%(t))
    if is_sat():
        cex_list = cex_get_vector() #does this get returned from a concurrent process?
        n = count_non_None(cex_list)
        L = list_non_None(cex_list)
        print '%d cexs found in %0.2f sec'%(n,(time.time()-x))
##        remove_disproved_pos(cex_list)
    else:
        L = []
    return L

def iso_slp(t=30):
    F = [eval('pyabc_split.defer(sleep)(t))')]
    F = F = F+[eval('(pyabc_split.defer(iso)())')]
    for i,res in pyabc_split.abc_split_all(F):
        if i == 0:
            return 

##def iter_par_multi_sat(t=10,m=1):
##    while True:
##        abc('w %s_save.aig'%f_name)
##        S,lst1 = par_multi_sat(t,m) #run 3 engines in parallel looking for SAT outputs
##        lst1.sort()
##        print 'Found %d SAT POs'%len(lst1)
##        abc('r %s_save.aig'%f_name)
##        if len(lst1)==0:
##            break
##        remove(lst1,1)
##        pre_simp(1,1)
##        iso()

def show_partitions(L):
    for i in range(len(L)):
        abc('&r -s %s.aig'%L[i])
        print '\nSize = ',
        run_command('&ps')
        abc('&popart')
        eqs = eq_classes()
        N = len(eqs)
        print 'No. of partitions = %d'%N
        if N == 1:
            continue
        l = []
        for j in range(N):
            l=l + [len(eqs[j])]
        print l


def r_part(name):
    read_file_quiet_i(name)
    abc('&get;&scl;&scorr -C 2;&put')
    res1 = reparam()
    res2 = False
    npos = n_pos()
##    if n_pos() < 100:
##        res2 = iso()
##    ps()
    if n_pos() < 1000:
        iso()
    if n_pos() < 500:
        abc('r %s.aig'%name)
        abc('w %s_leaf.aig'%name)
        return 
##        abc('w %s_leaf.aig'%name)
##        return 
    res = two_eq_part()
    if res == False:
        abc('r %s.aig'%name)
        abc('w %s_leaf.aig'%name)
        return
    elif min(res) < .2*max(res) and min(res) < 500:
        abc('r %s.aig'%name)
        abc('w %s_leaf.aig'%name)
        return
    else:                           #recur
        r_part('%s_p0'%name)
        r_part('%s_p1'%name)
        return

def two_eq_part():
    abc('&get;&popart')
    part = eq_classes()
    if len(part) == 1:
        print 'Partition has only one part'
        return False
    abc('w %s_save.aig'%f_name)
    nn = n_pos()
    p1=p0 = []
    init = True
    for i in range(len(part)): #union first half together together
        if init == True:
            p0=p0 + part[i]
            if len(p0)>nn/2:
                init = False
        else:
            p1 = p1 + part[i]
    p0.sort()
    p1.sort()
    abc('&get')
    remove(p1,1)
    n0=n_pos()
##    print 'writing %s_p0.aig'%f_name
    abc('w %s_p0.aig'%f_name)
    abc('r %s_save.aig'%f_name)
    remove(p0,1)
##    print 'writing %s_p1.aig'%f_name
    n1=n_pos()
    abc('w %s_p1.aig'%f_name)
    return [n0,n1]

def merge_parts(p,n):
    parts = []
    end = []
    for i in range(len(p)):
        if len(p[i]) > n:
            parts = parts + [p[i]]
        else:
            end =end + p[i]
    parts = parts + [end]
    return parts
        

def extract_parts(S=11):
    abc('&get;&popart -S %d'%S)
    part = eq_classes()
    if len(part) == 1:
        print 'Partition has only one part'
        return 1
    parts = merge_parts(part,2)
    lp=len(parts)
    print 'Found %d parts'%lp
    abc('w %s_save.aig'%f_name)
    for i in range(lp):
        abc('r %s_save.aig'%f_name)
        p=[]
        for j in range(lp):
            if i == j:
                continue
            else:
                p = p + parts[j]
        remove(p,1)
        abc('&get;&scl;&lcorr;&put')
        abc('w %s_part%d.aig'%(f_name,i))
    return len(parts)

def two_part():
    abc('&get;&popart')
    part = eq_classes()
    if len(part) == 1:
        print 'Partition has only one part'
        return False
    part1 = part[1:] #all but the 0th
    p1=[]
    for i in range(len(part1)): #union together
        p1=p1 + part1[i]
    p1.sort()
    abc('w %s_p.aig'%f_name)
    remove(p1,1)
##    print 'writing %s_p0.aig'%f_name
    abc('w %s_p0.aig'%f_name)
    n0=n_pos()
    abc('r %s_p.aig'%f_name)
    p0 = part[0]
    p0.sort()
    remove(p0,1)
##    print 'writing %s_p1.aig'%f_name
    n1=n_pos()
    abc('w %s_p1.aig'%f_name)
    return [n0,n1]

def set_t_gap(t1,t2):
    nam = max(30000,n_ands())
    ratio = 1+float(nam-30000)/float(70000)
    gp = .5*ratio*t2
    gp = min(100,gp)
    t = min(100,ratio*t1)
    return (t,gp)
    
def par_multi_sat(t=10,gap=0,m=1,H=0):
    """ m = 1 means multiple of 1000 to increment offset"""
    global last_gap
    abc('w %s_save.aig'%f_name)
    if not t == 0:
        if gap == 0:
            gap = max(.2,.2*t)
            gap = max(15,gap)
        if gap > t:
            t=gap
        t,gt = set_t_gap(t,gap)
        gt = max(15,gt)
        if gt <= last_gap:
            gt = 1.2*last_gap
    else:
        t = gt = 5
    if gt > t:
        t = gt
    last_gap = gt
##    H = max(100, t/n_pos()+1)
    if not H == 0:
        H = (gt*1000)/n_pos()
        H = max(min(H,1000*gt),100)
    tme = time.time()
    list0 = listr_0_pos() #reduces POs
    list0.sort()
##    print 'list0 = %s'%str(list0)
    if len(list0)>0:
        print 'temporarily removed %d cost-0 POs'%len(list0)
    ps()
    if len(list0)> 0:
        print 'Found %d const-0 POs, but not removed'%len(list0)
##        print ll
    print 'par_multi_sat entered for %.2f sec. and gap = %.2f  sec., H = %.2f'%(t,gt,H)
    base = m*1000
    if not m == 1:
        offset = (m-1)*32000
        abc('&get;&cycle -F %d;&put'%offset)
    mx = 1000000000/max(1,n_latches())
    N = n_pos()
    na = n_ands()
    F = [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,H))'%(0*base))]
##    if na < 50000:
    F = F + [eval('(pyabc_split.defer(pdraz)(t,gt,H))')] #need pdr in??
    F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d,4,0))'%(0*base))]
    F = F + [eval('(pyabc_split.defer(sleep)(t))')]
    F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d,4,0))'%(100))]
    F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(100))]
    if mx > 1*base:      
        F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d,1,97))'%(1*base))]
        F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(1*base))]
##    if mx > 2*base:
##        F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d))'%(2*base))]
##        F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(2*base))]
    if mx > 4*base and na < 400000:
        F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d,4,23))'%(4*base))]
        F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(4*base))]
##    if mx > 8*base and na < 300000:
##        F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d,3,53))'%(8*base))]
##        F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(8*base))]
##    if mx > 16*base and na < 200000 :
##        F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d,2,79))'%(16*base))]
##        F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(16*base))]
##    if mx > 32*base and na < 100000:      
##        F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d,1,97))'%(32*base))]
##        F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(32*base))]
    ss=LL=L = [] 
    S = 'UNDECIDED'
    zero_done = two_done = False
    s=ss = [-1]*n_pos()
    ii = []
    nn = len(F)
    for i,res in pyabc_split.abc_split_all(F):
        ii = ii + [i]
        if len(ii) == len(F)-1: #all done but sleep
            break
        if i == 3: #sleep timeout
            print 'sleep timeout'
            break
##        if i == 1:
##            print 'PDR produced: %s'%str(res)
####        print i
        if i == 0:
            zero_done = True # bmc with start at 0 is done
        if i == 2:
            two_done = True
        if res == None: #this can happen if one of the methods bombs out
            print 'Method %d returned None'%i
            continue
##        print res
        s1 = switch(res[1]) #res[1]= s
        s = merge_s(list(s),s1)
        print sumsize(s)
        ss = ss + [s1]
##        LL = LL + [res[0]]
##        L = L + res[0]
##        L = [x for x in set(L)] #uniquefy
        if count_less(s,0) == 0:
            S = 'UNSAT'
            break
 #        if i == 1 and is_unsat() and na < 50000: #pdr can return unsat.
##        if i == 1 and is_unsat(): #pdr can return unsat.
##            print 'Method pdr proved remaining POs UNSAT'
##            S = 'UNSAT'
##            L = res[0]
##            break
##        if not -1 in s:
##            S = 'UNSAT'
##            break
        if len(ss)>1 and zero_done and two_done:
            ss2 = ss[-2:] #checking if last 2 results agree
            r = ss2[0]
            if r == ss2[1] and count_less(r,1) < len(r): #at least 1 SAT PO found
                break
##        if len(LL) > 1 and zero_done and two_done:
##            ll2 = LL[-2:] #checking if last 2 results agree
##            if ll2[0] == ll2[1] and ll2[0] > 0:
##                break
    print 'Found %d SAT POs in '%(len(L)),
    print 'time = %.2f'%(time.time()-tme)
    print sumsize(s)
##    L.sort()
##    print 'L_before = %s'%(str(L))
####    check_None_status(L,s,1) #now 1 in s means sat. s can have 0 in it, meaning it found some POs unsat.
##    L = merge(list(list0),list(L),1) #shift L according to list0 but do not include list0.
##    print 'L_shifted = %s'%(str(L))
##    # Need to return only SAT POs have to do the same for s
    print 'len(s) = %d, len(list0) = %d'%(len(s),len(list0))
    ss = expand(s,list0,0)
##    assert list0 == indices(ss,0)
    print sumsize(ss)
##    assert check_consistancy(L,ss), 'inconsistant'
    abc('r %s_save.aig'%f_name)
    return S,[],ss


def check_consistancy(L,s):
    """ L is list of SAT's found. s is index of all"""
    consistant = True
    print 'checking s[L]'
    for j in L: #make sure that s[L] = 1
##        print j,
##        print s[j]
        if not s[j] == 1:
            print j,
            consistant = False
    print 'checking s=1 => L'
    for j in range(len(s)): #make sure that there are no other 1's
        if s[j] == 1:
            if not j in L:
                print j,
                consistant = False
    return consistant
        

def check_s(s1,s2):
    assert len(s1) == len(s2),'lengths do not match'
    miss = []
    for i in range(len(s1)):
        if (s1[i] == 0 and s2[i] == 1) or (s1[i] == 1 and s2[i] == 0):
            miss = miss + [i]
    print miss
        

def merge_s(s1,s2):
    assert len(s1) == len(s2), 'error in lengths, s1 = %s, s2 = %s'%(str(s1),str(s2))
    s = [-1]*len(s1)
    for i in range(len(s1)):
        if not s1[i] == s2[i]:
            if s1[i] == -1 or s2[i] == -1:
                s[i] = max(s1[i],s2[i])
            else:
                print 'error: conflict in values at i = %d'%i
                print 's1[i]=%d,s2[i]=%d'%(s1[i],s2[i])
        else: #put in common value
            s[i] = s1[i]
    return s

def switch(ss):
    """ This changes the convention of SAT and UNSAT to SAT = 1, UNSAT = 0"""
    s1 = ss
    for i in range(len(ss)):
        si = ss[i]
        if si == 0:
            s1[i] = 1
        elif si == 1:
            s1[i] = 0
    return s1
        

def pdr_ss_r(t):
    """
    assumes that 0 POs have been removed
    finds a set cexs in t seconds. Returns list of SAT POs found
    """
    global cex_list
    x = time.time()
    abc('pdr -az -T %f'%(t))
    if is_sat():
        print 'entering cex  get vector'
        cex_list = cex_get_vector() #does this get returned from a concurrent process?
##        n = count_non_None(cex_list)
        print len(cex_list)
        L = list_non_None(cex_list)
        n = len(L)
        print '%d cexs found in %0.2f sec.'%(n,(time.time()-x))
        if n == len(cex_list):
            print 'all remaining POs are SAT'
##            return L
        else:
            remove_disproved_pos(cex_list) #note that this will not remove all POs
    else:
        L = []
    print 'T = %0.2f'%(time.time()-x)
    return L

def bmc_ss_r(t):
    """
    assumes that 0 POs have been removed
    finds a set cexs in t seconds. Returns list of SAT POs found
    """
    global cex_list
    x = time.time()
    abc('bmc3 -az -C 1000000 -T %f'%(t))
    if is_sat():
        print 'entering cex  get vector'
        cex_list = cex_get_vector() #does this get returned from a concurrent process?
##        n = count_non_None(cex_list)
        L = list_non_None(cex_list)
        n= len(L)
        print '%d cexs found in %0.2f sec.'%(n,(time.time()-x))
        if n == len(cex_list):
            print 'all remaining POs are SAT'
##            return L
        else:
            remove_disproved_pos(cex_list) #note that this will not remove all POs
    else:
        L = []
    print 'T = %0.2f'%(time.time()-x)
    return L

def sim_ss_r(t):
    """
    assumes that 0 POs have been removed
    finds a set cexs in t seconds. Returns list of SAT POs found
    """
    global cex_list
    x = time.time()
    run_command('sim3 -az -T %f'%(t))
    if is_sat():
        print 'entering cex  get vector'
        cex_list = cex_get_vector() #does this get returned from a concurrent process?
##        n = count_non_None(cex_list)
        L = list_non_None(cex_list)
        n = len(L)
        print '%d cexs found in %0.2f sec.'%(n,(time.time()-x))
        if n == len(cex_list):
            print 'all remaining POs are SAT'
##            return L
        else:
            remove_disproved_pos(cex_list) #note that this will not remove all POs
    else:
        L = []
    print 'T = %0.2f'%(time.time()-x)
    return L

def check_None_status(L,s=[],v=0):
    """ L is the PO numbers that had non_None in
    0 means sat and 1 means unsat is
    v tells which value means sat"""
    if s == []:
        s = status_get_vector()
    error = False
    for j in L:
        if s[j] == v:
            continue
        else:
            error = True
    for i in range(len(s)):
        if s[i] == v:
            if i in L:
                continue
        else:
            error = True
    if error:
        print 'status and non_None do not agree'
        print 'L = %d'%L
        print 'SAT and UNSAT counts switched'
        print sumsize(s)


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
    l=remove_const_pos(0)

def remove_proved_pos(lst):
    for i in range(len(lst)):
        if  lst[i] > -1:
            abc('zeropo -N %d'%i)
    remove_const_pos(0)


        
def bmc_j(t=900):
    """ finds a cex in t seconds starting at 2*N where N is depth of bmc -T 1"""
    x = time.time()
    tt = min(5,max(1,.05*t))
    abc('bmc3 -T %0.2f'%tt)
    if is_sat():
##        print 'cex found in %0.2f sec at frame %d'%((time.time()-x),cex_frame())
        return get_status()
##    abc('bmc3 -T 1')
    N = n_bmc_frames()
    N = max(1,N)
##    print bmc_depth()
##    abc('bmc3 -C 1000000 -T %f -S %d'%(t,int(1.5*max(3,max_bmc))))
    cmd = 'bmc3 -J 2 -D 4000 -C 1000000 -T %f -S %d'%(t,2*N)
##    print cmd
    abc(cmd)
##    if is_sat():
##        print 'cex found in %0.2f sec at frame %d'%((time.time()-x),cex_frame())
    return RESULT[get_status()]

def pdrseed(t=900):
    """uses the abstracted version now"""
##    abc('&get;,treb -rlim=60 -coi=3 -te=1 -vt=%f -seed=521'%t)
    abc('&get;,treb -rlim=100 -vt=%f -seed=521'%t)
    return RESULT[get_status()]

def pdrold(t):
    abc('&get; ,pdr -vt=%f'%t)
    return RESULT[get_status()]

def pdr(t=900):
    abc('&get; ,treb -vt=%f'%t)
    return RESULT[get_status()]

def pdr0(t=900):
    abc('&get; ,pdr -rlim=100 -vt=%f'%t)
    return RESULT[get_status()]

def pdra(t=900):
##    abc('&get; ,treb -rlim=100 -ssize -pre-cubes=3 -vt=%f'%t)
    abc('&get; ,treb -abs -rlim=100 -sat=abc -vt=%f'%t)
    return RESULT[get_status()]

def pdrm(t=900):
    abc('pdr -C 0 -T %f'%t)
    return RESULT[get_status()]

def pdrmm(t):
    abc('pdr -C 0 -M 298 -T %f'%t)
    return RESULT[get_status()]

def bmc2(t):
   abc('bmc2 -C 1000000 -T %f'%t)
   return RESULT[get_status()]

def bmc(t=900):
    abc('&get; ,bmc -vt=%d'%t)
    return RESULT[get_status()]

def intrp(t=900):
    abc('&get; ,imc -vt=%d'%t)
    return RESULT[get_status()]

def bmc3az(t=900,gt=10,C=999,H=0):
    t_init = time.time()
    if  C > 999:
        abc('&get; &cycle -F %d; &put'%C) 
    abc('bmc3 -az -C 1000000 -T %d -G %d -H %.2f'%(t,gt,H))
    cex_list = cex_get_vector()
    L = list_non_None(cex_list)
##    check_None_status(L)
    print 'bmc3az(%.2f,%.2f,%d,%d): CEXs = %d, time = %.2f'%(t,gt,C,H,len(L),(time.time()-t_init))
##    s = status_get_vector()
    s = [-1]*n_pos()
    for j in L:
        s[j]=0 #0 here means SAT. It will be switched in par_multi_sat
    return L,s

def pdraz(t=900,gt=10,H=0):
    print 'pdraz entered with t = %.2f, gt = %.2f, H = %.2f'%(t,gt,H)
    t_init = time.time()
    run_command('pdr -az -T %d -G %d -H %.2f'%(t,gt,H))
    cex_list = cex_get_vector()
    L = list_non_None(cex_list)
##    check_None_status(L)
    s = status_get_vector()
    if s == None:
        print "status_get_vector returned None"
    else:
        print 'Number of UNSAT POs = %d'%(len(s) - count_less(s,1))
    print 'pdraz(%.2f,%.2f,%d): CEXs = %d, time = %.2f'%(t,gt,H,len(L),(time.time()-t_init))
    return L,s

def sim3az(t=900,gt=10,C=1000,W=5,N=0):
    """ N = random seed, gt is gap time, W = # words, F = #frames"""
    t_init = time.time()
    if  C > 1000:
        abc('&get; &cycle -F %d; &put'%C) 
    abc('sim3 -az -T %.2f -G %.2f -F 40 -W %d -N %d'%(t,gt,W,N))
    cex_list = cex_get_vector()
    L = list_non_None(cex_list)
##    check_None_status(L)
    s = [-1]*n_pos()
    for i in L:
        s[i] = 0 #0 indicates SAT here
    print 'sim3az(%.2f,%.2f,%d,%d,%d): CEXs=%d, time = %.2f'%(t,gt,C,W,N,len(L),(time.time()-t_init))
    return L,s
    
def bmc3(t=900):
    abc('bmc3 -C 1000000 -T %d'%t)
    return RESULT[get_status()]

def intrpm(t=900):
    abc('int -C 1000000 -F 10000 -K 1 -T %d'%t)
    print 'intrpm: status = %d'%get_status() 
    return RESULT[get_status()]

def split(n):
    global aigs
    abc('orpos;&get')
    abc('&posplit -v -N %d;&put;dc2'%n)
    res =a_trim()

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


def pre_reduce():
    x = time.clock()
    pre_simp()
    write_file('smp')
    abstract(ifbip)
####    write_file('abs')
    print 'Time = %0.2f'%(time.clock() - x)

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
    global cex_list,methods, pord_trace
    J = slps+[6] #6 is the 'simple' method
##    mtds = sublist(methods,J)
##    print mtds,
    print 'time = %0.2f'%t
    funcs = create_funcs(J,t) 
    y = time.time()
    for i,res in pyabc_split.abc_split_all(funcs):
##        print 'i,res = %d,%s'%(i,res)
        T = time.time()-y
        if i == 0:
            print 'Timer expired in %0.2f'%T
            return 'UNDECIDED'
        else:
##            print i,res
            #note simple returns a vector
            mtd = res[1]
            ress = res[0]
            if ress == 'UNSAT':
                print 'simple proved UNSAT in %0.2f sec.'%T
                add_pord('UNSAT by %s'%mtd)
                return 'UNSAT'
            elif ress == 'UNDECIDED':
                print 'simple returned UNDECIDED in %0.2f sec.'%T
                return 'UNDECIDED'
            if ress == 'SAT':
                print 'simple found cex in %0.2f sec.'%T
                add_pord('SAT by %s'%mtd)
                return 'SAT'
            else:
                assert False, 'ress = %s'%ress

def run_parallel(J,t,BREAK='US'):
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
            print 'sleep: time expired in %0.2f sec.'%(t)
##            return 0,[Undecided]+[M]
##            assert status >= Unsat,'status = %d'%status
            break
        if ((status > Unsat) and '?' in BREAK): #undecided
            break
        elif status == Unsat or res == 'UNSAT': #unsat
            print '%s: UNSAT in %0.2f sec.'%(M,(t))
            status = Unsat
            if 'U' in BREAK:
                break
        elif status < Unsat or res == 'SAT': #status == 0 - cex found
            status = Sat
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
    add_trace('%s by %s'%(RESULT[status],M))
    return i,[status]+[M]

def fork_best(funcs,mts):
    """ fork the functions, If not solved, take the best result in terms of AIG size"""
    global f_name
    n = len(mts)-1
    r = range(len(mts))
    y = time.time()
    m_best = -1
    best_size = [n_pis(),n_latches(),n_ands()]
##    print best_size
    abc('w %s_best_aig.aig'%f_name)
    for i,res in pyabc_split.abc_split_all(funcs):
        if mts[i] == 'sleep':
            m_best = i
            break
        r = delete(r,i)
        if len(r) == 1:
            if mts[r[0]] == 'sleep':
                break
        status = prob_status()
        if not status == -1: #solved here
            m = i
            t = time.time()-y
            if status == 1: #unsat
                print '%s proved UNSAT in %f sec.'%(mts[i],t)
            else:
                print '%s found cex in %f sec. - '%(mts[i],t),
            break
        else:
            cost = rel_cost(best_size)
            if cost < 0:
                best_size = [n_pis(),n_latches(),n_ands()]
                m_best = i
                abc('w %s_best_aig.aig'%f_name)
    abc('r %s_best_aig.aig'%f_name)
    add_trace('%s'%mts[m_best])
    return m_best,res

def delete(r,i):
    """ remove element in the list r that corresponds to i """
    ii = r.index(i)
    z = []
    for i in range(len(r)):
        if i == ii:
            continue
        else:
            z = z + [r[i]]
    return z
    

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
    global m_trace,hist,sec_options
    n = len(mtds)-1
    m = -1
    y = time.time()
    sres =lst = ''
##    print mtds
    #print 'starting fork_last'
    for i,res in pyabc_split.abc_split_all(funcs):
##        print i,res
        status = prob_status()
        if mtds[i] == 'par_scorr' and n_ands() == 0:
            add_trace('UNSAT by %s'%res)
            return i,Unsat
        if not status == -1 or res in ['SAT','UNSAT']: #solved here
            m = i
            t = int(time.time()-y)
            if status == 1 or res == 'UNSAT': #unsat
                sres = str(res)
                res = Unsat
                print '%s proved UNSAT in %d sec.'%(mtds[i],t)
            else:
                res = Sat
                print '%s found cex in %0.2f sec. - '%(mtds[i],(t)),
            break
        elif i == n:
##            print res
            if mtds[i] == 'pre_simp':
                m_trace = m_trace + [res[1]]
                hist = res[2]
            t = int(time.time()-y)
            m = i
            if mtds[i] == 'initial_speculate':
                return m,res
            else:
                print '%s: UNDECIDED in %d sec.'%(mtds[i],t)
                res = Undecided
                ps()                
                break
        elif mtds[i] == 'sleep':
            res = Undecided
            t = time.time()-y
            print 'Timer expired in %0.2f'%t
            break
        lst = lst + ', '+mtds[i]
##    sres = str(res)
    if sres[:5] == 'scorr':
        add_trace('UNSAT by %s'%sres)
        return m,Unsat
    add_trace('%s by %s'%(RESULT[res],mtds[i]))
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
    assert res[0] == get_status(),'res: %d, status: %d'%(res,get_status())
##    add_trace('%s by %s'%(RESULT[res[0]],mtds[i]))
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

def area_tradeoff(k=4):
    print nl(),
    best = n_nodes()
    abc('write_blif %s_bestsp.blif'%f_name)
    L_init = n_levels()
    while True:
        L_old = n_levels()
        L = L_old +1
        n_nodes_old = n_nodes()
        abc('speedup;if -a -D %d -F 2 -K %d -C 11'%(L,k))
        if n_nodes() < best:
            best = n_nodes()
            abc('write_blif %s_bestsp.blif'%f_name)
##        if n_levels() == L_old:
        if n_nodes == n_nodes_old:
            break
        print nl(),
        continue
    abc('r %s_bestar.blif'%f_name)
    return


def map_lut_dch(k=4):
    '''minimizes area '''
    abc('st; dch; if -a  -F 2 -K %d -C 11; mfs2 -a -L 50 ; lutpack -L 50'%k)
    
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

def shrink():
    tm = time.time()
    best = n_ands()
    while True:
        abc('&get;&if -K 4 -F 1 -A 0 -a;&shrink;&put')
        print n_ands(),
        if n_ands()< .99*best:
            best = n_ands()
            continue
        break
    print 't = %.2f, '%(time.time()-tm),
    ps()

def shrink_lut():
    tm = time.time()
    abc('&get;&if -K 4 -F 1 -A 0 -a;&put')
    best = n_nodes()
    print best,
    abc('&shrink')
    while True:
        abc('&if -K 4 -F 1 -A 0 -a;&put')
        print n_nodes(),
        if n_nodes() < .99*best:
            best = n_nodes()
            abc('&shrink')
            continue
        break
    abc('&put')
    print 'time = %.2f, '%(time.time()-tm),
    ps()


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
    tm = time.time()
    while True:
        na=n_ands()
        abc('dc2')
        print n_ands(),
##        print nl(),
        if n_ands() > th*na:
            break
    print 't = %.2f, '%(time.time()-tm),
    ps()
##    print n_ands()

def drw_iter(th=.999):
    abc('st')
    tm = time.time()
    while True:
        na=n_ands()
        abc('drw')
        print n_ands(),
##        print nl(),
        if n_ands() > th*na:
            break
    print 't = %.2f, '%(time.time()-tm),
    ps()
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
    abc('&r -s %s.aig;&put'%f_name)
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

def vta_abs(t):
    """ Do gate-level abstraction for F frames """
    r = 100 *(1 - abs_ratio)
##    abc('orpos; &get;&vta -dv -A %s_vabs.aig -P 2 -T %d -R %d; &vta_gla;&w %s_gla.aig;&gla_derive; &put; w %s_gabs.aig'%(f_name,t,r,f_name,f_name))
    abc('orpos; &get;&vta -dv -A %s_vabs.aig -P 2 -T %d -R %d; &vta_gla;&w %s_gla.aig'%(f_name,t,r,f_name))
    
##    write_file('abs')
    

def sizeof():
    return [n_pis(),n_pos(),n_latches(),n_ands()]

def abstract(ifb=2):
    global abs_ratio
##    print 'ifb = %d'%ifb
    if ifb == 0: #new way using vta_abs and no bip
        add_trace('abstracta')
        return abstracta(False)
    elif ifb == 1: #old way using ,abs
        assert ifb == ifbip, 'call to abstract has ifb not = global ifbip'
        add_trace('abstractb')
        return abstractb()
    else:
        #new way using ,abs -dwr -- (bip_abs)
        add_trace('abstracta')
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
        if gla:
            print 'using gla_abs_iter for %0.2f sec.'%(t-2)
            mtds = ['gla_abs_iter']
            add_trace('gla_abs')
            funcs = [eval('(pyabc_split.defer(gla_abs_iter)(t-2))')]
        else:
            print 'using vta_abs for %0.2f sec.'%(t-2)
            mtds = ['vta_abs']
            funcs = [eval('(pyabc_split.defer(vta_abs)(t-2))')]
    funcs = funcs + [eval('(pyabc_split.defer(monitor_and_prove)())')]
##    J = [34,30]
    J = pdrs[:1]+bmcs[:1] #just use one pdr and one bmc here.
##    J = pdrs+bmcs
##    J = modify_methods(J,2)
    funcs = funcs + create_funcs(J,1000)
    mtds = mtds + ['monitor_and_prove'] + sublist(methods,J)
    print 'methods = ',
    print mtds
    vta_term_by_time=0
    for i,res in pyabc_split.abc_split_all(funcs):
##        print i,res
        if i == 0: #vta or gla ended first
            print 'time taken = %0.2f'%(time.time() - tt)
            if is_sat():
                print 'vta/gla abstraction found cex in frame %d'%cex_frame()
                add_trace('SAT by gla')
                return Sat
            if is_unsat():
                print 'vta/gla abstraction proved UNSAT'
                add_trace('UNSAT by gla')
                return Unsat
            else: #undecided
                if if_bip:
                    abc('&r -s %s_greg.aig; &abs_derive; &put; w %s_gabs.aig'%(f_name,f_name))
                else:
                    abc('&r -s %s_gla.aig;&gla_derive; &put; w %s_gabs.aig'%(f_name,f_name))   
                if time.time() - tt < .95*t:
                    print 'abstraction terminated but not by timeout'
                    vta_term_by_time = 0
                    break
                else:
                    print 'abstraction terminated by a timeout of %0.2f'%t
##                    print 'final abstraction: ',
##                    ps()
                    vta_term_by_time=1
                    break
        if i == 1: #monitor and prove ended first (sleep timed out)
            print 'monitor_and_prove: '
##            print i,res
            if res == None:
                print 'monitor and prove had an error'
                continue
            result = res[0]
            if res[0] > Undecided: #we abandon abstraction
                add_trace('de_abstract')
                print 'monitor and prove timed out or too little reduction'
                abc('r %s_before_abs.aig'%f_name)
                return Undecided_no_reduction
            if res[0] == Undecided:
                break
            else: 
                if not initial_size == sizeof(): #monitor and prove should not return SAT in this case'
                    assert not is_sat(), 'monitor_and_prove returned SAT on abstraction!' 
                print 'time taken = %0.2f'%(time.time() - tt)
                if is_unsat() or res[0] == 'UNSAT' or res[0] == Unsat:
                    add_trace('UNSAT by %s'%res[1])
                    return Unsat
                elif is_sat() or res[0] < Unsat:
                    add_trace('SAT by %s'%res[1])
                    return Sat
                else:
                    abc('r %s_before_abs.aig'%f_name)
                    return Undecided_no_reduction
        else: #one of the engines got an answer
            print 'time taken = %0.2f'%(time.time() - tt)
##            add_trace('initial %s'%mtds[i])
            if is_unsat():
                print 'Initial %s proved UNSAT'%mtds[i]
                add_trace('UNSAT by initial %s'%mtds[i])
                return Unsat
            if is_sat():
                print 'Initial %s proved SAT'%mtds[i]
                add_trace('SAT by initial %s'%mtds[i])
                return Sat
            else: # an engine failed here
                print 'Initial %s terminated without result'%mtds[i]
                add_trace('method %s failed'%mtds[i])
##                return Undecided
                continue
    if  vta_term_by_time == 0 and if_bip == 0 and gabs: #vta timed out itself
        print 'Trying to verify final abstraction',
        ps()
        result = verify([7,9,19,23,24,30],100)
        if result[0] == Unsat:
            add_trace('UNSAT by %s'%result[1])
            print 'Abstraction proved valid'
            return result[0]
    # should do abstraction refinement here if if_bip==1
    if if_bip == 0 and gabs: # thus using vta or gla abstraction and no refinement
        print 'abstraction no good - restoring initial simplified AIG',
        abc('r %s_before_abs.aig'%f_name)
        add_trace('de_abstract')
        ps()
        return Undecided_no_reduction
    else: # thus using bip_abs (ifbip=1) or gate abstraction (ifbip=0&gabs=False) and refinement
        if is_sat():
            print 'Found true counterexample in frame %d'%cex_frame()
            add_trace('SAT')
            return Sat_true
        if is_unsat():
            add_trace('UNSAT')
            return Unsat
    ##    set_max_bmc(NBF)
        NBF = bmc_depth()
        print 'Abstraction good to %d frames'%max_bmc
        #note when things are done in parallel, the &aig is not restored!!!
        if if_bip:
            abc('&r -s %s_greg.aig; &w initial_greg.aig; &abs_derive; &put; w initial_gabs.aig; w %s_gabs.aig'%(f_name,f_name))
        else:
            run_command('&r -s %s_gla.aig; &w initial_gla.aig; &gla_derive; &put; w initial_gabs.aig; w %s_gabs.aig'%(f_name,f_name))
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
            print "Too little reduction!"
            print 'Abstract time wasted = %0.2f'%(time.time()-tt)
            add_trace('de_abstract')
            return Undecided_no_reduction
        sims_old = sims
        sims=sims[:1] #make it so that rarity sim is not used since it can't find a cex
##        result = Undecided_no_reduction
        print 'small_abs = %.2f, vta_term_by_time = %d'%(small_abs(abs_ratio),vta_term_by_time)
        if not vta_term_by_time:
            print 'Entering abstraction_refinement'
            result = abstraction_refinement(latches_before_abs, NBF,abs_ratio)
            sims = sims_old
            if result <= Unsat:
                return result
        if small_abs(abs_ratio): #r is ratio of final to initial latches in absstraction. If greater then True
##        if small_abs(abs_ratio) or result == Undecided_no_reduction or vta_term_by_time: #r is ratio of final to initial latches in absstraction. If greater then True
            abc('r %s_before_abs.aig'%f_name) #restore original file before abstract.
            print "Too little reduction!  ",
            print 'Abstract time wasted = %0.2f'%(time.time()-tt)
            add_trace('de_abstract')
            return Undecided_no_reduction
        elif vta_term_by_time:
            abc('r %s_gabs.aig'%f_name)
            print 'Simplifying and testing abstraction'
            reparam()
            result = simplify()
            assert result >= Unsat, 'simplify returned SAT'
            if result > Unsat: #test if abstraction is unsat
                result = simple()
                res = result[0]
                if res == 'UNSAT':
                    return Unsat
                else:
                    abc('r %s_before_abs.aig'%f_name) #restore original file before abstract.
                    print "Timed out with bad abstraction",
                    print 'Abstract time wasted = %0.2f'%(time.time()-tt)
                    add_trace('de_abstract')
                    return Undecided_no_reduction
##                if res == 'SAT':
####                    result = Sat #this was an error
##                    result = Undecided_no_reduction
##                elif res == 'UNSAT':
##                    result = Unsat
##                else:
##                    result = Undecided_no_reduction
##                return result
        else:
            write_file('abs') #this is only written if it was not solved and some change happened.
        print 'Abstract time = %0.2f'%(time.time()-tt)
    return result

def gla_abs_iter(t):
    """ this iterates &gla every x sec and checks if it should be stopped or continued.
        Uses the fact that when &gla ends
        it leaves the result in the &-space showing which elements are abstracted.
        cex_abs_depth, time_abs_prev and time_abs come from monitor_and_prove
        gla_abs_iter and monitor_and_prove are run in parallel
        """
    global cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
    it_interval = 10000 
    total = t
    tt = time.time()
    run_command('orpos;&get')
##    run_command('&w %s_gla.aig'%f_name)
    abs_depth = abs_depth_prev = 0
##    while True:
    r = 100 *(1 - abs_ratio)
    q = 99 #############TEMP
##    run_command('&r %s_gla.aig'%f_name)
    time_remain = total - (time.time() - tt) #time remaining
    it = min(it_interval,time_remain)
##    if it < 2:
##        break
    #gla and vabs are the file with the abstraction info and gabs is the derived file.
    cmd = '&gla -mvs -B 1 -A %s_vabs.aig -T %d -R %d -Q %d -S %d'%(f_name,it,r,q,abs_depth)
    print 'Executing %s'%cmd
    name = '%s_vabs.aig'%f_name
    run_command(cmd)
    if os.access(name,os.R_OK):
        run_command('&r -s %s_vabs.aig'%f_name) #get the last abstraction result
        run_command('&w %s_gla.aig'%f_name) #saves the result of abstraction.
    else:
        run_command('&r -s %s_abs_old.aig'%f_name) #get the last abstraction result
        run_command('&w %s_gla.aig'%f_name) #saves the result of abstraction.
    print 'wrote %s_gla file'%f_name
    run_command('&gla_derive;&put')
    run_command('w %s_gabs.aig'%f_name)
##        break
##        abs_depth_prev = abs_depth
##        abs_depth = n_bmc_frames()
##        print 'abs_depth = %d'%abs_depth
##        #test here if done
##        if (time.time()-tt) > total:
##            break
##        print 'reading abs_values'
##        read_abs_values()
##        print 'values read'
##        if abs_done(time_remain):
##            print 'abs_done'
##            break
##        else:
##            continue
    
def read_abs_values():
    """here we read in the abs values written by monitor and prove"""
    global cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
    if not os.access('%s_ab.txt'%f_name,os.R_OK):
        print '%s_ab.txt does not exist'%f_name
        return #file does not exist so do nochange values
##    print '%s_ab.txt file exists and is readable'%f_name
    ab = open('%s_ab.txt'%f_name,'r')
    print '%s_ab.txt is opened'%f_name
    s = ab.readline()
##    print s
    cex_abs_depth = int(s)
    s = ab.readline()
##    print s
    time_abs_prev = float(s)
    s = ab.readline()
##    print s
    time_abs = float(s)
    s = ab.readline()
##    print s
    abs_depth_prev = float(s)
    s = ab.readline()
##    print s
    abs_depth = float(s)
    ab.close()
##    print 'read: ',
##    print cex_abs_depth,time_abs_prev,time_abs,abs_depth_prev,abs_depth
##    print 'it is closed'

def write_abs_values():
    global cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
    """here we write in the abs values written by monitor and prove"""
##    print 'write: ',
##    print cex_abs_depth,time_abs_prev,time_abs,abs_depth_prev,abs_depth
    ab = open('%s_ab.txt'%f_name,'w')
    ab.write(str(cex_abs_depth)+'\n')
    ab.write(str(time_abs_prev)+'\n')
    ab.write(str(time_abs)+'\n')
    ab.write(str(abs_depth_prev)+'\n')
    ab.write(str(abs_depth))
    ab.close()

def abs_done(time_remain):
    """ heuristic to see if we are not making any progress and should quit
        look at frame of last cex found (cex_abs_depth)  for current abstraction using a parallel engine
        look at depth of current abstraction (abs_depth) and last abstraction (abs_deptth_prev)
        look at time between new abstractions time_abs - time_abs_prev.
        compute approximate frames_per_sec
        if  frames_to_next_cex > frames_per_sec * time_remain
        then won't get there is the time allowed.
        We have to pass all the information along when we are doing things in parallel by writing a file
        with this info in it and reading it in later. This is because monitor_and prove
        runs in parallel and global variables are not passed around.
    """
    global cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
##    print 'checking if abs has enough time to next cex'
    frames_to_next_cex = cex_abs_depth - abs_depth
    div = time_abs - time_abs_prev
    div = max(.1,div)
    frames_per_sec = (abs_depth - abs_depth_prev)/div
    if frames_per_sec <= 0:
        return False #something wrong 
    print 'frames_per_sec = %0.2f, frames_to_next_cex = %d, time remaining = %0.2f'%(frames_per_sec, frames_to_next_cex, time_remain)
    if frames_to_next_cex > 0.2*(frames_per_sec * time_remain): #later frames will take longer so factor of 5 here
        print 'not enough abs time to next cex'
        return True
    return False

##def gla_abs(t): 
##    """ Do gate-level abstraction for F frames """
##    r = 100 *(1 - abs_ratio)
##    run_command('orpos; &get;&gla -dv -A %s_vabs.aig -T %d -R %d; &w %s_gla.aig'%(f_name,t,r,f_name))
    
        
def monitor_and_prove():
    """
    monitor and prove. Runs in parallel with abstraction method.
    It looks for a new vabs and if found, will try to verify it in parallel
    We want to write a file that has variables
    cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
    which will be used by abs_done called by gla_abs_iter which is to replace gla_abs
    """
    global ifbip
    global cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
    #write the current aig as vabs.aig so it will be regularly verified at the beginning.
    name = '%s_vabs.aig'%f_name
    if os.access('%s'%name,os.R_OK): #make it so that there is no initial abstraction
        os.remove('%s'%name)
    initial_size = sizeof()
    print 'initial size = ',
    print initial_size
    time_abs = time_abs_prev = time.time()
    cex_abs_depth = 0
    abs_depth = abs_depth_prev = 0
    write_abs_values()
##    if read_and_sleep(5): # wait until first abstraction when res is False
##        #time has run out as controlled by abs_time
##        return [Undecided_no_reduction] + ['read_and_sleep']
    t = abs_time +10
    tt = time.time()
##    print 'first read and sleep done'
    #a return of Undecided means that abstraction might be good and calling routine will check this
    while True: #here we iterate looking for a new abstraction and trying to prove it
        time_done = abs_bad = 0
        funcs = [eval('(pyabc_split.defer(read_and_sleep)())')]
        J = sims+intrps+pdrs+bmcs
        J = modify_methods(J,1)
        funcs = funcs + create_funcs(J,t) 
        mtds = ['read_and_sleep'] + sublist(methods,J)
        print 'methods = %s'%mtds
        for i,res in pyabc_split.abc_split_all(funcs):
##            print 'Mon. & Pr.: ,
##            print i,res
            if i == 0: # read_and_sleep terminated
                if res == False: #found new abstraction
                    read_abs_values()
                    time_abs_prev = time_abs
                    time_abs = time.time()
                    print 'time between new abstractions = %0.2f'%(time_abs - time_abs_prev)
                    write_abs_values()
                    abs_bad = 0 #new abs starts out good.
                    if not initial_size == sizeof() and n_latches() > abs_ratio * initial_size[2]:
                        return [Undecided_no_reduction]+['read_and_sleep']
                    else:
                        break
                elif res == True: # read and sleep timed out
                    time_done = 1
                    print 'read_and_sleep timed out'
                    if abs_bad:
                        return [Undecided_no_reduction]+['read_and_sleep']
                    else: #abs is still good. Let other engines continue
                        return [Undecided]+['read_and_sleep'] #calling routine handles >Unsat all the same right now.
                else:
                    assert False, 'something wrong. read and sleep did not return right thing'
            if i > 0: #got result from one of the verify engines
                print 'monitor_and_prove: Method %s terminated'%mtds[i],
##                print i,res
                if res == None:
                    print 'Method %s failed'%mtds[i]
                    continue
##                print 'method %s found SAT in frame %d'%(mtds[i],cex_frame())
                if is_unsat() or res == Unsat or res == 'UNSAT':
                    print '\nParallel %s proved UNSAT on current abstr\n'%mtds[i]
                    return [Unsat] + [mtds[i]]
                elif is_sat() or res < Unsat or res == 'SAT': #abstraction is not good yet.
                    print 'method = %s'%mtds[i]
                    if not mtds[i] == 'RareSim': #the other engines give a better estimate of true cex depth
                        read_abs_values()
                        cex_abs_depth = cex_frame()
                        write_abs_values()
                    print '\nParallel %s found SAT on current abstr in frame %d\n'%(mtds[i],cex_frame())
##                    print 'n_vabs = %d'%n_vabs
                    if initial_size == sizeof():# the first time we were working on an aig before abstraction
                        print initial_size == abstraction_size
                        return [Sat]+[mtds[i]]
##                    print 'current abstraction invalid'
                    abs_bad = 1 
                    break #this kills off other verification engines working on bad abstraction
                else: #one of the engines undecided for some reason - failed?
                    print '\nParallel %s terminated without result on current abstr\n'%mtds[i]
                    continue
        if abs_bad and not time_done: #here we wait until have a new vabs.
            time_remain = t -(time.time() - tt)
            abc('r %s_abs.aig'%f_name) #read in the abstraction to destroy is_sat().
            if abs_done(time_remain):
                return [Undecided]+['timeout']
            res = read_and_sleep(5) #this will check every 5 sec, until abs_time sec has passed without new abs            
            if res == False: #found new vabs. Now continue if vabs small enough
##                print 'n_vabs = %d'%n_vabs
                if (not initial_size == sizeof()) and n_latches() > abs_ratio * initial_size[2]:
                    return [Undecided_no_reduction]+['no reduction']
                else:
                    continue
            elif res ==True: #read_and_sleep timed out
##                print 'read_and_sleep timed out'
                return [Undecided_no_reduction]+['no reduction']
            else:
                break #this should not happen
        elif abs_bad and time_done:
##            print 'current abstraction bad, time has run out'
            return [Undecided_no_reduction]+['no reduction']
        elif time_done: #abs is good here
##            print 'current abstraction still good, time has run out'
            return [Undecided]+['reduction'] #this will cause calling routine to try to verify the final abstraction
                            #right now handles the same as Undecided_no_reduction-if time runs out we quit abstraction
        else: #abs good and time not done
            continue
##            print 'current abstraction still good, time has not run out'
    return [len(funcs)]+['error']

def read_and_sleep(t=5):
    """
    keep looking for a new vabs every 5 seconds. This is usually run in parallel with
    &vta -d or &gla
    Returns False when new abstraction is found, and True when time runs out.
    """
    global cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
    #t is not used at present
    tt = time.time()
    T = 1000 #if after the last abstraction, no answer, then terminate
    T = abs_time + 10
    set_size()
    name = '%s_vabs.aig'%f_name
##    if ifbip > 0:
##        name = '%s_vabs.aig'%f_name
##    print 'name = %s'%name
    sleep(5)
    while True:
        if time.time() - tt > T: #too much time between abstractions
##            print 'read_and_sleep timed out in %d sec.'%T
            return True
        if os.access(name,os.R_OK):
            #possible race condition
            run_command('&r -s %s; &w %s_vabs_old.aig'%(name,f_name))
##            print '%s exists'%name
            if not os.access(name,os.R_OK): #if not readable now then what was read in might not be OK.
                print '%s does not exist'%name
                continue
##            print '%s is read'%name
##            run_command('&r %s;read_status %s_vabs.status'%(name,f_name)) #need to use & space to keep the abstraction information
            os.remove(name)
            run_command('read_status %s_vabs.status'%f_name)
##            print '%s and %s_vabs.status have been read'%(name,f_name)
##            print 'reading %s_vabs.status'%f_name
            #name is the derived model (not the model with abstraction info
            run_command('&r -s %s_vabs_old.aig'%f_name)
            run_command('&w %s_gla.aig'%f_name)
            run_command('&gla_derive;&put')
            run_command('w %s_gabs.aig'%f_name)
##            print '%s is removed'%name
            read_abs_values()
            time_abs_prev = time_abs
            time_abs = time.time()
##            print 'abs values has been read'
            run_command('read_status %s_vabs.status'%f_name) 
            abs_depth_prev = abs_depth
            abs_depth = n_bmc_frames()
            write_abs_values()
##            print 'abs values has been written'
            time_remain = T - (time.time() - tt)
            if abs_done(time_remain):
            	return True
##            if not check_size():
            if True:
                print '\nNew abstraction: ',
                ps()
##                print 'Time = %0.2f'%(time.time() - tt)
                set_size()
                abc('w %s_abs.aig'%f_name)
                return False
            #if same size, keep going.
        print '.',
        sleep(5)
####################################################
