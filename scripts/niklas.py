import os
import sys
import time
import tempfile
import subprocess

from contextlib import contextmanager

import pyabc
import pyabc_split

@contextmanager
def temp_file_names(N, suffix=""):
    
    files = []
    
    try:
        
        for i in xrange(N):
            files.append( tempfile.NamedTemporaryFile(suffix=suffix) )
            
        yield [ f.name for f in files ]
    
    finally:
        for f in files:
            f.close()
        
def parse_bip_status(status):
    
    res = {}
    
    for line in open(status, 'r'):
        
        line = line.strip()
        
        colon = line.find(':')
        
        if colon < 0:
            continue
            
        field = line[:colon]
        data = line[colon+2:]
        
        res[field] = data
    
    return res

def run_bip(args, aiger):

    with temp_file_names(1) as tmpnames:

        args = [
            'bip',
            '-abc',
            '-input=%s'%aiger,
            '-output=%s'%tmpnames[0],
        ] + args;
        
        rc = subprocess.call(args, preexec_fn=pyabc._set_death_signal)
        
        if rc!=0:
            return None
            
        return parse_bip_status(tmpnames[0])

from pyaig import AIG, read_aiger, write_aiger, utils

def run_niklas_single(aiger, simplify, report_result, timeout=None):
    
    orig_args = [
        [ ',live', '-k=l2s', '-eng=treb-abs' ],
        [ ',live', '-k=inc' ],
        [ ',live', '-k=l2s', '-eng=bmc' ],
    ]
    
    simplified_args = [
        [ ',live', '-k=inc' ],
        [ ',live', '-k=l2s', '-eng=bmc' ],
        [ ',live', '-k=l2s', '-eng=treb' ],
    ]
    
    with temp_file_names(1, suffix='.aig') as simple_aiger:

        orig_funcs = [ pyabc_split.defer(run_bip)(a, aiger) for a in orig_args ]
        simplified_funcs = [ pyabc_split.defer(run_bip)(a, simple_aiger[0]) for a in simplified_args ]

        with pyabc_split.make_splitter() as splitter:

            sleep_id = splitter.fork_one( lambda : time.sleep(timeout ) ) if timeout else None
            
            ids = splitter.fork_all( orig_funcs )
            kill_if_simplified = ids[1:]
            
            simplifier_id = splitter.fork_one( pyabc_split.defer(simplify)(aiger, simple_aiger[0]) )
            
            for id, res in splitter:
                
                if id == sleep_id:
                    return False
                
                if id == simplifier_id:
                    if not res:
                        continue
                    splitter.kill(kill_if_simplified)
                    splitter.fork_all( simplified_funcs )
                    continue
                    
                if report_result(res):
                    return True

    return False

def run_niklas_multi(aiger, simplify, report_result):
    
    with open(aiger, 'r') as fin:
        aig = read_aiger( fin )
        
    n_j_pos = aig.n_justice()
    assert n_j_pos > 0
    
    if n_j_pos==1:
        return run_niklas_single( aiger, simplify, report_result=lambda res: report_result(0, res) )
    
    with temp_file_names(n_j_pos, suffix='.aig') as single_aiger:
        
        def extract(j_po):
            with open(single_aiger[j_po], 'w') as fout:
                write_aiger(utils.extract_justice_po(aig, j_po), fout)
                
        for _ in pyabc_split.split_all_full( [pyabc_split.defer(extract)(i) for i in xrange(n_j_pos) ] ):
            pass
            
        unsolved = set( xrange(n_j_pos) )
        
        timeout = 1
        
        while unsolved:
            for j_po in sorted(unsolved):
                if run_niklas_single( single_aiger[j_po], simplify, report_result=lambda res: report_result(j_po, res), timeout=timeout ):
                    unsolved.remove(j_po)
            timeout *= 2
        
    return not unsolved
    
if __name__ == "__main__":    

    def simplify(aiger_in, aiger_out):

        with temp_file_names(2, suffix='.aig') as tmp:

            saved = utils.save_po_info(aiger_in, tmp[0])

            pyabc.run_command( 'read_aiger %s'%tmp[0] )
            pyabc.run_command( 'dc2 ; dc2 ; dc2 ; dc2' )
            pyabc.run_command( 'write_aiger %s'%tmp[1] )

            utils.restore_po_info( saved, tmp[1], aiger_out )
            
        return True

    def report_result(id, res):
        
        if res and 'result' in res:
            result = res['result']
            if result=='proved':
                print "PROVED: ", id
                return True
            elif result=='failed':
                print "FAILED:", id
                return True
            
        return False
        
    aiger = "test.aig"

    while True:
        try:
            run_niklas_multi(aiger, simplify=simplify, report_result=report_result)
        except:
            import traceback
            traceback.print_exc()

