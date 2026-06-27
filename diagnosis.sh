#!/bin/bash

python3 gen_diag_dofile.py "diag17.ptn" "./testcase/c17_pa.bench" "generated.dofile" "./Project_25S_diag/failLog/c17-001.failLog"
./abc -f generated.dofile
./diagnosis 22 diag0.cnf diag1.cnf diag2.cnf diag3.cnf diag4.cnf diag5.cnf diag6.cnf diag7.cnf
./kissat/build/kissat combined.cnf