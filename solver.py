import numpy as np
import os
import copy
import glob
import time
import argparse
from wrapper import *
import sys

if __name__ == '__main__':

    cnf_path = sys.argv[1]
    cnf, no_vars = cnf_utils.read_cnf(cnf_path)
    c2lsam_res, asg, c2lsam_timelist, bench_idx = cnf2lut_samsat_solve_withmap(cnf_path)  # bench_idx 原始cnf中的变量 在新cnf中的位置(不是PIPO 用-1填充)
    c2lsam_time = c2lsam_timelist[0] + c2lsam_timelist[1]

    # SOLVE
    if c2lsam_res == -1:
        print('s UNKNOWN')
    elif c2lsam_res == 0:
        print('s UNSATISFIABLE')
        
    elif c2lsam_res == 1:
        partial_asg = []
        for i in range(no_vars):
            if  bench_idx[i] != -1:
                partial_asg.append(asg[bench_idx[i]])
            else:
                partial_asg.append(-1)
        new_cnf = []
        for i in range(no_vars):
            if partial_asg[i] == 1:
                new_clause = [i+1]
                new_cnf.append(new_clause)
            elif partial_asg[i] == 0:
                new_clause = [-1*(i+1)]
                new_cnf.append(new_clause)
        cnf += new_cnf
        sat_status, new_asg, new_solvetime = cnf_utils.kissat_solve(cnf, no_vars, args='--time={}'.format(TIMEOUT))
        
        if sat_status == 1:
            # BCP  用自己的case检验过 后面可以删掉
            check_cnf_res = True
            bcp_cnf = copy.deepcopy(cnf)
            remove_flag = [False] * len(bcp_cnf)
            for var in range(1, no_vars +1):
                var_value = new_asg[var-1]
                for clause_k, clause in enumerate(bcp_cnf):
                    if remove_flag[clause_k]:
                        continue
                    if var_value == 1:
                        if var in clause:
                            remove_flag[clause_k] = True
                            continue
                        if -var in clause:
                            clause.remove(-var)
                    else:
                        if -var in clause:
                            remove_flag[clause_k] = True
                            continue
                        if var in clause:
                            clause.remove(var)

                for clause_k, clause in enumerate(bcp_cnf):
                    if len(clause) == 0:
                        # print('{:}, UNSAT'.format(var))
                        check_cnf_res = False
                        break
                if check_cnf_res == False:
                    break
            if check_cnf_res == False:
                print('s UNKNOWN')
            print('s SATISFIABLE')
            print('v {}'.format(new_asg))
        elif sat_status == 0:
            print('s UNSATISFIABLE')
        else:
            print('s UNKNOWN')