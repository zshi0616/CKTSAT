import numpy as np 
import os 
import copy
import glob
import time 
import argparse
from wrapper import *

def get_parse_args():
    parser = argparse.ArgumentParser()
    
    # Required
    parser.add_argument('--case_dir', type=str, default='./testcase/', help='Directory of the case')

    # Parse and Initialize
    args = parser.parse_args()
    if not os.path.exists('./tmp'):
        os.mkdir('./tmp')
        
    return args

if __name__ == '__main__':
    args = get_parse_args()
    case_list = []
    for case_path in glob.glob(os.path.join(args.case_dir, '*.cnf')):
        case = os.path.basename(case_path)[:-4]
        case_list.append(case)
    tot_bl_time = 0
    tot_our_solvetime = 0
    tot_our_transtime = 0
    
    for case in case_list:
        if case == 'b30' or case == 'b28':
            continue
        print('[INFO] Case: {:}'.format(case))
        cnf_path = os.path.join(args.case_dir, '{}.cnf'.format(case) )
        cnf, no_vars = cnf_utils.read_cnf(cnf_path)
        ####################################################################
        # Baseline: CNF -> SAT
        ####################################################################
        bl_res, _, bl_timelist = baseline_solve(cnf_path)
        bl_time = bl_timelist[1]
        if bl_res == -1:
            print('[WARNING] Baseline Timeout')
        print('[INFO] Result: {:}'.format(bl_res))
        print('Baseline Time: {:.2f}s'.format(bl_timelist[1]))
        tot_bl_time += bl_time
        
        ####################################################################
        # C2L: CNF -> LUT -> CNF -> SAT
        ####################################################################
        # c2l_res, _, c2l_timelist = cnf2lut_solve(cnf_path)
        # c2l_time = c2l_timelist[0] + c2l_timelist[1]
        # if c2l_res == -1:
        #     print('[WARNING] c2l Timeout')
        # assert c2l_res == bl_res
        # print('[INFO] C2L Trans. {:.2f}s, Solve: {:.2f}s, Tot: {:.2f}s | Red.: {:.2f}%'.format(
        #     c2l_timelist[0], c2l_timelist[1], c2l_time, 
        #     (bl_time - c2l_time) / bl_time * 100
        # ))
        
        ####################################################################
        # C2LSAM: CNF -> LUT -> SAM -> CNF -> SAT
        ####################################################################
        c2lsam_res, asg, c2lsam_timelist, bench_idx = cnf2lut_samsat_solve_withmap(cnf_path)  # bench_idx 原始cnf中的变量 在新cnf中的位置(不是PIPO 用-1填充)
        c2lsam_time = c2lsam_timelist[0] + c2lsam_timelist[1]
        if c2lsam_res == -1:
            print('[WARNING] c2lsam Timeout')
        if bl_res != -1:
            assert c2lsam_res == bl_res
        print('[INFO] C2LSAM Trans. {:.2f}s, Solve: {:.2f}s, Tot: {:.2f}s | Red.: {:.2f}%'.format(
            c2lsam_timelist[0], c2lsam_timelist[1], c2lsam_time, 
            (bl_time - c2lsam_time) / bl_time * 100
        ))
        tot_our_solvetime += c2lsam_timelist[1]
        tot_our_transtime += c2lsam_timelist[0]
        
        # SOLVE
        if c2lsam_res == 0:
            print('[INFO] RESULT UNSAT' )
        elif c2lsam_res == -1:
            print('[INFO] RESULT UNKNOWN' )
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
            tot_time = c2lsam_time + new_solvetime
            tot_our_solvetime += new_solvetime
            
            if sat_status == 1:
                # BCP
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
                            print('{:}, UNSAT'.format(var))
                            check_cnf_res = False
                            break
                    if check_cnf_res == False:
                        break
                assert check_cnf_res
                print('[INFO] RESULT SAT  Tot: {:.2f}s | Red.: {:.2f}%'.format(tot_time,  (bl_time - tot_time) / bl_time * 100))
                print('SAT Assignment:{}'.format(new_asg))
            elif sat_status == 0:
                print('[INFO] RESULT UNSAT')
            else:
                print('[INFO] RESULT UNKNOWN' )    
        
        print()
    
    print()
    print('=' * 10 + ' PASS ' + '=' * 10)
    print('Total Baseline Time: {:.2f}s'.format(tot_bl_time))
    print('Our Total Trans. Time: {:.2f}s, Solve Time: {:.2f}s'.format(
        tot_our_transtime, tot_our_solvetime
    ))
