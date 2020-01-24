# tomorow@ngc.is.ritsumei.ac.jp
# writing by python3 
# coding:utf-8
from network import *
from sub_network import *
from collections import defaultdict
from smt_minimum import *
from smt_synthesis import *
import sys

if __name__ == '__main__':
    # コマンドラインからファイルを引数で取得
    argv = sys.argv
    argc = len(argv)
    if argc!=2:
        # print ("Usage: python3 ",argv[0]," filename circuit_wide circuit_high")
        print ("Usage: python3 ", argv[0], "filename")
        quit()
    str = argv[1]
    circ = MakeNetwork.verilog(str)
    calc_cood(circ)
    calc_kmeans(circ, 3)
    print_node_all(circ)
    # do_smt_minimum(circ, 4, 5)
    print("---------\n---------\n---------\n---------\n")
    subc_list = list()
    subc_form_list = list()
    for i in range(1, 4):
        subc_list.append(MakeSubNetwork(circ, i))
    for subc in subc_list:
        min_size = 100
        min_circ = "None"
        for i in range(1,6):
            for j in range(i,6):
                if i * j >= min_size:
                    break
                tmp = do_smt_minimum(subc, i, j)
                if tmp != "unsat" and i*j < min_size:
                    min_circ = tmp
                    min_size = i*j
                    for ir in range(j):
                        for jr in range(i):
                            print("[%d]" % tmp[jr][ir], end='')
                        print()
                    print()
                    break
        subc_form_list.append(min_circ)
    do_smt_synthesis(circ, subc_list, subc_form_list, 8, 9)
    """
    check = list()
    for i in range (3):
        print(i)
        check.append(-1)
        for j in range(1, 4):
            for k in range(1, 4):
                check[i] = do_smt_minimum(subc_list[i], j, k)
                if check[i] != "unsat":
                    for ir in range(k):
                        for jr in range(j):
                            print(check[i][jr][ir])
                        print()
                    print()
                    break
    #calc_kmeans(subc_list, 2)
    """
