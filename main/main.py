# tomorow@ngc.is.ritsumei.ac.jp
# writing by python3 
# coding:utf-8
from network import *
from sub_network import *
from collections import defaultdict
from smt_minimum import *
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
    #print_node_all(circ)
    #print("---------\n---------\n---------\n---------\n")
    sub_circ = list()
    for i in range(1, 4):
        #print("\n\n")
        sub_circ.append(MakeSubNetwork(circ, i))
    print_node_all(sub_circ[0])
    for i in range(1,6):
        for j in range(1,6):
            tmp = do_smt_minimum(sub_circ[0], i, j)
            print("%d:%d" % (i, j))
            if tmp != "unsat":
                for ir in range(j):
                    for jr in range(i):
                        print("[%d]" % tmp[jr][ir], end='')
                    print()
                print()
                break
    """
    check = list()
    for i in range (3):
        print(i)
        check.append(-1)
        for j in range(1, 4):
            for k in range(1, 4):
                check[i] = do_smt_minimum(sub_circ[i], j, k)
                if check[i] != "unsat":
                    for ir in range(k):
                        for jr in range(j):
                            print(check[i][jr][ir])
                        print()
                    print()
                    break
    #calc_kmeans(sub_circ, 2)
"""
