# tomorow@ngc.is.ritsumei.ac.jp
# writing by python3 
# coding:utf-8
from network import *
from sub_network import *
from collections import defaultdict
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
    #print("---------\n---------\n---------\n---------\n")
    #sub_circ = MakeSubNetwork(circ, 2)
    #calc_kmeans(sub_circ, 2)
    
