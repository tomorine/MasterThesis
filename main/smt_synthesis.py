# tomorow@ngc.is.ritsumei.ac.jp
# writing by python3
# coding:utf-8
from z3 import *

def do_smt_synthesis(circ, subc_list, wd, hi):
    solve = Solver() # 制約式の集合
    nodelist = circ.intnode + circ.p_input + circ.p_output

    # 変数の集合
    # subc_cire_core[k]は座標[i][j]に存在する時に1になる。これ起点にsubcを配置する。
    # subc[k]が座標[i][j]に存在する時に1になる
    # wire[s][t]が座標[i][j]に存在する時に1になる
    # clock[i][j]はクロックゾーンの種類を保持
    # connect[i][j][k][l]はクロックゾーン[i][j]から[k][l]に対してのパスが存在する時に１になる
    # pathはwireのループを防ぐための変数
    # node_clockはノードの存在するクロックゾーンのクロックナンバーを保持
    # node_distanceは特定のノードのinputからの距離を保持
    # subc_angle[subc][ang]はsubcの置き方を決める
    subc_core = [[[Int("op_core[%d][%d][%d]" % (node, i, j)) for j in range(hi)] for i in range(wd)] for node in range(circ.global_node_num+1)]
    subc = [[[Int("op[%d][%d][%d]" % (node, i, j)) for j in range(hi)] for i in range(wd)] for node in range(circ.global_node_num+1)]
    wire = [[[[Int("wire[%d][%d][%d][%d]" % (s, t,  i, j)) for j in range(hi)] for i in range(wd)] for t in range(circ.global_node_num+1)] for s in range(circ.global_node_num+1)]
    clock = [[Int("clock[%d][%d]" % (i, j)) for j in range(hi)] for i in range(wd)]
    connect =[[[[Int("connect[%d][%d][%d][%d]" % (i, j, k, l)) for l in range(hi+1)] for k in range(wd+1)] for j in range(hi+1)] for i in range(wd+1)]
    path = [[[[Int("path[%d][%d][%d][%d]" % (i, j, k, l)) for l in range(hi+1)] for k in range(wd+1)] for j in range(hi+1)] for i in range(wd+1)]
    node_clock = [Int("node_clock[%d]" % node) for node in range(circ.global_node_num+1)]
    node_distance = [Int("node_distance[%d]" % node) for node in range(circ.global_node_num+1)]
    subc_angle = [[Int("subc_angle[i][j]" % (i, j)) for j in range(8)] for i in range(len(len(subc_list)))]
    # 制約：subcのコアはすべて配される。
    for subc in range(len(subc_list)):
        tmplsit = list()
        for i in range(wd):
            for j in range(hi):
                tmplist.append(subc_core[subc][i][j])
                solve.add(0 <= subc_core[subc][i][j], subc_core[id][i][j] <= 1) # subc_coreの値の範囲
        solve.add(Sum([tmp for tmp in tmplist]) == 1)
    # 制約：subc_angleは８種類のうち1つだけ
    for subc in range(len(subc_list)):
        tmplsit = list()
        for ang in range(8):
            tmplist.append(subc_angle[subc][ang])
            solve.add(0 <= subc_angle[subc][ang], subc_angle[subc][ang] <= 1)
        solve.add(Sum([tmp for tmp in tmplist]) == 1)
    # 制約：subc_coreを起点にsubcを配置
    for i in range(wd):
        for j in range(hi):
            for subc in range(len(subc_list)):
                
    
