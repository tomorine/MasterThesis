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
    # van_area[subc][i][j]が1の時subc以外のopがおけない
    # pin[op][i][j]はsubc内部のopの複数入出力を表現するために必要かも
    subc_core = [[[Int("subc_core[%d][%d][%d]" % (node, i, j)) for j in range(hi)] for i in range(wd)] for node in range(len(subc_list))]
    op = [[[Int("op[%d][%d][%d]" % (node, i, j)) for j in range(hi)] for i in range(wd)] for node in range(circ.global_node_num+1)]
    wire = [[[[Int("wire[%d][%d][%d][%d]" % (s, t,  i, j)) for j in range(hi)] for i in range(wd)] for t in range(circ.global_node_num+1)] for s in range(circ.global_node_num+1)]
    clock = [[Int("clock[%d][%d]" % (i, j)) for j in range(hi)] for i in range(wd)]
    connect =[[[[Int("connect[%d][%d][%d][%d]" % (i, j, k, l)) for l in range(hi+1)] for k in range(wd+1)] for j in range(hi+1)] for i in range(wd+1)]
    path = [[[[Int("path[%d][%d][%d][%d]" % (i, j, k, l)) for l in range(hi+1)] for k in range(wd+1)] for j in range(hi+1)] for i in range(wd+1)]
    node_clock = [Int("node_clock[%d]" % node) for node in range(circ.global_node_num+1)]
    node_distance = [Int("node_distance[%d]" % node) for node in range(circ.global_node_num+1)]
    subc_angle = [[Int("subc_angle[%d][%d]" % (i, j)) for j in range(8)] for i in range(len(subc_list))]
    van_area = [[[Int("van_area[%d][%d][%d]" % (subc, i, j)) for j in range(hi)] for i in range(wd)] for subc in range(len(subc_list))]
    pin = [[[Int("pin[%d][%d][%d]" % (node, i, j)) for j in range(hi)] for i in range(wd)] for node in range(circ.global_node_num+1)]
    # 制約：デバッグ用
    solve.add(subc_angle[0][7] == 1)
    # 制約：subcのコアはすべて配置される。
    for subc in range(len(subc_list)):
        tmplist = list()
        for i in range(wd): # angle = 0
            for j in range(hi):
                solve.add(0 <= subc_core[subc][i][j], subc_core[subc][i][j] <= 1) # subc_coreの値の範囲
                if i + len(subc_list[subc]) < wd and j + len(subc_list[subc][0]) < hi: 
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][0] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][0] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # anole = 1
            for j in range(hi):
                if i - len(subc_list[subc]) >= 0 and j + len(subc_list[subc][0]) < hi:
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][1] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][1] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # anole = 2
            for j in range(hi):
                if i + len(subc_list[subc]) < wd  and j - len(subc_list[subc][0]) >= 0:
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][2] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][2] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # anole = 3
            for j in range(hi):
                if i - len(subc_list[subc]) >= 0  and j - len(subc_list[subc][0]) >= 0:
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][3] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][3] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # angle = 4
            for j in range(hi):
                if i + len(subc_list[subc][0]) < wd and j + len(subc_list[subc]) < hi: 
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][4] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][4] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # angle = 5
            for j in range(hi):
                if i - len(subc_list[subc][0]) >= 0 and j + len(subc_list[subc]) < hi: 
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][5] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][5] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # angle = 6
            for j in range(hi):
                if i + len(subc_list[subc][0]) < wd and j - len(subc_list[subc]) >= 0: 
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][6] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][6] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # angle = 7
            for j in range(hi):
                if i - len(subc_list[subc][0]) >= 0 and j - len(subc_list[subc]) >= 0: 
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][7] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][7] == 1, Sum([tmp for tmp in tmplist]) == 1))
    # 制約：subcは同じ所には配置されない
    for i in range(wd):
        for j in range(hi):
            tmplist = list()
            for subc in range(len(subc_list)):
                tmplist.append(subc_core[subc][i][j])
            solve.add(Sum([tmp for tmp in tmplist]) <= 1)
    # 制約：subc_angleは８種類のうち1つだけ``
    for subc in range(len(subc_list)):
        tmplist = list()
        for ang in range(8):
            tmplist.append(subc_angle[subc][ang])
            solve.add(0 <= subc_angle[subc][ang], subc_angle[subc][ang] <= 1)
        solve.add(Sum([tmp for tmp in tmplist]) == 1)
    # 制約：subc_coreを起点にsubcを配置
    for i in range(wd):
        for j in range(hi):
            for subc in range(len(subc_list)):
                solve.add(0 <= van_area[subc][i][j], van_area[subc][i][j] <= 1) # van_areaの値域を設定
                sub_wd = len(subc_list[subc])
                sub_hi = len(subc_list[subc][0])
                for ir in range(sub_wd): # angle = 0
                    for jr in range(sub_hi):
                        if i + ir < wd and j + jr < hi:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 0,
                                                  subc_angle[subc][0] == 1),
                                              van_area[subc][i+ir][j+jr] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][0] == 1),
                                              op[subc_list[subc][ir][jr]][i+ir][j+jr] == 1))
                for ir in range(sub_wd): # angle = 1
                    for jr in range(sub_hi):
                        if i - ir >= 0 and j + jr < hi:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 0,
                                                  subc_angle[subc][1] == 1),
                                              van_area[subc][i-ir][j+jr] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][1] == 1),
                                              op[subc_list[subc][ir][jr]][i-ir][j+jr] == 1))
                for ir in range(sub_wd): # angle = 2
                    for jr in range(sub_hi):
                        if i + ir < wd and j - jr >= 0:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 0,
                                                  subc_angle[subc][2] == 1),
                                              van_area[subc][i+ir][j-jr] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][2] == 1),
                                              op[subc_list[subc][ir][jr]][i+ir][j-jr] == 1))
                for ir in range(sub_wd): # angle = 3
                    for jr in range(sub_hi):
                        if i - ir  >=  0 and j - jr >= 0:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 0,
                                                  subc_angle[subc][3] == 1),
                                              van_area[subc][i-ir][j-jr] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][3] == 1),
                                              op[subc_list[subc][ir][jr]][i-ir][j-jr] == 1))
                for ir in range(sub_wd): # angle = 4
                    for jr in range(sub_hi):
                        if i + jr < wd and j + ir < hi:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 0,
                                                  subc_angle[subc][4] == 1),
                                              van_area[subc][i+jr][j+ir] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][4] == 1),
                                              op[subc_list[subc][ir][jr]][i+jr][j+ir] == 1))
                for ir in range(sub_wd): # angle = 5
                    for jr in range(sub_hi):
                        if i - jr >= 0 and j + ir < hi:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 0,
                                                  subc_angle[subc][5] == 1),
                                              van_area[subc][i-jr][j+ir] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][5] == 1),
                                              op[subc_list[subc][ir][jr]][i-jr][j+ir] == 1))
                for ir in range(sub_wd): # angle = 6
                    for jr in range(sub_hi):
                        if i + jr < wd and j - ir >= 0:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 0,
                                                  subc_angle[subc][6] == 1),
                                              van_area[subc][i+jr][j-ir] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][6] == 1),
                                              op[subc_list[subc][ir][jr]][i+jr][j-ir] == 1))
                for ir in range(sub_wd): # angle = 7
                    for jr in range(sub_hi):
                        if i - jr >= 0 and j - ir >= 0:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 0,
                                                  subc_angle[subc][7] == 1),
                                              van_area[subc][i-jr][j-ir] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][7] == 1),
                                              op[subc_list[subc][ir][jr]][i-jr][j-ir] == 1))
    # 制約：subc_coreは自分以外van_areaに配置されない
    for subc in range(len(subc_list)):
        for others in range(len(subc_list)):
            if subc != others:
                for i in range(wd):
                    for j in range(hi):
                        solve.add(Implies(van_area[others][i][j] == 1, subc_core[subc][i][j] == 0))
                        solve.add(Implies(van_area[others][i][j] == 1, van_area[subc][i][j] == 0))
    # 制約：pinはvan areaには配置されない
    for i in range(wd):
        for j in range(hi):
            vanlist = list()
            tmplist = list()
            for subc in range(len(subc_list)):
                vanlist.append(van_area[subc][i][j])
            for node in nodelist:
                id = node.id
                tmplist.append(pin[id][i][j])
                solve.add(0 <= pin[id][i][j], pin[id][i][j] <= 1)
            solve.add(Implies(Sum([tmp for tmp in vanlist]) >= 1, Sum([tmp for tmp in tmplist]) == 0))
            solve.add(Sum([tmp for tmp in tmplist]) <= 1)
    # 制約：各Pinはどこかに１つだけ
    for node in nodelist:
        id = node.id
        tmplist = list()
        for i in range(wd):
            for j in range(hi):
                tmplist.append(pin[id][i][j])
        solve.add(Sum([tmp for tmp in tmplist]) <= 1)
    # 制約：subcの内部のopから必要ならpinが出る（未完）
    for i in range(wd):
        for j in range(hi):
            for node in nodelist:
                id = node.id
                tmplist = list()
                if i < wd-1:
                    tmplist.append(pin[id][i+1][j])
                if i > 0:
                    tmplist.append(pin[id][i-1][j])
                if j < hi-1:
                    tmplist.append(pin[id][i][j+1])
                if j > 0:
                    tmplist.append(pin[id][i][j-1])
                solve.add(Implies(op[id][i][j] == 1, Sum([tmp for tmp in tmplist]) == 1))
    # 制約：すべてのopは0か1の値を取る
    # 制約：すべてのopは必ずどこかに配置する
    for node in nodelist:
        id = node.id
        tmplist = list()
        for i in range(wd):
            for j in range(hi):
                solve.add(0 <= op[id][i][j], op[id][i][j] <=1)
                tmplist.append(op[id][i][j])
        solve.add(Sum([tmp for tmp in tmplist]) == 1)
    #print sat or
    print("z3ちゃんは必死に考えてます")
    reason = solve.check()
    if reason == sat:
        model = solve.model()
        print("van area")
        for j in range(hi):
            for i in range(wd):
                frg = 0
                for subc in range(len(subc_list)):
                    if model[van_area[subc][i][j]].as_long() == 1:
                        frg = 1
                print("[%d]" % frg, end = '')
            print()
        print()
        print("op")
        for j in range(hi):
            for i in range(wd):
                frg = '*'
                for node in nodelist:
                    id = node.id
                    if model[op[id][i][j]].as_long() == 1:
                        frg = id
                print("[%s]" % frg, end ='')
            print()
        print()
        print("subc core")
        for subc in range(len(subc_list)):
            for j in range(hi):
                for i in range(wd):
                    if model[subc_core[subc][i][j]].as_long() == 1:
                        print("[%d]" % subc, end = '')
                    else:
                        print("[ ]", end = '')
                print()
            print()
        print("pin")
        for j in range(hi):
            for i in range(wd):
                frg = '*'
                for node in nodelist:
                    id = node.id
                    # print("pin[%d][%d][%d] == %d" % (id, i, j, model[pin[id][i][j]].as_long()))
                    if model[pin[id][i][j]].as_long() == 1:
                        frg = id
                print("[%s]" % frg, end='')
            print()
        print()     
    else:
        print(reason)
                
    
