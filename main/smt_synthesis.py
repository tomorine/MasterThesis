# tomorow@ngc.is.ritsumei.ac.jp
# writing by python3
# coding:utf-8
from z3 import *
import time

# 特定のidを持つopと同じidを持つ部分回路所属するopを探す
def find_sub_node_id(id, subc_list):
    for tmp in range(len(subc_list)):
        sub_node = subc_list[tmp].find_node_id(id)
        if sub_node != -1:
            return sub_node
    return -1 # 存在しない場合1を返す

# opがどの部分回路に所属しているか判定
def check_sub_node(id, subc):
    if subc.find_node_id(id) != -1:
        return 1
    else:
        return -1

# 部分回路同士を繋ぎ合わせる制約
def do_smt_synthesis(circ, subc_list, subc_form_list, wd, hi):
    solve = Solver() # 制約式の集合
    nodelist = circ.intnode + circ.p_input + circ.p_output
    start = time.time()

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
    # ban_area[subc][i][j]が1の時subc以外のopがおけない
    # pin[op][i][j]はsubc内部のopの複数入出力を表現するために必要かも
    subc_core = [[[Int("subc_core[%d][%d][%d]" % (node, i, j)) for j in range(hi)] for i in range(wd)] for node in range(len(subc_form_list))]
    op = [[[Int("op[%d][%d][%d]" % (node, i, j)) for j in range(hi)] for i in range(wd)] for node in range(circ.global_node_num+1)]
    wire = [[[[Int("wire[%d][%d][%d][%d]" % (s, t,  i, j)) for j in range(hi)] for i in range(wd)] for t in range(circ.global_node_num+1)] for s in range(circ.global_node_num+1)]
    clock = [[Int("clock[%d][%d]" % (i, j)) for j in range(hi)] for i in range(wd)]
    connect =[[[[Int("connect[%d][%d][%d][%d]" % (i, j, k, l)) for l in range(hi+1)] for k in range(wd+1)] for j in range(hi+1)] for i in range(wd+1)]
    path = [[[[Int("path[%d][%d][%d][%d]" % (i, j, k, l)) for l in range(hi+1)] for k in range(wd+1)] for j in range(hi+1)] for i in range(wd+1)]
    node_clock = [Int("node_clock[%d]" % node) for node in range(circ.global_node_num+1)]
    node_distance = [Int("node_distance[%d]" % node) for node in range(circ.global_node_num+1)]
    subc_angle = [[Int("subc_angle[%d][%d]" % (i, j)) for j in range(8)] for i in range(len(subc_form_list))]
    ban_area = [[[Int("ban_area[%d][%d][%d]" % (subc, i, j)) for j in range(hi)] for i in range(wd)] for subc in range(len(subc_form_list))]
    #detour = [[Int("detour[%d][%d]" % (i, j)) for j in range(circ.global_node_num+1)] for i in range(circ.global_node_num+1)]
    input_length = [Int("input_length[%d]" % i) for i in range(circ.global_node_num+1)]
    # pin = [[[Int("pin[%d][%d][%d]" % (node, i, j)) for j in range(hi)] for i in range(wd)] for node in range(circ.global_node_num+1)]
    # 制約：デバッグ用
    for subc in range(len(subc_list)):
        solve.add(subc_angle[subc][0] == 1)
    # 制約：subcのコアはすべて配置される。
    print("# 制約：subcのコアはすべて配置される。")
    for subc in range(len(subc_form_list)):
        tmplist = list()
        for i in range(wd): # angle = 0
            for j in range(hi):
                solve.add(0 <= subc_core[subc][i][j], subc_core[subc][i][j] <= 1) # subc_coreの値の範囲
                if i + len(subc_form_list[subc]) < wd and j + len(subc_form_list[subc][0]) < hi: 
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][0] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][0] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # anole = 1
            for j in range(hi):
                if i - len(subc_form_list[subc]) >= 0 and j + len(subc_form_list[subc][0]) < hi:
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][1] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][1] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # anole = 2
            for j in range(hi):
                if i + len(subc_form_list[subc]) < wd  and j - len(subc_form_list[subc][0]) >= 0:
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][2] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][2] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # anole = 3
            for j in range(hi):
                if i - len(subc_form_list[subc]) >= 0  and j - len(subc_form_list[subc][0]) >= 0:
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][3] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][3] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # angle = 4
            for j in range(hi):
                if i + len(subc_form_list[subc][0]) < wd and j + len(subc_form_list[subc]) < hi: 
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][4] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][4] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # angle = 5
            for j in range(hi):
                if i - len(subc_form_list[subc][0]) >= 0 and j + len(subc_form_list[subc]) < hi: 
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][5] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][5] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # angle = 6
            for j in range(hi):
                if i + len(subc_form_list[subc][0]) < wd and j - len(subc_form_list[subc]) >= 0: 
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][6] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][6] == 1, Sum([tmp for tmp in tmplist]) == 1))
        tmplist.clear()
        for i in range(wd): # angle = 7
            for j in range(hi):
                if i - len(subc_form_list[subc][0]) >= 0 and j - len(subc_form_list[subc]) >= 0: 
                    tmplist.append(subc_core[subc][i][j])
                else:
                    solve.add(Implies(subc_angle[subc][7] == 1, subc_core[subc][i][j] == 0))
        solve.add(Implies(subc_angle[subc][7] == 1, Sum([tmp for tmp in tmplist]) == 1))
    # 制約：subcは同じ所には配置されない
    print("# 制約：subcは同じ所には配置されない")
    for i in range(wd):
        for j in range(hi):
            tmplist = list()
            for subc in range(len(subc_form_list)):
                tmplist.append(subc_core[subc][i][j])
            solve.add(Sum([tmp for tmp in tmplist]) <= 1)
    # 制約：subc_angleは８種類のうち1つだけ``
    print("# 制約：subc_angleは８種類のうち1つだけ``")
    for subc in range(len(subc_form_list)):
        tmplist = list()
        for ang in range(8):
            tmplist.append(subc_angle[subc][ang])
            solve.add(0 <= subc_angle[subc][ang], subc_angle[subc][ang] <= 1)
        solve.add(Sum([tmp for tmp in tmplist]) == 1)
    # 制約：subc_coreを起点にsubcを配置
    print("# 制約：subc_coreを起点にsubcを配置")
    for subc in range(len(subc_form_list)):
        sub_wd = len(subc_form_list[subc])
        sub_hi = len(subc_form_list[subc][0])
        for i in range(wd):
             for j in range(hi):
                solve.add(0 <= ban_area[subc][i][j], ban_area[subc][i][j] <= 1) # ban_areaの値域を設定
                for ir in range(sub_wd): # angle = 0
                    for jr in range(sub_hi):
                        if i + ir < wd and j + jr < hi:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                             subc_form_list[subc][ir][jr] >= 0,
                                             subc_angle[subc][0] == 1),
                                         ban_area[subc][i+ir][j+jr] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_form_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][0] == 1),
                                              op[subc_form_list[subc][ir][jr]][i+ir][j+jr] == 1))
                for ir in range(sub_wd): # angle = 1
                    for jr in range(sub_hi):
                        if i - ir >= 0 and j + jr < hi:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                             subc_form_list[subc][ir][jr] >= 0,
                                             subc_angle[subc][1] == 1),
                                         ban_area[subc][i-ir][j+jr] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_form_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][1] == 1),
                                              op[subc_form_list[subc][ir][jr]][i-ir][j+jr] == 1))
                for ir in range(sub_wd): # angle = 2
                    for jr in range(sub_hi):
                        if i + ir < wd and j - jr >= 0:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                             subc_form_list[subc][ir][jr] >= 0,
                                             subc_angle[subc][2] == 1),
                                         ban_area[subc][i+ir][j-jr] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_form_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][2] == 1),
                                              op[subc_form_list[subc][ir][jr]][i+ir][j-jr] == 1))
                for ir in range(sub_wd): # angle = 3
                    for jr in range(sub_hi):
                        if i - ir  >=  0 and j - jr >= 0:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                             subc_form_list[subc][ir][jr] >= 0,
                                             subc_angle[subc][3] == 1),
                                         ban_area[subc][i-ir][j-jr] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_form_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][3] == 1),
                                              op[subc_form_list[subc][ir][jr]][i-ir][j-jr] == 1))
                for ir in range(sub_wd): # angle = 4
                    for jr in range(sub_hi):
                        if i + jr < wd and j + ir < hi:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                             subc_form_list[subc][ir][jr] >= 0,
                                             subc_angle[subc][4] == 1),
                                         ban_area[subc][i+jr][j+ir] == 1))
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_form_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][4] == 1),
                                              op[subc_form_list[subc][ir][jr]][i+jr][j+ir] == 1))
                for ir in range(sub_wd): # angle = 5
                    for jr in range(sub_hi):
                        if i - jr >= 0 and j + ir < hi:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                             subc_form_list[subc][ir][jr] >= 0,
                                             subc_angle[subc][5] == 1),
                                         ban_area[subc][i-jr][j+ir] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_form_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][5] == 1),
                                              op[subc_form_list[subc][ir][jr]][i-jr][j+ir] == 1))
                for ir in range(sub_wd): # angle = 6
                    for jr in range(sub_hi):
                        if i + jr < wd and j - ir >= 0:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                             subc_form_list[subc][ir][jr] >= 0,
                                             subc_angle[subc][6] == 1),
                                         ban_area[subc][i+jr][j-ir] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_form_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][6] == 1),
                                              op[subc_form_list[subc][ir][jr]][i+jr][j-ir] == 1))
                for ir in range(sub_wd): # angle = 7
                    for jr in range(sub_hi):
                        if i - jr >= 0 and j - ir >= 0:
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                             subc_form_list[subc][ir][jr] >= 0,
                                             subc_angle[subc][7] == 1),
                                         ban_area[subc][i-jr][j-ir] == 1)) 
                            solve.add(Implies(And(subc_core[subc][i][j] == 1,
                                                  subc_form_list[subc][ir][jr] >= 1,
                                                  subc_angle[subc][7] == 1),
                                              op[subc_form_list[subc][ir][jr]][i-jr][j-ir] == 1))
    # 制約：すべてのopは0か1の値を取る
    print("# 制約：すべてのopは0か1の値を取る")
    # 制約：すべてのopは必ずどこかに配置する
    print("# 制約：すべてのopは必ずどこかに配置する")
    for node in nodelist:
        id = node.id
        tmplist = list()
        for i in range(wd):
            for j in range(hi):
                solve.add(0 <= op[id][i][j], op[id][i][j] <=1)
                tmplist.append(op[id][i][j])
        solve.add(Sum([tmp for tmp in tmplist]) == 1)
    # 制約：opが存在するクロックゾーンにはwireと別のopは存在できない。
    print("# 制約：opが存在するクロックゾーンにはwireと別のopは存在できない。")
    # 制約：wireの交差の限度
    print("# 制約：wireの交差の限度")
    for i in range(wd):
        for j in range(hi):
            oplist = list()
            wirelist = list()
            for node in nodelist:
                id = node.id
                oplist.append(op[id][i][j])
                for source in circ.find_node_id(id).input:
                    sid = source.id
                    wirelist.append(wire[sid][id][i][j])
            solve.add(Implies(Sum([tmp for tmp in oplist]) == 1, Sum([tmp for tmp in wirelist]) == 0))
            solve.add(Sum([tmp for tmp in oplist]) <= 1)
            solve.add(Sum([tmp for tmp in wirelist]) <= 3) # ここでwireの交差を許可するか決める
    # 制約：subc_coreは自分以外ban_areaに配置されない
    print("# 制約：subc_coreは自分以外ban_areaに配置されない")
    for subc in range(len(subc_form_list)):
        for others in range(len(subc_form_list)):
            if subc != others:
                for i in range(wd):
                    for j in range(hi):
                        solve.add(Implies(ban_area[others][i][j] == 1, subc_core[subc][i][j] == 0))
                        solve.add(Implies(ban_area[others][i][j] == 1, ban_area[subc][i][j] == 0))
    # 制約：すべてのクロックゾーンは1~4の値を持つ
    print("# 制約：すべてのクロックゾーンは1~4の値を持つ")
    for i in range(wd):
        for j in range(hi):
            solve.add(1 <= clock[i][j], clock[i][j] <= 4)
    # 制約：すべてのwireは0か1の値を取る
    print("# 制約：すべてのwireは0か1の値を取る")
    for node in nodelist:
        s = node.id
        for target in circ.find_node_id(s).output:
            t = target.id
            for i in range(wd):
                for j in range(hi):
                    tmplist = list()
                    for subc in range(len(subc_list)):
                        tmplist.append(ban_area[subc][i][j])
                    solve.add(0 <= wire[s][t][i][j], wire[s][t][i][j] <= 1)
                    solve.add(Implies(Sum([tmp for tmp in tmplist]) == 1, wire[s][t][i][j] == 0)) #ban_area
    # 制約：すべてのconnectは0か1の値を取る
    print("# 制約：すべてのconnectは0か1の値を取る")
    for i in range(wd):
        for j in range(hi):
            for k in range(wd):
                for l in range(hi):
                    solve.add(0 <= connect[i][j][k][l], connect[i][j][k][l] <= 1)
    # 制約：connectは空白のクロックゾーを跨ぐようには配置されない
    print("# 制約：connectは空白のクロックゾーを跨ぐようには配置されない")
    for i in range(wd):
        for j in range(hi):
            tmplist = list()
            tmplist.append(0)
            if i < wd and j < hi:
                for node in nodelist:
                    id = node.id
                    tmplist.append(op[id][i][j])
                    for source in circ.find_node_id(id).input:
                        sid = source.id # nodeの入力ノードのid
                        tmplist.append(wire[sid][id][i][j])
            if i < wd:
                solve.add(Implies(Sum([tmp for tmp in tmplist]) == 0,
                                  And(connect[i][j][i+1][j] == 0, connect[i+1][j][i][j] == 0)))
            if i > 0:
                solve.add(Implies(Sum([tmp for tmp in tmplist]) == 0,
                                  And(connect[i][j][i-1][j] == 0, connect[i-1][j][i][j] == 0)))
            if j < hi:
                solve.add(Implies(Sum([tmp for tmp in tmplist]) == 0,
                                  And(connect[i][j][i][j+1] == 0, connect[i][j+1][i][j] == 0)))
            if j > 0:
                solve.add(Implies(Sum([tmp for tmp in tmplist]) == 0,
                                  And(connect[i][j][i][j-1] == 0, connect[i][j-1][i][j] == 0)))
    # 制約：wireはループできない
    print("# 制約：wireはループできない")
    # 制約：pathは1か0の値を取る
    print("# 制約：pathは1か0の値を取る")
    for i in range(wd+1):
        for j in range(hi+1):
            for ir in range(wd+1):
                for jr in range(hi+1):
                    solve.add(0 <= path[i][j][ir][jr], path[i][j][ir][jr] <= 1)
                    solve.add(path[i][j][i][j] == 0)
                    for irr in range(wd+1):
                        for jrr in range(hi+1):
                            solve.add(Implies(And(path[i][j][ir][jr] == 1, path[ir][jr][irr][jrr] == 1), path[i][j][irr][jrr] == 1))
    # 制約：connectが存在する所にはpathも存在する
    print("# 制約：connectが存在する所にはpathも存在する")
    for i in range(wd):
        for j in range(hi):
            for ir in range(wd):
                for jr in range(hi):
                    solve.add(Implies(connect[i][j][ir][jr] == 1, path[i][j][ir][jr] == 1))
    """
    # 制約：部分回路外と繋がるパスが１以下の時、opと隣接するconnectが存在する
    # 制約：pinが存在する場所にはconncetが存在する
    for i in range(wd):
        for j in range(hi):
            inlist = list()
            outlist = list()
            if i < wd - 1:
                inlist.append(connect[i+1][j][i][j])
                outlist.append(connect[i][j][i+1][j])
            if i > 0:
                inlist.append(connect[i-1][j][i][j])
                outlist.append(connect[i][j][i-1][j])
            if j < hi - 1:
                inlist.append(connect[i][j+1][i][j])
                outlist.append(connect[i][j][i][j+1])
            if j > 0:
                inlist.append(connect[i][j-1][i][j])
                outlist.append(connect[i][j][i][j-1])
            for node in nodelist:
                id = node.id
                sub_node = find_sub_node_id(id, subc_list)
                diff_input = len(node.input) - len(sub_node.input)
                diff_output = len(node.output) - len(sub_node.output)
                diff_connect = diff_input + diff_output
                solve.add(Implies(op[id][i][j] == 1,
                                  Sum([tmp for tmp in inlist]) == diff_input))
                solve.add(Implies(op[id][i][j] == 1,
                                  Sum([tmp for tmp in outlist]) == diff_output))
                solve.add(Implies(And(diff_connect == 1, op[id][i][j] == 1),
                                  Sum([tmp for tmp in inlist]) == diff_input))
                solve.add(Implies(And(diff_connect == 1, op[id][i][j] == 1),
                                  Sum([tmp for tmp in outlist]) == diff_output))
                solve.add(Implies(pin[id][i][j] == 1, Sum([tmp for tmp in inlist]) == diff_input))
                solve.add(Implies(pin[id][i][j] == 1, Sum([tmp for tmp in outlist]) == diff_output))
                """
    """
    # 制約：wireが存在するクロックゾーンにはconnectが存在する
    for i in range(wd):
        for j in range(hi):
            for node in nodelist:
                id = node.id
                inlist = list()
                outlist = list()
                if i < wd - 1:
                    inlist.append(connect[i+1][j][i][j])
                    outlist.append(connect[i][j][i+1][j])
                if i > 0:
                    inlist.append(connect[i-1][j][i][j])
                    outlist.append(connect[i][j][i-1][j])
                if j < hi - 1:
                    inlist.append(connect[i][j+1][i][j])
                    outlist.append(connect[i][j][i][j+1])
                if j > 0:
                    inlist.append(connect[i][j-1][i][j])
                    outlist.append(connect[i][j][i][j-1])
                for source in circ.find_node_id(id).input:
                    sid = source.id # nodeの入力ノードのid
                    solve.add(Implies(wire[sid][id][i][j] == 1, Sum([tmp for tmp in inlist]) == 1))
                    solve.add(Implies(wire[sid][id][i][j] == 1, Sum([tmp for tmp in outlist]) == 1))
    """
    # 制約：wireの交差が無限にできる場合の特殊な制約式
    print("# 制約：wireの交差が無限にできる場合の特殊な制約式")
    for node in nodelist:
        id = node.id
        for k in range(len(subc_list)):
            if check_sub_node(id, subc_list[k]) == 1:
                for source in circ.find_node_id(id).input:
                    sid = source.id
                    if check_sub_node(sid, subc_list[k]) == -1:
                        tmplist = list()
                        for i in range(wd):
                            for j in range(hi):
                                for ir in range(wd):
                                    for jr in range(hi):
                                        solve.add(Implies(And(op[id][i][j] == 1, op[sid][ir][jr] == 1),
                                                          input_length[id] == abs(i-ir) + abs(j-jr)))
                                        """
    # 制約：connectが存在するクロックゾーンにはopかwireが存在する
    print("#　制約：connectが存在するクロックゾーンにはopかwireが存在する")
    for i in range(wd):
        for j in range(hi):
            for node in nodelist:
                id = node.id
                for k in range(len(subc_list)):
                    if check_sub_node(id, subc_list[k]) == 1:
                        for source in circ.find_node_id(id).input:
                             sid = source.id 
                             if check_sub_node(sid, subc_list[k]) == -1:
                                right = list()
                                left = list()
                                up = list()
                                down = list()
                                if i < wd - 1:
                                    right.append(wire[sid][id][i+1][j])
                                    right.append(op[sid][i+1][j])
                                if i > 0:
                                    left.append(wire[sid][id][i-1][j])
                                    left.append(op[sid][i-1][j])
                                if j < hi - 1:
                                    down.append(wire[sid][id][i][j+1])
                                    down.append(op[sid][i][j+1])
                                if j > 0:
                                    up.append(wire[sid][id][i][j-1])
                                    up.append(op[sid][i][j-1])
                                solve.add(Implies(Or(op[id][i][j] == 1, wire[sid][id][i][j] == 1),
                                                  Sum([tmp for tmp in right]) * connect[i+1][j][i][j]
                                                  + Sum([tmp for tmp in left]) * connect[i-1][j][i][j]
                                                  + Sum([tmp for tmp in down]) * connect[i][j+1][i][j]
                                                  + Sum([tmp for tmp in up]) * connect[i][j-1][i][j] == 1))
                                """
                                """
                        for target in circ.find_node_id(id).output:
                            tid = target.id
                            if check_sub_node(tid, subc_list[k]) == -1:
                                right = list()
                                left = list()
                                up = list()
                                down = list()
                                if i < wd - 1:
                                    right.append(wire[id][tid][i+1][j])
                                    right.append(op[tid][i+1][j])
                                if i > 0:
                                    left.append(wire[id][tid][i-1][j])
                                    left.append(op[tid][i-1][j])
                                if j < hi - 1:
                                    down.append(wire[id][tid][i][j+1])
                                    down.append(op[tid][i][j+1])
                                if j > 0:
                                    up.append(wire[id][tid][i][j-1])
                                    up.append(op[tid][i][j-1])
                                solve.add(Implies(Or(op[id][i][j] == 1, wire[id][tid][i][j] == 1),
                                                  Sum([tmp for tmp in right]) * connect[i][j][i+1][j]
                                                  + Sum([tmp for tmp in left]) * connect[i][j][i-1][j]
                                                  + Sum([tmp for tmp in down]) * connect[i][j][i][j+1]
                                                  + Sum([tmp for tmp in up]) * connect[i][j][i][j-1] == 1))

    """
    """
    # 制約：connectは双方向にならない
    for i in range(wd):
        for j in range(hi):
            tmplist = list()
            if i < wd:
                tmplist.append(connect[i+1][j][i][j])
                tmplist.append(connect[i][j][i+1][j])
                solve.add(Sum([tmp for tmp in tmplist]) <= 1)
                tmplist.clear()
            if i > 0:
                tmplist.append(connect[i-1][j][i][j])
                tmplist.append(connect[i][j][i-1][j])
                solve.add(Sum([tmp for tmp in tmplist]) <= 1)
                tmplist.clear()
            if j < hi:
                tmplist.append(connect[i][j+1][i][j])
                tmplist.append(connect[i][j][i][j+1])
                solve.add(Sum([tmp for tmp in tmplist]) <= 1)
                tmplist.clear()
            if j > 0:
                tmplist.append(connect[i][j-1][i][j])
                tmplist.append(connect[i][j][i][j-1])
                solve.add(Sum([tmp for tmp in tmplist]) <= 1)
                tmplist.clear()
    # 制約：pinはban areaには配置されない
    for i in range(wd):
        for j in range(hi):
            banlist = list()
            tmplist = list()
            for subc in range(len(subc_form_list)):
                banlist.append(ban_area[subc][i][j])
            for node in nodelist:
                id = node.id
                tmplist.append(pin[id][i][j])
                solve.add(0 <= pin[id][i][j], pin[id][i][j] <= 1)
            solve.add(Implies(Sum([tmp for tmp in banlist]) >= 1, Sum([tmp for tmp in tmplist]) == 0))
            solve.add(Sum([tmp for tmp in tmplist]) <= 1)
    # 制約：各Pinはどこかに１つだけ
    for node in nodelist:
        id = node.id
        tmplist = list()
        for i in range(wd):
            for j in range(hi):
                tmplist.append(pin[id][i][j])
        solve.add(Sum([tmp for tmp in tmplist]) <= 1)
    # 制約：subcの内部のopから必要ならpinが出る
    for i in range(wd):
        for j in range(hi):
            for node in nodelist:
                id = node.id
                sub_node = find_sub_node_id(id, subc_list)
                all_connect = len(node.input + node.output)
                inter_connect = len(sub_node.input + sub_node.output)
                diff_connect = all_connect - inter_connect
                tmplist = list()
                if i < wd-1:
                    tmplist.append(pin[id][i+1][j])
                if i > 0:
                    tmplist.append(pin[id][i-1][j])
                if j < hi-1:
                    tmplist.append(pin[id][i][j+1])
                if j > 0:
                    tmplist.append(pin[id][i][j-1])
                solve.add(Implies(And(op[id][i][j] == 1, diff_connect >= 2),
                             Sum([tmp for tmp in tmplist]) == 1))
                solve.add(Implies(diff_connect <= 1, Sum([tmp for tmp in tmplist]) == 0))
    # 制約：connectが存在するクロックゾーンにはopかwireかpinが存在する
    for i in range(wd):
        for j in range(hi):
            for node in nodelist:
                id = node.id
                sub_node = find_sub_node_id(id, subc_list)
                sub_id = sub_node.id
                diff_input = len(node.input) - len(sub_node.input)
                diff_output = len(node.output) - len(sub_node.output)
                diff_connect = diff_input + diff_output
                for k in range(len(subc_list)):
                    if check_sub_node(id, subc_list[k]) == 1:
                        for source in node.input:
                            sid = source.id
                            if check_sub_node(sid, subc_list[k]) == -1:
                                right = list()
                                left = list()
                                up = list()
                                down = list()
                                if i < wd - 1:
                                    right.append(wire[sid][id][i+1][j])
                                    right.append(op[sid][i+1][j])
                                    right.append(pin[sid][i+1][j])
                                if i > 0:
                                    left.append(wire[sid][id][i-1][j])
                                    left.append(op[sid][i-1][j])
                                    left.append(pin[sid][i-1][j])
                                if j < hi - 1:
                                    down.append(wire[sid][id][i][j+1])
                                    down.append(op[sid][i][j+1])
                                    down.append(pin[sid][i][j+1])
                                if j > 0:
                                    up.append(wire[sid][id][i][j-1])
                                    up.append(op[sid][i][j-1])
                                    up.append(pin[sid][i][j-1])
                                if diff_connect >= 2 and diff_input >= 1:
                                    solve.add(Implies(Or(pin[id][i][j] == 1, wire[sid][id][i][j] == 1),
                                                      Sum([tmp for tmp in right]) * connect[i+1][j][i][j]
                                                      + Sum([tmp for tmp in left]) * connect[i-1][j][i][j]
                                                      + Sum([tmp for tmp in down]) * connect[i][j+1][i][j]
                                                      + Sum([tmp for tmp in up]) * connect[i][j-1][i][j]
                                                      == 1))
                                elif diff_input >= 1:
                                    solve.add(Implies(Or(op[id][i][j] == 1, wire[sid][id][i][j] == 1),
                                                      Sum([tmp for tmp in right]) * connect[i+1][j][i][j]
                                                      + Sum([tmp for tmp in left]) * connect[i-1][j][i][j]
                                                      + Sum([tmp for tmp in down]) * connect[i][j+1][i][j]
                                                      + Sum([tmp for tmp in up]) * connect[i][j-1][i][j]
                                                      == 1))
                        for target in node.output:
                            tid = target.id
                            if check_sub_node(tid, subc_list[k]) == -1:
                                right = list()
                                left = list()
                                up = list()
                                down = list()
                                if i < wd - 1:
                                    right.append(wire[id][tid][i+1][j])
                                    right.append(op[id][i+1][j])
                                    right.append(pin[id][i+1][j])
                                if i > 0:
                                    left.append(wire[id][tid][i-1][j])
                                    left.append(op[id][i-1][j])
                                    left.append(pin[id][i-1][j])
                                if j < hi - 1:
                                    down.append(wire[id][tid][i][j+1])
                                    down.append(op[id][i][j+1])
                                    down.append(pin[id][i][j+1])
                                if j > 0:
                                    up.append(wire[id][tid][i][j-1])
                                    up.append(op[id][i][j-1])
                                    up.append(pin[id][i][j-1])
                                if diff_connect >= 2 and diff_output >= 1:
                                    solve.add(Implies(Or(pin[id][i][j] == 1, wire[id][tid][i][j] == 1),
                                                      Sum([tmp for tmp in right]) * connect[i][j][i+1][j]
                                                      + Sum([tmp for tmp in left]) * connect[i][j][i-1][j]
                                                      + Sum([tmp for tmp in down]) * connect[i][j][i][j+1]
                                                      + Sum([tmp for tmp in up]) * connect[i][j][i][j-1]
                                                      == 1))
                                elif diff_output >= 1:
                                    solve.add(Implies(Or(op[id][i][j] == 1, wire[id][tid][i][j] == 1),
                                                      Sum([tmp for tmp in right]) * connect[i][j][i+1][j]
                                                      + Sum([tmp for tmp in left]) * connect[i][j][i-1][j]
                                                      + Sum([tmp for tmp in down]) * connect[i][j][i][j+1]
                                                      + Sum([tmp for tmp in up]) * connect[i][j][i][j-1]
                                                      == 1))
    # pinからopにはconnectがつながらない（双方向）
    for node in nodelist:
        id = node.id
        for i in range(wd):
            for j in range(hi):
                for ir in range(wd):
                    for jr in range(hi):
                        solve.add(Implies(And(pin[id][i][j] == 1, op[id][ir][jr] == 1),
                                          And(connect[i][j][ir][jr] == 0, connect[ir][jr][i][j] == 0)))
                        solve.add(Implies(And(op[id][i][j] == 1, pin[id][ir][jr] == 1),
                                          And(connect[i][j][ir][jr] == 0, connect[ir][jr][i][j] == 0)))
                                    """
    #print sat or
    print("z3ちゃんは必死に考えてます")
    reason = solve.check()
    elapsed_time = time.time() - start
    print("elapsed time:{0}".format(elapsed_time) + "[sec]")
    if reason == sat:
        model = solve.model()
        # print subc_core
        print("subc_core")
        for j in range(hi):
            for i in range(wd):
                frg = " "
                for subc in range(len(subc_form_list)):
                    if model[subc_core[subc][i][j]].as_long() == 1:
                        frg = subc
                print("[%s]" % frg, end = '')
            print()
        print()
        # print op
        print("op")
        for j in range(hi):
            for i in range(wd):
                frg = ' '
                for node in nodelist:
                    id = node.id
                    if model[op[id][i][j]].as_long() == 1:
                        frg = id
                print("[%s]" % frg, end ='')
            print()
        print()
        """
        # print pin
        print("pin")
        for j in range(hi):
            for i in range(wd):
                frg = ' '
                for node in nodelist:
                    id = node.id
                    # print("pin[%d][%d][%d] == %d" % (id, i, j, model[pin[id][i][j]].as_long()))
                    if model[pin[id][i][j]].as_long() == 1:
                        frg = id
                print("[%s]" % frg, end='')
            print()
        print()
        """
        # print connect
        """
        print("\nconnect") 
        for j in range(hi):
            for i in range(wd-1):
                print("[ ]", end='')
                model_right = model[connect[i][j][i+1][j]].as_long()
                model_left =  model[connect[i+1][j][i][j]].as_long()
                if model_right + model_left == 2:
                    print("-", end='')
                elif model_right == 1:
                    print(">", end='')
                elif model_left == 1:
                    print("<", end='')
                elif model_right == 0 and model_left == 0:
                    print(" ", end='')
            print("[ ]")
            for i in range(wd):
                model_down = model[connect[i][j][i][j+1]].as_long()
                model_up = model[connect[i][j+1][i][j]].as_long()
                if j < hi-1 and model_down == 1 and model_up == 1:
                    print(" | ", end='')
                elif j < hi-1 and model_down == 1:
                    print(" v ", end='')
                elif j < hi-1 and model_up == 1:
                    print(" ^ ", end='')
                elif j < hi-1 and model_down == 0 and model_up == 0:
                    print("   ", end='')
                print(" ", end='')
            print()
        """
        # print ban area
        print("ban area")
        for subc in range(len(subc_form_list)):
            for j in range(hi):
                for i in range(wd):
                    if model[ban_area[subc][i][j]].as_long() == 1:
                        print("[1]" , end = '')
                    else:
                        print("[ ]", end = '')
                print()
            print()
            """
        #print wire
        print("\nwire")
        for node in nodelist:
            print(node.id)
            for j in range(hi):
                frg = '*'
                frg2 = '*'
                for i in range(wd):
                    t = node.id
                    for source in circ.find_node_id(t).input:
                        s = source.id
                        if model[wire[s][t][i][j]].as_long() != 0:
                            frg = s
                            frg2 = t
                    print(' [%s:%s] ' % (frg, frg2), end='')
                frg = '*'
                frg2 = '*'
                print()
            print()
            """
    else:
        print(reason)
