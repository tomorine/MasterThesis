# tomorow@ngc.is.ritsumei.ac.jp
# writing by python3
# coding:utf-8
# todo：instanceとかいうくそわかりにくい変数名を変える
from z3 import *
import network
import sub_network

def do_smt_minimum(circ, wd, hi):
    solve = Solver() # 制約式の集合
    nodelist = circ.p_input + circ.p_output + circ.intnode
    
    # 変数の集合
    # op[k]が座標[i][j]に存在する時に1になる
    # wire[s][t]が座標[i][j]に存在する時に1になる
    # clock[i][j]はクロックゾーンの種類を保持
    # connect[i][j][k][l]はクロックゾーン[i][j]から[k][l]に対してのパスが存在する時に１になる
    # pathはwireのループを防ぐための変数
    # node_clockはノードの存在するクロックゾーンのクロックナンバーを保持
    # node_distanceは特定のノードのinputからの距離を保持
    op = [[[Int("op[%d][%d][%d]" % (node, i, j)) for j in range(hi)] for i in range(wd)] for node in range(circ.global_node_num+1)]
    wire = [[[[Int("wire[%d][%d][%d][%d]" % (s, t,  i, j)) for j in range(hi)] for i in range(wd)] for t in range(circ.global_node_num+1)] for s in range(circ.global_node_num+1)]
    clock = [[Int("clock[%d][%d]" % (i, j)) for j in range(hi)] for i in range(wd)]
    connect =[[[[Int("connect[%d][%d][%d][%d]" % (i, j, k, l)) for l in range(hi+1)] for k in range(wd+1)] for j in range(hi+1)] for i in range(wd+1)]
    path = [[[[Int("path[%d][%d][%d][%d]" % (i, j, k, l)) for l in range(hi+1)] for k in range(wd+1)] for j in range(hi+1)] for i in range(wd+1)]
    node_clock = [Int("node_clock[%d]" % node) for node in range(circ.global_node_num+1)]
    node_distance = [Int("node_distance[%d]" % node) for node in range(circ.global_node_num+1)]
    # 制約：回路内に存在しないゲートは配置しない
    for i in range(circ.global_node_num+1):
        frg = 0
        for instance in nodelist:
            node = instance.id
            if node == i:
                frg = 1
        if frg == 0:
            for j in range(wd):
                for k in range(hi):
                    solve.add(op[i][j][k] == 0)
    # 制約：すべてのopは0か1の値を取る
    # 制約：すべてのopは必ずどこかに配置する
    for instance in nodelist:
        node = instance.id
        tmplist = list()
        for i in range(wd):
            for j in range(hi):
                solve.add(0 <= op[node][i][j], op[node][i][j] <=1)
                tmplist.append(op[node][i][j])
        solve.add(Sum([tmp for tmp in tmplist]) == 1)
    # 制約：すべてのwireは0か1の値を取る
    for instance in nodelist:
        s = instance.id
        for node in circ.find_node_id(s).output:
            t = node.id
            for i in range(wd):
                for j in range(hi):
                    solve.add(0 <= wire[s][t][i][j], wire[s][t][i][j] <= 1)
    # 制約：connectは0か1の値を取る
    for i in range(wd+1):
        for j in range(hi+1):
            for k in range(wd+1):
                for l in range(hi+1):
                    solve.add(0 <= connect[i][j][k][l], connect[i][j][k][l] <= 1)
    # 制約：すべてのクロックゾーンは1~4の値を持つ
    for i in range(wd):
        for j in range(hi):
            solve.add(1 <= clock[i][j], clock[i][j] <= 4)
    """
    # 制約：各クロックゾーンには1つのopかwireしか存在できない
    for j in range(hi):
        for i in range(wd):
            tmplist = list()
            for s in range(len(nodelist)):
                for node in circ.find_node_id(s).output:
                    t = node.id
                    tmplist.append(wire[s][t][i][j])
                tmplist.append(op[s][i][j])
            solve.add(Sum([tmp for tmp in tmplist]) <= 1)
    """
    # 制約：opが存在するクロックゾーンにはwireと別のopは存在できない。
    # 制約：wireの交差の限度
    for i in range(wd):
        for j in range(hi):
            oplist = list()
            wirelist = list()
            for instance in nodelist:
                node = instance.id
                oplist.append(op[node][i][j])
                for source in circ.find_node_id(node).input:
                    id = source.id
                    wirelist.append(wire[id][node][i][j])
            solve.add(Implies(Sum([tmp for tmp in oplist]) == 1, Sum([tmp for tmp in wirelist]) == 0))
            solve.add(Sum([tmp for tmp in oplist]) <= 1)
            solve.add(Sum([tmp for tmp in wirelist]) <= 1) # ここでwireの交差を許可するか決める
    # todo:オプショナル制約：wireは交差以外で交わらない
    # 制約：opが存在するクロックゾーンの、隣接するクロックゾーンには同じ数のファンイン（アウト）connectが存在する
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
            for instance in nodelist:
                node = instance.id
                solve.add(Implies(op[node][i][j] == 1, Sum([tmp for tmp in inlist]) == len(circ.find_node_id(node).input)))
                solve.add(Implies(op[node][i][j] == 1, Sum([tmp for tmp in outlist]) == len(circ.find_node_id(node).output)))
    # 制約：wireが存在するクロックゾーンにはconnectが存在する
    for i in range(wd):
        for j in range(hi):
            for instance in nodelist:
                node = instance.id
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
                for source in circ.find_node_id(node).input:
                    id = source.id # nodeの入力ノードのid
                    solve.add(Implies(wire[id][node][i][j] == 1, Sum([tmp for tmp in inlist]) == 1))
                    solve.add(Implies(wire[id][node][i][j] == 1, Sum([tmp for tmp in outlist]) == 1))
    #　制約： connectが存在するクロックゾーンにはopかwireが存在する
    for i in range(wd):
        for j in range(hi):
            for instance in nodelist:
                node = instance.id
                for source in circ.find_node_id(node).input:
                    id = source.id # nodeの入力ノードのid
                    right = list()
                    left = list()
                    up = list()
                    down = list()
                    if i < wd - 1:
                        right.append(wire[id][node][i+1][j])
                        right.append(op[id][i+1][j])
                    if i > 0:
                        left.append(wire[id][node][i-1][j])
                        left.append(op[id][i-1][j])
                    if j < hi - 1:
                        down.append(wire[id][node][i][j+1])
                        down.append(op[id][i][j+1])
                    if j > 0:
                        up.append(wire[id][node][i][j-1])
                        up.append(op[id][i][j-1])
                    solve.add(Implies(Or(op[node][i][j] == 1, wire[id][node][i][j] == 1),
                                  Sum([tmp for tmp in right]) * connect[i+1][j][i][j]
                                  + Sum([tmp for tmp in left]) * connect[i-1][j][i][j]
                                  + Sum([tmp for tmp in down]) * connect[i][j+1][i][j]
                                  + Sum([tmp for tmp in up]) * connect[i][j-1][i][j] == 1))
                for target in circ.find_node_id(node).output:
                    id = target.id # nodeの出力ノードのid
                    right = list()
                    left = list()
                    up = list()
                    down = list()
                    if i < wd - 1:
                        right.append(wire[node][id][i+1][j])
                        right.append(op[id][i+1][j])
                    if i > 0:
                        left.append(wire[node][id][i-1][j])
                        left.append(op[id][i-1][j])
                    if j < hi - 1:
                        down.append(wire[node][id][i][j+1])
                        down.append(op[id][i][j+1])
                    if j > 0:
                        up.append(wire[node][id][i][j-1])
                        up.append(op[id][i][j-1])
                    solve.add(Implies(Or(op[node][i][j] == 1, wire[node][id][i][j] == 1),
                                  Sum([tmp for tmp in right]) * connect[i][j][i+1][j]
                                  + Sum([tmp for tmp in left]) * connect[i][j][i-1][j]
                                  + Sum([tmp for tmp in down]) * connect[i][j][i][j+1]
                                  + Sum([tmp for tmp in up]) * connect[i][j][i][j-1] == 1))
    # 制約：wireはループできない
    # 制約：pathは1か0の値を取る
    for i in range(wd+1):
        for j in range(hi+1):
            for ir in range(wd+1):
                for jr in range(hi+1):
                    solve.add(0 <= path[i][j][ir][jr], path[i][j][ir][jr] <= 1)
                    solve.add(path[i][j][i][j] == 0)
                    for irr in range(wd+1):
                        for jrr in range(hi+1):
                            solve.add(Implies(And(path[i][j][ir][jr] == 1, path[ir][jr][irr][jrr] == 1), path[i][j][irr][jrr] == 1))
    # 制約：connectの距離は1以上にならない
    for i in range(wd+1):
        for j in range(hi+1):
            for ir in range(wd+1):
                for jr in range(hi+1):
                    if abs(j -jr) + abs (i-ir) >= 2:
                        solve.add(connect[i][j][ir][jr] == 0)
    # 制約：connectが存在する所にはpathも存在する
    for i in range(wd):
        for j in range(hi):
            for ir in range(wd):
                for jr in range(hi):
                    solve.add(Implies(connect[i][j][ir][jr] == 1, path[i][j][ir][jr] == 1))
    # 制約：空白のクロックゾーンからconnectは出ない
    for i in range(wd+1):
        for j in range(hi+1):
            tmplist = list()
            tmplist.append(0)
            if i < wd and j < hi:
                for instance in nodelist:
                    node = instance.id
                    tmplist.append(op[node][i][j])
                    for source in circ.find_node_id(node).input:
                        id = source.id # nodeの入力ノードのid
                        tmplist.append(wire[id][node][i][j])
            if i < wd:
                solve.add(Implies(Sum([tmp for tmp in tmplist]) == 0, And(connect[i][j][i+1][j] == 0, connect[i+1][j][i][j] == 0)))
            if i > 0:
                solve.add(Implies(Sum([tmp for tmp in tmplist]) == 0, And(connect[i][j][i-1][j] == 0, connect[i-1][j][i][j] == 0)))
            if j < hi:
                solve.add(Implies(Sum([tmp for tmp in tmplist]) == 0, And(connect[i][j][i][j+1] == 0, connect[i][j+1][i][j] == 0)))
            if j > 0:
                solve.add(Implies(Sum([tmp for tmp in tmplist]) == 0, And(connect[i][j][i][j-1] == 0, connect[i][j-1][i][j] == 0)))
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
    # 制約：クロックゾーンの数字に従ってのみconnectは1になる
    for i in range(wd):
        for j in range(hi):
            if i < wd - 1:
                solve.add(If(connect[i][j][i+1][j] == 1, Or(And(clock[i][j] == 1, clock[i+1][j] == 2),
                                                        And(clock[i][j] == 2, clock[i+1][j] == 3),
                                                        And(clock[i][j] == 3, clock[i+1][j] == 4),
                                                        And(clock[i][j] == 4, clock[i+1][j] == 1)),
                         connect[i][j][i+1][j] == 0))
            if i > 0:
                solve.add(If(connect[i][j][i-1][j] == 1, Or(And(clock[i][j] == 1, clock[i-1][j] == 2),
                                                        And(clock[i][j] == 2, clock[i-1][j] == 3),
                                                        And(clock[i][j] == 3, clock[i-1][j] == 4),
                                                        And(clock[i][j] == 4, clock[i-1][j] == 1)),
                         connect[i][j][i-1][j] == 0))
            if j < hi -1:
                solve.add(If(connect[i][j][i][j+1] == 1, Or(And(clock[i][j] == 1, clock[i][j+1] == 2),
                                                        And(clock[i][j] == 2, clock[i][j+1] == 3),
                                                        And(clock[i][j] == 3, clock[i][j+1] == 4),
                                                        And(clock[i][j] == 4, clock[i][j+1] == 1)),
                         connect[i][j][i][j+1] == 0))
            if j > 0:
                solve.add(If(connect[i][j][i][j-1] == 1, Or(And(clock[i][j] == 1, clock[i][j-1] == 2),
                                                        And(clock[i][j] == 2, clock[i][j-1] == 3),
                                                        And(clock[i][j] == 3, clock[i][j-1] == 4),
                                                        And(clock[i][j] == 4, clock[i][j-1] == 1)),
                         connect[i][j][i][j-1] == 0))
    # 制約：node_clock[id] => op[id][i][j]=1時のclock[i][j]の値
    for i in range(wd):
        for j in range(hi):
            for instance in nodelist:
                node = instance.id
                solve.add(Implies(op[node][i][j] == 1, node_clock[node] == clock[i][j]))
   
    # 関数：スループットを向上させる関数
    def search_length(source, target, tmplist):
        for i in range(wd):
            for j in range(hi):
                tmplist.append(wire[source.id][target.id][i][j])
        if source.type == "input" or source.type == "p_input" or len(source.input) == 0:
            tmplist.append(node_clock[source.id])
            return (tmplist)
        else:
            tmplist.append(1)
            tmplist = search_length(source.input[0], source, tmplist)
            return tmplist
    # 制約：スループットを向上させる（再帰的）
    for instance in nodelist:
        node = instance.id
        tmplistlist = list()
        target = circ.find_node_id(node)
        #if circ.find_node_id(node).type == "output":
        if len(target.input) >= 2:
            for source in target.input:
                tmplist = list()
                search_length(source, target, tmplist)
                tmplistlist.append(tmplist)
            solve.add(Sum([tmp for tmp in tmplistlist[0]]) == Sum([tmp for tmp in tmplistlist[1]]))
    """
    # 制約：inputとoutputのノードが一番外側に来る
    for node in nodelist:
        id = node.id
        if node.type == "input" or node.type == "output":
            outermost = list()
            if hi >= 2:
                for i in range(wd):
                    outermost.append(op[id][i][0])
                    outermost.append(op[id][i][hi-1])
            if wd >= 2:
                for j in range(1, hi-1):
                    outermost.append(op[id][0][j])
                    outermost.append(op[id][wd-1][j])
            if len(outermost) >= 2:
                solve.add(Sum([tmp for tmp in outermost]) == 1)
    """
    # 制約：inputとoutputのノードが一番外側に来る（各位置固定）
    for node in nodelist:
        id = node.id
        if node.type == "input":
            outermost = list()
            if hi >= 2:
                for i in range(wd):
                    outermost.append(op[id][i][0])
            if wd >= 2:
                for j in range(1, hi-1):
                    outermost.append(op[id][0][j])
            if len(outermost) >= 2:
                solve.add(Sum([tmp for tmp in outermost]) == 1)
        if node.type == "output":
            outermost = list()
            if hi >= 2:
                for i in range(wd):
                    outermost.append(op[id][i][hi-1])
            if wd >= 2:
                for j in range(1, hi-1):
                    outermost.append(op[id][wd-1][j])
            if len(outermost) >= 2:
                solve.add(Sum([tmp for tmp in outermost]) == 1)
            
    # print model or
    # print("z3ちゃんは考え中です")
    reason = solve.check()
    if reason == sat:
        model = solve.model()
        circ_form =[[-1 for j in range(hi)] for i in range(wd)]
        for i in range(wd):
            for j in range(hi):
                for node in nodelist:
                    id = node.id
                    if model[op[id][i][j]].as_long() == 1:
                        circ_form[i][j] = id
                        #print("[%d]" % id, end='')
                        break
                    else:
                        for source in node.input:
                            sid = source.id
                            if model[wire[sid][id][i][j]].as_long() == 1:
                                circ_form[i][j] = 0
    if reason == sat:
        print("QCA circuit [%s] size is %d:%d" % (circ.name, wd, hi))
        return circ_form
    elif reason == unsat:
        return("unsat")
    """
    if reason == sat:
        model = solve.model()
        print("operator") # print operator
        for j in range(hi):
            frg = '*'
            for i in range(wd):
                for instance in nodelist:
                    node = instance.id
                    if model[op[node][i][j]].as_long() != 0:
                        frg = node
                print(" [%s] " % frg, end='')
                frg = '*'
            print()
        print("\nwire") # print wire
        for j in range(hi):
            frg = '*'
            frg2 = '*'
            for i in range(wd):
                for instance in nodelist:
                    t = instance.id
                    for source in circ.find_node_id(t).input:
                        s = source.id
                        if model[wire[s][t][i][j]].as_long() != 0:
                            frg = s
                            frg2 = t
                print(' [%s:%s] ' % (frg, frg2), end='')
                frg = '*'
                frg2 = '*'
            print()
        print("\nconnect") # print connect
        for j in range(hi):
            for i in range(wd-1):
                print("[ ]", end='')
                if model[connect[i][j][i+1][j]].as_long() == 1:
                    print(">", end='')
                if model[connect[i+1][j][i][j]].as_long() == 1:
                    print("<", end='')
                if model[connect[i][j][i+1][j]].as_long() == 0 and model[connect[i+1][j][i][j]].as_long() == 0:
                    print(" ", end='')
            print("[ ]")
            for i in range(wd):
                if j < hi-1 and model[connect[i][j][i][j+1]].as_long() == 1:
                    print(" v ", end='')
                if j < hi-1 and model[connect[i][j+1][i][j]].as_long() == 1:
                    print(" ^ ", end='')
                if j < hi-1 and model[connect[i][j][i][j+1]].as_long() == 0 and model[connect[i][j+1][i][j]].as_long() == 0:
                    print("   ", end='')
                print(" ", end='')
            print()
        print("\nclock_zone") # print clokc zone
        for j in range(hi):
            for i in range(wd):
                print(" [%d] " % model[clock[i][j]].as_long(), end='')
            print()
        print()
    else:
        print(reason)
    """
