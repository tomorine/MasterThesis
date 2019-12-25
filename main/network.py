# tomorow@ncg.is.ritsumei.ac.jp
# writing by python3
# coding:utf-8
import re
import random
import numpy as np
import sys
import sub_network

# ネットワーククラス
class CreateNetwork:
    def __init__(self, name):
        self.name = name
        self.intnode = list()
        self.p_input = list()
        self.p_output = list()
        self.max_depth = 0 # 回路の中のゲートが持つ最大のdepth
        self.depth = 0
        
    # 中間ノードの追加
    def add_intnode(self, node):
        frg = 0
        for tmp in self.intnode:
            if tmp == node:
                frg = 1
        if frg == 0:
            self.intnode.append(node)
            node.type = "intnode"
            return
        print("error: already exist %s" % node.name)

    # 外部入力の追加
    def add_input(self, node):
        frg = 0
        for tmp in self.p_input:
            if tmp == node:
                frg = 1
        if frg == 0:
            self.p_input.append(node)
            node.depth = 0
            node.type = "input"
            return
        print("error: already exist %s" % node.name)

    # 外部出力の追加
    def add_output(self, node):
        frg = 0
        for tmp in self.p_output:
            if tmp == node:
                frg = 1
        if frg == 0:
            self.p_output.append(node)
            node.type = "output"
            return
        print("error: already exist %s" % node.name)
            
    # ノードを名前で探す
    def find_node(self, name):
        for tmp in self.intnode:
            if tmp.name == name:
                return (tmp)
        for tmp in self.p_input:
            if tmp.name == name:
                return (tmp)
        for tmp in self.p_output:
            if tmp.name == name:
                return (tmp)
        # print("error: no exist %s" % name)
        return(-1) # 存在しない場合は-1を返す

# ノードクラス
class CreateNode:
    def __init__(self, name):
        self.name = name
        self.type = "None"
        self.input = list()
        self.output = list()
        #self.clstr = -1
        self.clstr = [-1]
        self.depth = -1
        self.height = -1

    # ノードの入力の追加
    def add_input(self, node):
        self.input.append(node)

    # ノードの出力の追加
    def add_output(self, node):
        self.output.append(node)

    # ノードのクラスタ（いらないかも）
    def define_cluster(self, clstr, dep):
        self.clstr[dep] = clstr
        

# ファイルから回路情報を読み取ってネットワークを作成する関数
class MakeNetwork:
    @classmethod
    def verilog(cls, filename):
        f = open(filename)
        for line in f:
            data = [i for i in re.split("[, ;\n]", line) if i != '']
            # ネットワークの生成
            if data[0] == "endmodule":
                break
            if data[0] == "module":
                circ = CreateNetwork(data[1])
            # 外部入力の定義
            if data[0] == "input":
                for tmp in data:
                    if tmp != "input":
                        circ.add_input(CreateNode(tmp))
            # 外部出力の定義
            if data[0] == "output":
                for tmp in data:
                    if tmp != "output":
                        circ.add_output(CreateNode(tmp))
            # 中間ノードの定義
            if data[0] == "wire":
                for tmp in data:
                    if tmp != "wire":
                        circ.add_intnode(CreateNode(tmp))
            # ノード情報の登録
            if data[0] == "assign":
                data.pop(0) # "assign"を削除
                main_node = circ.find_node(data[0])
                for tmp in data:
                    if tmp != '&' and tmp != '=' and tmp != '|' and tmp != main_node.name:
                        if tmp[0] == '~':
                            if circ.find_node(tmp) == -1:
                                tmp_node = CreateNode(tmp)
                                tmp_node.add_input(circ.find_node(tmp.lstrip('~')))
                                circ.find_node(tmp.lstrip('~')).add_output(tmp_node)
                                circ.add_intnode(tmp_node)
                            else:
                                tmp_node = circ.find_node(tmp)
                            tmp_node.add_output(main_node)
                            main_node.add_input(tmp_node)
                        else:
                            main_node.add_input(circ.find_node(tmp))
                            circ.find_node(tmp).add_output(main_node)
        f.close()
        return circ
                        
# ノードの情報を表示
def print_node(node, dep):
    print("node: %s (%d. %.1f)" % (node.name, node.depth, node.height)) # 第２位以下切捨表示
    print("cluster = %d" % (node.clstr[dep]))
    if len(node.input) != 0:
        print("input = ", end ='')
        for tmp in node.input:
            print("%s, " %  tmp.name, end = '')
        print()
    if len(node.output) != 0:
        print("output = ", end ='')
        for tmp in node.output:
            print("%s, " %  tmp.name, end = '')
        print("\n")

# 回路全体のノードの情報を表示
def print_node_all(circ):
    print('circuit name:', circ.name)
    print("--------intnode list--------")
    for node in circ.intnode:
        print_node(node, circ.depth)
    print("--------input list--------")
    for node in circ.p_input:
        print_node(node, circ.depth)
    print("--------output list--------")
    for node in circ.p_output:
        print_node(node, circ.depth)        

# すべてのノードの座標を計算
def calc_cood(circ):
    for input in circ.p_input:# 深さの計算
        for node in input.output:  
            calc_depth(node)
    calc_height_init(circ)# 高さの初期化
    for node in circ.p_output: # 最大高さの計算
        circ.max_depth = max(circ.max_depth, node.depth)
    for i in range(1, circ.max_depth):
        for node in circ.intnode:
            if node.depth == i:
                calc_height(node)
    for node in circ.p_output:
        calc_height(node)
    

# 深さを計算するための再起関数
def calc_depth(node):
    depth = -2
    for tmp in node.input:
        depth = max(depth, tmp.depth)
    node.depth = depth +1
    if node.type == "output":
        return
    for tmp in node.output:
        calc_depth(tmp)

# 高さを計算するための再起関数
def calc_height(node):
    sum = 0.0
    for tmp in node.input:
        sum += tmp.height
    node.height = sum/len(node.input)

# 初期の高さを計算（暫定）
def calc_height_init(circ):
    max = 0
    for node in circ.p_output:
        if max < node.depth:
            max = node.depth
    unit = max/len(circ.p_input) # 単位あたりの高さを計算（深さに対して）
    # for i in circ.p_input: 
    for i in range(1, len(circ.p_input)+1):
        circ.p_input[i-1].height = float(i*unit)
            
# k-means本体
def calc_kmeans(circ, k):
    node_list = circ.intnode + circ.p_output + circ.p_input
    init_clstr(circ, k)
    # 初期クラスタをランダムに配置(k++に変更)
    # for node in circ.intnode: 
    #    node.clstr = int(random.uniform(1.0, k+0.99999999))
    # for node in circ.p_output:
    #    node.clstr = int(random.uniform(1.0, k+0.99999999))
    #print_node_all(circ)
    gp_list_p = list() # すべての重心が変わらなくなるまで計算
    while(1):
        #print_node_clstr(circ, k)
        frg = 0 # かっこ悪い
        gp_list = list()
        for i in range(1, k+1):
            gp_list.append(calc_gp(circ, i))
        for node in node_list:
            min_distance = 10000000 # とてつもなく大きい数字
            for i in range(k):
                distance = ((gp_list[i][0]-node.depth)**2 + (gp_list[i][1]-node.height)**2)**(1/2)
                #print("gp[%d] = (%.2f %.2f)" % (i+1, gp_list[i][0], gp_list[i][1]))
                if distance < min_distance:
                    min_distance = distance
                    node.clstr[circ.depth] = i+1
        for i in range(len(gp_list_p)):
            if gp_list[i][0] != gp_list_p[i][0] or gp_list[i][1] != gp_list_p[i][1]:
                frg = 1
                break
        if len(gp_list_p) == 0:
            frg = 1
        if frg == 1:
            gp_list_p = gp_list
        else:
            break

# 初期クラスタの設定（k-means++）
def init_clstr(circ, k):
    node_list = circ.intnode + circ.p_output + circ.p_input
    print("number of circ node = ", len(node_list))
    first_node = random.choice(node_list)
    first_node.clstr[circ.depth] = 1
    print("1 clstr node is %s" % first_node.name)
    print(print_node(first_node, 0))
    clstr_list = list()
    clstr_list.append(first_node)
    for i in range(2, k+1):
        candidates= dict()
        values = list()
        weights = list()
        for node in node_list:
            min = 10000000000 # とてつもなく大きい数字
            for comp in clstr_list:
                distance = ((node.depth-comp.depth)**2 + (node.height-comp.height)**2)
                if distance < min:
                    min = distance
            if node.clstr[circ.depth] == -1:
                candidates[node.name] = min
        #values = candidates.keys() これ無理なのpythonのミスでしょ
        #weights = candidates.values()
        for k in candidates.keys():
            values.append(k)
        for k in candidates.values():
            weights.append(k)
        #print(candidates)
        chosen_node = random.choices(values, weights = weights)[0]
        print("%d cluster node is %s" % (i, circ.find_node(chosen_node).name))
        #print(print_node(circ.find_node(chosen_node), 0))
        circ.find_node(chosen_node).clstr[circ.depth] = i
        clstr_list.append(circ.find_node(chosen_node))
              
# 特定のクラスタの重心を計算
def calc_gp(circ, clstr): 
    clstr_list = list()
    sum_depth = 0
    sum_height = 0
    node_list = circ.intnode + circ.p_output + circ.p_input
    for node in node_list:
        if node.clstr[circ.depth] == clstr:
            clstr_list.append(node)
            sum_depth += node.depth
            sum_height += node.height
    ans = list()
    if len(clstr_list) != 0:
        ans.append(sum_depth/len(clstr_list))
        ans.append(sum_height/len(clstr_list))
        print("cluster[%d]'s gp = (%.2f %.2f)" % (clstr, sum_depth/len(clstr_list), sum_height/len(clstr_list)))
    else:
        ans.append(-1111111)
        ans.append(-1111111)
    return ans
    
# クラスタ毎にノードを表示
def print_node_clstr(circ, k):
    node_list = circ.intnode + circ.p_output + circ.p_input
    for i in range(1, k+1):
        print("cluster %d list:" % i)
        for node in node_list:
            if node.clstr[circ.depth] == i:
                print(node.name)

# main関数（network.pyを実行した時に処理される部分）
if __name__ == '__main__':
    # コマンドラインからファイルを引数で取得
    argv = sys.argv
    argc = len(argv)
    if argc!=2:
        # print ("Usage: python3 ",argv[0]," filename circuit_wide circuit_high")
        print ("Usage: python3 ",argv[0])
        quit()
    str = argv[1]
    circ = MakeNetwork.verilog(str)
    calc_cood(circ)
    calc_kmeans(circ, 3)
    print_node_all(circ)
