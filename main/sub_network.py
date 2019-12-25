# tomorow@ncg.is.ritsumei.ac.jp
# writing by python3
# coding:utf-8
import sys
import network

# サブネットワーククラス
class CreateSubNetwork:
    def __init__(self, circ, k):
        self.name = circ.name + '_' + str(k)
        self.intnode = list()
        self.p_input = list()
        self.p_output = list()
        self.depth = circ.depth + 1
        print(self.name, "'s depth = ", self.depth)

    # 中間ノードの追加
    def add_intnode(self, node):
        frg = 0
        for tmp in self.intnode:
            if tmp == node:
                frg = 1
        if frg == 0:
            self.intnode.append(node)
            return
        print("error: already exist %s" % node.name)
        return

    # 外部入力の追加
    def add_input(self, node):
        frg = 0
        for tmp in self.p_input:
            if tmp == node:
                frg = 1
        if frg == 0:
            self.p_input.append(node)
            return
        print("error: already exist %s" % node.name)
        return
    
    # 外部出力の追加
    def add_output(self, node):
        frg = 0
        for tmp in self.p_output:
            if tmp == node:
                frg = 1
        if frg == 0:
            self.p_output.append(node)
            return
        print("error: already exist %s" % node.name)
        return

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
        return(-1) # 存在しない場合は-1を返す
    
# 特定のクラスタの部分回路を作成
def MakeSubNetwork(circ, k):
    sub_circ = CreateSubNetwork(circ, k)  
    node_list = circ.intnode + circ.p_output + circ.p_input
    sub_node = list()
    for node in node_list:
        if node.clstr[circ.depth] == k:
            sub_node.append(node)
    for node in sub_node:
        node.clstr.append(-1)
        frg = 0
        for tmp in node.input:
            if tmp.clstr[circ.depth] != k:
                sub_circ.add_input(node)
                frg = 1
                break
        for tmp in node.output:
            if tmp.clstr[circ.depth] != k:
                sub_circ.add_output(node)
                frg = 1
                break
        if frg == 0:
            sub_circ.add_intnode(node)
    return sub_circ
        
                
