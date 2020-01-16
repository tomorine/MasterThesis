# tomorow@ncg.is.ritsumei.ac.jp
# writing by python3
# coding:utf-8
import sys
from network import *

# サブネットワーククラス
class CreateSubNetwork:
    def __init__(self, circ, k):
        self.name = circ.name + '_' + str(k)
        self.intnode = list()
        self.p_input = list()
        self.p_output = list()
        self.depth = circ.depth + 1
        self.global_node_num = 0
        print(self.name, "'s depth = ", self.depth)  

    # 中間ノードの追加
    def add_intnode(self, node):
        frg = 0
        for tmp in self.intnode + self.p_input + self.p_output:
            if tmp == node:
                frg = 1
        if frg == 0:
            self.intnode.append(node)
            node.type = "intnode"
            return
        print("error: already exist %s" % node.name)
        return

    # 外部入力の追加
    def add_input(self, node):
        frg = 0
        for tmp in self.intnode + self.p_input + self.p_output:
            if tmp == node:
                frg = 1
        if frg == 0:
            self.p_input.append(node)
            if node.type != "p_input":
                node.type = "input"
            return
        print("error: already exist %s" % node.name)
        return
    
    # 外部出力の追加
    def add_output(self, node):
        frg = 0
        for tmp in self.intnode + self.p_input + self.p_output:
            if tmp == node:
                frg = 1
        if frg == 0:
            self.p_output.append(node)
            if node.type != "p_output":
                node.type = "output"
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

    # ノードをIDで探す
    def find_node_id(self, id):
        nodelist = self.intnode + self.p_input + self.p_output
        for tmp in nodelist:
            if tmp.id == id:
                return(tmp)
        return(-1) # 存在しない場合は-1を返す

    
# 特定のクラスタの部分回路を作成
def MakeSubNetwork(circ, k):
    sub_circ = CreateSubNetwork(circ, k)
    node_list = circ.intnode + circ.p_output + circ.p_input
    sub_node = list()
    new_sub_node = list()
    for node in node_list:
        if node.clstr == k:
            sub_node.append(node)
            new_node = CreateNode(node.name + "_" + str(circ.depth+1))
            new_node.id = node.id
            new_sub_node.append(new_node)            
    for node in sub_node:
        frg = 0
        for new in new_sub_node:
            if new.id == node.id:
                if node.type == "p_input":
                    sub_circ.add_input(new)
                    frg = 1
                for tmp in node.input:
                    if tmp.clstr != k:
                        sub_circ.add_input(new)
                        frg = 1
                    else:
                        for i in new_sub_node:
                            if tmp.id == i.id:
                                new.add_input(i)
                if node.type == "p_output":
                    new.type = "p_output"
                    sub_circ.add_output(new)
                    frg = 1
                for tmp in node.output:
                    if tmp.clstr != k:
                        if frg == 0:
                            sub_circ.add_output(new)
                            frg = 1
                    else:
                        for i in new_sub_node:
                            if tmp.id == i.id:
                                new.add_output(i)
                if frg == 0:
                    sub_circ.add_intnode(new)
        sub_circ.global_node_num = circ.global_node_num
    return sub_circ
        
                
