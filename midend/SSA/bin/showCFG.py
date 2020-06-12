# This python script draw the CFG of an .ssa file given
# It uses graphviz lib to generate .gv and .pdf files.
# It's possible to generate other format (.dot or .svg)

# Dependencies:
# - python3
# - graphviz

# Use: $python3 showCFG.py myFiles.ssa …

import sys
import re
from os import path
from graphviz import Digraph

fname = sys.argv[1]
print("file to parse : ",fname)

fbname = path.basename(fname)

print("file basename : ",fbname)

g = Digraph(fbname, filename=fbname+'.gv')

pat_func_start = re.compile("^(\w+)\((.*)\) {")
pat_func_end = re.compile("^}$")
pat_inst = re.compile("\s*(\d+):\s*(.*)$")
pat_goto = re.compile("goto (\d+)")
pat_simpl_goto = re.compile("\s*(goto (\d+))")
pat_simpl_inst = re.compile("\s+([^:]*)$")
pat_if = re.compile("if \((.*)\) goto (\d+) else goto (\d+)")
pat_case = re.compile("\s+case \d+: (goto \d+)")

def addNode(g,pc,i_list):
    if len(i_list)>0:
        l_i = i_list[0]
        for i in i_list[1:]:
            l_i = l_i + '\n' + i
        g.node(pc,l_i)

def startFunction(f):
    line = f.readline()
    while line and line == "\n":
        line = f.readline()
    if line:
        r = pat_func_start.match(line)
        while not r :
            r = pat_func_start.match(line)
            line = f.readline()
        return r.groups()[0]
    else:
        return False


def addEdges(g,gotos):
    for k in gotos:
        if(len(gotos[k])>2):
            print("More than 2 parents !")
        for t in gotos[k]:
            g.edge(str(k),str(t))

def drawFunction(g,f):
    line = f.readline()
    end = pat_func_end.match(line)
    pc = 0
    entry = False
    gotos = {}
    insts_list = []
    while not end:
        # Find entry first ?
        simpl_goto_inst = pat_simpl_goto.match(line)
        if simpl_goto_inst and not entry:
            g.node('entry',simpl_goto_inst.groups()[0])
            gotos['entry'] = [simpl_goto_inst.groups()[1]]
            entry = True
            line = f.readline()
        res = pat_inst.match(line)
        pc = 0

        # new pc
        while res:
            if pc == 0: # First instruction
                pc = res.groups()[0]
                instr = res.groups()[1]
            else: # others instructions
                instr = res.groups()[0]
            insts_list.append(instr)
            # If it's a goto
            goto_inst = pat_simpl_goto.match(instr)
            # If it's a if FIXME match all goto from a line in a row…
            if_inst = pat_if.match(instr)
            if if_inst:
                if pc in gotos:
                    gotos[pc].extend[int(if_inst.groups()[1]),int(if_inst.groups()[2])]
                else:
                    gotos[pc] = [int(if_inst.groups()[1]),int(if_inst.groups()[2])]
            elif goto_inst:
                if pc in gotos:
                    gotos[pc].append(goto_inst.groups()[1])
                else:
                    gotos[pc] = [goto_inst.groups()[1]]
            line = f.readline()
            # Search for next instruction in same pc (goto or phi)
            res = pat_simpl_inst.match(line)
            if not res:
                res = pat_case.match(line)
        if pc not in gotos:
            gotos[pc] = [int(pc)-1]
        addNode(g,pc,insts_list)
        insts_list = []
        end = pat_func_end.match(line)

    addEdges(g,gotos) # Create all edges from gotos map
    g.render(filename=func_file+'.gv', view=True)
    # g.view()

for i in range(1,len(sys.argv)):
    fname = sys.argv[i]
    print(i,"file",fname)
    with open(fname,'r') as f:
        func_name = startFunction(f)
        while func_name:
            func_file = fbname+func_name
            g = Digraph(func_file,filename=func_file+'.gv')
            drawFunction(g,f)
            func_name = startFunction(f)
