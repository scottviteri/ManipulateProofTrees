import math
import copy
import itertools
import pickle
import ast
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import json
import functools
import pdb
import cProfile
import subprocess
import networkx as nx
import os
import random
import community
import re

def focusToNewLetters(focus_string):
    if focus_string[1] == '(': return '['
    elif focus_string[1] == ')': return ']'
    elif focus_string[1] == ' ': return ','
    if focus_string[1].isalnum() \
        and (focus_string[0] == '(' or focus_string[0] == ' ') \
        and (focus_string[2] == ')' or focus_string[2] == ' '):
        return '\"'+focus_string[1]+'\"'
    if focus_string[1] not in '( )' and (focus_string[0] == '(' or focus_string[0] == ' '):
        # (a -> ("a or ' a' -> ' "a'
        return '\"'+focus_string[1]
    if focus_string[1] not in '( )' and (focus_string[2] == ')' or focus_string[2] == ' '):
        # b) -> b") or 'b ' -> 'b" '
        return focus_string[1]+'\"'
    return focus_string[1]

def isFlat(l):
    return not any(filter(lambda x: isinstance(x,list), l))

def concat(lst_of_lsts):
    return functools.reduce(lambda x,y:x+y, lst_of_lsts, [])

def printTreeHelper(tree):
    """ Prints tree by prepending '+---' to each layer
    Example: printTreeHelper(['Definition', 'Top.ev_2', ['App', 'ev_SS', 'O', 'ev_0']])
    # base: ['App', 'ev_SS', 'O', 'ev_0'] -> ['App', '+---ev_SS', '+---O', '+---ev_0']
    # ind_step: ['Definition', 'Top.ev_2', ['App', '+---ev_SS', '+---O', '+---ev_0']]
    #  -> ['Definition', '+---Top.ev_2', '+---App', '+---+---ev_SS', '+---+---O', '+---+---ev_0']]
    """
    h,t = tree[0], tree[1:]
    if not isinstance(tree, list):
        assert(isinstance(tree, str))
        return [tree]
    if isFlat(tree):
        return [h] + list(map(lambda x: "+---"+x, t))
    return [h] + concat([list(map(lambda x: "+---"+x, printTreeHelper(x))) for x in t])

def printTree(tree, max_depth=None):
    for x in printTreeHelper(tree):
        if max_depth is not None:
            if "+---"*max_depth not in x:
                print(x)
        else:
            print(x)

def replaceFlatList(lst_of_lsts, match, replacement):
    any_replacements = False
    if isinstance(lst_of_lsts, list):
        for i, lst in enumerate(lst_of_lsts):
            if lst == match:
                lst_of_lsts[i] = replacement
                any_replacements = True
            else:
                any_replacements |= replaceFlatList(lst, match, replacement)
    return any_replacements

def subNats(lst_of_lsts):
    l = copy.deepcopy(lst_of_lsts)
    replaceFlatList(l, ['App','S','O'], '1')
    replaced, n = True, 1
    while replaced:
       replaced = replaceFlatList(l, ['App','S',str(n)], str(n+1))
       n += 1
    return l

def parenStringToLists(paren_string, debug=False):
    accum = ''
    paren_string = paren_string.strip()
    #print(paren_string.count('('), paren_string.count(')'))
    assert(paren_string.count('(') == paren_string.count(')'))
    focus = "  " + paren_string[0]
    for char in paren_string[1:]:
        focus = focus[1:] + str(char)
        accum += focusToNewLetters(focus)
        #print(focus[1], focusToNewLetters(focus))
    accum += ']'
    if debug:
        with open('paren_lists_debug.txt','w') as f:
            f.write(accum)
    theorem_rev = subNats(json.loads(accum))
    return [theorem_rev[0]] + theorem_rev[1:][::-1]

def theoremNameToLists(theorem_name, depth=2, debug=False, mod_libs=False):
    theorem_folder = './ProofTrees/'+theorem_name
    if not os.path.exists(theorem_folder + '/d'+str(depth)+'.txt'):
        print('Generating proof objects for', theorem_name)
        subprocess.call(["./coq_proof_to_trees.sh", theorem_name])
    tree_file = theorem_folder + '/d'+str(depth)+('_mod.txt' if mod_libs else '.txt')
    with open(tree_file, 'r') as f:
        paren_string = f.read()
    if (paren_string != ''):
        return parenStringToLists('(Top ' + paren_string.strip() + ')', debug=debug)
    return []

assert(parenStringToLists('(a b (c d e))') in [['a','b',['c','d','e']], ['a',['c','d','e'],'b']])

ev_4_tree = theoremNameToLists('ev_4')
ev_4_alt_tree = theoremNameToLists('ev_4_alt')
ev_8_tree = theoremNameToLists('ev_8')
ev_8_alt_tree = theoremNameToLists('ev_8_alt')
sqrt2_tree = theoremNameToLists('sqrt2_not_rational')
#sqrt2_d3_tree = theoremNameToLists('sqrt2_not_rational', depth=3)
#bday_tree = theoremNameToLists('birthday_paradox')

#printTree(ev_4_tree)
#printTree(ev_4_alt_tree)

def replaceVal(lst_of_lsts, search_val, replace_val):
    """ similar to subRec, but search target is a single value """
    lst = []
    for elem in lst_of_lsts:
        if search_val == elem:
            lst.append(replace_val)
        else:
            if isinstance(elem,list):
                lst.append(replaceVal(elem, search_val, replace_val))
            else:
                lst.append(elem)
    return lst

def replaceVals(lst_of_lsts, search_replace_dict):
    """ similar to replaceVal, but multiple search targets with different replace_vals """
    l = []
    for x in lst_of_lsts:
        if isinstance(x,list):
            l.append(replaceVals(x, search_replace_dict))
        else:
            if x in search_replace_dict:
                l.append(search_replace_dict[x])
            else:
                l.append(x)
    return l

def replaceValsEffect(lst_of_lsts, search_replace_dict):
    for i in range(len(lst_of_lsts)):
        x = lst_of_lsts[i]
        if isinstance(x,list):
            replaceValsEffect(x, search_replace_dict)
        else:
            if x in search_replace_dict:
                lst_of_lsts[i] = search_replace_dict[x]


def accumMatches(lst_of_lsts, test):
    l = []
    for x in lst_of_lsts:
        if isinstance(x, list):
            l.extend(accumMatches(x, test))
        else:
            if test(x):
                l.append(x)
    return l

def inNestedList(elem, lst_of_lsts):
    for x in lst_of_lsts:
        if isinstance(x,list):
            if inNestedList(elem, x):
                return True
        else:
            if elem == x:
                return True
    return False


def allAtLeaves(elems, tree):
    l = []
    if isinstance(tree, list):
        for x in tree[1:]:
            l.extend(allAtLeaves(elems, x))
    else:
        if tree in elems:
            l.append(tree)
    return l

assert(allAtLeaves(['a','b','c'], ['a',['b','c']]) == ['c'])

def replaceDefinitions(lst_of_lsts, max_depth=math.inf, debug=False):
    """ Substitute unrolled definitions back into main top level definition """
    orig_tree, dep_trees = lst_of_lsts[1], lst_of_lsts[2:]
    replace_string_candidates = list(map(lambda x:x[1], dep_trees))
    def_to_subtree = {x[1]:x[2] for x in lst_of_lsts}
    dep_dict = {x[1]: set(allAtLeaves(replace_string_candidates, x[2])) for x in lst_of_lsts}
    replace_strings = dep_dict[orig_tree[1]]
    depth = 0
    search_replace_dict = {}
    while replace_strings and depth < max_depth:
        search_replace_dict = {k:def_to_subtree[k] for k in replace_strings}
        orig_tree = replaceVals(orig_tree, search_replace_dict)
        depth += 1
        replace_strings = set().union(*[dep_dict[x] for x in replace_strings])
    search_replace_dict = {k:def_to_subtree[k] for k in replace_strings}
    orig_tree = replaceVals(orig_tree, search_replace_dict)
    if debug:
        with open('replace_def_debug.txt','w') as f:
            f.write(str(orig_tree))
    return orig_tree

#printTree(replaceDefinitions(ev_8_alt_tree),4)

def sumLsts(lsts):
    max_len = max(map(len, lsts))
    def zeroFill(lst): return lst + [0]*(max_len - len(lst))
    return list(map(sum, zip(*map(zeroFill,lsts))))

def countNodesAtDepths(tree):
    """ Counts num nodes at each depth
    Example: countNodesAtDepths(['a', 'b', ['c','d','e'], ['c','d','e']])
    # base: ['c','d','e'] -> [1,2], 'b' -> [1]
    # ind_step: ['a', [1], [1,2], [1,2]] -> [1,3,4]
    """
    if not isinstance(tree, list): return [1]
    h,t = tree[0], tree[1:]
    if isFlat(tree): return [1,len(t)]
    return [1] + sumLsts(list(map(countNodesAtDepths, t)))

def countNodes(tree):
    if not isinstance(tree, list): return 1
    return 1 + sum([countNodes(branch) for branch in tree[1:]])

def findAdd(tree):
    if not isinstance(tree, list):
        return False
    else:
        if tree[0] == 'add':
            print(tree)
            return True
        return any([findAdd(t) for t in tree[1:]])

def strip(s):
    return s.split('/')[-1]

def modStrip(s):
    l = s.split('/')
    return l[-2] + '_' + l[-1]

assert(countNodesAtDepths(['a', 'b', ['c','d','e'], ['c','d','e']]) == [1,3,4])



def plotNodesVTreeDepth(theorem_name, max_depth, debug=False):
  f = 'Images/'+theorem_name+'_tree_depth_'+str(max_depth)+'.png'
  if not os.path.isfile(f):
      fig, ax = plt.subplots(figsize=(6,6))
      for d in range(1,max_depth+1):
          if d == 1:
              ax = plt.subplot(max_depth,1,d)
          else:
              ax = plt.subplot(max_depth,1,d, sharex = ax)
          ax.set_title(theorem_name + ' expansion #'+str(d))
          tree = theoremNameToLists(theorem_name, depth=d, debug=debug)
          ax.plot(countNodesAtDepths(replaceDefinitions(tree)))
          ax.set_xlabel('Tree Depth (Distance from Root)')
          ax.set_ylabel('Number of Nodes')
          #else:
          #    ax.plot(countNodesAtDepths(tree)[1:], '_', label='No substitution')
          #    ax.plot(countNodesAtDepths(replaceDefinitions(tree)), '|', label='Defn substitution')
          fig.tight_layout()
          #ax.legend()
          #if d != max_depth:
          #    plt.setp(ax.get_xticklabels(), visible=False)
      plt.savefig(f)

def depthToNumNodes(depth, theorem_name):
   tree = theoremNameToLists(theorem_name, depth=depth)
   substitutionTree = replaceDefinitions(tree)
   return countNodes(substitutionTree)

def plotNodesVExtractionDepth(theorem_name, max_depth, figsize = (6,6)):
   f = 'Images/'+theorem_name+'_extraction_depth_'+str(max_depth)+'.png'
   if not os.path.isfile(f):
       fig, axs = plt.subplots(1, 1, sharex = True, figsize=figsize)
       depth_list = list(range(1,max_depth+1))
       #log_depth_list = list(map(lambda x: math.log(x), depth_list))
       num_nodes = list(map(lambda depth: depthToNumNodes(depth, theorem_name), depth_list))
       axs.plot(depth_list, num_nodes, 'r+')
       axs.set_title('Substitution Tree # Nodes Vs Extraction Depth')
       axs.set_xlabel('Extraction Depth')
       axs.set_ylabel('Number of Nodes')
       #axs[1][1].plot(log_depth_list, list(map(lambda x: math.log(x), sub_tree_num_nodes)))
       #axs[1][1].set_xlabel('Log Extraction Depth')
       fig.tight_layout()
       plt.savefig(f)

def libNameToTheoremNames(library_name, depth=1):
    with open('ProofTrees/'+library_name+'_d'+str(depth)+'.txt','r') as f:
        names = f.readlines()
    return list(map(lambda x: x.strip(), names))

def libNameToTheoremDict(library_name, debug=False, depth=2, mod_libs=False, limit=None):
    if not os.path.exists('./ProofTrees/'+library_name+'_d'+str(depth)+'.txt'):
        subprocess.call(['./lib_to_trees.sh', library_name, str(depth)])
    theorem_names = libNameToTheoremNames(library_name, depth)
    if limit:
        theorem_names = theorem_names[:limit]
    theorems = {}
    for theorem_name in theorem_names:
        print(theorem_name)
        theorem_tree = theoremNameToLists(theorem_name, depth=depth, mod_libs=mod_libs, debug=debug)
        if theorem_tree != []:
            theorems[theorem_name] = theorem_tree
    return theorems
