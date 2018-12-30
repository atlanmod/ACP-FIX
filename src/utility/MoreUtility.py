# ------------------------------
# 29/5/2018
# some additional utility functions
#--------------------------
from z3 import * #@UnusedWildImport

#------------- tactic from Z3
skip = Tactic('skip')
nnf =Tactic('nnf')
simplify = Tactic('simplify')
split = Tactic('split-clause')
cnf = Tactic('tseitin-cnf')
tactic = Then(nnf, simplify, Repeat(OrElse(split, skip)), simplify) 

# in fact there is a bin() fonction
# list(bin(5))[2:] could be used
# ---------------------
# from google
def dec2bin(d,nb=8):
    """Représentation d'un nombre entier positif en liste binaire (nb: nombre de bits du mot)"""
    if d == 0:
        # fill list with 0
        # return "0".zfill(nb)
        return [0] * nb
    b=[]
    while d != 0:
        d, r = divmod(d, 2)
        # concatene b avec [0, 1] 
        # b = "01"[r] + b
        b =  [r] + b
    # remplissage avec 0 ?
    # return b.zfill(nb)
    return [0] * (nb-len(b)) + b 
# -- end dec2bin

# ---------------------
# from google
def bin2pos(binary):
    """ inverse conversion to positive integer """
    res = 0
    for pos in range(0, len(binary)):
        res = binary[len(binary)-pos-1] + 2*res
    return res
# -- end bin2pos

# ---------------------
# generate a list of Z3 Const of type sort
def gener_const(nb, sort):
    res = []
    for i in range(0, nb):
        res += [Const(str(sort)+str(i), sort)]
    return res
# -- end gener_const

# -------------------
# remove one level of and
# TODO more distribute ? see also simplify ...
def combine(exp1, exp2):
    if (is_app(exp1) and (exp1.decl().kind() == Z3_OP_AND) and is_bool(exp1)
        and is_app(exp2) and (exp2.decl().kind() == Z3_OP_AND) and is_bool(exp2)):
        return And(*(exp1.children() + exp2.children()))
    else:
        return And(exp1, exp2)
# --- end of combine

# -------------------
# check if a  position of sub is active in sup
def included(sub, sup):
    res = False
    i = 0
    while (i < len(sub) and not res):
        res = (sup[sub[i]] == 1)
        i += 1
    return res
# --- end of included

# -------------------
# compute the difference between sub a list of position and
# in sup a list of binary digit List[{-1, 0, 1}]
# and return the list of position
# REQUIRED not included
def diff(sub, sup):
    res = []
    for i in range(0, len(sup)):
        if ((sup[i] == 1) and not (i in sub)):
            res += [i]
    # --- end for
    return res
# --- end of diff

# -------------------
# rels and shared positions become -1 don't care
# and return this binary characteristic
# both needed 
def dontcare(rels, binary):
    res = []
    for i in range(0, len(binary)):
        if (i in rels):
            res.append(-1)
        else:
            res.append(binary[i])      
    return res
# --- end of dontcare

# -------------------
# build a last binary with don't care
# TODO side effect ? remove useles !!!
def change(binary):
    res = []
    for i in range(0, len(binary)):
        if (binary[i] == -1):
            res.append(-1)
        else:
            res.append(0)
    return res
# --- end of change

#----------------------
# Compose two lists of exclusive binary characteristics
# none list is empty
# last should be the last thus ordering important
def compose_binary(bins1, bins2):
    res = []
    last2 = [0]*len(bins2[0])
    for i in range(0, len(bins1)):
        b1 = bins1[i]
        for j in range(0, len(bins2)):
            res.append(b1 + bins2[j])
        # --
        res.append(b1 + last2)
    # --
    last1 = [0]*len(bins1[0])
    # but the last
    for b2 in bins2:
        res.append(last1 + b2)
    # --
    return res
# --- end compose_binary

# ---------------------
# add O,1 combinations to bin
# return a list of binary of length n
def complete(n, binary):
    if (n == 1):
        return [binary+[0], binary+[1]]
    else:
        res = []
        for l in complete(n-1, binary):
            res.append(l+[0])
            res.append(l+[1])
        return res
# --- end complete

#----------------------
# expand don't care in a binary
# and return a list of binary
def expand(binary):
    tmp = [[]]
    for i in binary:
        if (i==-1):
            aux = [x+[0] for x in tmp]
            aux += [x+[1] for x in tmp]
            tmp = aux
        else:
            tmp = [x+[i] for x in tmp]
    # --- end for
    return tmp
# --- end of expand

# ----------------------
# add in list of BoolRef but simplify
# to return True/False/BoolRef/List[BoolRef l>=2]
# list1 represents a conjunction
def add_exp(list1, exp):
    #print (str(list1))
    if (exp == False):
        return False
    elif (exp == True): 
        return list1
    else:
        if (list1 == False):
            return False
        elif (list1 == True):
            return exp
        else:
            if (isinstance(list1, list)):
                return list1 + [exp]
            else:
                return [list1, exp]
        # --- end if list1 false
    # --- end if exp
# --- end add_exp

# ---------------
# size(BoolRef or class bool) : compute nb of nodes
def size_nodes(exp):
    #print ("size_nodes " + str(exp) + str(type(exp)) + str(is_int(exp)))
    res = 0
    # may be bad ...
    if isinstance(exp, bool):
        return 1
    elif is_const(exp):
        return 1
    elif is_int(exp): # come from Var(?) in quantifiers
        return 1
#     elif (exp.num_args() == 0):
#         return 1
    elif (is_expr(exp)):
            if (is_app(exp)):
                res = 0
                for arg in exp.children():
                    res += size_nodes(arg)
                # --- end for
                return res+1
            else:
                # quantifiers ?
                res = exp.num_vars()
                res += size_nodes(exp.children()[0])
                return res+1
    # --- end if
    else:
        print ("size_nodes ? " + str(exp))
        return 0
# --- end size_nodes

