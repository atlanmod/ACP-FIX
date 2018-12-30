# ------------------
# 30/10/2018
# simple rule
# -------------------

from z3 import * #@UnusedWildImport
from z3.z3util import * #@UnusedWildImport
from MoreUtility import * #@UnusedWildImport

# --------------------
# conversion to TSPASS for a BoolRef
# requires self:BoolRef
def tspass(self):
    if (is_const(self)):
        return str(self) 
    elif (self == False):
        return "false"
    elif (self == True):
        return "true"    
    else:
        # it is an app
        return tspassApp(self)
# --- end tspass

# --------------------
# conversion to TSPASS for a BoolRef
# requires self:BoolRef it's an App ?
def tspassApp(self):
    op = self.decl().kind()
    sons = self.children()
    tmp = ""
    if (op == Z3_OP_AND):
        # could be 0,  1 and take care of the binary op
        size = len(sons)
        if (size > 0):
            tmp = Rule.PARIN + tspass(sons[0])
            for i in range(1, size):
                tmp += Rule.AND + tspass(sons[i])
            # --- for i
            tmp += Rule.PAROUT
        return tmp
    elif (op == Z3_OP_OR):
        # could be 0,  1 and take care of the binary op
        size = len(sons)
        if (size > 0):
            tmp = Rule.PARIN + tspass(sons[0])
            for i in range(1, size):
                tmp += Rule.OR + tspass(sons[i])
            # --- for i
            tmp += Rule.PAROUT
        return tmp
    elif (op == Z3_OP_NOT):
        return Rule.NOT +  Rule.PARIN + tspass(sons[0]) + Rule.PAROUT
    elif (op == Z3_OP_IMPLIES):
        return Rule.PARIN + tspass(sons[0]) + Rule.IMPLY + tspass(sons[1]) + Rule.PAROUT
    elif (op == Z3_OP_XOR):
        return "tspass:XOR not defined"
    elif (op == Z3_OP_EQ):
        # only for bool !!!
        return Rule.EQUAL + Rule.PARIN + tspass(sons[0]) + Rule.COMMA + tspass(sons[1]) + Rule.PAROUT
    elif (op == Z3_OP_DISTINCT):
        return Rule.NOT + Rule.EQUAL + Rule.PARIN + tspass(sons[0]) + Rule.COMMA + tspass(sons[1]) + Rule.PAROUT
    elif (op == Z3_OP_UNINTERPRETED):
        # case for predicates 
        return str(self)
    else:
        return "PB in tspass"
    # lacks specific predicates cases ?
    # --- end tspass  

# -----------------------------------------------------
# Class rule
# Free variables are assumed to be shared and declared at the top
# Implies(cond, conc) basically
class Rule():
    
    # TSPASS keywords 
    WHITE = ' '
    AND = ' & '
    OR = ' | ' # ????|||| pb italique ?
    NOT = ' ~'
    IMPLY = ' => '
    EQUIV = ' <=> '
    PARIN = '('
    PAROUT = ')'
    EQUAL = 'EQUAL '
    COMMA = ', '
    
    def __init__(self, cond, conc):
        # BoolRef condition
        self.cond = cond
        # BoolRef conclusion
        self.conc = conc
    # --- end init
    
    # --------------------
    def __str__(self):
        return "<" + str(self.cond) + " => " + str(self.conc) + ">"
    # --- end str
    
    # --------------------
    def tspass(self):
        return Rule.PARIN + tspass(self.get_cond()) + Rule.IMPLY + tspass(self.get_conc()) + Rule.PAROUT
    # --- end tspass
    
    # --------------------
    # generate a Z3 BoolRef
    def z3(self):
        cond = self.get_cond()
        conc = self.get_conc()
        return Implies(cond, conc)
    # --- end z3
    
    # --------------------
    # readers
    def get_cond(self):
        return self.cond
    def get_conc(self):
        return self.conc
    # --- end readers    
    
    # --------------------
    # setter
    def set_cond(self, new):
        self.cond = new
    def set_conc(self, new):
        self.conc = new
    # --- end setter
    
    # --------------------
    # test obvious and return yes or no
    # with free variables
    # if unknown return no
    def is_obvious(self, variables):
        if (isinstance(self.get_cond(), bool)):
            return not self.get_cond()
        else:
            S = Solver()
            if (variables):
                S.add(Exists(variables, self.get_cond()))
            else:
                S.add(self.get_cond())
            return (S.check().__eq__(unsat))
    # --- end is_obvious  
    
    # --------------------
    # Test if explicit unsafe that is the conclusion is unsat
    # with free variables and if unknown return no
    def is_explicit_unsafe(self, variables):
        if (isinstance(self.get_conc(), bool)):
            return not self.get_conc()
        else:
            S = Solver()
            if (variables):
                S.add(ForAll(variables, self.get_conc()))
            else:
                S.add(self.get_conc())
            return (S.check().__eq__(unsat))
    # --- end is_explicit_unsafe  
    
    # --------------------
    # test tautology and return yes or no
    # with free variables
    # if unknown return no
    def is_tautology(self, variables):
        S = Solver()
        if (variables):
            S.add(Exists(variables, And(self.get_cond(), Not(self.get_conc()))))
        else:
            S.add(And(self.get_cond(), Not(self.get_conc())))
        return (S.check().__eq__(unsat))
    # --- end is_tautology     
    
    # --------------------
    # test unsafety and return True or False
    # with free variables
    # if unknown return False
    def is_unsafe(self, variables):
        S = Solver()
        if (variables):
            S.add(ForAll(variables, self.z3()))
        else:
            S.add(self.z3())
        cond = self.get_cond()
        if (isinstance(cond, bool)):
            S.add(cond)
        else:
            if (variables):
                S.add(Exists(variables, cond))
            else:
                S.add(cond)
        return (S.check().__eq__(unsat))
    # --- end is_unsafe   
    
    # --------------------
    # size = number of nodes
    def size_nodes(self):
        return size_nodes(self.get_cond()) + size_nodes(self.get_conc()) +1 
    # --- end size  
    
    # --------------------
    # Built the corresponding BoolRef
    # without the ForAll quantifier 
    def toBoolRef(self):
        return Implies(self.get_cond(), self.get_conc())
    # --- end of toBoolRef
    
    # --------------------
    # fix U in conclusion of the rule
    # U is without free variables
    def fix(self, U):
        return Rule(self.get_cond(), Or(self.get_cond(), U))
    # --- end fix
    
# --- end Rule