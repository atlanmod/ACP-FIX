# ------------------
# 29/4/2018
# Class for rule system
# -------------------

from z3 import * #@UnusedWildImport
from Rule import * #@UnusedWildImport
#from partition import * #@UnusedWildImport
#from measure import * #@UnusedWildImport
#from functools import *  #@UnusedWildImport

# ---------------------
# self.variables: universally quantified
class RuleSet():
    
    # by default it is True
    def __init__(self):
        # quantifier variables common to all
        self.variables = []
        # cond => conc list of rules
        self.rules = []
    # --- end init
    
    # --------------------
    def __str__(self):
        result = "Quantifiers: " + str(self.variables) + "\n rules \n"
        #result += "\n".join(map((lambda x: str(x)), self.rules))
        result += "\n".join([str(x) for x in self.rules])
        result += "\n #nodes= " + str(self.size_nodes())
        return result + "\n"
    # --- end str
    
    # --------------------
    # tspass translation without ahead quantifiers
    def tspass(self, rules):
        result = ""
        size = len(rules)
        if (size > 0):
            result = Rule.PARIN + rules[0].tspass()
            # take care of binary and
            for i in range(1, size):
                result += Rule.AND + "\n" + rules[i].tspass()
            # --- end for i
            result += Rule.PAROUT
        return result
    # --- end str
    
    # --------------------
    # Built the corresponding BoolRef
    # without the ForAll quantifier 
    # only the first end rules
    def toBoolRef(self, end):
        args = []
        for k in range(0, end):
            r = self.rules[k]
            args.append(Implies(r.get_cond(), r.get_conc()))
        return And(*args)
    # --- end of toBoolRef
    
    # --------------------
    # make it False
    def false(self):
        self.variables = []
        self.rules = []
    # --- end of false
    
    # --------------------
    # add a variable: name sort
    def add_variable(self, name, sort):
        self.variables.append(Const(name, sort))
    # --- end add_variable
    
    # --------------------
    # one getter
    def get_variable(self, i):
        return self.variables[i]
    # --- end get_variable

    # --------------------
    # add a rule
    # cond, conc: are ExpRef 
    # rule (cond => conc)
    def add_rule(self, cond, conc):
        self.rules.append(Rule(cond, conc))
    # --- end add_rule
    
    # --------------------
    # one rule getter
    def get_rule(self, i):
        return self.rules[i]
    # --- end get_rule
    
    # --------------------
    # some size informations
    def number_rule(self):
        return len(self.rules)
    def number_variable(self):
        return len(self.variables)
    # --- end of some informations

    # -------------------
    # compute list of conditions
    def get_conds(self):
        return list(map((lambda x: x.get_cond()), self.rules))
    # --- end get_conds
    
    # -------------------
    # compute list of conclusions
    def get_concs(self):
        return list(map((lambda x: x.get_conc()), self.rules))
    # --- end get_concs
    
    # -------------------
    # compute AND of conditions
    # and return the AstRef
    def computeDef(self):
        result = list(map((lambda x: self.get_rule(x).get_cond()), range(self.number_rule())))
        return And(*result)
    # --- end computeDef
    
    # -------------------
    # compute AND of conclusions
    # and return the AstRef
    def computePrecond(self):
        result = list(map((lambda x: self.get_rule(x).get_conc()), range(self.number_rule())))
        return And(*result)
    # --- end computePrecond
    
    # --------------------
    # size = number of nodes
    def size_nodes(self):
        return sum([x.size_nodes() for x in self.rules])
    # --- end size  
    

# --- end RuleSet