#------------
# 4/5/2018 Rich rules.
#------------

from z3.z3util import * #@UnusedWildImport
from Rule import * #@UnusedWildImport

#--------------
# Rule with binary characteristic
# cond and conc are lists of BoolRef: a conjunction
# but covers also bool=TRUE or False, ExpRef, and lists of ExpRef (n>=2)
class ExclusiveRule(Rule):
 
    # --------------------
    # create a new rule 
    def __init__(self, binary, cond, conc):
        super().__init__(cond, conc)
        # binary characteristic a list of digit
        self.characteristic = binary
    # --- end init
 
    # --------------------
    def __str__(self):
        return str(self.characteristic) + " " + super().__str__()
    # --- end str
    
    # --------------------
    def get_binary(self):
        return self.characteristic
    # --- end get_binary
    
    # --------------------
    # TODO errors
    # return an BoolRef
    def get_cond(self):
        if (isinstance(self.cond, bool)):
            return self.cond
        elif (is_expr(self.cond)):
            return self.cond
        elif (self.cond):
            if (not self.cond):
                return True
            elif (len(self.cond)==1):
                return self.cond[0]
            else:
                return And(*self.cond)
        else:
            print ("Rule.get_cond: erreur syntaxe!" )
    # --- end get_cond
    
    # --------------------
    def get_conc(self):
        if (isinstance(self.conc, bool)):
            return self.conc
        elif (is_expr(self.conc)):
            return self.conc
        elif (self.conc):
            if (not self.conc):
                return True
            elif (len(self.conc)==1):
                return self.conc[0]
            else:
                return And(*self.conc)
        else:
            print ("Rule.get_conc: erreur syntaxe!" )        
    # --- end get_conc
    
    # --------------------
    # conversion to tspass
    def tspass(self):
        return Rule.PARIN + tspass(self.get_cond()) + Rule.IMPLY + tspass(self.get_conc()) + Rule.PAROUT
    # --- end tspass
    
    # --------------------
    # redefine Z3 BoolRef generation
    # attention False possible
    def z3(self):
        D = self.get_cond()
        C = self.get_conc()
        return Implies(D, C)
    # --- end z3

# -- end class EclusiveRule
