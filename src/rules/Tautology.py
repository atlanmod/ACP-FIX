# ------------------
# 16/4/2018
# tautaology rule
# -------------------

from z3 import * #@UnusedWildImport
from z3.z3util import * #@UnusedWildImport
from ExclusiveRule import * #@UnusedWildImport

#--------------------
# Tautology rule 
# ?* D&~C is unsat
# thus should be eliminated
class Tautology(ExclusiveRule):
    
    # --------------------
    # create a new unsafe rule 
    def __init__(self, binary, cond, conc):
        super().__init__(binary, cond, conc)
    # --- end init
 
    # --------------------
    def __str__(self):
        return "TAUTO " + super().__str__()
    # --- end str
    
# --- end Tautology