# ------------------
# 16/4/2018
# simple rule
# -------------------

from z3 import * #@UnusedWildImport
from z3.z3util import * #@UnusedWildImport
from ExclusiveRule import * #@UnusedWildImport

#--------------------
# Safe rule 
# !* (D=>C) & ?*D is sat
class Safe(ExclusiveRule):
    
    # --------------------
    # create a new safe rule 
    def __init__(self, binary, cond, conc):
        super().__init__(binary, cond, conc)
    # --- end init
 
    # --------------------
    def __str__(self):
        return "NOT UNSAFE " + super().__str__()
    # --- end str
    
# --- end Safe