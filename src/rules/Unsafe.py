# ------------------
# 16/4/2018
# unsafe rule
# -------------------

from z3 import * #@UnusedWildImport
from z3.z3util import * #@UnusedWildImport
from ExclusiveRule import * #@UnusedWildImport

#--------------------
# Unafe rule 
# !* (D=>C) & ?*D is unsat
# thus reduce to D=>False
class Unsafe(ExclusiveRule):
    
    # --------------------
    # create a new unsafe rule 
    def __init__(self, binary, cond):
        super().__init__(binary, cond, False)
    # --- end init
 
    # --------------------
    def __str__(self):
        return "UNSAFE " + super().__str__()
    # --- end str
    
# --- end Unafe