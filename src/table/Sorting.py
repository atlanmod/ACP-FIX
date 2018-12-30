# ------------------
# 6/5/2018
# Table for sorting
# obvious tautologies and all unsafe  +inclusions + sorting
# -------------------

from Iterative import *  #@UnusedWildImport
from Inclusion import * #@UnusedWildImport

# --------------------------
# Class for Table inheriting rule set 
# j will be the new rule and i one already seen
class Sorting(Iterative):
    
    # --------------------
    # init constructor 
    def __init__(self):
        super().__init__()
        # dicos for inclusion relations
        self.dicoconcneg = dict()  # ~Cj&Ci unsat
        # to store sorted rules
        self.sorted = []
        # to store equals relations on conclusions
        self.same_conclusion = dict()
        # to store ordering new = G.sorted[old]
        self.ordering = {}
    # --- end init
    
    # --------------------
    def __str__(self):
        result = ""
        #result += "\n #nodes= " + str(self.size_nodes())
        #result = super().__str__()
#         result = RuleSet.__str__(self)
#         result += " ----------- Correct -------------- \n"
#         for r in self.correct:
#             result += str(r) + "\n"
        result += "\n ----------- Sorted -------------- \n"
        for r in self.sorted:
            result += str(r) + "\n"
        result += " ----------- Not unsafe -------------- \n"
        for r in self.safe:
            result += str(r) + "\n"
        result += " ----------- Unsafe -------------- \n"
        for r in self.unsafe:
            result += str(r) + "\n"
        return result 
    # --- end str
    
    # ---------------------
    def reset(self):
        super().reset()
        self.sorted = []
        self.dicoconcneg = dict()
    # -- end reset
        
    # ----------------------
    def get_sorted(self, i):
        return self.sorted[i]
    # -- end get_sorted
 
    #------------------
    # Processing from the sorted rules ...
    # compute table with the new iterative process
    # take into account tautology and unsafe cases
    # with binary characteristic (in reverse counting order) and with don'tcare
    # bound is the number of processed rules (<= self.size()) and toview to print
    def compute_table(self, end):
        self.reset()
        self.clean(end)
        #print (str(self))
        self.inclusions()
        if (len(self.sorted) > 0):
            self.process_table(self.sorted)
    # --- end compute_table

    # ----------------------
    # compute the new rules and put in self.safe
    # nth number of the current correct and sorted rule
    # add management of add_exp and the inclusion cases
    def computeNewRules(self, new, negnew, conc, nth):
        self.tempaux = []
        nb_rules = len(self.safe)
        # check the empty case
        for k in range(0, nb_rules):
            # analyze existing rules
            rulek = self.safe[k] 
            binary = rulek.get_binary()
            lcond = Rule.get_cond(rulek)
            lconc = Rule.get_conc(rulek)
            # add here test exclusion
            rels = self.dicoconcneg[nth]
            # test if a rule in rels is active in binary
            if (included(rels, binary)):
                # copy the old rule with a dont'care
                self.tempaux.append((binary+[-1], lcond, lconc))
                #     # TODO simplify last for inclusions ?
            else:
                # evaluate and store both new rules  
                self.build(add_exp(lcond, new), add_exp(lconc, conc), binary+[1])
                # -- handle negative case
                self.build(add_exp(lcond, negnew), lconc, binary+[0])
            # --- end if inclusions
        # -- end for k
        # add the last negative terms &_i ~D_i & D_j
        self.build(add_exp(self.lastNot, new), conc, self.lastBinary+[1])
        self.lastBinary.append(0)
        # update last negative conjunction 
        self.lastNot = add_exp(self.lastNot, negnew)
        # transfer to safe
        self.safe = []
        for r in self.tempaux:
            self.safe.append(Safe(r[0], r[1], r[2]))
        # --- end 
    # --- end computeNewRules

    # -------------------------
    # Analyze (from correct rules) inclusions relations for conclusion only
    # with sorting the rules 
    # Need quantifiers 
    def inclusions(self):
        size = len(self.correct)
        # graph for topological sort 
        G = Inclusion(size)
        self.solver.reset()
        # analyze rule j 
        for j in range(1, size):
            rulej = self.get_correct(j)
            Cj = rulej.get_conc()
            # compute relations with Cj => Ci and Ci => Cj
            for i in range(0, j):
                rulei = self.get_correct(i)
                Ci = rulei.get_conc()
                # check Cj&~Ci unsat
                #print ("inclusions " + str(Exists(self.variables, And(Cj, Not(Ci)))))
                if (self.variables):
                    self.solver.add(Exists(self.variables, And(Cj, Not(Ci))))
                else:
                    self.solver.add(And(Cj, Not(Ci)))
                sat = self.solver.check()
                self.solver.reset()
                if (sat.__eq__(unsat)):
                    #print("inclusions " + str(j) + " in " + str(i))
                    G.add(j, i)  
                # check ~Cj&Ci unsat
                #print ("inclusions " + str(Exists(self.variables, And(Not(Cj), Ci))))
                if (self.variables):
                    self.solver.add(Exists(self.variables, And(Not(Cj), Ci)))
                else:
                    self.solver.add(And(Not(Cj), Ci))
                sat = self.solver.check()
                self.solver.reset()
                if (sat.__eq__(unsat)):
                    #print("inclusions " + str(i) + " in " + str(j))
                    G.add(i, j) 
            # -- end for i
        # -- end for j
        # sort the and sort the rules 
        #print ("graph " + str(G))
        G.sort()
        #print ("graph " + str(G))
        # TODO reconsider the place of without relation
        # store ordering
        self.ordering = G.sorted
        # reset sorted and inclusions relations
        self.sorted = [0]*size
        for i in range(0, size):
            self.dicoconcneg[i] = []
        # TODO optimize it ?
        for old in G.sorted:
            new = G.sorted[old]
            self.sorted[new] = self.get_correct(old)
            # transfer and sort relations before inc from neg to dicoconcneg
            # no inversion and forget greater relations
            if (old in G.dico):
                rels = G.dico[old]
                for inc in rels:
                    incnew = G.sorted[inc]
                    if (incnew > new):
                        self.dicoconcneg[incnew].append(new)
                # --- end for inc
                # convert with  G.sorted equals relations too
                rels = G.equals[old]
                self.same_conclusion[G.sorted[old]] = [G.sorted[x] for x in rels]
            # --- end if old
        #print("Sorting.inclusions= " + str(self.dicoconcneg))
        #print("Sorting.equals= " + str(self.same_conclusion))
        # --- end for old
    # --- end inclusions
    
# --- end class Sorting