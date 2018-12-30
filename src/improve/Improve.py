# ------------------
# 23/8/2018
# Sorting improvements with inclusions conditions 
# and apply exclusive 
# -------------------

from Sorting import *  #@UnusedWildImport
from Partition import *
from itertools import * #@UnusedWildImport

# --------------------------
# Class for Table inheriting Sorting 
# j will be the new rule and i one already seen
class Improve(Sorting):
    
    # --------------------
    # init constructor 
    def __init__(self):
        super().__init__()
        # dicos for inclusion relations
        self.conditions = dict()  #  
        # graph to compute the partition
        self.graph = None
        # to count built
        self.built = 0
        # to capture common radix due to clean explicit unsafe
        self.radixNot = []
        self.radixBinary = []
        self.explicit = []
        # to store tautology
        self.tautology = []
    # --- end init
    
    # --------------------
    # check if rule i is redundant related to other sorted rules
    # return True or False
    # R/ri => ri thus check ?* R\ri & ~ri unsat
    def is_redundant(self, i):
        args = []
        for k in range(0, len(self.sorted)):
            if (not k == i):
                r = self.sorted[k]
                args.append(Implies(r.get_cond(), r.get_conc()))
        # and use the solver
        self.solver.reset()
        if (self.variables):
            self.solver.add(Exists(self.variables, And(*args, self.sorted[i].get_cond(), Not(self.sorted[i].get_conc()))))
        else: 
            self.solver.add(And(*args))
            self.solver.add(self.sorted[i].get_cond())
            self.solver.add(Not(self.sorted[i].get_conc()))
        return self.solver.check().__eq__(unsat)
    # --- end is_redundant
    
    # ------------------------
    # check each rule, and remove  tautologies
    # and unsafe rule are separated and last tuned
    # end last rule to stop analysis
    def clean(self, end):
        self.correct = []
        for i in range(0, end):
            r = self.rules[i]
            if (not r.is_tautology(self.variables)):
                # explicit unsafe is independent of the ordering
                if (r.is_explicit_unsafe(self.variables)):
                    cond = r.get_cond()
                    self.unsafe.append(Unsafe(self.radixBinary+[1], self.radixNot+[cond]))
                    self.radixNot.append(Not(cond))
                    self.radixBinary.append(0)     
                    self.explicit.append(i)       # store rule number             
                else:
                    self.correct.append(r)
            else:
                self.tautology.append(i) # store rule number             
        # -- end for
    # -- end clean
        
    #------------------
    # Processing from the sorted rules ...
    # compute table with the new iterative process
    # take into account tautology and unsafe cases
    # with binary characteristic (in reverse counting order) and with don'tcare
    # bound is the number of processed rules (<= self.size()) and toview to print
    def compute_table(self, end):
        self.reset()
        self.clean(end)
        self.inclusions()
        self.cond_inclusions()
        if (len(self.sorted) > 0):
            self.process_table(self.sorted)
    # --- end compute_table

    # -----------------------
    # redefine process a set of rules
    def process_table(self, rules):
        # j is the processed rule
        size = len(rules)
        # compute list of conditions and conclusions 
        # newrules only triple: binary, list conditions list conclusions
        rule = rules[0]
        # initialize with the first rule now it is not unsafe (or don't be proved like that)
        # and simplify it
        cond = rule.get_cond()
        conc = rule.get_conc()
        # initialize with the first rule and radix for unsafe
        if (self.is_unsafe(cond, conc)):
            self.unsafe.append(Unsafe(self.radixBinary + [1], self.radixNot + [cond]))
        else:
            self.safe = [Safe([1], cond, conc)]
        self.lastNot = Not(cond)
        self.lastBinary = [0]     
        # ------------
        # iterative process for each  rules
        for j in range(1, size):
            rule = rules[j]
            #print ("----------  with rule " + str(j) + " = " + str(rule))
            new = rule.get_cond()
            if (isinstance(new, bool)):
                negnew = not new
            else: 
                negnew = Not(new) 
            conc = rule.get_conc()
            self.computeNewRules(new, negnew, conc, j)
        # --- end for
    # -- end process_table
    
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
            # print (str(k) + " --> " + str(rulek))
            binary = rulek.get_binary()
            lcond = Rule.get_cond(rulek)
            lconc = Rule.get_conc(rulek)
            # add here test exclusion
            rels = self.dicoconcneg[nth]
            # test if a rule in rels is active in binary
            if (included(rels, binary)):
                # copy the old rule with a dont'care
                self.tempaux.append((binary+[-1], lcond, lconc))
            # condition inclusion TODO may be simplif
            elif (included(self.conditions[nth], binary)):
                #print ("Newrules: conditions " + str(lcond))
                self.build(lcond, add_exp(lconc, conc), binary+[1])
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
        # transfer tempaux to safe
        # self.radix if last turn
        self.safe = []
        if (nth < len(self.sorted)-1): 
            for r in self.tempaux:
                self.safe.append(Safe(r[0], r[1], r[2]))
        else:
            for r in self.tempaux:
                if (self.radixNot):
                    if (isinstance(r[1], list)):
                        condsaux = self.radixNot+r[1]
                    else:
                        condsaux = self.radixNot+[r[1]]
                    self.safe.append(Safe(self.radixBinary+r[0], condsaux, r[2]))
                else:
                    self.safe.append(Safe(r[0], r[1], r[2]))            
            # --- end for r
        # -- end if last trun
    # --- end computeNewRules
        
    # -------------------
    # build the rules, store unsafe and remove tautology
    # store new rule triple in tempaux
    # needs binary to store characteristic and tautology indicator
    # remove obvious only, classify unsafe
    # cope with the new radix information
    def build(self, conds, concs, binary):
        #print ("build for " + str(binary) + " : " + str(conds) + " " + str(concs) )
        # radix only for storing or final result
        if (isinstance(conds, list)):
            condsaux = self.radixNot + conds
        else:
            condsaux = self.radixNot + [conds]
        binaryaux = self.radixBinary + binary
        if (not self.is_obvious(condsaux)):
            if (self.is_unsafe(condsaux, concs)):
                # TODO ?
                if (self.is_strange(condsaux)):
                    skip
                    #print ("Strange: " + str(binaryaux))
                else: 
                    # print ("build unsafe " + str(binary) + " : " + str(conds) + " " + str(concs) )
                    self.unsafe.append(Unsafe(binaryaux, condsaux))
            else:
                # print ("build safe " + str(binary) + " : " + str(conds) + " " + str(concs) )
                self.tempaux.append((binary, conds, concs))
        # -- end if obvious
    # -- end of build
    
    # ---------------------
    # compute inclusions of conditions
    def cond_inclusions(self):
        size = len(self.sorted)
        # analyze rule j
        for j in range(1, size):
            rulej = self.sorted[j]
            self.conditions[j] = []
            #print ("rulej " + str(rulej) )
            Dj = rulej.get_cond()
            # compute relations 
            for i in range(0, j):
                rulei = self.sorted[i]
                #print ("rulei " + str(rulei) )
                Di = rulei.get_cond()
                #print ("inclusions " + str(Di) + " => " + str(Dj))
                # check Di&~Dj unsat (Di => Dj)
                self.solver.reset()
                if (self.variables):
                    self.solver.add(Exists(self.variables, And(Di, Not(Dj))))
                else:
                    self.solver.add(And(Di, Not(Dj)))
                check = self.solver.check()
                if (check.__eq__(unsat)):
                    #print("Inclusion condition " + str(i) + " in " + str(j))
                    self.conditions[j].append(i)
            # -- end for i
        # -- end for j
        #print ("Conditions relations " + str(self.conditions))
    # --- end cond_inclusions
    
    # --------------------------
    # check the validity of the transformation
    # self.rules <=> unsafe AND self.safe AND self.explicit
    # take care of self.variables !!!  
    # end to stop checking 
    def check(self, end):
        allcomputed = self.safe + self.unsafe + [self.rules[i] for i in self.explicit]
        #print (str(allcomputed))
        expcomputed = And(*[r.z3() for r in allcomputed]) 
        print("check: " + str(expcomputed))
        # rules and NOT(explict+unsafe+safe)
        self.solver.reset()
        if (self.variables):
            self.solver.add(ForAll(self.variables, self.toBoolRef(end)))
            self.solver.add(Exists(self.variables, Not(expcomputed)))
        else:
            self.solver.add(self.toBoolRef(end))
            self.solver.add(Not(expcomputed))
        print (" => " + str(self.solver.check()))
        # Not(rules) AND explict+unsafe+safe
        self.solver.reset()
        if (self.variables):
            self.solver.add(Exists(self.variables, Not(self.toBoolRef(end))))
            self.solver.add(ForAll(self.variables, expcomputed))
        else:
            self.solver.add(Not(self.toBoolRef(end)))
            self.solver.add(expcomputed)
        print (" <= " + str(self.solver.check()))
    # ----- end check
        
    # -------------------------
    # build the partition (from correct rules) inclusions relations for conclusion only
    # with sorting the rules 
    # Need quantifiers 
    # TODO sharing with inclusions ...
    def partition(self):
        size = len(self.correct)
        # graph for topological sort 
        self.graph = Partition(size)
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
                if (self.variables):
                    self.solver.add(Exists(self.variables, And(Cj, Not(Ci))))
                else:
                    self.solver.add(And(Cj, Not(Ci)))
                sat = self.solver.check()
                self.solver.reset()
                if (sat.__eq__(unsat)):
                    self.graph.add(j, i)  
                # check ~Cj&Ci unsat
                if (self.variables):
                    self.solver.add(Exists(self.variables, And(Not(Cj), Ci)))
                else:
                    self.solver.add(And(Not(Cj), Ci))
                sat = self.solver.check()
                self.solver.reset()
                if (sat.__eq__(unsat)):
                    self.graph.add(i, j) 
            # -- end for i
        # -- end for j
        self.graph.connexes()
        print ("graph " + str(self.graph))
    # --- end partition
    
# --- end Improve
