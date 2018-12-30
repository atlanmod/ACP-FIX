# ------------------
# 23/8/2018
# Sorting improvements with inclusions conditions 
# and apply exclusive 
# TODO apply exclusive
# -------------------

#TODO review it and clean
# TODO fix pb clean unsafe to change in others ?
# use self.radix but only in final results ?
# clean unsafe! DEACTIVATED !!!

# TODO redfine check for taking intoaccount explicit ?

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
#         # TODO should add radix to not unsafe 
#         self.safe = []
#         for r in self.tempaux:
#             if (self.radixNot):
#                 if (isinstance(r[1], list)):
#                     condsaux = self.radixNot+r[1]
#                 else:
#                     condsaux = self.radixNot+[r[1]]
#                 self.safe.append(Safe(self.radixBinary+r[0], condsaux, r[2]))
#             else:
#                 self.safe.append(Safe(r[0], r[1], r[2]))
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
    # TODO remove nth use nth ?
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
    # TODO may be something inexpected with unsafe / +++
    # TODO erreur condaux ?
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
    # TODO pb with assign2007 ?
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
    
    # -------------------------
    # Composition exclusive with partition
    # REQUIRE: ? non void partition
    # take care consistency rules numbering and partition
    # TODO use compose_exclusive and paratemetize partition
    def apply_exclusive(self, end):
        self.reset()
        self.clean(end)
        # from correct rules
        self.partition()
        # TODO simple partition
        #self.graph = Partition(len(self.correct))
        #self.graph.split(3)
        # create subsystems 
        subsystem = []
        for i in range(0, self.graph.packet):
            # create a subsystem
            aux = Improve()
            aux.variables = self.variables
            part = self.graph.partition[i]
            # store the local partition for the mapping
            aux.partition = part
            size = len(part)
            # fill the correct rules
            for j in range(0, size):
                # rule numbering in original
                nb = part[j]
                aux.rules.append(self.correct[nb])
            # --- end for j
            # use compute_table(size) or optimize
            aux.compute_table(size)
            subsystem.append(aux)
        # --- end for i
        # transfer all other rules
        for m in subsystem:
            # TODO add binary correct for unsafe
            self.unsafe.extend(m.unsafe)
        # if one packet simply transfer 
        if (self.graph.packet >= 1):
            self.safe = subsystem[0].safe
            self.sorted.extend(subsystem[0].sorted)
            self.lastNot = [Not(r.get_cond()) for r in self.sorted]
            self.lastBinary = [0]*len(self.sorted) 
            for i in range(1, self.graph.packet):
                ### only if there are rules
                if (subsystem[i].safe):
                    self.compose_3(subsystem[i])                  
#         # if one packet simply transfer 
#         if (self.graph.packet == 1):
#             self.safe = subsystem[0].safe
#             # TODO binary ?
#             self.unsafe = subsystem[0].unsafe
#         else:
#             # TODO compose_modules
#             self.compose_modules_3(subsystem)
#             #self.enum_all(subsystem)
    # --- end apply_exclusive 
    
    ### nary exclusive combination but not optimized
    #### since build is global 
#     # -------------------------
#     # modules is a list of subsystems
#     # Combined  the not unsafe rules and collects the unsafe !!! binaries ???
#     # exclusive will compute the table for each of them and combined all
#     def compose_modules(self, modules):
#         how = len(modules)
#         for table in modules:
#             size = table.number_rule()
#             table.compute_table(size)
#             #table.check(size)
#         # --- end for i
#         # if one packet simply transfer 
#         if (how == 1):
#             self.safe = modules[0].safe
#             self.unsafe = modules[0].unsafe
#         else:
#             self.enum_all(modules)
#     # --- end exclusive
#     
#     # -----------------------
#     # use an enumerative method based on the number of packets
#     # REQUIRE: subs is not empty
#     # How to enumerate sbinary ?
#     def enum_all(self, subs):
#         nbpacket = len(subs)
#         self.tempaux = []
#         # self.safe = []
#         # self.unsafe = [] # 
#         # limits of the safe rule in each subsystem 
#         limits = [len(x.safe) for x in subs]
#         # all binaries (structured)
#         binaries =  [[r.get_binary() for r in sys.safe] for sys in subs]
#         # enumerate binary of length nbpacket
#         finish = False
#         charac = [0] * nbpacket
#         first = True # to forget 0*
#         while (not finish):
#             if (not first):
#                 #print ("Binary packets " + str(charac))
#                 # ----------------------------------
#                 # TODO enumerate structured binary 
#                 # 0 means negation of packet conditions
#                 # 1 means a binary of this packet is active
#                 # -1 for unsafe TODO
#                 # built a counters with limits
#                 counters = [0] * nbpacket
#                 fin = False
#                 while (not fin):
#                     # built structured binary but with 0 if charac==0
#                     #print ("counters " + str(counters))
#                     current = [binaries[i][counters[i]] if (charac[i]==1) else 0 for i in range(0, nbpacket)]
#                     #print ("current " + str(current))
#                     self.make(current, subs)  
#                     # the first counter which is not zero (there is one)
#                     l = 0
#                     while (charac[l] == 0): 
#                         l += 1
#                     counters[l] += 1
#                     # increment counters
#                     for k in range(0, nbpacket):
#                         # only non zero counters
#                         if (not charac[k] == 0):
#                             if (counters[k] >= limits[k]):
#                                 # find next counter
#                                 next = k+1
#                                 while (next < nbpacket) and (charac[next] == 0):
#                                     next += 1
#                                 if (next < nbpacket):
#                                     counters[k] = 0
#                                     counters[next] += 1
#                                 else:
#                                     fin = True
#                             # -- end if counters
#                         # --- end if not charac
#                     # -- end for i
#                 # -- end while
#             # --- end if enumeration sbinary -------------------
#             # enumerate 2^nbpacket
#             charac[0] += 1
#             first = False
#             for i in range(0, nbpacket):
#                 if (charac[i] > 1):
#                     if (i+1 < nbpacket):
#                         charac[i] = 0
#                         charac[i+1] += 1
#                     else:
#                         finish = True
#                 # -- end if charac
#             # -- end for i
#         # --- end while 
#         # transfer to safe 
#         for r in self.tempaux:
#             self.safe.append(Safe(r[0], r[1], r[2]))
#         # transfer all unsafe
#         # TODO but binary are not structured here
#         # use [-1] to show unused group
#         tmp = []
#         for sys in subs:
#             tmp.extend(sys.unsafe)
#         self.unsafe = tmp + self.unsafe
#     # --- end of enum_all
# 
#     # ----------------------------
#     # make a new rule from a structured binary characteristic with 0
#     # and a set of subsystems
#     # with don't care and build list of Z3Exp
#     def make(self, sbinary, subs):
#         #print ("Make: binary " + str(sbinary))
#         nbpacket = len(subs)
#         # make conditions
#         conds = []
#         for j in range(0, nbpacket):
#             binary = sbinary[j]
#             # it is a  zero or a list
#             if (binary == 0):
#                 for i in range(0, len(subs[j].sorted)):
#                     conds.append(Not(subs[j].get_sorted(i).get_cond()))
#             else:
#                 for i in range(0, len(binary)):
#                     if (not binary[i] == -1):
#                         if (binary[i] == 1):
#                             conds.append(subs[j].get_sorted(i).get_cond())
#                         else:
#                             conds.append(Not(subs[j].get_sorted(i).get_cond()))
#                         # -- useful case
#                     # -- don't care
#                 # --- end for i
#             # --- end if not binary
#         # --- end for j
#         # make conclusions
#         concs = []
#         for j in range(0, nbpacket):
#             binary = sbinary[j]
#             # it is a  zero or a list
#             if (not binary == 0):
#                 for i in range(0, len(binary)):
#                     if (not binary[i] == -1):
#                         if (binary[i] == 1):
#                             concs.append(subs[j].get_sorted(i).get_conc())
#                         # -- useful case
#                     # -- don't care
#                 # -- end for i
#             # --- end if not binary
#         # --- end for j
#         # print ("make: call build on " + str(conds) + str(concs) + str(sbinary))
#         self.build(conds, concs, sbinary)
#     # --- end make
#     
    # -------------- another version of exclusive 
    # -----------------
    
    # -----------------
    # Another modular composition
    def compose_modules_3(self, modules):
        self.reset()
        self.rules = []
        how = len(modules)
        for table in modules:
            size = table.number_rule()
            table.compute_table(size)
            #table.check(size)
            #print ("Compose_modules_3 " + str(table))
        # --- end for i
        print("Compose_modules_3 sizes= " + str([len(m.safe) for m in modules]))
        # transfer all other rules
        for m in modules:
            self.rules.extend(m.rules)
            self.correct.extend(m.correct)
            # TODO add binary correct for unsafe
            self.unsafe.extend(m.unsafe)
        # if one packet simply transfer 
        if (how >= 1):
            self.safe = modules[0].safe
            self.sorted.extend(modules[0].sorted)
            self.lastNot = [Not(r.get_cond()) for r in self.sorted]
            self.lastBinary = [0]*len(self.sorted) 
            for i in range(1, how):
                ### only if there are rules
                if (modules[i].safe):
                    self.compose_3(modules[i])
    # --- end compose_modules_3
        
#     #----------------------
#     # Compose self.exclusive with another sets of exclusive
#     # use compose_binary and result in self
#     # REQUIRE: same variables for all already in self
#     # TODO binary of unsafe not correct ?
#     # TODO voir une approche +iterative and forget rebuild too ?
#     def compose_2(self, erules):
#         self.tempaux = []
#         # merging original systems for checking
#         self.rules.extend(erules.rules)
#         # merging of the two correct rule lists
#         self.sorted.extend(erules.sorted)
#         # merge existing unsafe TODO binary ?
#         self.unsafe.extend(erules.unsafe)
#         # extract binary characteristics
#         bins1 = [X.get_binary() for X in self.safe]
#         # TODO pb here if safe empty
# #         if (not bins1):
# #             bins1 = [[-1]*len(self.sorted)]
#         bins2 = [X.get_binary() for X in erules.safe]
#         #print ("compose_2 " + str(bins1) + str(bins2))
#         newbins = compose_binary(bins1, bins2)
#         for binary in newbins:
#             #print ("compose_2 " + str(binary))
#             conds = self.rebuildCond(binary)
#             concs = self.rebuildConc(binary)
#             self.build(conds, concs, binary)
#         # --- end for
#         # don't forget transfer
#         self.safe = []
#         for r in self.tempaux:
#             self.safe.append(Safe(r[0], r[1], r[2]))
#     # --- end compose_2
# 
#     # ----------------------------
#     # rebuild a  condition list of BoolRef from a binary characteristic
#     # and return the list of conditions
#     def rebuildCond(self, binary):
#         res = []
#         for i in range(0, len(binary)):
#             if (not binary[i] == -1):
#                 if (binary[i] == 1):
#                     res.append(self.get_sorted(i).get_cond())
#                 else:
#                     res.append(Not(self.get_sorted(i).get_cond()))
#                 # -- useful case
#             # -- don't care
#         # -- for i
#         return res
#     # --- end rebuildCond
#     
#     # ----------------------------
#     # rebuild a  conclusion list of BoolRef from a diff relation
#     def rebuildConc(self, binary):
#         res = []
#         for i in range(0, len(binary)):
#             if (not binary[i] == -1):
#                 if (binary[i] == 1):
#                     res.append(self.get_sorted(i).get_conc())
#                 # -- useful case
#             # -- don't care
#         # -- for i
#         return res
#     # --- end rebuildConc
    
    #----------------------
    # Compose self.exclusive with another sets of exclusive
    # try a better iterative approach than compose_2
    # REQUIRE: same variables for all already in self and Exclusive rules
    # TODO make it more iterative 
    def compose_3(self, erules):
        self.tempaux = []
        # compute last indicators at right
        lastright = [Not(r.get_cond()) for r in erules.sorted]
        lastr = [0]*len(erules.sorted)
        # iterate on safe rules at left
        for left in self.safe:
            bins1 = left.get_binary()
            condl = Rule.get_cond(left)
            if (not isinstance(condl, list)):
                condl = [condl]
            concl = Rule.get_conc(left)
            if (not isinstance(concl, list)):
                concl = [concl]
            # iterate on safe rules at right
            for right in erules.safe:
                # build and evaluate the new rule
                condr = Rule.get_cond(right)
                if (not isinstance(condr, list)):
                    condr = [condr]
                concr = Rule.get_conc(right)
                if (not isinstance(concr, list)):
                    concr = [concr]
                self.build(condl+condr, concl+concr, bins1+right.get_binary())
            # --- end for right
            # add last right for each left
            self.build(condl+lastright, concl, bins1+lastr)
        # add last left for each right 
        for right in erules.safe:
            condr = Rule.get_cond(right)
            if (not isinstance(condr, list)):
                condr = [condr]
            concr = Rule.get_conc(right)
            if (not isinstance(concr, list)):
                concr = [concr]
            self.build(self.lastNot+condr, concr, self.lastBinary+right.get_binary())
        # don't forget transfer and update
        self.sorted.extend(erules.sorted)
        self.lastBinary.extend(lastr)
        self.lastNot.extend(lastright)
        self.safe = []
        for r in self.tempaux:
            self.safe.append(Safe(r[0], r[1], r[2]))
    # --- end compose_3   

# --- end Improve
