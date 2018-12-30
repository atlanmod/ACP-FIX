# ------------------
# 26/6/2018
# Iterative method
# remove obvious tautologies and separate unsafe  from safe
# -------------------
from Enumerative import  * #@UnusedWildImport
from Unsafe import *  #@UnusedWildImport
from Safe import *  #@UnusedWildImport
from math import * #@UnusedWildImport
from quine import * #@UnusedWildImport
from _hashlib import new

# --------------------------
# Class for Iterative method inheriting Enumerative
# j will be the new rule and i one already seen
class Iterative(Enumerative):
    
    # --------------------
    # init constructor 
    def __init__(self):
        super().__init__()
        # store safe cases
        self.safe = []
        # separate unsafe cases 
        self.unsafe = []
        # to store rules temporary 
        self.tempaux = []
        # to store information for last rule generation
        self.lastBinary = []
        self.lastNot = []
        # to count obvious
        self.obvious = 0
    # --- end init
    
    # --------------------
    def __str__(self):
        result = super().__str__()
        result += " ----------- Not unsafe -------------- \n"
        for er in self.safe:
            result += str(er) + "\n"
        result += " ----------- Unsafe -------------- \n"
        for e in self.unsafe:
            result += str(e) + "\n"
        result += " Count of nodes for safe+unsafe= " + str(self.count_nodes())
        return result 
    # --- end str
    
    # ---------------------
    def reset(self):
        super().reset()
        self.safe = []
        self.unsafe = []
        self.tempaux = []
        self.lastBinary = []
        self.lastNot = []
    # -- end reset
        
    # -------------------
    # check if unsafe rules exists 
    def has_unsafe(self):
        return (self.unsafe != [])
    # --- end has_unafe
    
    # --------------------
    # Built the corresponding Z3 BoolRef from safe rules
    # without the ForAll quantifier
    def z3_safe(self):
        args = []
        rules = self.safe
        if (rules):
            for r in rules:
                args.append(r.z3())
            # -- end for
            return And(*args)
        else:
            # 
            return True
    # --- end of z3

    # --------------------
    # Built the corresponding Z3 BoolRef from unsafe
    # without the  quantifiers
    def z3_unsafe(self):
        args = list(map(lambda x: x.z3(), self.unsafe))
        if (args):
            if (len(args)==1):
                return args[0]
            else:
                return And(*args)
        else:
            return True
    # --- end of z3_unsafe
    
    # --------------------
    # build the undefined expression with quantifiers
    def z3_undefined(self):
        args = []
        rules = self.unsafe
        # build exp for unsafe
        for r in rules:
            cond = r.get_cond()
            args.append(cond)
        # --- end for
        undef = self.one_undefined()
        if (is_expr(undef)):
            args.append(undef)
        else:
            args.extend(undef)
        if (args):
            if (self.variables):
                return ForAll(self.variables, Or(*args))
            else:
                return Or(*args)
        else:
            return False
    # --- end z3undefined
    
    # -------------------
    # Compute the union of 1-undefined in safe rules
    def one_undefined(self):
        args = []
        for r in self.safe:
            # optimize ?
            args.append(And(r.get_cond(), Not(r.get_conc())))
        if (args):
            return Or(*args)
        else:
            return False
    # --- end one-undefined

    #------------------
    # compute table with the new iterative process
    # take into account obvious and unsafe cases
    # with binary characteristic (in reverse counting order) and with don'tcare
    # bound is the number of processed rules (<= self.size()) 
    def compute_table(self, end):
        self.reset()
        self.clean(end)
        self.process_table(self.correct)
    # --- end compute_table
    
    # -----------------------
    # process a set of rules
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
        # initialize with the first rule 
        if (self.is_unsafe(cond, conc)):
            self.unsafe = [Unsafe([1], cond)]
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
    # simplify expressions with add_exp
    def computeNewRules(self, new, negnew, conc, nth):
        self.tempaux = []
        nb_rules = len(self.safe)
        # check the empty case
        for k in range(0, nb_rules):
            # analyze existing rules
            rulek = self.safe[k] 
            binary = rulek.get_binary()
            # TODO how to use super ?
            lcond = Rule.get_cond(rulek)
            lconc = Rule.get_conc(rulek)
            # evaluate and store both new rules  
            self.build(add_exp(lcond, new), add_exp(lconc, conc), binary+[1])
            # -- handle negative case
            self.build(add_exp(lcond, negnew), lconc, binary+[0])
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
    # --- end computeNewRules

    # -------------------
    # build the rules, store unsafe and remove tautology
    # conds, concs, binary are lists
    # store new rule triple in tempaux
    # needs binary + last to store characteristic
    # remove obvious only, classify unsafe
    # TODO strange case
    def build(self, conds, concs, binary):
        #print ("build for " + str(binary) + " : " + str(conds) + " " + str(concs) )
        if (not self.is_obvious(conds)):
            #print ("is not obvious")
            ### check safe unsafe 
            if (self.is_unsafe(conds, concs)):
                # TODO ?
                if (self.is_strange(conds)):
                    print ("Strange: " + str(binary))
                else:
                    self.unsafe.append(Unsafe(binary, conds))
            else:
                self.tempaux.append((binary, conds, concs))
        # -- end if obvious
    # -- end of build

    # --------------------------
    # check the validity of the transformation
    # self.rules <=> unsafe AND self.safe
    # take care of self.variables !!!  
    # end to stop checking 
    def check(self, end):
        # rules and Not(safe) OR Not(unsafe)
        self.solver.reset()
        if (self.variables):
            self.solver.add(ForAll(self.variables, self.toBoolRef(end)))
        else:
            self.solver.add(self.toBoolRef(end))
        if (self.has_unsafe()):
            if (self.variables):
                self.solver.add(Exists(self.variables, Or(Not(self.z3_safe()), Not(self.z3_unsafe()))))
            else:
                self.solver.add(Or(Not(self.z3_safe()), Not(self.z3_unsafe())))
        else:
            if (self.variables):
                self.solver.add(Exists(self.variables, Not(self.z3_safe())))
            else:
                self.solver.add(Not(self.z3_safe()))
        print (" => " + str(self.solver.check()))
        # Not(rules) AND safe AND unsafe
        self.solver.reset()
        if (self.variables):
            self.solver.add(Exists(self.variables, Not(self.toBoolRef(end))))
        else:
            self.solver.add(Not(self.toBoolRef(end)))
        rprime = self.z3_safe()
        if (self.has_unsafe()):
            rprime = And(rprime, self.z3_unsafe())
        if (self.variables):
            rprime = ForAll(self.variables, rprime)
#         if (not isinstance(rprime, bool)):
#             self.solver.add(rprime)
        self.solver.add(rprime)
        print (" <= " + str(self.solver.check()))
    # ----- end check
    
    # ----------------------
    # check safety of request set
    # check if REQ with quantifiers & undefined are disjoint
    # TODO useful or correct ?
    def isSafe(self, REQ):
        self.solver.reset()
        self.solver.add(REQ)
        #print ("undefined ? " + str(self.z3undefined()))
        self.solver.add(self.z3_undefined())
        print ("isSafe " + str(REQ) + " is " + str(self.solver.check().__eq__(unsat)))
    # --- end isSafe
    
    # ----------------------
    # check req against Safe(R)
    # req with free variables and return the states
    # defined = both are sat
    # TODO not correct ? U is ?*
    def check2safe(self, req):
        self.solver.reset()
        if (self.variables):
                req = Exists(self.variables, req) # ?
        self.solver.add(req)
        self.solver.push()
        self.solver.add(self.get_safe())
        print (str(req) + " is undefined " + str(self.solver.check().__eq__(unsat)))
        self.solver.pop()
        # is included in Safe
        self.solver.add(Not(self.get_safe()))
        print (str(req) + " is safe " + str(self.solver.check().__eq__(unsat)))
    # --- end check2safe
    
    # -------------------
    # get_safe compute the safe formula  with quantifiers
    def get_safe(self):
        res = [And(x.get_cond(), x.get_conc()) for x in self.safe]
        if (res):
            if (len(res) == 1):
                if (self.variables):
                    return ForAll(self.variables, res[0])
                else:
                    return res[0]
            else:
                if (self.variables):
                    return ForAll(self.variables, Or(*res))
                else:
                    return Or(*res)
        else:
            return True
    # ---- end get_safe

    # -------------------------
    # csv output of some tests
    # name is a local filename to create
    def perf(self, name):
        csvfile = open(name +".csv", "w+")
        try:
            outwriter = writer(csvfile)
            # use classe name here 
            outwriter.writerow( ['rules', 'correct', 'safe', 'unsafe', 'time'] )
            # for i in range(2, 31): #1+self.number_rule()):
            for i in range(2, 1+self.number_rule()):
                start = clock()
                self.compute_table(i)
                outwriter.writerow( [i,  len(self.correct), len(self.safe), len(self.unsafe), floor(clock()-start)])
                #print (str(self))
                print( str([i,  len(self.correct), len(self.safe), len(self.unsafe), floor(clock()-start)]))
        finally:
            csvfile.close()
    # ----- end of perf
    
    # -------------------
    # call Quine on unsafe and return a BoolRef
    # but need to complete the binaries
    # TODO lack 1-undefined ?
    def quine(self):
        # number of correct rules
        n = len(self.correct)
        # to cope with dont'care 
        listbin = list(map(lambda x: x.get_binary(), self.unsafe))
        tmp = []
        for l in listbin:
            tmp += expand(l)
        #print("quine listbin " + str(Simplify0))
        #  complete binary with 0/1
        # TODO to optimize or avoid this
        allmins = []
        for l in tmp:
            nb = (n - len(l))
            if (nb > 0):
                allmins += complete(nb, l)
            else:
                allmins.append(l)
        # --- for l
        #print ("allmins " + str(allmins))
        #if allmins
        if (allmins):
            listbin = quine(n, allmins)
            res = []
            for binary in listbin:
                res.append(And(*self.rebuildCond(binary))) #TODO here
            if (len(res) == 0):
                res = True
            elif (len(res) == 1):
                res = res[0]
            else:
                res = Or(*res)
            # ---
            print ("Quine= " + str(res))
            print ("+tactic= " + str(tactic(res)))
        # -- 
    # --- end of quine
    
    # -----------------------
    # count nodes in safe and unsafe rules
    def count_nodes(self):
        return sum([x.size_nodes() for x in self.safe]) + sum([x.size_nodes() for x in self.unsafe])
    # --- end count_nodes


# --- end class 