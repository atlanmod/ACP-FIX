# ------------------
# 3/8/2018
# Table for exclusive rules and enumerative
# -------------------

from ExclusiveRule import * #@UnusedWildImport
from RuleSet import * #@UnusedWildImport
from MoreUtility import * #@UnusedWildImport
from csv import * #@UnusedWildImport
from time import * #@UnusedWildImport
from math import * #@UnusedWildImport

# --------------------------
# Class for Table inheriting rule set 
# TODO simplification of expressions check True and False ?
class Enumerative(RuleSet):
    
    # --------------------
    # init constructor 
    def __init__(self):
        super().__init__()
        # to store exclusive rules a list of rules
        # binary characteristic = dec2bin(index+1)
        self.exclusive = []
        # local solvers
        self.solver = Solver()
        self.solver.set(timeout = 1000) ### 1second
        # to store non tautology
        self.correct = []
    # --- end init
    
    # --------------------
    def __str__(self):
        result = super().__str__()
        result += "\n ----------- Correct -------------- \n"
        for r in self.correct:
            result += str(r) + "\n"
        result += " ----------- Exclusive -------------- \n"
        for er in self.exclusive:
            result += str(er) + "\n"
        return result 
    # --- end str
    
    # ---------------------
    def reset(self):
        self.exclusive = []
        self.correct = []
    # -- end reset
        
    # ----------------------
    def get_correct(self, i):
        return self.correct[i]
    # -- end get_correct

    # -------------------
    # compute list of conditions
    # TODO use list comprehensions!
    def get_conds(self):
        return list(map((lambda x: x.get_cond()), self.correct))
    # --- end get_conds
    
    # -------------------
    # compute list of conclusions
    def get_concs(self):
        return list(map((lambda x: x.get_conc()), self.correct))
    # --- end get_concs

    # ------------------------
    # check each rule, and remove only tautologies 
    # end last rule to stop analysis
    def clean(self, end):
        self.correct = []
        for i in range(0, end):
            r = self.rules[i]
            if (not r.is_tautology(self.variables)):
                self.correct.append(r)
        # -- end for
    # -- end clean

    # --------------------
    # Enumerative computation
    # without simplification but respecting the binary characteristic
    # same quantifiers as the original rules
    # end to only process the first end rules
    def compute_table(self, end):
        # remove tautology
        self.clean(end)
        # size of the rule set 
        n = len(self.correct)
        # compute list of conditions and conclusions 
        conds = self.get_conds()
        concs = self.get_concs()
        # print ("liste " + str(conds) + " " + str(concs))
        limit = 2 ** n
        # enumerate non void combinaitions of [1 .. n]
        # it is a list of binary digits of length n 
        for j in range(1, limit):
            # compute the binary characteristic
            charac = dec2bin(j, n)
            complexcond = True
            complexconc = True
            for i in range(0, n):
                if (charac[i]==1):
                    complexcond = add_exp(complexcond, conds[i])
                    complexconc = add_exp(complexconc, concs[i])
                else:
                    arg = conds[i]
                    if not (arg == False):
                        if (arg == True):
                            complexcond = False
                        else: 
                            complexcond = add_exp(complexcond, Not(conds[i]))
                    # -- end if arg
                # -- end if charac
            # -- end for i
            # compute the conjunctions 
            if (isinstance(complexcond, list)):
                complexcond = And(*complexcond)
            # -- end if complexcond
            if (isinstance(complexconc, list)):
                    complexconc = And(*complexconc)
            # -- end if complexconc
            #  test and remove tautology
            # reset solvers 
            self.solver.reset()
            if (self.variables):
                self.solver.add(Exists(self.variables, And(complexcond, Not(complexconc))))
            else:
                self.solver.add(And(complexcond, Not(complexconc)))
            valid = self.solver.check()
            if (not valid.__eq__(unsat)):
                self.exclusive.append(ExclusiveRule(charac, complexcond, complexconc))
        # -- end for j
    # --- end compute_table

    # --------------------
    # Built the corresponding Z3 ExpRef
    # without the ForAll quantifier
    def z3_exclusive(self):
        args = []
        rules = self.exclusive
        if (rules):
            for r in rules:
                args.append(r.z3())
            # -- end for
            return And(*args)
        else:
            return True
    # --- end of z3
    
    # --------------------------
    # check if exp1 <=> exp2
    # return 0, or 1 if => -1 if <= else 2
    def check_exp(self, exp1, exp2):
        self.solver.reset()
        self.solver.add(ForAll(self.variables, exp1))
        self.solver.add(Exists(self.variables, Not(exp2)))
        way1 = self.solver.check()
        self.solver.reset()
        self.solver.add(Exists(self.variables, Not(exp1)))
        self.solver.add(ForAll(self.variables, exp2))
        way2 = self.solver.check()
        if (way1.__eq__(unsat)):
            if (way2.__eq__(unsat)):
                return 0;
            else:
                return 1
        elif (way2.__eq__(unsat)):
                return -1;
        else:
            return 2
    # --- end check_exp

    # --------------------------
    # check the validity of the transformation
    # self.rules <=> self.exclusive
    def check(self, end):
        # rules and Not(exclusive) 
        self.solver.reset()
        self.solver.add(ForAll(self.variables, self.toBoolRef(end)))
        self.solver.add(Exists(self.variables, Not(self.z3_exclusive())))
        #print (" => "  + str(self.solver))
        print (" => " + str(self.solver.check()))
        self.solver.reset()
        self.solver.add(Exists(self.variables, Not(self.toBoolRef(end))))
        rprime = self.z3_exclusive()
        if (not isinstance(rprime, bool)):
            self.solver.add(ForAll(self.variables, rprime))
        #print ("<= " + str(self.solver))
        print (" <= " + str(self.solver.check()))
    # ----- end check
    
    # ----------------------
    # check pair wise exclusivity of conditions
    def checkExclu(self):
        print ("check condition exclusivity ...... ")
        for j in range(0, len(self.exclusive)):
            condj = self.exclusive[j].get_cond()
            for i in range(j+1, len(self.exclusive)):
                condi = self.exclusive[i].get_cond()
                self.solver.reset()
                self.solver.add(ForAll(self.variables, And(condj, condi)))
                if (not self.solver.check().__eq__(unsat)):
                    print ("checkExclu problem with " + str(j) + " " + str(i))
                    print ("rules j & i " + str(self.exclusive[j]) + " \n " + str(self.exclusive[i]))
            # -- end for i
        # --- end for j
    # --- end checkExclu
    
    # ----------------------
    # check pair wise exclusivity on binary
    def checkSingleExclu(self):
        print ("check binary exclusivity ...... ")
        for j in range(0, len(self.exclusive)):
            binj = self.exclusive[j].get_binary()
            for i in range(j+1, len(self.exclusive)):
                bini = self.exclusive[i].get_binary()
                if (binj == bini):
                    print ("checkSingleExclu problem with " + str(j) + " " + str(i))
            # -- end for i
        # --- end for j
    # --- end checkSingleExclu
    
    # -------------------------
    # csv output of some tests
    # name is a local filename to create
    def perf(self, name):
        csvfile = open(name +"20.csv", "w+")
        try:
            start = clock()
            outwriter = writer(csvfile)
            outwriter.writerow( ['Enumerative'] )
            outwriter.writerow( ['rule', 'correct', 'exclusive', 'time'] )
            for i in range(2, 21): #self.number_rule()):
                self.compute_table(i)
                outwriter.writerow( [i , len(self.correct),  len(self.exclusive) ,  floor((clock()-start))])
                print( str([i , len(self.correct),  len(self.exclusive) ,  floor((clock()-start))]))
        finally:
            csvfile.close()
    # ----- end of perf

    # ----------------------------
    # rebuild a  condition list of BoolRef from a binary characteristic
    # and return the list of conditions
    def rebuildCond(self, binary):
        res = []
        for i in range(0, len(binary)):
            if (not binary[i] == -1):
                if (binary[i] == 1):
                    res.append(self.get_sorted(i).get_cond())
                else:
                    res.append(Not(self.get_sorted(i).get_cond()))
                # -- useful case
            # -- don't care
        # -- for i
        return res
    # --- end rebuildCond
    
    # ----------------------------
    # build a conclusion from the rules and a binary
    # from original rules
    # return a list of Z3 for AND
    def build_conc(self, binary):
        res = []
        for i in range(0, len(binary)):
            if (not binary[i] == -1):
                if (binary[i] == 1):
                    res.append(self.rules[i].get_conc())
                # -- useful case
            # -- don't care
        # -- for i
        return res
    # --- end build_conc
    
    # ----------------------------
    # build a condition from the rules and a binary
    # from original rules
    # return a list of Z3 for AND
    def build_cond(self, binary):
        res = []
        for i in range(0, len(binary)):
            if (not binary[i] == -1):
                if (binary[i] == 1):
                    res.append(self.rules[i].get_cond())
                else:
                    res.append(Not(self.rules[i].get_cond()))
                # -- useful case
            # -- don't care
        # -- for i
        return res
    # --- end build_cond
    
    # --------------------
    # test obvious and return True if unsat
    # else False if sat or unknown
    # cope with free variables
    def is_obvious(self, conds):
        #print ("isobvious" + str(conds))
        self.solver.reset()
        # True/False cases
        if (isinstance(conds, bool)):
            return not conds
        elif (isinstance(conds, BoolRef)):
            if (self.variables):
                self.solver.add(Exists(self.variables, conds))
            else:
                self.solver.add(conds)
            return self.solver.check().__eq__(unsat)
        else:  ### list of length >= 2
            if (self.variables):
                self.solver.add(Exists(self.variables, And(*conds)))
            else:
                self.solver.add(And(*conds))
            return self.solver.check().__eq__(unsat)
    # --- end is_obvious  

    # --------------------
    # TODO new test for problem
    def is_strange(self, conds):
        #print ("is strange" + str(conds))
        self.solver.reset()
        # True/False cases
        if (isinstance(conds, bool)):
            return not conds
        elif (isinstance(conds, BoolRef)):
            if (self.variables):
                self.solver.add(ForAll(self.variables, conds))
            else:
                self.solver.add(conds)
        else:  ### list of length >= 2
            if (self.variables):
                self.solver.add(ForAll(self.variables, And(*conds)))
            else:
                self.solver.add(And(*conds))
        #print (" ? " + str(self.solver.check().__eq__(unsat)))
        return self.solver.check().__eq__(unsat)
    # --- end is_strange
    
    # --------------------
    # test tautology 
    # with free variables
    # REQUIRE: better if test is_obvious before
    # and return True if unsat else False if sat or unknown
    def is_tautology(self, conds, concs):
        # manage concs
        if (isinstance(concs, bool) or isinstance(concs, BoolRef)):
            conc = concs
        else: 
            conc = And(*concs)
        self.solver.reset()
        # bool case conds should be True 
        if (isinstance(conds, bool)):
            if (isinstance(conc, bool)):
                self.solver.add(Not(conc))
            else: 
                if (self.variables):
                    self.solver.add(Exists(self.variables, Not(conc)))
                else:
                    self.solver.add(Not(conc))
            return self.solver.check().__eq__(unsat)
        elif (isinstance(conds, BoolRef)):
            if (self.variables):
                self.solver.add(Exists(self.variables, And(conds, Not(conc))))
            else:
                self.solver.add(And(conds, Not(conc)))
            return self.solver.check().__eq__(unsat)
        else: # it is a list with two
            cond = And(*conds)
            #print ("is tauto " + str(Exists(self.variables, And(cond, Not(conc)))))
            if (self.variables):
                self.solver.add(Exists(self.variables, And(cond, Not(conc))))
            else:
                self.solver.add( And(cond, Not(conc)))
            return self.solver.check().__eq__(unsat)
        # --- end if conds
    # --- end is_tautology     
    
    # --------------------
    # test unsafeness with free variables
    # REQUIRE: better if is_obvious done before only conds=True is possible
    # concs could be True/False 
    # and return True if unsat else False if sat or unknown
    # TODO if not obvious ?
    def is_unsafe(self, conds, concs):
        # shortcut for unsafe
        if (concs == False):
            return True
        # manage concs
        if (isinstance(concs, bool) or isinstance(concs, BoolRef)):
            conc = concs
        else: 
            conc = And(*concs)
        # other cases
        self.solver.reset()
        # bool  case conds should be True
        if (isinstance(conds, bool)):
            if (isinstance(conc, bool)):
                self.solver.add(conc)
            else: 
                if (self.variables):
                    self.solver.add(ForAll(self.variables, conc))
                else:
                    self.solver.add(conc)
            return self.solver.check().__eq__(unsat)
        elif (isinstance(conds, BoolRef)):
            if (self.variables):
                # brute formula
                self.solver.add(ForAll(self.variables, Implies(conds, conc)))
                self.solver.add(Exists(self.variables, conds))
            else:
                self.solver.add(And(conds, conc))
            return self.solver.check().__eq__(unsat)
        else: # it is a list with two
            cond = And(*conds)
            if (self.variables):
                self.solver.add(ForAll(self.variables, Implies(cond, conc)))
                self.solver.add(Exists(self.variables, cond))
            else:
                self.solver.add(And(cond, conc))
            return self.solver.check().__eq__(unsat)
    # --- end is_unsafe   
    
    
    
    # ----------------------
    # check if exp is undefined for the rule system
    # apply req !* R from definition
    # req should have explicit quantifiers
    def check_undefined(self, req, end):
        self.solver.reset()
        if (self.variables):
            #print("toboolref " + str(self.toBoolRef(end)))
            self.solver.add(ForAll(self.variables, self.toBoolRef(end)))
            self.solver.add(req)
        else:
            self.solver.add(And(self.toBoolRef(end), req))
        #print ("Check_undefined: " + str(exp) + " is " + str(self.solver.check()))
        return self.solver.check()
    # --- end check_undefined
# --- end Enumerative