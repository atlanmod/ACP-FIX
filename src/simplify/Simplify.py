# -------------------
# 21/8/2018
# with rule simplification
# -------------------
# use exp.hash() -> key and dico[key] -> exp
# and also a relation and its inverse between propositional variables and keys
# but collect and store all propositions and their negations in separate dico
# with a link from the positive to the negative one
# new version with binary ({1, 0, -1),*) list for and terms 
# simplification of sum in case of inclusions
# analyze two levels because of sum of terms and their negation
# coming from iteration of simplification
# process product using binary list which is simpler
# factorization using Prime.py
# --------------------

# TODO simplify_fix

# TODO build_prop => build_list_lbinary removing IREP ???
# and clarify analysis from collect_store

# TODO self.radixNot ...

from z3 import *  # @UnusedWildImport
from Improve import *  #@UnusedWildImport
from Prime import *  #@UnusedWildImport

# --------------------------
# Class for rule simplification
class Simplify(Improve):
    
    # --------------------
    # init constructor with sys: <= Iterative
    def __init__(self):
        super().__init__()
        #  dico for positive subexpressions indexed by hashkey
        self.memo = dict() 
        #  dico for negative subexpressions 
        self.memo_not = dict()
        # relations between positive key and the negative one
        self.pos2neg = dict()
        self.neg2pos = dict()
        # temp to compute conc equal
        self.equal = dict()
    # --- end init
    
    # ---------------
    def __str__(self):
        result = super().__str__()
        return result + "\n Simplify: \n" + str(self.memo) + "\n" + str(self.memo_not) + "\n" + str(self.pos2neg)  + "\n" + str(self.neg2pos)
    # --- end str
    
    # --------------------
    # number of propositions
    def propositions(self):
        return self.memo.__len__()    
    # --- end of propositions
    
    # --------------------
    # store both positive and negative formulas
    # and update the links between the keys
    def add_in_dicos(self, exp, key):
        if ((not key in self.memo) or (not key in self.memo_not)):
            if (is_app(exp) and (exp.decl().kind() == Z3_OP_NOT)):
                self.memo_not[key] = exp
                exp1 = exp.children()[0]
                key1 = exp1.hash()
                self.memo[key1] = exp1
                self.pos2neg[key1] = key
                self.neg2pos[key] = key1
            else:
                self.memo[key] = exp
                exp1 = Not(exp)
                key1 = exp1.hash()
                self.memo_not[key1] = exp1
                self.pos2neg[key] = key1
                self.neg2pos[key1] = key
            # --- end if is_app
    # --- end add_in_dicos

    # ----------------
    # get Z3exp from a key
    def get(self, key):
        if (key in self.memo):
            return self.memo[key]
        else:
            return self.memo_not[key]
        # --- end if key in
    # --- end get
    
    # ----------------
    # get opposite key from a key
    def get_not(self, key):
        if (key in self.pos2neg):
            return self.pos2neg[key]
        else:
            return self.neg2pos[key]
        # --- end if key in
    # --- end get_not
    
    # ----------------
    # are opposite keys
    def are_opposite(self, key1, key2):
        if (key1 in self.pos2neg):
            return (self.pos2neg[key1] == key2) 
        else:
            return (self.neg2pos[key1] == key2)
    # --- end are_opposite

    # ---------------
    # traverse a Z3 BoolRef but only the toplevel
    # should go deeper and analyze Or(And(PROP)) and negation
    # store the hashkey -> subexpression
    # store PROP formulae and their negation
    def collect_store(self, Z3exp):
        if (is_app(Z3exp)):
            op = Z3exp.decl().kind()
            # check kinds of root 
            if  (op == Z3_OP_NOT):
                # if only collect no need to propagate
                son = Z3exp.children()[0]
                if (is_app(son)):
                    ops = son.decl().kind()
                    # comes from simplifications
                    if (ops == Z3_OP_OR):
                        # only analyze inner and
                        for sub in son.children():
                            if (is_app(sub)):
                                if (sub.decl().kind() == Z3_OP_AND):
                                    for inner in sub.children():
                                        self.add_in_dicos(inner, inner.hash())
                                else:
                                    self.add_in_dicos(sub, sub.hash())
                            else:
                                self.add_in_dicos(sub, sub.hash())
                    else:
                        self.add_in_dicos(Z3exp, Z3exp.hash())
                else:
                    self.add_in_dicos(Z3exp, Z3exp.hash())
            elif (op == Z3_OP_AND):
                # should be sequence of prop or not prop
                for exp in Z3exp.children():
                    self.add_in_dicos(exp, exp.hash())
                # --- end for exp
            elif (op == Z3_OP_OR):
                # should be sequence of PROP/NOT AND(PROP)
                for exp in Z3exp.children():
                    # analyze AND case
                    if (is_app(exp) and (exp.decl().kind() == Z3_OP_AND)):
                        for sub in exp.children():
                            self.add_in_dicos(sub, sub.hash())
                        # --- end for exp
                    else:
                        self.add_in_dicos(exp, exp.hash())
                # --- end for exp
            else:
                self.add_in_dicos(Z3exp, Z3exp.hash()) #PROP
        elif (is_expr(Z3exp)):
            # quantifier case
            self.add_in_dicos(Z3exp, Z3exp.hash()) #PROP
        else:
            # store True/False (useless ?)
            if (isinstance(Z3exp, bool)):
                self.add_in_dicos(Z3exp, hash(Z3exp))  #PROP
            else:
                # should be a problem 
                print ("Simplify0.collect_store: case not covered: " + str(Z3exp))
    # --- end collect_store
    
    # ---------------
    # traverse a Z3 BoolRef but only the two levels
    # store the hashkey -> subexpression
    # store PROP formulae and their negation
    # and built an element of IREP with list
    # IREP1 ::= key | {Z3_OP_AND + Z3_OP_OR} key* 
    # IREP2 ::= {Z3_OP_AND + Z3_OP_OR} IREP1
    def build_prop(self, Z3exp):
        if (is_expr(Z3exp)):
            key = Z3exp.hash()
        elif (isinstance(Z3exp, bool)):
            key = hash(Z3exp)
        else: 
            print ("Simplify.build_prop : case not covered: " + str(Z3exp))
        if (key in self.memo or key in self.memo_not):
                return key
        elif (is_app(Z3exp)):
            op = Z3exp.decl().kind()
            # TODO eliminate NOT NOT ?
            if  (op == Z3_OP_NOT):
                # if only collect no need to propagate
                son = Z3exp.children()[0]
                if (is_app(son)):
                    ops = son.decl().kind()
                    # comes from simplifications
                    if (ops == Z3_OP_OR):
                        resand = [Z3_OP_AND] 
                        # only analyze inner and
                        for sub in son.children():
                            if (is_app(sub)):
                                if (sub.decl().kind() == Z3_OP_AND):
                                    resor = [Z3_OP_OR] 
                                    for inner in sub.children():
                                        resor.append(self.get_not(inner.hash()))
                                    # --- for inner
                                    resand.append(resor)
                                else:
                                    # TODO do not consider NOT(NOT())
                                    resand.append(self.get_not(sub.hash()))
                            else:
                                resand.append(self.get_not(sub.hash()))
                        # --- end for
                        return resand
                    elif (ops == Z3_OP_AND):
                        # TODO should also build this one from combination
                        resor = [Z3_OP_OR] 
                        for sub in son.children():
                            resor.append(self.get_not(sub.hash()))
                        # --- for inner
                        return resor
                    elif (ops == Z3_OP_NOT):
                        return son.children()[0].hash()
                    else:
                        return key
                else:
                    return key
            elif (op == Z3_OP_AND):
                # should be sequence of prop or not prop
                resand = [Z3_OP_AND] 
                for exp in Z3exp.children():
                    resand.append(exp.hash())
                # --- end for exp
                return resand
            elif (op == Z3_OP_OR):
                # should be sequence of PROP/NOT AND(PROP)
                resor = [Z3_OP_OR] 
                for exp in Z3exp.children():
                    # analyze AND case
                    if (is_app(exp) and (exp.decl().kind() == Z3_OP_AND)):
                        resand = [Z3_OP_AND]
                        for sub in exp.children():
                            resand.append(sub.hash())
                        # --- end for exp
                        resor.append(resand)
                    else:
                        resor.append(exp.hash())
                # --- end for exp
                return resor
            else:
                return key
        elif (is_expr(Z3exp)):
            # quantifier case
            return key
        else:
            # store True/False (useless ?)
            if (isinstance(Z3exp, bool)):
                return key
            else:
                # should be a problem 
                print ("Simplify.build_prop: case not covered: " + str(Z3exp))
                return None
    # --- end build_prop

    # --------------------------
    # rebuild a Z3exp from exprop : element of IREP
    # should look at two levels 
    # return a Z3exp
    def rebuild_z3(self, exprop):
        if (isinstance(exprop, list)):
            op = exprop[0]
            if (op == Z3_OP_AND):
                result = []
                for sub in exprop[1:]:
                    if (isinstance(sub, list)): # should be a OR
                        result.append(Or(*[self.get(k) for k in sub[1:]]))
                    else:
                        result.append(self.get(sub))
                # --- end for
                return And(*result)
            elif (op == Z3_OP_OR):
                result = []
                for sub in exprop[1:]: 
                    if (isinstance(sub, list)): # should be a AND
                        result.append(And(*[self.get(k) for k in sub[1:]]))
                    else:
                        result.append(self.get(sub))
                # --- end for
                return Or(*result)
            # --- end if
        else:
            return self.get(exprop)
    # --- end rebuild_z3
    
    # --------------------------
    # analyze the contents of a rule system
    # must done before product
    def analyze(self):
        for r in self.rules:
            self.collect_store(r.get_cond())
            self.collect_store(r.get_conc())
    # --- end analyze
    
    # --------------------------
    # Compute a product of And-terms in condition
    # the rule is Enumerative 
    # return a sum of and terms
    def compute_product(self, rule):
        lcond = Rule.get_cond(rule)
        # compute product
        if (is_expr(lcond) or isinstance(lcond, bool)):
            #print ("prop " + str(self.build_prop(lcond)))
            tosimplify = [self.build_prop(lcond)]
        else:
            tosimplify = [] 
            for exp in lcond:
                prop = self.build_prop(exp)
                tosimplify.append(prop)
            # ---
        #print ("tosimplify " + str(tosimplify))
        prod = self.process_lbinary(tosimplify)
        #print ("Compute product for " + str(rule.get_binary()) + " -> " + str(prod))
        return prod
    # --- and simplify_sum       
    
    # --------------------------
    # rebuild and simplify one exclusive rule expression
    # cond/conc is True | False | BoolRef | [BoolRef BoolRef+]
    # return the simplified Z3exp version
    def simplify_exp(self, lcond):
        #print ("here " + str(lcond) )
        if (is_expr(lcond) or isinstance(lcond, bool)):
            return lcond
        else:
            # Should be of length 2 or greater
            # first build the propositional version and reduce NOT ahead
            tosimplify = []
            for exp in lcond:
                prop = self.build_prop(exp)
                #print ("simpl exp " + str(prop)) 
                tosimplify.append(prop)
            # --- end for exp
            # rebuild a Z3exp
            #print ("simpl-exp " + str(tosimplify)) # + str(self.show(tosimplify)))
            prod = self.process_lbinary(tosimplify)
            if prod:
                return self.z3(prod)
            else:
                return False 
    # --- end simplify_exp
    
    # --------------------------
    # compute the table and simplify the rules iteratively
    def compute_simplify(self, end):
        self.analyze()
        self.compute_table(end)
        self.check(end)
    # --- end compute_simplify
    
    # --------------------------
    # compute the table and simplify the rules globally
    def compute_simplify2(self, end):
        # should be done here to catch the right propositions
        self.analyze()
        # transfert rules to table
        table = Improve()
        table.rules = self.rules
        table.variables = self.variables
        table.compute_table(end)
        #table.check(end)
        # global simplify 
        for r in table.safe:
            lcond = Rule.get_cond(r)
            if is_expr(lcond):
                lcond = [lcond]
            scond = self.simplify_exp(lcond)
            #print ("check condition: " + str(self.check_exp(And(*lcond), scond)))
            lconc = Rule.get_conc(r)
            if is_expr(lconc):
                lconc = [lconc]
            sconc = self.simplify_exp(lconc)
            self.safe.append(Rule(scond, sconc))
        for r in table.unsafe:
            lcond = Rule.get_cond(r)
            if is_expr(lcond):
                lcond = [lcond]
            scond = self.simplify_exp(lcond)
            #print ("check condition: " + str(self.check_exp(And(*lcond), scond)))
            self.unsafe.append(Rule(scond, False))            
        self.check(end)
        #print (str(self))
    # --- end compute_simplify2

#     # -------------------
#     # build the rules, store unsafe and remove tautology
#     # store new rule triple in tempaux
#     # needs binary to store characteristic and tautology indicator
#     # remove obvious only, classify unsafe
#     # cope with the new radix information
#     # TODO simplification are really slow !!!
#     def build(self, conds, concs, binary):
#         # self.built += 1
#         #print ("build for " + str(binary) + " : " + str(conds) + " " + str(concs) )
#         print ("build for " + str(binary))
#         # radix only for storing or final result
#         # TODO pb boolref
#         if (isinstance(conds, list)):
#             condsaux = self.radixNot + conds
#         else:
#             condsaux = self.radixNot + [conds]
#         binaryaux = self.radixBinary + binary
#         # simplifications
#         scond = self.simplify_exp(condsaux)
#         sconc = self.simplify_exp(concs)
#         if (not self.is_obvious(scond)):
#             if (self.is_unsafe(scond, sconc)):
#                 # print ("build unsafe " + str(binary) + " : " + str(conds) + " " + str(concs) )
#                 self.unsafe.append(Unsafe(binaryaux, scond))
#             else:
#                 # print ("build safe " + str(binary) + " : " + str(conds) + " " + str(concs) )
#                 # should be binary here
#                 self.tempaux.append((binary, scond, sconc))
#         # -- end if obvious
#     # -- end of build
         
    #================================utility for displaying Z3exp
    # ---------------------
    # show the Z3exp as a sum of and terms
    # REQUIRE a sum of and key terms
    #  [-1*] is True
    def show(self, sumand):
        # expecting ordering is stable
        pos = list(self.memo.keys())
        neg = list(self.memo_not.keys())
        result = []
        for binary in sumand:
            aux = []
            for i in range(self.propositions()):
                if (binary[i] == 1):
                    aux.append(self.get(pos[i]))
                elif (binary[i] == 0):
                    aux.append(self.get(neg[i]))
            # --- end for i
            if aux:
                result.append(And(*aux) if (len(aux) > 1) else aux[0])
            else:
                result.append(True) 
        # --- end for binary
        return result
    # --- end show
    
    # ---------------------
    # create the Z3exp from a sum of an key terms 
    def z3(self, sumand):
        result = self.show(sumand)
        if (len(result) == 0):
            return False
        elif (len(result)==1):
            return result[0]
        else:
            return Or(*result)
    # --- end z3
    
    # ====================== 
    # new version of product based on binary lists computation
    # ---------------------
    # create a binary list [{1,0,-1},*)]
    # from a IREP1 elem : key | [AND key*]  
    def make_lbinary(self, elem):
        #manage case single key
        if not isinstance(elem, list):
            elem = [elem]
        else:
            elem = elem[1:]
        binary = [-1,] * self.propositions()
        # expecting ordering is stable
        pos = list(self.memo.keys())
        neg = list(self.memo_not.keys())
        for key in elem:
            if (key in self.memo):
                binary[pos.index(key)] = 1
            else:
                binary[neg.index(key)] = 0
        # --- end for
        return binary
    # --- end make_tuple    
    
    # ----------------------
    # logical AND of two  binary lists
    # should check the False
    def and_lbinary(self, tuple1, tuple2):
        #print("and_lbinary " + str(tuple2))
        if (tuple1 == []):
            return tuple2
        elif (tuple2 == []):
            return tuple1
        else:
            result = []
            for i in range(self.propositions()):
                if (tuple1[i] == -1):
                    result.append(tuple2[i])
                elif (tuple2[i] == -1):
                    result.append(tuple1[i])
                elif (tuple1[i] == tuple2[i]):
                    result.append(tuple1[i])
                else:
                    # failure 
                    return []
            return result
    # --- end and

    # ----------------------
    # compute product of factor with each lbinary in llbinary
    # return a llbinary or [] for False
    # TODO if result = [] after one step should stop
    def distribute_and(self, factor, llbinary):
        if llbinary:
            result = []
            for prod in llbinary:
                #print (" self.and_lbinary(prod, factor) " + str(self.and_lbinary(prod, factor)))
                tmp = self.and_lbinary(prod, factor)
                if tmp:
                    result.append(tmp)
            return result
        else:
            ### TODO PB here factor is and AND but could be false !
            return [factor]
    # --- end distribute_and
    
    # ------------------------
    # flatten an IREP into a sum of and terms
    # TODO pb with PY&~PY if sumprod = []false ?
    # TODO add a test sumprod=[] and modify distribute ?
    def flatten(self, irep):
        if (isinstance(irep, list)):
            # aux empty implies fail
            if (irep[0] == Z3_OP_AND):
                sumprod = [] # will be a list of lbinary
                #print ("irep[1:] " + str(irep[1:]))
                # should check case OR 
                for son in irep[1:]:
                    #print (" son" + str(son))
                    if (isinstance(son, list)):
                        if (son[0] == Z3_OP_OR):
                            temp = []
                            for fils in son[1:]:
                                lbinfils = self.make_lbinary(fils)
                                temp.extend(self.distribute_and(lbinfils, sumprod))
                            # --- for fils
                            sumprod = temp
                        else:
                            lbinson = self.make_lbinary(son)
                            sumprod = self.distribute_and(lbinson, sumprod)
                    else: 
                        #print (" make_lbinary " + str(self.make_lbinary(son)) + str(sumprod))
                        lbinson = self.make_lbinary(son)
                        ### TODO JCR if result = []
                        if (sumprod):
                            sumprod = self.distribute_and(lbinson, sumprod)
                        else:
                            sumprod = [lbinson]
                    # --- end if isinstance(son, )
                # --- for son
                return sumprod
            else: # it is an OR
                # no need to simplify since comes from our assumptions TODO?
                return [self.make_lbinary(x) for x in irep[1:]]
        else:
            return[self.make_lbinary(irep)]
        # --- end if irep 
    # --- end flatten
    
    # ----------------------
    # process an IREP and compute the simplified product (distribute the product)
    # the result is a list  representing a sum of and terms
    # that is a list of binary lists ([{1,0,-1},*)])
    # return a sum of and terms as lbinary
    def process_lbinary(self, lprop):
        i = 0
        result = [] # temporary storage of the list of sumprod
        fail = False
        while (i <len(lprop)) and not fail:
            aux = self.flatten(lprop[i])
            #print ("aux flatten " + str(aux) + str(self.show(aux)))
            # product of two sum of terms
            product = []
            for factor in aux:
                # product of left and each in result
                product.extend(self.distribute_and(factor, result))
            # --- end for aux
            #print ("product result= " + str(product) + str(self.show(product)))
            result = prime(product)
            if not result:
                fail = True
            i += 1
        # --- end while lprop
        return prime(result)
    # --- end process_lbinary
    
    # ============================= methods for gluing rules
    
    #------------------------
    # TODO after an analyze and compute_table and same for others
    # merge safe rules which are included in the same conclusion
    # this is a global final simplification for safe reversing the enumerative formula
    # basic version which produces number_rule - #explicit unsafe
    # take care of same conclusion using .equal information
    # discard tautologies
    # TODO build a new rule with OR conditions
    # TODO mask computetable
    def glue_safe_simplify(self, end):
        # should be done here to catch the right propositions
        self.analyze()
        # transfer rules to table
        table = Improve()
        table.rules = self.rules
        table.variables = self.variables
        table.compute_table(end)
        print(str(table))
        table.check(end)
        print ("rules= " + str(len(table.correct)) + " safe= " + str(len(table.safe)) 
               + " unsafe= " + str(len(table.unsafe)) + " built= " + str(table.built) + " nodes= " + str(table.count_nodes()))
        # process conclusions of the original system
        conclusions = [i for i in range(len(table.sorted))]
        #print ("conclusions " + str(conclusions))
        while conclusions:
            # indice of a rule conclusion to consider
            i = conclusions.pop(0) 
            active = False
            # other same conclusions to consider
            tolook = [i]
            if (i in table.same_conclusion):
                tolook.extend(table.same_conclusion[i])
                # forget other equals
                for k in table.same_conclusion[i]:
                    conclusions.remove(k)
            #print ("i= " + str(i) + " " + str(tolook))
            # process the not unsafe and active rules for i
            activerules = []
            for rs in table.safe:
                for j in tolook:
                    if (rs.get_binary()[j] == 1):
                        active = True
                        activerules.append(rs)
            # --- for rs in safe
            #print ("i= " + str(i) + " actives= " + str(activerules))
            # compute sum of product terms in the active rules conditions
            sumprod = []
            for rs in activerules:
                prod = self.compute_product(rs)
                #print ("active rule " + str(rs) + " prod = " + str(prod))
                sumprod.extend(prod)
            # --- end for rs
            newcond = prime(sumprod)
            #print ("sumprod " + str(sumprod) + " -> " + str(newcond))
            scond =  False  
            conc = table.sorted[i].get_conc()
            # build the rule expression 
            if newcond:
                scond = self.z3(newcond) 
                # simplify tautology
                self.solver.reset()
                self.solver.add(Exists(self.variables, And(scond, Not(conc))))
                if (not self.solver.check().__eq__(unsat)):
                    print ("Safe simplified= " + str(scond) + "=> " + str(conc))
                    self.safe.append(Rule(scond, conc))
        # --- end while conclusions
        # check equiv with the safe parts
        self.solver.reset()
        safe = table.z3_safe()
        if (not isinstance(safe, bool)):
            safe = ForAll(self.variables, safe)
        simplified = self.z3_safe()
        if (not isinstance(simplified, bool)):
            simplified = ForAll(self.variables, simplified)
        #print ("table.safe= " + str(safe))
        #print ("self.safe= " + str(simplified))
        self.solver.add(safe)
        self.solver.add(Not(simplified))
        print (" => " + str(self.solver.check()))  
        self.solver.reset()
        self.solver.add(simplified)
        self.solver.add(Not(safe))
        print (" <= " + str(self.solver.check()))         
    # --- end of glue_safe_simplify
    
    #------------------------
    # merge all unsafe conditions and simplify
    # this is a global final simplification
    # after table and need analyze
    # TODO and show simplified unsafe conditions
    # TODO improve the rule management 
    # TODO table management ?
    def glue_unsafe_simplify(self, end):
        # should be done here to catch the right propositions
        self.analyze()
        # transfer rules to table
        table = Improve()
        table.rules = self.rules
        table.variables = self.variables
        table.compute_table(end)
        self.unsafe = table.unsafe
        self.sorted = table.sorted
        self.radixNot = table.radixNot
        self.radixBinary = table.radixBinary 
        print(str(table))
        table.check(end)
        print ("rules= " + str(len(table.correct)) + " safe= " + str(len(table.safe)) 
               + " unsafe= " + str(len(table.unsafe))) # + " built= " + str(table.built) + " nodes= " + str(table.count_nodes()))
        # sum of prod
        sumprod = []
        # process simplification of unsafe rules
        for r in table.unsafe:
            prod = self.compute_product(r)
            print ("Simplified condition for " + str(r.get_binary()) + " -> " + str(self.show(prime(prod))))
            sumprod.extend(prod)
        # --- end for r unsafe
        # use the prime implicants computation from Prime.py
        #print ("sumprod= " + str(sumprod))
        #print (" with Prime " + str(prime(sumprod)))
        result = prime(sumprod)
        # build the z3 expression for unsafe simplified
        if result:
            print ("Unsafe simplified= " + str(len(result)) + " conflict problems \n" + str(self.z3(result)))
        else:
            print ("Unsafe simplified= " + str(False)) 
    # --- end of glue_unsafe_simplify
    
    # -----------------------
    # simplify the not unsafe rules
    # TODO improve with conclusions 
    # TODO table computation ?
    def simplify_notunsafe(self, end):
        # should be done here to catch the right propositions
        self.analyze()
        # transfer rules to table
        table = Improve()
        table.rules = self.rules
        table.variables = self.variables
        table.compute_table(end)
        self.unsafe = table.unsafe
        self.sorted = table.sorted
        self.radixNot = table.radixNot
        self.radixBinary = table.radixBinary 
        # process simplification of safe rules
        for r in table.safe:
            prod = self.compute_product(r)
            print ("Simplified condition for " + str(r.get_binary()) + " -> " + str(self.show(prime(prod))))
        # --- end for r safe    
    # --- end simplify_notunsafe
    
    # -------------------------
    # simplify the not unsafe problems
    # TODO change the table management 
    def simplify_notunsafe_problems(self, end):
        # should be done here to catch the right propositions
        self.analyze()
        self.compute_table(end)
        # sum of prod
        sumprod = []
        # process computation of 1-undefined
        for r in self.safe:
            lcond = Rule.get_cond(r)
            lconc = Rule.get_conc(r)
            #print (str(lconc) + " SUM= " + str(self.not_conclusion(lconc)))
            # compute product of lcond
            if (is_expr(lcond) or isinstance(lcond, bool)):
                tosimplify = [self.build_prop(lcond)]
            else:
                tosimplify = [] 
                for exp in lcond:
                    prop = self.build_prop(exp)
                    tosimplify.append(prop)
            # --- end if
            # and Not(lconc)
            tosimplify.append(self.not_conclusion(lconc))
            prod = self.process_lbinary(tosimplify)
            sumprod.extend(prod)
            #print (str(tosimplify) + " prod " + str(prod) + " " + str(self.show(prod)))
        # --- for safe
        print ("sumprod " + str(len(sumprod)))
        result = prime(sumprod)
        # build the z3 problems
        if result:
            print ("All not unsafe simplified= " + str(len(result)) + " problems \n")
            res = Or(*[self.z3([x]) for x in result])
            print (str(res))
            return res
        else:
            print ("All simplified= NO")
            return False
    # ---- end simplify_notunsafe_problems
    
    #------------------------
    # compute all problems (1_undefined + unsafe) and simplify
    # return the Z3 simplified expression
    # TODO use simplify_sum
    # TODO add test inclusion for problems
    def get_all_problems(self, end):
        # should be done here to catch the right propositions
        self.analyze()
        self.compute_table(end)
        # sum of prod
        sumprod = []
        # process computation of 1-undefined
        for r in self.safe:
            lcond = Rule.get_cond(r)
            lconc = Rule.get_conc(r)
            #print (str(lconc) + " SUM= " + str(self.not_conclusion(lconc)))
            # compute product of lcond
            if (is_expr(lcond) or isinstance(lcond, bool)):
                tosimplify = [self.build_prop(lcond)]
            else:
                tosimplify = [] 
                for exp in lcond:
                    prop = self.build_prop(exp)
                    tosimplify.append(prop)
            # --- end if
            # and Not(lconc)
            tosimplify.append(self.not_conclusion(lconc))
            prod = self.process_lbinary(tosimplify)
            sumprod.extend(prod)
            #print (str(tosimplify) + " prod " + str(prod) + " " + str(self.show(prod)))
        # --- for safe
        # process simplification of unsafe rules
        for r in self.unsafe:
            prod = self.compute_product(r)
            sumprod.extend(prod)
        # --- end for r unsafe
        # use the prime implicants computation from Prime.py
        print ("sumprod= " + str(len(sumprod)))
        result = prime(sumprod)
        # build the z3 problems
        if result:
            print ("All simplified= " + str(len(result)) + " conflict problems \n")
            return Or(*[self.z3([x]) for x in result])
        else:
            print ("All simplified= NO")
            return False
    # --- end of get_all_problems
    
    # --------------------
    # process the negation of a conclusion
    # lconc is Z3exp or list and of Z3exp
    # return an IREP OR (!!! [OR one] possible)
    def not_conclusion(self, lconc):
        result = [Z3_OP_OR] 
        if (is_expr(lconc)):
            new = self.build_prop(Not(lconc))
            if (isinstance(new, list) and new[0] == Z3_OP_OR):
                result.extend(new[1:])
            else:
                result.append(new)
        else:
            for exp in lconc:
                new = self.build_prop(Not(exp))
                if (isinstance(new, list) and new[0] == Z3_OP_OR):
                    result.extend(new[1:])
                else:
                    result.append(new)
        return result
    # ---- end of not_conclusion
    
    # ---------------------------
    # D is an original  condition but Or And terms works
    # U is a problem as a sum of Andterms (simplified Z3exp)
    # should compute and simplify D&~U
    # return the z3 simplified sum of and terms
    def simplify_fix(self, D, U):
        #print ("Simplify.simplify_fix " + str(D) + " " + str(U))
        # should inner NOT compute OR IREP 
        listNotU = [] # a list of OR IREP
        if (U.decl().kind() == Z3_OP_OR):
            # should be an OR
            lexp = U.children()
        else: # it is AND ?
            lexp = [U]
        for exp in lexp:
            result = [Z3_OP_OR] 
            new = self.build_prop(Not(exp))
            if (isinstance(new, list) and new[0] == Z3_OP_OR):
                result.extend(new[1:])
            else:
                result.append(new)
            listNotU.append(result) # contains list of OR IREP representing a AND
        # --- end for exp    
        #print ("list not U " + str(listNotU))
        prod = self.process_lbinary(listNotU+[self.build_prop(D)])
        #print ("prod " + str(prod) + "show " + str(self.show(prod)))
        simplif = prime(prod) 
        #print ("show " + str(self.show(simplif)))
        return self.z3(simplif)
    # --- end simplify_fix
    
    # ---------------------------
    # variant of the previous
    # Where U is a list of enumerative unsafe conditions
    # D is an original  condition but Or And terms works
    # return the z3 simplified sum of And terms
    # TODO optimize/shortcut ?
    def simplify_fix2(self, D, listofunsafe):
        sumprod = []
        for i in listofunsafe:
            sumprod.extend(self.compute_product(self.unsafe[i]))
        simpleU = self.z3(prime(sumprod))
        return self.simplify_fix(D, simpleU)
    # --- end simplify_fix2
# --- end simplify