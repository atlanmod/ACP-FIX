# -------------------
# 30/12/2018
# Subclass for informations about analysis and fixing
### -------------

from Improve import * #@UnusedWildImport

# --------------------------
# Class for rule simplification
class Removing(Improve):
    
    # --------------------
    # init constructor with sys: <= Iterative
    def __init__(self):
        super().__init__()
        # counter for new variables
        self.COUNTER_VARS = 0
        self.ROOT_VARS = "U_"
    # --- end init
    
    # ---------------
    def __str__(self):
        result = super().__str__()
        return result 
    # --- end str

    # ---------------------
    # compute the reverse correspondance from sorting
    # to original ordering of the rules
    # after analyze+compute_table
    # TODO tautology not correct ?
    # TODO optimization by caching inverse, shift
    def full_mapping(self, size):
        # ordering inverse
        inverse = {}
        for key in self.ordering:
            inverse[self.ordering[key]] = key
        offset = len(self.explicit)   
        # define shifting encoding explicit unsafe
        shift = list(range(size))
        for eu in self.explicit:
            shift.remove(eu)
        # converts to original rule numbering 
        numbers = []
        for i in range(size):
            if (i < offset):
                numbers.append(self.explicit[i])
            else:
                knew = inverse[i-offset]  
                numbers.append(shift[knew])
        #print("numbers= " + str(numbers))
        return numbers
    # --- end full_mapping
    
    # ---------------------------
    # fixing conclusion with +U
    # U with explicit quantifiers
    def fix_conclusion(self, U, F, end):
        # define a new rules system
        newR = Improve()
        newR.variables = self.variables
        for i in range(end): 
            oldr = self.rules[i]
            if (i in F):
                newR.add_rule(oldr.get_cond(), Or(oldr.get_conc(), U))
            else:
                # format compatible with Improve()
                newR.add_rule(oldr.get_cond(), oldr.get_conc())
        # --- for i
        return newR
    # --- end of fix_conclusion
 
    # --------------------
    # naive lookup for a minimal solution
    # bottom up enumeration of rule combinations 
    # test all combination on R_~F
    # TODO see assignV4 ?
    def naive(self, U, size):
        #print(" ---------- naive -------------")
        #  maximal selection
        selection = range(size)
        # optimized selection with negatives
        #selection = [i for i in range(size) if i not in negatives]
        sizeS = len(selection)  #size
        found = False # additional condition
        sizeL = 1
        # each time 
        while (sizeL <= sizeS) and not found:
            #print ("sizeL " + str(sizeL) + " ------")
            # counters initialized
            K =  [i for i in range(sizeL)]
            #increment counter one by one but in reverse order
            k = sizeL-1
            while (k >= 0) and not found:
                #print ("combination " + str(K))
                # test the current selection 
                test = [selection[j] for j in K]
                notest = [selection[j] for j in range(sizeS) if j not in K]
                #compute R_~F
                notfixed = [self.rules[i].toBoolRef() for i in notest]
                # check satisfiability against U
                self.solver.reset()
                self.solver.add(U)
                if (self.variables):
                    # only R_~F
                    self.solver.add(ForAll(self.variables, And(*notfixed)))
                else:
                    self.solver.add(*notfixed)
                found = self.solver.check().__eq__(sat) 
                # increment the k counter and check limit 
                if (K[k] < sizeS-sizeL+k):
                    K[k] += 1
                else: # go back and next 
                    # go back until limit reached
                    while (k >= 0) and (K[k] >= sizeS-sizeL+k):
                        k += -1 
                    # if possible reinit counters and k to end
                    if (k >= 0):
                        K[k] += 1
                        for j in range(k+1, sizeL):
                            K[j] = K[j-1]+1 
                        k = sizeL-1 
                    # to stop since finished
                    else:
                        k = -1
                # --- end if K
            # --- end while k
            sizeL += 1
        # --- end while sizeL
        return test
    # --- end naive

    # -----------
    # give a mean size*time for 10 runs
    # for both lookup and naive ways 
    def compare(self, U, Ubinary, size, number):
        # mapping completed to simplify
        numbers = self.full_mapping(size) #PB with testAdi ?
        negatives = [numbers[i] for i in range(len(Ubinary)) if (Ubinary[i] == 0)]  
        positives = [numbers[i] for i in range(len(Ubinary)) if (Ubinary[i] == 1)]  
        #howmany = len([i for i in range(len(Ubinary)) if (Ubinary[i] != -1)])
        maxrun = 10
        # naive algorithm
        start = clock()
        for k in range(maxrun):
            Fnaive = self.naive(U, negatives, size)
        # --- end naive
        naivetime = (clock() - start) / maxrun
        # for lookup 
        start = clock()
        #start = process_time()
        for k in range(maxrun):
            #Fmin = self.lookup_complex(U, Ubinary, size)
            Fmin = self.lookup_unsafe(U, Ubinary, size)
        # --- end naive
        meantime = (clock() - start) / maxrun
        # Compare BOTH
        print (str(number) + " ; " + str(len([i for i in Ubinary if i == 1])) + " ; " + str(Fnaive) + " ; " + str(naivetime) + " ; " + str(Fmin) + " ; " + str(meantime) + " ; " 
               + str(len(Fnaive)) + " ; " + str(len(Fmin))  + " ; " + str(len(Fnaive) - len(Fmin)) + " ; " + str((naivetime/meantime * 100)) + " ; "
               + str(len(positives)) + " ; " + str(len(negatives)) + " ; " + str(size - len(positives) - len(negatives)))
    # --- end of compare
    
    # --------------------
    # lookup for a minimal solution
    # bottom up enumeration of rule combinations
    # use a CNS checking for definedness 
    # with shortcut
    def lookup_complex(self, U, Ubinary, size):
        # mapping completed to simplify
        numbers = self.full_mapping(size)
        positives = [numbers[i] for i in range(len(Ubinary)) if (Ubinary[i] == 1)]
        negatives = [numbers[i] for i in range(len(Ubinary)) if (Ubinary[i] == 0)]  
        focused = positives+negatives
        # compute G
        G = [i for i in range(size) if (i not in focused)]
        # check only F => positives+G
        selection = positives + G
        #print ("Maximal selection " + str(selection))
        sizeS = len(selection)
        found = False # additional condition
        sizeL = 1
        # each time 
        while (sizeL <= sizeS) and not found:
            # counters initialized
            K =  [i for i in range(sizeL)]
            #increment counter one by one but in reverse order
            k = sizeL-1
            while (k >= 0) and not found:
                # test the current selection F
                test = [selection[j] for j in K]
                #print ("test " + str(test))
                # universal conditions
                D_I_1 = And(*[self.rules[i].get_cond() for i in positives])
                NOTD_I_0 = And(*[Not(self.rules[i].get_cond()) for i in negatives])
                # check universal complex with necessary check
                I1_NOTF = [i for i in positives if i not in test]
                self.solver.reset()
                self.solver.add(U) # U is there
                self.solver.push() # create breakpoint
                if (self.variables):
                    self.solver.add(ForAll(self.variables, D_I_1))                  
                    self.solver.add(ForAll(self.variables, NOTD_I_0))                  
                    for i in I1_NOTF:
                        self.solver.add(ForAll(self.variables, self.rules[i].get_conc()))
                    found = self.solver.check().__eq__(sat)
                    # shortcut 
                    if found:
                        G_NOTF = [i for i in G if (i not in test)] 
                        for g in G_NOTF:
                            self.solver.add(Or(ForAll(self.variables, And(self.rules[g].get_cond(), self.rules[g].get_conc())), 
                                            ForAll(self.variables, Not(self.rules[g].get_cond()))))
                        found = self.solver.check().__eq__(sat)   
                    # check existential part  U & ?* ~(D_I1~D_I0) & R_~F
                    if not found:
                        #print ("radix is ? = " + str(found))   
                        # compute R reduced to ~F !!! here all rules and not in F
                        notest = [j for j in range(size) if j not in test]
                        #print ("F= " + str(test) + "~F= " + str(notest))   
                        R_NOTF = [self.rules[i].toBoolRef() for i in notest]
                        self.solver.pop() # backtrack to evaluate another term
                        self.solver.add(Exists(self.variables, Or(Not(D_I_1), Not(NOTD_I_0))))
                        self.solver.add(ForAll(self.variables, And(*R_NOTF)))
                        found = self.solver.check().__eq__(sat)
                        #print ("found existentielle= " + str(found))
                else:
                    self.solver.add(D_I_1)                  
                    self.solver.add(NOTD_I_0)                       
                    for i in I1_NOTF:
                        self.solver.add(self.rules[i].get_conc())
                    found = self.solver.check().__eq__(sat)   
                    if found:
                        G_NOTF = [i for i in G if (i not in test)] 
                        for g in G_NOTF:
                            self.solver.add(self.rules[g].z3())
                        found = self.solver.check().__eq__(sat)   
                    # TODO as above
                # --- end check universal complex             
                # increment the k counter and check limit 
                if (K[k] < sizeS-sizeL+k):
                    K[k] += 1
                else: # go back and next 
                    # go back until limit reached
                    while (k >= 0) and (K[k] >= sizeS-sizeL+k):
                        k += -1 
                    # if possible reinit counters and k to end
                    if (k >= 0):
                        K[k] += 1
                        for j in range(k+1, sizeL):
                            K[j] = K[j-1]+1 
                        k = sizeL-1 
                    # to stop since finished
                    else:
                        k = -1
                # --- end if K
            # --- end while k
            sizeL += 1
        # --- end while sizeL
        return test
    # --- end lookup_complex3    
    
    # --------------------
    # lookup for a minimal solution
    # bottom up enumeration of rule combinations
    # use a CNS checking for definedness 
    # with shortcut BUT U is an unsafe problem
    # ONLY for unsafe problem 
    def lookup_unsafe(self, U, Ubinary, size):
        # mapping completed to simplify
        numbers = self.full_mapping(size)
        positives = [numbers[i] for i in range(len(Ubinary)) if (Ubinary[i] == 1)]
        negatives = [numbers[i] for i in range(len(Ubinary)) if (Ubinary[i] == 0)]  
        focused = positives+negatives
        # compute G
        G = [i for i in range(size) if (i not in focused)]
        # check only F => positives+G
        selection = positives + G
        #print ("Maximal selection " + str(selection))
        sizeS = len(selection)
        found = False # additional condition
        sizeL = 1
        # each time 
        while (sizeL <= sizeS) and not found:
            # counters initialized
            K =  [i for i in range(sizeL)]
            #increment counter one by one but in reverse order
            k = sizeL-1
            while (k >= 0) and not found:
                # test the current selection F
                test = [selection[j] for j in K]
                # check universal complex with necessary check
                I1_NOTF = [i for i in positives if i not in test]
                self.solver.reset()
                self.solver.add(U)
                self.solver.push()
                if (self.variables):
                    for i in I1_NOTF:
                        self.solver.add(ForAll(self.variables, self.rules[i].get_conc()))
                    found = self.solver.check().__eq__(sat)
                    # shortcut 
                    if found:
                        G_NOTF = [i for i in G if (i not in test)] 
                        for g in G_NOTF:
                            self.solver.add(Or(ForAll(self.variables, And(self.rules[g].get_cond(), self.rules[g].get_conc())), 
                                            ForAll(self.variables, Not(self.rules[g].get_cond()))))
                        found = self.solver.check().__eq__(sat)   
                    # check existential part  U & ?* ~(D_I1~D_I0) & R_~F
                    else:
                        # compute R reduced to ~F !!! here all rules and not in F
                        notest = [j for j in range(size) if j not in test]
                        #print ("F= " + str(test) + "~F= " + str(notest))   
                        R_NOTF = [self.rules[i].toBoolRef() for i in notest]
                        self.solver.pop()
                        # universal conditions
                        D_I_1 = And(*[self.rules[i].get_cond() for i in positives])
                        NOTD_I_0 = And(*[Not(self.rules[i].get_cond()) for i in negatives])
                        self.solver.add(Exists(self.variables, Or(Not(D_I_1), Not(NOTD_I_0))))
                        self.solver.add(ForAll(self.variables, And(*R_NOTF)))
                        found = self.solver.check().__eq__(sat)
                else:
                    # no variables
                    for i in I1_NOTF:
                        self.solver.add(self.rules[i].get_conc())
                    found = self.solver.check().__eq__(sat)   
                    if found:
                        G_NOTF = [i for i in G if (i not in test)] 
                        for g in G_NOTF:
                            self.solver.add(self.rules[g].z3())
                        found = self.solver.check().__eq__(sat)   
                    # TODO complete as above
                # --- end check universal complex             
                # increment the k counter and check limit 
                if (K[k] < sizeS-sizeL+k):
                    K[k] += 1
                else: # go back and next 
                    # go back until limit reached
                    while (k >= 0) and (K[k] >= sizeS-sizeL+k):
                        k += -1 
                    # if possible reinit counters and k to end
                    if (k >= 0):
                        K[k] += 1
                        for j in range(k+1, sizeL):
                            K[j] = K[j-1]+1 
                        k = sizeL-1 
                    # to stop since finished
                    else:
                        k = -1
                # --- end if K
            # --- end while k
            sizeL += 1
        # --- end while sizeL
        return test
    # --- end lookup_unsafe
    
    # ----------------------
    # Fix multiple problems in conclusions, from a list of unsafe numbers ONLY
    # and generate a new rule system fixing all these problems minimally
    # end should be there else copy too much rules
    # U are unsafe problems  
    def fix_multiple(self, lbinary, end):
        how = len(lbinary)
        # define a new rules system or Fixing ?
        newR = Improve()
        newR.variables = self.variables
        # build the list of U and of fix
        lproblems = []
        lfixes = []
        for i in lbinary:
            rule = self.unsafe[i]
            Ubinary = rule.get_binary()
            if self.variables:
                U = Exists(self.variables, rule.get_cond()) # explicit quantifiers
            else:
                U = rule.get_cond()
            # --- quantifiers
            fix = self.lookup_complex(U, Ubinary, end)
            lproblems.append(U)
            lfixes.append(fix)
        # --- end for 
        # build and apply the fix for each rule
        for i in range(end): 
            oldr = self.rules[i]
            # compute list of fixes for i 
            correctif = [lproblems[j] for j in range(how) if (i in lfixes[j])]
            if correctif:
                #print ("fix rule " + str(i) + " with " + str(correctif))
                newR.add_rule(oldr.get_cond(), Or(oldr.get_conc(), *correctif))
            else:
                # format compatible with Improve()
                newR.add_rule(oldr.get_cond(), oldr.get_conc())
        # --- for i
        return newR
    # --- end of fix_multiple
    
# --- end class Removing