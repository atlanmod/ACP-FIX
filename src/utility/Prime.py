# --------------
# 17/7/2018
# compute prime implicants with -1
# from https://en.wikipedia.org/wiki/Quine%E2%80%93McCluskey_algorithm
# Do not find the essential prime
# Try to work with -1 in inputs and do not use groups
# In Quine binary are distinct this is not our case
# and combine_all could produce duplicated which should be eliminated
# the combine is also more complex 
### 1=simple merge, 2=left 3=right 4=both 
###  third may be a merge of lres/rres yes but useless
# ---------------

# ----------
# test binary subsumption
def is_subsumed_by(lbin1, lbin2):
    subsumed = True
    i = 0
    while (i < len(lbin1)) and subsumed:
        digit1 = lbin1[i]
        digit2 = lbin2[i]
        subsumed = subsumed and ((digit2 == -1) or (digit1 == digit2))
        i += 1
    # --- end while
    return subsumed
# ------------

# ----------------
# combine two lists of binary with -1
# they have the same length and works if only one diff
### -1 /{0,1} => -1 ; 1/0 = -1 only once ; equal
# return two values -1 failure, 0 equal,  1,2 else merging
# 1 = one result combined, 2,3, left or right is one and rres/lres the other
# 4 both are there plus one common third this case is raising problems of loop
def combine(lbin1, lbin2):
    #print ("bin1,2 " + str(lbin1) + " " + str(lbin2))
    res = []
    lres = [] # result for special left case
    rres = [] # results for special right case
    third = [] # last common term 
    i = 0
    left = 0 # number of -1 in left not in right 
    right = 0 # number of -1 in right not in left 
    diff = 0 # number of 1/0 differences
    while ((i < len(lbin1)) and diff < 2):
        if (lbin1[i] == lbin2[i]):
            res.append(lbin1[i])
            lres.append(lbin1[i])
            rres.append(lbin1[i])
            third.append(lbin1[i])
        elif (lbin1[i] == -1):
            left += 1
            res.append(-1)
            lres.append(-1)
            rres.append(lbin2[i])
            third.append(lbin2[i])
        elif (lbin2[i] == -1):
            right += 1
            res.append(-1)
            lres.append(lbin1[i])
            rres.append(-1)
            third.append(lbin1[i])
        else:
            diff += 1 # 0 versus 1
            res.append(-1)
            lres.append(-1)
            rres.append(-1)   
            third.append(-1)                     
        # --- end if
        i += 1
    # --- end while
    #print ("diff= " + str(diff)  + "/" + str(posdiff) + " left= " + str(left) + " right= " + str(right))
    #print (" res= " + str(res)  + " lres= " + str(lres) + " rres= " + str(rres))
    # analyze results
    if (diff == 0):
        if (left == 0) and (right == 0):
            return 0, None # equal
        elif (left > 0) and (right == 0):
            return 1, res
        elif (left == 0) and (right > 0):
            return 1, res
        else:
            return -1, None
    elif (diff == 1):
        if (left == 0) and (right == 0):
            return 1, res
        elif (left > 0) and (right == 0):
            return 2, rres
        elif (left == 0) and (right > 0):
            return 3, lres
        else:
            # without 4 case not so closed to Quine Mc Cluskey
            return 4, third
            #return -1, None # alternative more efficient but less accurate 
    else:
        return -1, None # failure
# --- end combine

# ------------------
# compute all combinations of mins in lmins
# check uncombined and remove duplications
# Two condition terminations: no change or occurence of True
def combine_all(lmins):
    result = []
    combined = [] # to store lbinary combined
    alls = [] # all without double
    nochange = True
    i = 0
    finish = False 
    # main loop for combining
    while (i < len(lmins) and not finish):
        lmin = lmins[i]
        if lmin not in alls: 
            alls.append(lmin)
        j = i+1
        while (j < len(lmins)  and not finish):
            rmin = lmins[j]
            value, new = combine(lmin, rmin)
#             if (value != -1):
#                 print ("i " + str(lmin) + " j= " + str(rmin))
#                 print ("   => " + str(value) + " " + str(new))
            # test if equal or merge 
            if (value == 0):
                # equal should be removed
                del lmins[j] 
                nochange = False
            elif (value == -1):
                j += 1
            elif (value == 2): # left remains uncombined
                if (new not in result):
                    result.append(new)
                    nochange = False
                # store selection
                if rmin not in combined:
                    combined.append(rmin)
                j += 1
            elif (value == 3): # right remains uncombined
                if (new not in result):
                    result.append(new)
                    nochange = False
                # store selection
                if lmin not in combined:
                    combined.append(lmin)
                j += 1     
            elif (value == 4): # both remains uncombined
                # take care of this test
                if all([not is_subsumed_by(new, x) for x in lmins+result]):
                    result.append(new)
                    nochange = False
                j += 1                
            else:
                finish = (sum(new) == -1*len(new)) # only in this case
                # new is a lbinary
                if (new not in result):
                    result.append(new)
                    nochange = False
                # store selection
                if lmin not in combined:
                    combined.append(lmin)
                if rmin not in combined:
                    combined.append(rmin)
                j += 1
            # --- end if new
        # --- end while rmin
        i += 1
    # --- end while lmin
    #print ("result " + str(result))
    # compute uncombined
    uncombined = [l for l in alls if l not in combined]
    #print ("uncombined " + str(uncombined))
    return nochange, result+uncombined
# --- end combine_all

# ------------------
# compute the prime implicants of a list of min terms
# each is a list of {1, 0, -1}
# iterate the combination of all until not possible
def prime(lmins):
    #print ("--- start " + str(lmins) + " ------------ ")
    # initial groups
    iterate = lmins 
    while True:
        nochange, result = combine_all(iterate)
        #print ("-------------- result " + str(result) + " nochange= " + str(nochange))
        #input("wait ? ")
        iterate = result
        if nochange:
            break;
    return result
# --- end prime

#### --------------
#print(str(is_subsumed_by([0, 1, 1, 0, 1, -1], [0, 1, -1, 0, 1, -1])))
# print(str(is_subsumed_by([-1, -1, -1, -1, -1, -1, -1], [-1, -1, 0, -1, -1, -1, -1])))
# print(str(is_subsumed_by([-1, -1, -1, -1, -1, -1, -1], [-1, -1, 1, -1, -1, -1, -1])))
# print(str(is_subsumed_by([-1, -1, -1, -1, -1, -1, -1], [-1, -1, -1, -1, -1, 0, -1])))

#print(str(prime([[-1, 0], [1, -1]]))) ????
