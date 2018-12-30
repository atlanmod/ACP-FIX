# ------------------
# 9/6/2018
# Simple graph to topological sorting
# -------------------
# TODO impact of without conclusions ?

# ------ 
# Should store all the inclusions relations 
# from two dico pos and neg
# in this king of graph we have at most only 2-cycles
# with sorting degree 
class Inclusion():
    
    # --------------------
    # init constructor 
    def __init__(self, n):
        # size
        self.number = n
        # the relations with direction 
        # (i in dico[j]) means i should be before j  (Ci => Cj)
        self.dico = {}
        # the in degree a dico of values -> j
        self.indegree = {}
        self.indegree[0] = list(range(0, n))
        # mapping of resulting sorted nodes 
        self.sorted = {}
        # store equals relations
        self.equals = dict()
    # --- init
    
    # --------------------
    def __str__(self):
        return str(self.indegree) + "\n"+ str(self.dico) + "\n"+ str(self.sorted)
    # --- str
    
    # --------------------
    # add an inclusion from i to j
    def add(self, i, j):
        if (i in self.dico):
            self.dico[i].append(j)
        else:
            self.dico[i] = [j]
        # update  degree and add +1
        self.insert(j)
    # --- add
    
    # --------------------
    # get degree of j 
    # or else return -1
    def get(self, j):
        for val in self.indegree:
            if (j in self.indegree[val]):
                return val
        # --- end for
        return -1
    # --- end get
    
    # --------------------
    # add +1 to degree of j and sort it
    def insert(self, j):
        val = self.get(j)
        self.indegree[val].remove(j)
        val += 1
        #print ("insert " + str(val) + " " + str(j))
        if (val in self.indegree):
            self.indegree[val].append(j)
        else:
            self.indegree[val] = [j]
    # --- insert
    
    # --------------------
    # decrease degree of j 
    # if degree = 0 j is lost
    def decrease(self, j):
        val = self.get(j)
        if (val >= 0):
            self.indegree[val].remove(j)
            if (val > 0):
                self.indegree[val-1].append(j)
        # --- end if val >=0
    # --- decrease
    
    # --------------------
    # number of nodes
    def size(self):
        return self.number
    # --- size
    
    # --------------------
    # return a node with the least degree
    # and remove it from indegree
    def select(self):
        for i in self.indegree:
            if ((i >= 0) and self.indegree[i]):
                node = self.indegree[i][0]
                self.indegree[i].remove(node)
                return node
    # --- size
    
    # --------------------
    # topological sorting but forget cycles
    def sort(self):
        # external loop to repeat the selection of nodes
        for i in range(0, self.size()):
            self.equals[i] = []
            # compute equals
            if (i in self.dico):
                for k in self.dico[i]:
                    if (k in self.dico):
                        if (i in self.dico[k]):
                            self.equals[i].append(k)
            # --- end if
            # search first node select and remove
            node = self.select()
            #print("selected " + str(i) + " " + str(node))
            # put in sorted
            self.sorted[node] = i
            # remove all its out edges
            if (node in self.dico):
                #print("sort " + str(node) + "  " + str(self.dico[node]))
                for j in self.dico[node]:
                    self.decrease(j)
            # --- end if dico
        # --- end for i
        #print("inclusion.dico " + str(self.dico))
        #print("inclusion.sorted " + str(self.sorted))
        #print ("inclusion.equals= " + str(self.equals))
    # --- end topological
    
# --- end Partition
