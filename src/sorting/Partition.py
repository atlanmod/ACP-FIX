# ------------------
# 25/6/2018
# Compute connected component
# -------------------

# ------ 
# Should store all the inclusions relations 
# and the inverse relation
# in this king of graph we have at most only 2-cycles
class Partition():
    
    # --------------------
    # init constructor 
    def __init__(self, n):
        # size
        self.number = n
        # the relations with direction 
        # (i in dico[j]) means i should be before j  
        # because Ci => Cj
        self.dico = {}
        # inverse edge
        self.inverse = {}
        # nodes to visit
        self.tovisit = list(range(0, n))
        # partition of nodes
        self.partition = []
        # number of packets
        self.packet = 0
    # --- init
    
    # --------------------
    def __str__(self):
        return "\n Dico "+ str(self.dico) + "\n Inverse "+ str(self.inverse) + "\n Partition" + str(self.partition) + "\n How= "+ str(self.packet) 
    # --- str
    
    # --------------------
    # add an inclusion from i to j
    # and build the inverse relation 
    def add(self, i, j):
        if (i in self.dico):
            self.dico[i].append(j)
        else:
            self.dico[i] = [j]
        # store inverse graph
        if (j in self.inverse):
            self.inverse[j].append(i)
        else:
            self.inverse[j] = [i]
    # --- add
    
    # --------------------
    # number of nodes
    def size(self):
        return self.number
    # --- size

    # --------------------
    # computes in partition the connecting components
    def connexes(self):
        while (not self.tovisit == []):
            # new partition
            self.partition.append([])
            self.connexes_aux(self.tovisit[0])
            self.packet += 1 
        # --- end while
    # --- end of connexes
    
    # --------------------
    # computes a connecting components with node
    def connexes_aux(self, node):
        #print ("connexes_aux visit " + str(node) + " " +str(self.packet))
        self.tovisit.remove(node)
        self.partition[self.packet].append(node)
        # visit neighbors
        neighbors = []
        if (node in self.dico):
            neighbors = self.dico[node]
        if (node in self.inverse):
            neighbors += self.inverse[node]
        #print("neighbors " + str(neighbors))
        for voisin in neighbors:
            #print("voisin= " + str(voisin) + " in " + str(self.tovisit))
            if (voisin in self.tovisit):
                self.connexes_aux(voisin)
        # --- end for voisin
    # --- end of connexes_aux
    
    # --------------------
    # arbitrary partition in n equal parts + rest
    def split(self, n):
        self.packet = n
        taille = self.number // n
        for i in range(0, n-1):
            self.partition.append(list(range(i,i+taille)))
        # --- end for
        # last packet
        last = taille*(n-1)
        self.partition.append(list(range(last, last + taille + (self.number % n))))
        print ("Simple partition " + str(self.partition))
    # --- end of split
# --- end Partition
