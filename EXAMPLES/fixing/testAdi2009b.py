# -------------------
# 24/06/2019
# Test Adi2009 
# -------------------

from Removing import * #@UnusedWildImport
from time import * #@UnusedWildImport

# --------------------------
Patient = DeclareSort('Patient')
Hospital = DeclareSort('Hospital')

table = Removing()
# Variables
table.add_variable("p", Patient)
table.add_variable("h", Hospital)
p = table.get_variable(0)
h = table.get_variable(1)
# more 
X= Const('X', Hospital)
toubib = Const('toubib', Hospital)
nounou = Const('nounou', Hospital)
bob = Const('bob', Patient)

# 4/1 + 3/2 predicates 
hospital = Function('hospital', Hospital, BoolSort()) 
doctor = Function('doctor', Hospital, BoolSort())     
nurse = Function('nurse', Hospital, BoolSort())
chief = Function('chief', Hospital, BoolSort())
pread = Function('pread', Hospital, Patient, BoolSort())
pwrite = Function('pwrite', Hospital, Patient, BoolSort())
sameward = Function('sameward', Hospital, Patient, BoolSort())

### SORTED ORDERING
# 0: 
table.add_rule(And(nurse(h), doctor(h)), sameward(h, p)) # A
#table.add_rule(And(nurse(h), doctor(h), sameward(h, p)), sameward(h, p)) # TEST1 A fixed becomes tautology
# 1: 
table.add_rule(doctor(h), And(pread(h, p), pwrite(h, p))) # B
#table.add_rule(Or(And(doctor(h), Not(nurse(h))), And(doctor(h), sameward(h, p))), And(pread(h, p), pwrite(h, p))) # TEST1 B fixed
# 2: 
table.add_rule(And(nurse(h), Not(sameward(h, p))), Not(pread(h, p))) # C
#table.add_rule(And(nurse(h), Not(doctor(h)), Not(sameward(h, p))), Not(pread(h, p))) # TEST1 C fixed
#table.add_rule(Or(And(nurse(h), doctor(h), Not(sameward(h, p))), And(nurse(h), Not(sameward(h, p)), Not(chief(h)))), Not(pread(h, p))) # TEST2
#table.add_rule(And(nurse(h), Not(doctor(h)), Not(sameward(h, p)), Not(chief(h))), Not(pread(h, p))) # TEST1 then second fix
# 3: 
table.add_rule(And(doctor(h), sameward(h, p)), pread(h, p))
# 4: 
table.add_rule(chief(h), pread(h, p))
#table.add_rule(Or(And(chief(h), Not(nurse(h))), And(chief(h), doctor(h)), And(chief(h), sameward(h, p))), pread(h, p)) # TEST2
#### ---------------
# start = clock()
size = 5
#table.analyze()
table.compute_table(size)
# #print ("rules= " + str(len(table.correct)) + " safe= " + str(len(table.safe)) + " unsafe= " + str(len(table.unsafe)))
# # rules= 5 safe= 4 unsafe= 2
# print (str(table))
### =========================
#  ----------- Sorted -------------- 
# <And(nurse(h), doctor(h)) => sameward(h, p)>
# <doctor(h) => And(pread(h, p), pwrite(h, p))>
# <And(nurse(h), Not(sameward(h, p))) => Not(pread(h, p))>
# <And(doctor(h), sameward(h, p)) => pread(h, p)>
# <chief(h) => pread(h, p)>
#  ----------- Unsafe -------------- 
# UNSAFE [1, 1, 1] <And(nurse(h), doctor(h), Not(sameward(h, p))) => False>
# UNSAFE [0, 0, 1, 0, 1] <And(nurse(h), Not(doctor(h)), Not(sameward(h, p)), chief(h)) => False>
# ----
# 0,1 0,2 are minimal for the first problem
# 2 and 4 for the second
### -----
### ----------

#### ===================== TEST1 incomplete case
U0 = Exists(table.variables, And(nurse(h), doctor(h), Not(sameward(h, p))))
UB0 = [1, 1, 1]
# UNSAFE [1, 1, 1] <And(nurse(h), doctor(h), Not(sameward(h, p))) => False>

print(str(table.lookup_complex(U0, UB0, size))) # [0, 1] OK

table.compare(U0, UB0, size, 0)

# ### 4/9/2018  a complete case OK
# # ======== UNSAFE [0, 0, 1, 0, 1] <And(nurse(h), Not(doctor(h)), Not(sameward(h, p)), chief(h)) => False>
U1 = Exists(table.variables, And(nurse(h), Not(doctor(h)), Not(sameward(h, p)), chief(h))) # simplif ???
UB1 = [0, 0, 1, 0, 1]

print(str(table.lookup_complex(U1, UB1, size))) # [2] OK 

table.compare(U1, UB1, size, 1)

