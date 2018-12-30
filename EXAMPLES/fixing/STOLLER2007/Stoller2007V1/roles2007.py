# -------------------
# 6/12/2018
# RBAC2 from http://www3.cs.stonybrook.edu/~stoller/ccs2007/
# -------------------
# other encoding are possible
# we add parameters
# SMER are disjunction rules
# roles are predicates, herarchies are implications
# ----------------------
### With time each predicate take int parameter
### Fix the 4st unsafe TODO

from Removing import * #@UnusedWildImport

# --------------------------
Person = DeclareSort('Person')
Resource = DeclareSort('Resource')

table = Removing()
# Variables
table.add_variable("X", Person)
table.add_variable("R", Resource)
table.add_variable("Y", Person)
table.add_variable("T", IntSort()) # linear time
X = table.get_variable(0)
R = table.get_variable(1)
Y = table.get_variable(2)
T = table.get_variable(3)

### --------------------------
### predicates for roles
Employee = Function('Employee', IntSort(), Person, BoolSort()) 
Nurse = Function('Nurse', IntSort(), Person, BoolSort()) 
Doctor = Function('Doctor', IntSort(), Person, BoolSort()) 
Receptionist = Function('Receptionist', IntSort(), Person, BoolSort()) 
MedicalManager= Function('MedicalManager', IntSort(), Person, BoolSort()) 
MedicalTeam = Function('MedicalTeam', IntSort(), Person, BoolSort()) 
Manager= Function('Manager', IntSort(), Person, BoolSort()) 
Agent = Function('Agent', IntSort(), Person, BoolSort()) 
Patient = Function('Patient', IntSort(), Person, BoolSort())
PrimaryDoctor = Function('PrimaryDoctor', IntSort(), Person, BoolSort()) 
ReferredDoctor = Function('ReferredDoctor', IntSort(), Person, BoolSort()) 
ThirdParty = Function('ThirdParty', IntSort(), Person, BoolSort())
PatientWithTPC = Function('PatientWithTPC', IntSort(), Person, BoolSort())

### ----------------------------------------------
### roles hierarchy : we add all because could cause problem (8)
# Employee > Nurse 
#          > Doctor
#          > Receptionist
#      > MedicalManager
#          > Manager
#  to include Patient > PatientWithTPC,Similarly, Doctor > ReferredDoctor  and Doctor > PrimaryDoctor 
table.add_rule(Nurse(T, X), Employee(T, X))  #0
table.add_rule(Doctor(T, X), Employee(T, X))  #1
table.add_rule(Receptionist(T, X), Employee(T, X)) #2
table.add_rule(MedicalManager(T, X), Employee(T, X)) #3
table.add_rule(Manager(T, X), Employee(T, X)) #4
# ### qualified as unnecessary 
table.add_rule(Patient(T, X), PatientWithTPC(T, X))  #5 
# ### qualified as unnecessary 
table.add_rule(Doctor(T, X), ReferredDoctor(T, X))  #6
# ### qualified as unnecessary 
table.add_rule(Doctor(T, X), PrimaryDoctor(T, X))   #7
# ## mutual exclusion of roles (3)
table.add_rule(And(Patient(T, X), PrimaryDoctor(T, X)), False) #8
table.add_rule(And(Receptionist(T, X), Doctor(T, X)), False) #9
table.add_rule(And(Nurse(T, X), Doctor(T, X)), False) #10
#### ---
start = clock()
size = 8+3
table.compute_table(size) ### with Improve !
#print ("rules= " + str(len(table.correct)) + " safe= " + str(len(table.safe)) + " unsafe= " + str(len(table.unsafe)))
#print(str(table))
# print (str(table.ordering) + " explicit " + str(table.explicit) + " tauto " + str(table.tautology)) #{5: 0, 6: 1, 7: 2, 0: 3, 1: 4, 2: 5, 3: 6, 4: 7} explicit [8, 9, 10] tauto []
#print(" analysis time: " + str(floor(clock()-start)))
### use compute_table
#  ----------- Unsafe -------------- 
# UNSAFE [1] <[And(Patient(T, X), PrimaryDoctor(T, X))] => False>
# UNSAFE [0, 1] <[Not(And(Patient(T, X), PrimaryDoctor(T, X))), And(Receptionist(T, X), Doctor(T, X))] => False>
# UNSAFE [0, 0, 1] <[Not(And(Patient(T, X), PrimaryDoctor(T, X))), Not(And(Receptionist(T, X), Doctor(T, X))), And(Nurse(T, X), Doctor(T, X))] => False>
# UNSAFE [0, 0, 0, 1, 1, 1] <[Not(And(Patient(T, X), PrimaryDoctor(T, X))), Not(And(Receptionist(T, X), Doctor(T, X))), Not(And(Nurse(T, X), Doctor(T, X))), Patient(T, X), Doctor(T, X)] => False>

### first 
U1 = Exists(table.variables, And(Patient(T, X), PrimaryDoctor(T, X)))
UB1 = [1] 
# numbers= [8, 9, 10, 5, 6, 7, 0, 1, 2, 3, 4]

#print(str(table.lookup_complex(U1, UB1, size))) # [8] OK
table.compare(U1, UB1, size, 0)

### second
U2 = Exists(table.variables, And(Not(And(Patient(T, X), PrimaryDoctor(T, X))), And(Receptionist(T, X), Doctor(T, X))))
UB2 = [0, 1] 

# print(str(table.lookup_complex(U2, UB2, size))) # [9] OK
table.compare(U2, UB2, size, 1)

#### third 

######## the fourth problem 
# ### check single unsafe the 4st
U4 =  Exists(table.variables, And(Not(And(Patient(T, X), PrimaryDoctor(T, X))), Not(And(Receptionist(T, X), Doctor(T, X))), 
                                  Not(And(Nurse(T, X), Doctor(T, X))), Patient(T, X), Doctor(T, X)))
UB4 = [0, 0, 0, 1, 1, 1]

# print(str(table.lookup_complex(U4, UB4, size))) # [7] OK
table.compare(U4, UB4, size, 3)

#### this suggest to fix the rule 7 (because also was not necessary in original text)
