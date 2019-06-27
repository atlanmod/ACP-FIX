# -------------------
# 25/6/2019
# RBAC2 from http://www3.cs.stonybrook.edu/~stoller/ccs2007/
# -------------------
### assign modul V4 alone
# -----------------

### ------
from Removing import * #@UnusedWildImport

# --------------------------
Person = DeclareSort('Person')
Resource = DeclareSort('Resource')
Time = DeclareSort('Time')

table = Removing()
# Variables
table.add_variable("X", Person)
table.add_variable("R", Resource)
table.add_variable("Y", Person)
table.add_variable("T", Time) # linear time
X = table.get_variable(0)
R = table.get_variable(1)
Y = table.get_variable(2)
T = table.get_variable(3)

#### Time with succ
succ = Function('succ', Time, Time) 

### --------------------------
### predicates for roles
Employee = Function('Employee', Time, Person, BoolSort()) 
Nurse = Function('Nurse', Time, Person, BoolSort()) 
Doctor = Function('Doctor', Time, Person, BoolSort()) 
Receptionist = Function('Receptionist', Time, Person, BoolSort()) 
MedicalManager= Function('MedicalManager', Time, Person, BoolSort()) 
MedicalTeam = Function('MedicalTeam', Time, Person, BoolSort()) 
Manager= Function('Manager', Time, Person, BoolSort()) 
Agent = Function('Agent', Time, Person, BoolSort()) 
Patient = Function('Patient', Time, Person, BoolSort())
PrimaryDoctor = Function('PrimaryDoctor', Time, Person, BoolSort()) 
ReferredDoctor = Function('ReferredDoctor', Time, Person, BoolSort()) 
ThirdParty = Function('ThirdParty', Time, Person, BoolSort())
PatientWithTPC = Function('PatientWithTPC', Time, Person, BoolSort())

### for action (no relation known between them) (8)
view = Function('view', Time, Person, Resource, BoolSort())
add = Function('add',  Time, Person, Resource, BoolSort())
modify = Function('modify',  Time, Person, Resource, BoolSort())
access = Function('access',  Time, Person, Resource, BoolSort())
enter = Function('enter',  Time, Person, Resource, BoolSort())
update = Function('update',  Time, Person, Resource, BoolSort())
create = Function('create',  Time, Person, Resource, BoolSort())
sign = Function('sign',  Time, Person, Resource, BoolSort())

### for resources  (13) we do not know possible relation ???
OldMedicalRecords = Function('OldMedicalRecords',  Time, Resource, BoolSort()) 
RecentMedicalRecords = Function('RecentMedicalRecords',  Time, Resource, BoolSort()) 
PrivateNotes = Function('PrivateNotes',  Time, Resource, BoolSort()) 
Prescriptions = Function('Prescriptions',  Time,  Resource, BoolSort()) 
PatientPersonalInfo = Function('PatientPersonalInfo',  Time, Resource, BoolSort()) 
PatientFinancialInfo = Function('PatientFinancialInfo',  Time, Resource, BoolSort()) 
PatientMedicalInfo = Function('PatientMedicalInfo',  Time, Resource, BoolSort()) 
CarePlan = Function('CarePlan',  Time, Resource, BoolSort()) 
Appointment = Function('Appointment',  Time, Resource, BoolSort()) 
ProgressNotes = Function('ProgressNotes',  Time, Resource, BoolSort()) 
MedicalRecordsWithThirdPartyInfo = Function('MedicalRecordsWithThirdPartyInfo',  Time, Resource, BoolSort()) 
LegalAgreement = Function('LegalAgreement',  Time, Resource, BoolSort()) 
Bills = Function('Bills',  Time, Resource, BoolSort()) 
### assign
assign = Function('assign',  Time, Person, Person, BoolSort()) 
### revoke
revoke = Function('revoke',  Time, Person, Person, BoolSort()) 

##### the rules -------------
# 
### ----------------------------------------------roles fixed (8+3) 
table.add_rule(Nurse(T, X), Employee(T, X))  # 0
table.add_rule(Doctor(T, X), Employee(T, X))
table.add_rule(Receptionist(T, X), Employee(T, X)) #
table.add_rule(MedicalManager(T, X), Employee(T, X))
table.add_rule(Manager(T, X), Employee(T, X))
table.add_rule(Patient(T, X), PatientWithTPC(T, X))  #
table.add_rule(Doctor(T, X), ReferredDoctor(T, X))  # 
#table.add_rule(Doctor(T, X), PrimaryDoctor(T, X))   # remove it?
### change it 
table.add_rule(Doctor(T, X), Or(PrimaryDoctor(T, X), 
                                Exists(table.variables, And(Not(And(Patient(T, X), PrimaryDoctor(T, X))), Not(And(Receptionist(T, X), Doctor(T, X))), 
                                 Not(And(Nurse(T, X), Doctor(T, X))), Patient(T, X), Doctor(T, X)))
                                ))
# ---
table.add_rule(And(Patient(T, X), PrimaryDoctor(T, X)), False) #
table.add_rule(And(Receptionist(T, X), Doctor(T, X)), False) #
table.add_rule(And(Nurse(T, X), Doctor(T, X)), False) #10
### ---- 

# ------------------------------- (13) 
table.add_rule(And(Doctor(T, X), assign(T, X, Y)), ThirdParty(succ(T), Y)) #
table.add_rule(And(Doctor(T, X), Doctor(T, Y), assign(T, X, Y)), ReferredDoctor(succ(T), Y)) #
table.add_rule(And(MedicalManager(T, X), Doctor(T, Y), assign(T, X, Y)), MedicalTeam(succ(T), Y)) #
table.add_rule(And(MedicalManager(T, X), Nurse(T, Y), assign(T, X, Y)), MedicalTeam(succ(T), Y)) #
  
table.add_rule(And(Manager(T, X), assign(T, X, Y)), Employee(succ(T), Y))  # 
###these three produce conflicts thus changed 
table.add_rule(And(Manager(T, X), Not(Doctor(T, Y)), assign(T, X, Y)), Receptionist(succ(T), Y)) #
table.add_rule(And(Manager(T, X), Not(Doctor(T, Y)), assign(T, X, Y)), Nurse(succ(T), Y))  #
table.add_rule(And(Manager(T, X), Not(PrimaryDoctor(T, Y)), assign(T, X, Y)), Doctor(succ(T), Y)) #
### old ones
# table.add_rule(And(Manager(T, X), assign(T, X, Y)), Receptionist(succ(T), Y)) #
# table.add_rule(And(Manager(T, X), assign(T, X, Y)), Nurse(succ(T), Y))  #
# table.add_rule(And(Manager(T, X), assign(T, X, Y)), Doctor(succ(T), Y)) #
table.add_rule(And(Manager(T, X), assign(T, X, Y)), MedicalTeam(succ(T), Y)) # 47
 
table.add_rule(And(Patient(T, X), assign(T, X, Y)), Agent(succ(T), Y)) #
table.add_rule(And(Patient(T, X), Doctor(T, Y), assign(T, X, Y)), PrimaryDoctor(succ(T), Y)) # 
 
table.add_rule(And(Receptionist(T, X), assign(T, X, Y)), Patient(succ(T), Y)) # 
table.add_rule(And(ThirdParty(T, X), Patient(T, Y), assign(T, X, Y)), PatientWithTPC(succ(T), Y)) #
# --------------------------------------------

# ### incompatibility revoke assign at the same date
# table.add_rule(And(revoke(T, X, Y), assign(T, X, Y)), False) #
# 
# ### ************************** new formulation revoke (10) 
# # for each rule can_assign(r_a, c, r), there is a corresponding rule
# # can_revoke(r_a, r), except that a doctor, not a receptionist, can revoke
# # the Patient role.  this reflects the policy that a patient must be
# # discharged from the facility by a doctor.  or, we could make the patient
# # role irrevocable.
# ### New encoding: 
# #### A cond assign => newrole becomes
# #### A newrole revoke  => Not(newrole at T+1) 
#  
# table.add_rule(And(Doctor(T, X), ThirdParty(T, Y), revoke(T, X, Y)), Not(ThirdParty(succ(T), Y))) #
# table.add_rule(And(Doctor(T, X), ReferredDoctor(T, Y), revoke(T, X, Y)), Not(ReferredDoctor(succ(T), Y))) #
# table.add_rule(And(Manager(T, X), Employee(T, Y), revoke(T, X, Y)), Not(Employee(succ(T), Y))) #
# 
# # # redundant
# # table.add_rule(And(Manager(T, X), Receptionist(T, Y), revoke(T, X, Y)), Not(Receptionist(succ(T), Y))) #
# # table.add_rule(And(Manager(T, X), Nurse(T, Y), revoke(T, X, Y)), Not(Nurse(succ(T), Y))) #
# # table.add_rule(And(Manager(T, X), Doctor(T, Y), revoke(T, X, Y)), Not(Doctor(succ(T), Y))) #
#  
# table.add_rule(And(Patient(T, X), Agent(T, Y), revoke(T, X, Y)), Not(Agent(succ(T), Y))) #
# table.add_rule(And(Patient(T, X), PrimaryDoctor(T, Y), revoke(T, X, Y)), Not(PrimaryDoctor(succ(T), Y))) #
# table.add_rule(And(Receptionist(T, X), Patient(T, Y), revoke(T, X, Y)), Not(Patient(succ(T), Y))) #
# table.add_rule(And(ThirdParty(T, X), PatientWithTPC(T, Y), revoke(T, X, Y)), Not(PatientWithTPC(succ(T), Y))) #
# table.add_rule(And(MedicalManager(T, X), MedicalTeam(T, Y), revoke(T, X, Y)), Not(MedicalTeam(succ(T), Y))) #
# table.add_rule(And(Manager(T, X), MedicalTeam(T, Y), revoke(T, X, Y)), Not(MedicalTeam(succ(T), Y))) #
# ### a doctor, not a receptionist, can revoke the Patient role
# table.add_rule(And(Doctor(T, X), Not(Receptionist(T, X)), Patient(T, Y), revoke(T, X, Y)), Not(Patient(succ(T), Y))) #
# # # --------------------------------------------

## --
start = process_time()
size = 8+3+13
table.compute_table(size) 
#table.check(size)
#print(str(table))
for r in table.unsafe:
    print (str(r))
print ("rules= " + str(len(table.correct)) + " safe= " + str(len(table.safe)) 
       + " unsafe= " + str(len(table.unsafe)) + " time: " + str(floor(process_time()-start))) # + " built= " + str(table.built))


#### ========================
### size = 13 assignement alone
### rules= 13 safe= 187 unsafe= 0 time: 20

#### ========================
### size = 8+3+13 # roles+assignement
# UNSAFE [1] <[And(Patient(T, X), PrimaryDoctor(T, X))] => False>
# UNSAFE [0, 1] <[Not(And(Patient(T, X), PrimaryDoctor(T, X))), And(Receptionist(T, X), Doctor(T, X))] => False>
# UNSAFE [0, 0, 1] <[Not(And(Patient(T, X), PrimaryDoctor(T, X))), Not(And(Receptionist(T, X), Doctor(T, X))), And(Nurse(T, X), Doctor(T, X))] => False>
# UNSAFE [0, 0, 0, 1, 1, 1] <[Not(And(Patient(T, X), PrimaryDoctor(T, X))), Not(And(Receptionist(T, X), Doctor(T, X))), Not(And(Nurse(T, X), Doctor(T, X))), Patient(T, X), Doctor(T, X)] => False>
# rules= 21 safe= 227 unsafe= 4 time: 37

# #### first
# U0 = Exists(table.variables, And(Not(And(Patient(T, X), PrimaryDoctor(T, X))), Not(And(Receptionist(T, X), Doctor(T, X))), 
#                                  Not(And(Nurse(T, X), Doctor(T, X))), Patient(T, X), Doctor(T, X)))
#     
# B0= [0, 0, 0, 1, 1, 1]
#  
# print(str(table.lookup_complex(U0, B0, size))) #[7] is minimal
# table.compare(U0, B0, size, 0) 
# # 0 ; 3 ; [7] ; 0.1251349999999995 ; [5, 7] ; 6.209179600000001 ; 1 ; 2 ; -1 ; 2.0153226039716983 ; 3 ; 3 ; 18 
# ### TODO bug here in naive ?

### after fix
###rules= 21 safe= 252 unsafe= 3 time: 43
### ---
