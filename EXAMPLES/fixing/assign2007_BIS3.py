# -------------------
# 3/12/2018
# RBAC2 from http://www3.cs.stonybrook.edu/~stoller/ccs2007/
# -------------------
# see healthcare2007.py
# Here focus on can_assign rule and adding the unsafe rule
### test simplification
### not really useful as fix but testing simplification
### -------------

### TODO attention au existential universal problem

from time import * #@UnusedWildImport
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
#table.add_variable("P", IntSort()) # linear time
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

### for action (no relation known between them)
view = Function('view', IntSort(), Person, Resource, BoolSort())
add = Function('add',  IntSort(), Person, Resource, BoolSort())
modify = Function('modify',  IntSort(), Person, Resource, BoolSort())
access = Function('access',  IntSort(), Person, Resource, BoolSort())
enter = Function('enter',  IntSort(), Person, Resource, BoolSort())
update = Function('update',  IntSort(), Person, Resource, BoolSort())
create = Function('create',  IntSort(), Person, Resource, BoolSort())
sign = Function('sign',  IntSort(), Person, Resource, BoolSort())
### for resources we do not know possible relation
OldMedicalRecords = Function('OldMedicalRecords',  IntSort(), Resource, BoolSort()) 
RecentMedicalRecords = Function('RecentMedicalRecords',  IntSort(), Resource, BoolSort()) 
PrivateNotes = Function('PrivateNotes',  IntSort(), Resource, BoolSort()) 
Prescriptions = Function('Prescriptions',  IntSort(),  Resource, BoolSort()) 
PatientPersonalInfo = Function('PatientPersonalInfo',  IntSort(), Resource, BoolSort()) 
PatientFinancialInfo = Function('PatientFinancialInfo',  IntSort(), Resource, BoolSort()) 
PatientMedicalInfo = Function('PatientMedicalInfo',  IntSort(), Resource, BoolSort()) 
CarePlan = Function('CarePlan',  IntSort(), Resource, BoolSort()) 
Appointment = Function('Appointment',  IntSort(), Resource, BoolSort()) 
ProgressNotes = Function('ProgressNotes',  IntSort(), Resource, BoolSort()) 
MedicalRecordsWithThirdPartyInfo = Function('MedicalRecordsWithThirdPartyInfo',  IntSort(), Resource, BoolSort()) 
LegalAgreement = Function('LegalAgreement',  IntSort(), Resource, BoolSort()) 
Bills = Function('Bills',  IntSort(), Resource, BoolSort()) 
### assign
assign = Function('assign',  IntSort(), Person, Person, BoolSort()) 
### revoke
revoke = Function('revoke',  IntSort(), Person, Person, BoolSort()) 

#### REORDERING compatible with sorted to simplify things
# can_assign(Doctor, true, ThirdParty)
table.add_rule(And(Doctor(T, X), assign(T, X, Y)), ThirdParty(T, Y)) #0 
# # # # can_assign(Doctor, Doctor, ReferredDoctor)
table.add_rule(And(Doctor(T, X), Doctor(T, Y), assign(T, X, Y)), ReferredDoctor(T, Y)) #1 
# # 
# # can_assign(Manager, true, Employee)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), Employee(T, Y))  #2 
# # can_assign(Manager, true, Receptionist)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), Receptionist(T, Y)) #3
# # can_assign(Manager, true, Nurse)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), Nurse(T, Y))  #4 

# # can_assign(Manager, true, Doctor)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), Doctor(T, Y)) #5 

# # can_assign(Patient, true, Agent)
table.add_rule(And(Patient(T, X), assign(T, X, Y)), Agent(T, Y)) #6 
# # can_assign(Patient, Doctor, PrimaryDoctor)
table.add_rule(And(Patient(T, X), Doctor(T, Y), assign(T, X, Y)), PrimaryDoctor(T, Y)) # 7 
# 
# can_assign(Receptionist, true, Patient)
table.add_rule(And(Receptionist(T, X), assign(T, X, Y)), Patient(T, Y)) # 8 
# can_assign(ThirdParty, Patient, PatientWithTPC)
table.add_rule(And(ThirdParty(T, X), Patient(T, Y), assign(T, X, Y)), PatientWithTPC(T, Y)) #9 
# can_assign(MedicalManager, Doctor, MedicalTeam)
table.add_rule(And(MedicalManager(T, X), Doctor(T, Y), assign(T, X, Y)), MedicalTeam(T, Y)) #10
# can_assign(MedicalManager, Nurse, MedicalTeam)
table.add_rule(And(MedicalManager(T, X), Nurse(T, Y), assign(T, X, Y)), MedicalTeam(T, Y)) #11 
# can_assign(Manager, true, MedicalManager)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), MedicalTeam(T, Y)) #12
# --------------------------------------------

start = clock()
size = 13
# all = range(size)
table.analyze()
table.compute_table(size) ### needed for mapping
# print ("rules= " + str(len(table.correct)) + " safe= " + str(len(table.safe)) + " unsafe= " + str(len(table.unsafe)))
# print(" analysis time: " + str(floor(clock()-start)))
# print(str(table))
# print("ordering= " + str(table.ordering) + " explicit = " + str(table.explicit) + " tauto = " + str(table.tautology))
# ordering= {0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, 11: 11, 12: 12} explicit = [] tauto = []
# rules= 13 safe= 91 unsafe= 3  analysis time: 9
#---

#  ----------- Unsafe -------------- 
# UNSAFE [0, 0, 1, 1, 1, 1, 1, 0] <[Not(And(Doctor(T, X), assign(T, X, Y))), Not(And(Doctor(T, X), Doctor(T, Y), assign(T, X, Y))), And(Manager(T, X), assign(T, X, Y)), And(Patient(T, X), assign(T, X, Y)), Not(And(Patient(T, X), Doctor(T, Y), assign(T, X, Y)))] => False>
# UNSAFE [0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1] <[Not(And(Doctor(T, X), assign(T, X, Y))), Not(And(Doctor(T, X), Doctor(T, Y), assign(T, X, Y))), And(Manager(T, X), assign(T, X, Y)), Not(And(Patient(T, X), assign(T, X, Y))), Not(And(Patient(T, X), Doctor(T, Y), assign(T, X, Y))), And(Receptionist(T, X), assign(T, X, Y)), Not(And(ThirdParty(T, X), Patient(T, Y), assign(T, X, Y))), Not(And(MedicalManager(T, X), Doctor(T, Y), assign(T, X, Y))), And(MedicalManager(T, X), Nurse(T, Y), assign(T, X, Y))] => False>
# UNSAFE [0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1] <[Not(And(Doctor(T, X), assign(T, X, Y))), Not(And(Doctor(T, X), Doctor(T, Y), assign(T, X, Y))), And(Manager(T, X), assign(T, X, Y)), Not(And(Patient(T, X), assign(T, X, Y))), Not(And(Patient(T, X), Doctor(T, Y), assign(T, X, Y))), Not(And(Receptionist(T, X), assign(T, X, Y))), Not(And(ThirdParty(T, X), Patient(T, Y), assign(T, X, Y))), Not(And(MedicalManager(T, X), Doctor(T, Y), assign(T, X, Y))), And(MedicalManager(T, X), Nurse(T, Y), assign(T, X, Y))] => False>


#### ============= Checking unsafe without simplification
#### first
U0 = Exists(table.variables, And(Not(And(Doctor(T, X), assign(T, X, Y))), Not(And(Doctor(T, X), Doctor(T, Y), assign(T, X, Y))), 
                                    And(Manager(T, X), assign(T, X, Y)),
                                  And(Patient(T, X), assign(T, X, Y)), Not(And(Patient(T, X), Doctor(T, Y), assign(T, X, Y)))))
B0= [0, 0, 1, 1, 1, 1, 1, 0]
 
#print(str(table.lookup_complex(U0, B0, size))) #[5] is minimal
#print(str(table.naive(U0, B0, size))) #[5]
table.compare(U0, B0, size, 0) 

#### second
U1 = Exists(table.variables, And(Not(And(Doctor(T, X), assign(T, X, Y))), Not(And(Doctor(T, X), Doctor(T, Y), assign(T, X, Y))), 
                                 And(Manager(T, X), assign(T, X, Y)), Not(And(Patient(T, X), assign(T, X, Y))), 
                                 Not(And(Patient(T, X), Doctor(T, Y),  assign(T, X, Y))), And(Receptionist(T, X), assign(T, X, Y)), 
                                 Not(And(ThirdParty(T, X), Patient(T, Y), assign(T, X, Y))), Not(And(MedicalManager(T, X), Doctor(T, Y), assign(T, X, Y))), 
                                 And(MedicalManager(T, X), Nurse(T, Y), assign(T, X, Y))))
B1 = [0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1]

# print(str(table.lookup_complex(U1, B1, size))) # [5, 8]
# print(str(table.naive(U1, size))) # [5, 8]
table.compare(U1, B1, size, 1)

#### third
U2 = Exists(table.variables, And(Not(And(Doctor(T, X), assign(T, X, Y))), Not(And(Doctor(T, X), Doctor(T, Y), assign(T, X, Y))), 
                                 And(Manager(T, X), assign(T, X, Y)), Not(And(Patient(T, X), assign(T, X, Y))), 
                                 Not(And(Patient(T, X), Doctor(T, Y), assign(T, X, Y))), Not(And(Receptionist(T, X), assign(T, X, Y))), 
                                 Not(And(ThirdParty(T, X), Patient(T, Y), assign(T, X, Y))), Not(And(MedicalManager(T, X), Doctor(T, Y), assign(T, X, Y))), 
                                 And(MedicalManager(T, X), Nurse(T, Y), assign(T, X, Y))))
B2 = [0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1]
# numbers= [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
# positives= [2, 3, 4, 5, 11] negatives= [0, 1, 6, 7, 8, 9, 10]

#print(str(table.lookup_complex(U2, B2, size))) # [3, 5]
#print(str(table.naive(U2, size))) # U2=[5] 

table.compare(U2, B2, size, 2)
### ==================

