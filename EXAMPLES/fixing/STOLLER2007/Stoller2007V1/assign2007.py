# -------------------
# 15/9/2018
# RBAC2 from http://www3.cs.stonybrook.edu/~stoller/ccs2007/
# -------------------
# see healthcare2007.py
# Here focus on can_assign rule and adding the unsafe rule
### test simplification
### not really useful as fix but testing simplification
### -------------
### With time we consider it as next step 

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

### for action (no relation known between them)
view = Function('view', IntSort(), Person, Resource, BoolSort())
add = Function('add',  IntSort(), Person, Resource, BoolSort())
modify = Function('modify',  IntSort(), Person, Resource, BoolSort())
access = Function('access',  IntSort(), Person, Resource, BoolSort())
enter = Function('enter',  IntSort(), Person, Resource, BoolSort())
update = Function('update',  IntSort(), Person, Resource, BoolSort())
create = Function('create',  IntSort(), Person, Resource, BoolSort())
sign = Function('sign',  IntSort(), Person, Resource, BoolSort())
### for resources
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
revoke = Function('can_revoke',  IntSort(), Person, Person, BoolSort()) 

# -------------------------------
#### can assign role(X) and otherrole*(Y) => newrole(Y) (13)
# can_assign(Doctor, true, ThirdParty)
table.add_rule(And(Doctor(T, X), assign(T, X, Y)), ThirdParty(T+1, Y)) #1 
# # # # can_assign(Doctor, Doctor, ReferredDoctor)
table.add_rule(And(Doctor(T, X), Doctor(T, Y), assign(T, X, Y)), ReferredDoctor(T+1, Y)) #2 
# # 
# # # can_assign(Manager, true, Employee)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), Employee(T+1, Y))  #3 
# # # can_assign(Manager, true, Receptionist)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), Receptionist(T+1, Y)) #4 
# # # can_assign(Manager, true, Nurse)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), Nurse(T+1, Y))  #5 
# # can_assign(Manager, true, Doctor)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), Doctor(T+1, Y)) #6 
# # # 
# # # can_assign(Patient, true, Agent)
table.add_rule(And(Patient(T, X), assign(T, X, Y)), Agent(T+1, Y)) #7 
# # # can_assign(Patient, Doctor, PrimaryDoctor)
table.add_rule(And(Patient(T, X), Doctor(T, Y), assign(T, X, Y)), PrimaryDoctor(T+1, Y)) # 8 
# # 
# # can_assign(Receptionist, true, Patient)
table.add_rule(And(Receptionist(T, X), assign(T, X, Y)), Patient(T+1, Y)) # 9 
# # 
# # can_assign(ThirdParty, Patient, PatientWithTPC)
table.add_rule(And(ThirdParty(T, X), Patient(T, Y), assign(T, X, Y)), PatientWithTPC(T+1, Y)) #10 
# # 
# # can_assign(MedicalManager, Doctor, MedicalTeam)
table.add_rule(And(MedicalManager(T, X), Doctor(T, Y), assign(T, X, Y)), MedicalTeam(T+1, Y)) #11 
# # can_assign(MedicalManager, Nurse, MedicalTeam)
table.add_rule(And(MedicalManager(T, X), Nurse(T, Y), assign(T, X, Y)), MedicalTeam(T+1, Y)) #12 
# # can_assign(Manager, true, MedicalManager)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), MedicalTeam(T+1, Y)) #13
# # --------------------------------------------

####

# ### ===============
start = clock()
size =  13
table.compute_table(size) 
# with improve without T rules= 21 safe= 91 unsafe= 8 time: 11 built= 374 nodes= 25924
# rules= 13 safe= 119 unsafe= 0 time: 11
#table.check(size)

# # ---
print ("rules= " + str(len(table.correct)) + " safe= " + str(len(table.safe)) 
        + " unsafe= " + str(len(table.unsafe)) + " time: " + str(floor(clock()-start))) # + " built= " + str(table.built) + " nodes= " + str(table.count_nodes()))
print(str(table))
## ===================

