# -------------------
# 15/10/2018
# RBAC2 from http://www3.cs.stonybrook.edu/~stoller/ccs2007/
# -------------------
# see healthcare2007.py
# Here focus on revoke rules and adding the unsafe rule
### without simplification
### encoding revoke: similar to assign
### assign(Doctor, true, ThirdParty)
### table.add_rule(Doctor(X), revoke(X, Y))
### seems not sufficient !!!
### needs assign conditions and role is lost ?
### Version with discrete time, need to condition each revoke application
### else we get many unsafe problems
### ---------------

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
table.add_variable("P", IntSort()) # linear time
X = table.get_variable(0)
R = table.get_variable(1)
Y = table.get_variable(2)
T = table.get_variable(3)
P = table.get_variable(4)

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

# ****************************************
# ARBAC POLICY: revoke
# 
# for each rule assign(r_a, c, r), there is a corresponding rule
# revoke(r_a, r), except that a doctor, not a receptionist, can revoke
# the Patient role.  this reflects the policy that a patient must be
# discharged from the facility by a doctor.  or, we could make the patient
# role irrevocable.

# **************************************** # revoke  (13)
# assign(Doctor, true, ThirdParty)
table.add_rule(And(Doctor(T, X), revoke(T, X, Y), (P < T), assign(P, X, Y), Not(assign(T, X, Y))), Not(ThirdParty(T+1, Y)))
# assign(Doctor, Doctor, ReferredDoctor)
table.add_rule(And(Doctor(T, X), revoke(T, X, Y), (P < T), assign(P, X, Y), Not(assign(T, X, Y))), Not(ReferredDoctor(T+1, Y)))
# 
# assign(MedicalManager, Doctor, MedicalTeam)
table.add_rule(And(MedicalManager(T, X),  revoke(T, X, Y), (P < T), assign(P, X, Y), Not(assign(T, X, Y))), Not(MedicalTeam(T+1, Y)))
# assign(MedicalManager, Nurse, MedicalTeam)
table.add_rule(And(MedicalManager(T, X), revoke(T, X, Y), (P < T), assign(P, X, Y), Not(assign(T, X, Y))),Not(MedicalTeam(T+1, Y)))
# 
# assign(Manager, true, Employee)
table.add_rule(And(Manager(T, X), revoke(T, X, Y), (P < T), assign(P, X, Y), Not(assign(T, X, Y))), Not(Employee(T+1, Y)))
# assign(Manager, true, MedicalManager)
table.add_rule(And(Manager(T, X), revoke(T, X, Y), (P < T), assign(P, X, Y), Not(assign(T, X, Y))), Not(MedicalTeam(T+1, Y)))
# assign(Manager, true, Receptionist)
table.add_rule(And(Manager(T, X), revoke(T, X, Y), (P < T), assign(P, X, Y), Not(assign(T, X, Y))), Not(Receptionist(T+1, Y)))
# assign(Manager, true, Nurse)
table.add_rule(And(Manager(T, X), revoke(T, X, Y), (P < T), assign(P, X, Y), Not(assign(T, X, Y))), Not(Nurse(T+1, Y)))
# assign(Manager, true, Doctor)
table.add_rule(And(Manager(T, X), revoke(T, X, Y), (P < T), assign(P, X, Y), Not(assign(T, X, Y))), Not(Doctor(T+1, Y)))
# 
# assign(Patient, true, Agent)
table.add_rule(And(Patient(T, X), revoke(T, X, Y), (P < T), assign(P, X, Y), Not(assign(T, X, Y))), Not(Agent(T+1, Y)))
# assign(Patient, Doctor, PrimaryDoctor)
table.add_rule(And(Patient(T, X), revoke(T, X, Y), (P < T), assign(P, X, Y), Not(assign(T, X, Y))), Not(PrimaryDoctor(T+1, Y)))
# 
# assign(Receptionist, true, Patient)
### table.add_rule(And(Receptionist(T, X), revoke(T, X, Y)), Patient(T, Y))
### the newone ?
table.add_rule(And(Doctor(T, X), Not(Receptionist(T, X)), revoke(T, X, Y), (P < T), assign(P, X, Y), Not(assign(T, X, Y))), Patient(T+1, Y))
# 
# assign(ThirdParty, Patient, PatientWithTPC)
table.add_rule(And(ThirdParty(T, X), revoke(T, X, Y), (P < T), assign(P, X, Y), Not(assign(T, X, Y))), Not(PatientWithTPC(T+1, Y)))
# --------------------------------------------

# ### ===============
start = clock()
size = 13  
table.compute_table(size) 
#table.check(size)
print(str(table))
print ("rules= " + str(len(table.correct)) + " safe= " + str(len(table.safe)) 
       + " unsafe= " + str(len(table.unsafe)) + " time: " + str(floor(clock()-start))) # + " built= " + str(table.built))
##table.quine()
## ===================
### rules= 13 safe= 47 unsafe= 0 time: 7

