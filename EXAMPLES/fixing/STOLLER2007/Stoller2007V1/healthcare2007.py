# -------------------
# 15/10/2018
# RBAC2 from http://www3.cs.stonybrook.edu/~stoller/ccs2007/
# -------------------
### without simplification
### encoding revoke: similar to assign
### but needs to add extra condition and discrete time
# -----------------
### RQ1: avoiding Not(assign) in revoke rules we get conflicting problems 
### in conjunction with the assign rules

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

### ---------------------------------------------- (8+3)
### roles hierarchy : we add all because could cause problem (8)
# Employee > Nurse 
#          > Doctor
#          > Receptionist
#      > MedicalManager
#          > Manager
#  to include Patient > PatientWithTPC,Similarly, Doctor > ReferredDoctor  and Doctor > PrimaryDoctor 
table.add_rule(Nurse(T, X), Employee(T, X))  #D
table.add_rule(Doctor(T, X), Employee(T, X))
table.add_rule(Receptionist(T, X), Employee(T, X)) #E
table.add_rule(MedicalManager(T, X), Employee(T, X))
table.add_rule(Manager(T, X), Employee(T, X))
# ### qualified as unnecessary 
table.add_rule(Patient(T, X), PatientWithTPC(T, X))  #A 
# ### qualified as unnecessary 
table.add_rule(Doctor(T, X), ReferredDoctor(T, X))  #B  
# ### qualified as unnecessary 
### table.add_rule(Doctor(T, X), PrimaryDoctor(T, X))   #C remove it
# # ## mutual exclusion of roles (3)
table.add_rule(And(Patient(T, X), PrimaryDoctor(T, X)), False) #1 
table.add_rule(And(Receptionist(T, X), Doctor(T, X)), False) #2
table.add_rule(And(Nurse(T, X), Doctor(T, X)), False) #3
### ----
 
# ---------------------permission assignement  (24)
### role(X) and resource(Y) => action(X, Y) 
# PA(Doctor, [View, OldMedicalRecords])
table.add_rule(And(Doctor(T, X),  OldMedicalRecords(T, R)), view(T, X, R))
# PA(Doctor, [View, RecentMedicalRecords])
table.add_rule(And(Doctor(T, X),  RecentMedicalRecords(T, R)), view(T, X, R))
# PA(Doctor, [View, PrivateNotes])
table.add_rule(And(Doctor(T, X),  PrivateNotes(T, R)), view(T, X, R))
# PA(Doctor, [Add, PrivateNotes])
table.add_rule(And(Doctor(T, X),  PrivateNotes(T, R)), add(T, X, R))
# PA(Doctor, [Add, RecentMedicalRecords])
table.add_rule(And(Doctor(T, X),  RecentMedicalRecords(T, R)), add(T, X, R))
# PA(Doctor, [View, Prescriptions])
table.add_rule(And(Doctor(T, X),  Prescriptions(T, R)), view(T, X, R))
# PA(Doctor, [Modify, Prescriptions])
table.add_rule(And(Doctor(T, X),  Prescriptions(T, R)), modify(T, X, R))
#
# PA(Manager, [Access, PatientPersonalInfo])
table.add_rule(And(Manager(T, X),  PatientPersonalInfo(T, R)), access(T, X, R))
# PA(Manager, [Access, PatientFinancialInfo])
table.add_rule(And(Manager(T, X),  PatientFinancialInfo(T, R)), access(T, X, R))
# PA(Manager, [Access, PatientMedicalInfo])
table.add_rule(And(Manager(T, X),  PatientMedicalInfo(T, R)), access(T, X, R))
# PA(Manager, [Enter, OldMedicalRecords])
table.add_rule(And(Manager(T, X),  OldMedicalRecords(T, R)), enter(T, X, R))
# PA(Manager, [Enter, RecentMedicalRecords])
table.add_rule(And(Manager(T, X),  RecentMedicalRecords(T, R)), enter(T, X, R))
# PA(Manager, [Update, CarePlan])
table.add_rule(And(Manager(T, X),  CarePlan(T, R)), update(T, X, R))
# 
# PA(Receptionist, [Create, Appointment])
table.add_rule(And(Receptionist(T, X),  Appointment(T, R)), create(T, X, R))
# 
# PA(Nurse, [Access, OldMedicalRecords])
table.add_rule(And(Nurse(T, X),  OldMedicalRecords(T, R)), access(T, X, R))
# PA(Nurse, [View, CarePlan])
table.add_rule(And(Nurse(T, X),  CarePlan(T, R)), view(T, X, R))
# PA(Nurse, [Add, ProgressNotes])
table.add_rule(And(Nurse(T, X),  ProgressNotes(T, R)), add(T, X, R))
# PA(Nurse, [View, RecentMedicalRecords])
table.add_rule(And(Nurse(T, X),  RecentMedicalRecords(T, R)), view(T, X, R))
# 
# PA(Patient, (View, [OldMedicalRecords])
table.add_rule(And(Patient(T, X),  OldMedicalRecords(T, R)), view(T, X, R))
# PA(Patient, (View, [RecentMedicalRecords])
table.add_rule(And(Patient(T, X),  RecentMedicalRecords(T, R)), view(T, X, R))
# PA(PatientWithTPC, [View, MedicalRecordsWithThirdPartyInfo])
table.add_rule(And(PatientWithTPC(T, X),  MedicalRecordsWithThirdPartyInfo(T, R)), view(T, X, R))
# PA(Patient, [Sign, LegalAgreement])
table.add_rule(And(Patient(T, X),  LegalAgreement(T, R)), sign(T, X, R))
# PA(Patient, [View, Prescriptions])
table.add_rule(And(Patient(T, X),  Prescriptions(T, R)), view(T, X, R))
# PA(Patient, [View, Bills])
table.add_rule(And(Patient(T, X),  Bills(T, R)), view(T, X, R))
# -------

# ------------------------------- (13)
#### can assign role(X) and otherrole*(Y) => newrole(Y) 
# can_assign(Doctor, true, ThirdParty)
table.add_rule(And(Doctor(T, X), assign(T, X, Y)), ThirdParty(T+1, Y)) #1 
# # # # can_assign(Doctor, Doctor, ReferredDoctor)
table.add_rule(And(Doctor(T, X), Doctor(T, Y), assign(T, X, Y)), ReferredDoctor(T+1, Y)) #2 
# # 
# # can_assign(Manager, true, Employee)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), Employee(T+1, Y))  #3 
# # can_assign(Manager, true, Receptionist)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), Receptionist(T+1, Y)) #4 
# # can_assign(Manager, true, Nurse)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), Nurse(T+1, Y))  #5 
# # can_assign(Manager, true, Doctor)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), Doctor(T+1, Y)) #6 
# # # 
# # can_assign(Patient, true, Agent)
table.add_rule(And(Patient(T, X), assign(T, X, Y)), Agent(T+1, Y)) #7 
# # can_assign(Patient, Doctor, PrimaryDoctor)
table.add_rule(And(Patient(T, X), Doctor(T, Y), assign(T, X, Y)), PrimaryDoctor(T+1, Y)) # 8 
# 
# can_assign(Receptionist, true, Patient)
table.add_rule(And(Receptionist(T, X), assign(T, X, Y)), Patient(T+1, Y)) # 9 
# 
# can_assign(ThirdParty, Patient, PatientWithTPC)
table.add_rule(And(ThirdParty(T, X), Patient(T, Y), assign(T, X, Y)), PatientWithTPC(T+1, Y)) #10 
# 
# can_assign(MedicalManager, Doctor, MedicalTeam)
table.add_rule(And(MedicalManager(T, X), Doctor(T, Y), assign(T, X, Y)), MedicalTeam(T+1, Y)) #11 
# can_assign(MedicalManager, Nurse, MedicalTeam)
table.add_rule(And(MedicalManager(T, X), Nurse(T, Y), assign(T, X, Y)), MedicalTeam(T+1, Y)) #12 
# can_assign(Manager, true, MedicalManager)
table.add_rule(And(Manager(T, X), assign(T, X, Y)), MedicalTeam(T+1, Y)) #13
# --------------------------------------------

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
### RQ1: generate conflicts with assign rules
###table.add_rule(And(Doctor(T, X), revoke(T, X, Y), (P < T), assign(P, X, Y)), Not(ThirdParty(T+1, Y)))
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
size =  60 
##table.analyze() ?
table.compute_table(size) 
table.check(size)
#print(str(table))
print ("rules= " + str(len(table.correct)) + " safe= " + str(len(table.safe)) 
       + " unsafe= " + str(len(table.unsafe)) + " time: " + str(floor(clock()-start))) # + " built= " + str(table.built))


