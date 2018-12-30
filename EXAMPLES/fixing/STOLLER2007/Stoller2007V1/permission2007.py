# -------------------
# 15/10/2018
# RBAC2 from http://www3.cs.stonybrook.edu/~stoller/ccs2007/
# -------------------
# other encoding are possible
# we add parameters
# SMER are disjunction rules
# roles are predicates, herarchies are implications
# actions are binary predicates: a person and a resource
# with assign predicate
# Timed version
#----------------------------

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
### can_revoke
revoke = Function('can_revoke',  IntSort(), Person, Person, BoolSort()) 

# ---------------------permission assignement
### role(X) and resource(Y) => action(X, Y)  (24)
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

# ### ===============
start = clock()
size = 24
# ----
table.compute_table(size) 
# rules= 24 safe= 1207 unsafe= 0 time: 130
# ----
print ("rules= " + str(len(table.correct)) + " safe= " + str(len(table.safe)) 
       + " unsafe= " + str(len(table.unsafe)) + " time: " + str(floor(clock()-start))) # + " built= " + str(table.built) + " nodes= " + str(table.count_nodes()))
#print(str(table))

