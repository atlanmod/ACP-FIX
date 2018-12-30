# -------------------
# 30/12/2018
# test Table ...pour Shaikh2010
# -------------------

### -------------
from Removing import * #@UnusedWildImport
from time import * #@UnusedWildImport

# version sans sous-typage
Data = DeclareSort('Data')
Person = DeclareSort('Person')

root = Const('root', Person)
tech = Const('tech', Person)
data = Const('data', Data)

table = Removing() 
#table = Iterative() 
# Variables
table.add_variable("A", Person)
table.add_variable("C", Person)
table.add_variable("D", Data)
A = table.get_variable(0)
C = table.get_variable(1)
D = table.get_variable(2)

#  predicates 
rights = Function('rights', Person, Data, BoolSort()) 
pread = Function('pread', Person, Data, BoolSort()) 
pwrite = Function('pwrite', Person, Data, BoolSort()) 
pdelete = Function('pdelete', Person, Data, BoolSort()) 
person = Function('person', Person, BoolSort()) 
administrator = Function('administrator', Person, BoolSort()) 
technician = Function('technician', Person, BoolSort()) 
delegate = Function('delegate', Person, Person, BoolSort()) 

# subtyping 
table.add_rule(administrator(A), person(A)) #0
table.add_rule(technician(A), person(A))  #1
# # explicit unsafe
table.add_rule(And(administrator(A), technician(A)), False) #2
# # rights
table.add_rule(rights(A, D), And(pread(A, D), pwrite(A, D), pdelete(A, D))) #3
table.add_rule(administrator(A), rights(A, D)) #4
table.add_rule(technician(C), And(pread(C, D), pwrite(C, D))) #5
table.add_rule(And(administrator(A), technician(C), delegate(A, C)), rights(C, D)) #6
# # # delete only for administrators
table.add_rule(pdelete(A, D), administrator(A)) #7

#### --------------- 
size = 8 #
table.analyze()
table.compute_table(size)
# print ("rules= " + str(len(table.correct)) + " safe= " + str(len(table.safe)) + " unsafe= " + str(len(table.unsafe)))
#print (str(table))
#table.check(size)
################# check it with size=8
#  ----------- Unsafe -------------- 
# UNSAFE [1] <[And(administrator(A), technician(A))] => False>
# UNSAFE [0, 0, 1] <[Not(And(administrator(A), technician(A))), Not(rights(A, D)), administrator(A)] => False>
# UNSAFE [0, 1, 1, 0, 0, 0] <[Not(And(administrator(A), technician(A))), rights(A, D), administrator(A), Not(technician(C)), Not(And(administrator(A), technician(C), delegate(A, C))), Not(pdelete(A, D))] => False>
# UNSAFE [0, 1, 0, 1, 0, 1] <[Not(And(administrator(A), technician(A))), rights(A, D), Not(administrator(A)), technician(C), Not(And(administrator(A), technician(C), delegate(A, C))), pdelete(A, D)] => False>
# UNSAFE [0, 1, 0, 1, 0, 0] <[Not(And(administrator(A), technician(A))), rights(A, D), Not(administrator(A)), technician(C), Not(And(administrator(A), technician(C), delegate(A, C))), Not(pdelete(A, D))] => False>
# UNSAFE [0, 1, 0, 0, 0, 1] <[Not(And(administrator(A), technician(A))), rights(A, D), Not(administrator(A)), Not(technician(C)), Not(And(administrator(A), technician(C), delegate(A, C))), pdelete(A, D)] => False>
# UNSAFE [0, 1, 0, 0, 0, 0] <[Not(And(administrator(A), technician(A))), rights(A, D), Not(administrator(A)), Not(technician(C)), Not(And(administrator(A), technician(C), delegate(A, C))), Not(pdelete(A, D))] => False>
# UNSAFE [0, 0, 0, 1, 0, 1] <[Not(And(administrator(A), technician(A))), Not(rights(A, D)), Not(administrator(A)), technician(C), Not(And(administrator(A), technician(C), delegate(A, C))), pdelete(A, D)] => False>
# UNSAFE [0, 0, 0, 0, 0, 1] <[Not(And(administrator(A), technician(A))), Not(rights(A, D)), Not(administrator(A)), Not(technician(C)), Not(And(administrator(A), technician(C), delegate(A, C))), pdelete(A, D)] => False>

#### first one explicit unsafe 
U0 = Exists(table.variables, And(administrator(A), technician(A)))
UB0 = [1]
# numbers= [2, 3, 4, 5, 6, 7, 0, 1]
# positives= [2] negatives= []

# print(str(table.lookup_complex(U0, UB0, size))) # [2] 
#print(str(table.naive(U0, size))) # [2] 
table.compare(U0, UB0, size, 1) 

#### 
U1 = Exists(table.variables, And(Not(And(administrator(A), technician(A))), Not(rights(A, D)), administrator(A)))
UB1 = [0, 0, 1]
# numbers= [2, 3, 4, 5, 6, 7, 0, 1]

# print(str(table.lookup_complex(U1, UB1, size))) # [4] 
#print(str(table.naive(U1, size))) # [4]
table.compare(U1, UB1, size, 1) 

#### 
U2 = Exists(table.variables, And(Not(And(administrator(A), technician(A))), rights(A, D), administrator(A), Not(technician(C)), 
                                 Not(And(administrator(A), technician(C), delegate(A, C))), Not(pdelete(A, D))))
UB2 = [0, 1, 1, 0, 0, 0]
# numbers= [2, 3, 4, 5, 6, 7, 0, 1]
# positives= [3, 4] negatives= [2, 5, 6, 7]

# print(str(table.lookup_complex(U2, UB2, size))) # [3] 
#print(str(table.naive(U2, size))) # [3] 
table.compare(U2, UB2, size, 1) 

#### 
U3 = Exists(table.variables, And(Not(And(administrator(A), technician(A))), rights(A, D), Not(administrator(A)), technician(C), 
                                 Not(And(administrator(A), technician(C), delegate(A, C))), pdelete(A, D)))
UB3 = [0, 1, 0, 1, 0, 1]
# numbers= [2, 3, 4, 5, 6, 7, 0, 1]

#print(str(table.lookup_complex(U3, UB3, size))) # [7] 
#print(str(table.naive(U3, size))) # [7] 
table.compare(U3, UB3, size, 1) 

#### 
U4 = Exists(table.variables, And(Not(And(administrator(A), technician(A))), rights(A, D), Not(administrator(A)), technician(C), 
                                 Not(And(administrator(A), technician(C), delegate(A, C))), Not(pdelete(A, D))))
UB4 = [0, 1, 0, 1, 0, 0]
# numbers= [2, 3, 4, 5, 6, 7, 0, 1]

#print(str(table.lookup_complex3(U4, UB4, size))) # [3] 
#print(str(table.naive(U4, size))) # [3] 
table.compare(U4, UB4, size, 1) 

#### 
U5 = Exists(table.variables, And(Not(And(administrator(A), technician(A))), rights(A, D), Not(administrator(A)), Not(technician(C)), 
                                 Not(And(administrator(A), technician(C), delegate(A, C))), pdelete(A, D)))
UB5 = [0, 1, 0, 0, 0, 1]
# numbers= [2, 3, 4, 5, 6, 7, 0, 1]

#print(str(table.lookup_complex(U5, UB5, size))) # [7] 
#print(str(table.naive(U5, size))) # [7] 
table.compare(U5, UB5, size, 1) 

#### 
U6 = Exists(table.variables, And(Not(And(administrator(A), technician(A))), rights(A, D), Not(administrator(A)), Not(technician(C)), 
                                 Not(And(administrator(A), technician(C), delegate(A, C))), Not(pdelete(A, D))))
UB6 = [0, 1, 0, 0, 0, 0]
# numbers= [2, 3, 4, 5, 6, 7, 0, 1]

#print(str(table.lookup_complex(U6, UB6, size))) # [3] 
#print(str(table.naive(U6, size))) # [3] 
table.compare(U6, UB6, size, 1) 

#### 
U7 = Exists(table.variables, And(Not(And(administrator(A), technician(A))), Not(rights(A, D)), Not(administrator(A)), technician(C),
                                  Not(And(administrator(A), technician(C), delegate(A, C))), pdelete(A, D)))
UB7 = [0, 0, 0, 1, 0, 1]
# numbers= [2, 3, 4, 5, 6, 7, 0, 1]

#print(str(table.lookup_complex(U7, UB7, size))) # [7]  
#print(str(table.naive(U7, size))) # [7] 
table.compare(U7, UB7, size, 1) 

#### 
U8 = Exists(table.variables, And(Not(And(administrator(A), technician(A))), Not(rights(A, D)), Not(administrator(A)), Not(technician(C)), 
                                 Not(And(administrator(A), technician(C), delegate(A, C))), pdelete(A, D)))
UB8 = [0, 0, 0, 0, 0, 1]
# numbers= [2, 3, 4, 5, 6, 7, 0, 1]

#print(str(table.lookup_complex(U8, UB8, size))) # [7] 
#print(str(table.naive(U8, size))) # [7] 
table.compare(U8, UB8, size, 1) 
