AdderType : (numargs : Nat) -> Type
AdderType Z = Int 
AdderType (S k) = (next : Int) -> AdderType k

adder : (numargs : Nat) -> (acc : Int) -> AdderType numargs
adder Z acc = acc 
adder (S k) acc = \next => adder k (next + acc)

TupleVect : (length : Nat) -> (ty : Type) -> Type
TupleVect Z _ = ()
TupleVect (S k) x = (x, TupleVect k x)

test : TupleVect 4 Nat
test = (1,2,3,4,())

