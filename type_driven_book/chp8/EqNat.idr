data EqNat : (num1 : Nat) -> (Num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

sameS : (k : Nat) -> (j : Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS j j (Same j) = Same (S j)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same 0)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              (Just eq) => Just (sameS _ _ eq)

data Vect : Nat -> Type -> Type where 
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case checkEqNat m len of
                                 Nothing => Nothing
                                 (Just (Same len)) => Just input 

same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x ::xs = x :: ys
same_cons Refl = Refl

same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl Refl = Refl

data ThreeEq : (a : Nat) -> (b : Nat) -> (c : Nat) -> Type where
  ThreeSame : (num : Nat) -> ThreeEq num num num

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS Z Z Z (ThreeSame Z) = ThreeSame (S Z)
allSameS (S k) (S k) (S k) (ThreeSame (S k)) = ThreeSame (S (S k))

zeroNotSuc : (0 = S k) -> Void
zeroNotSuc Refl impossible

sucNotZero : (S k = 0) -> Void
sucNotZero Refl impossible

noRec : (contra : (k = j) -> Void) -> (S k = S j) -> Void
noRec contra Refl = contra Refl

decCheckEqNat : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
decCheckEqNat Z Z = Yes Refl
decCheckEqNat Z (S k) = No zeroNotSuc
decCheckEqNat (S k) Z = No sucNotZero
decCheckEqNat (S k) (S j) = case decCheckEqNat k j of
                                 (Yes prf) => Yes (cong prf)
                                 (No contra) => No (noRec contra)

decExactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
decExactLength {m} len input = case decEq m len of
                                (Yes Refl) => Just input 
                                (No contra) => Nothing

headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> 
    (contra : (x = y) -> Void) -> ((x::xs) = (y::ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
    (contra : (xs = ys) -> Void) -> ((x::xs) = (y::ys)) -> Void
tailUnequal contra Refl = contra Refl

DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) = case decEq x y of
                                 (Yes Refl) => (case decEq xs ys of
                                                     (Yes Refl) => Yes Refl
                                                     (No contra) => No (tailUnequal contra))
                                 (No contra) => No (headUnequal contra) 
