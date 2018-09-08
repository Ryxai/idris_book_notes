# Chapter 8
1. The definition of *same_cons* follows below:
```idris
same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x ::xs = x :: ys
same_cons Refl = Refl
```
2. The definition of *same_lists* follows below:
```idris
same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl Refl = Refl
```
3. The definition of *ThreeEq* follows:
```idris
data ThreeEq : (a : Nat) -> (b : Nat) -> (c : Nat) -> Type where
  ThreeSame : (num : Nat) -> ThreeEq num num num
```
4. The definition of *allSameS* follows:
```idris
allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS Z Z Z (ThreeSame Z) = ThreeSame (S Z)
allSameS (S k) (S k) (S k) (ThreeSame (S k)) = ThreeSame (S (S k))
```
The type means that if all of the values *x, y, z* and *ThreeEq* are the
same then return the successor value of them. 
5. The definition of *myPlusCommutes* follows:
```idris
myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = sym (plusZeroRightNeutral m)
myPlusCommutes (S k) m = rewrite myPlusCommutes k m in plusSuccRightSucc m k
```
6. The definition of *myReverse* follows:
```idris
myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
  where reverse' : Vect n a -> Vect m a -> Vect (n + m) a
        reverse' {n} acc [] = rewrite (plusZeroRightNeutral n) in acc
        reverse' {n} {m = S k} acc (x :: xs) =
          rewrite sym (plusSuccRightSucc n k) in (reverse' (x::acc) xs)
```
7. The definition of *headUnequal* and *tailUnequal* follows:
```idris
headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> 
    (contra : (x = y) -> Void) -> ((x::xs) = (y::ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
    (contra : (xs = ys) -> Void) -> ((x::xs) = (y::ys)) -> Void
tailUnequal contra Refl = contra Refl
```
8. The definition of *DecEq* for *Vect* follows:
```idris
DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) = case decEq x y of
                                 (Yes Refl) => (case decEq xs ys of
                                                     (Yes Refl) => Yes Refl
                                                     (No contra) => No (tailUnequal contra))
                                 (No contra) => No (headUnequal contra) 
```
