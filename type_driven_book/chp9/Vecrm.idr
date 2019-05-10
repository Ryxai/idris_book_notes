{-data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : (x : a) -> (xs : Vect k a) -> Vect (S k) a

data Elem : a -> Vect k a -> Type where
  Here : Elem x (x :: xs)
  There : (later : Elem x xs) -> Elem x (y :: xs)

import Data.Vect

removeElem : DecEq a => (value : a) -> (xs : Vect (S n) a) -> Vect n a
removeElem value (x :: xs) = case decEq value x of
                                  (Yes prf) => xs
                                  (No contra) => ?removeElem_rhs_3

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)-}

import Data.Vect

removeElem: (value : a) ->
            (xs : Vect (S n) a) ->
            (prf : Elem value xs) ->
            Vect n a
removeElem value (value :: ys) Here = ys
removeElem value {n = Z} (y :: []) (There later) = absurd later
removeElem value {n = (S k)} (y :: ys) (There later)
                                              = y :: removeElem value ys later
Uninhabited (2 + 2 = 5) where
  uninhabited Refl impossible

removeElem_auto : (value : a) -> (xs : Vect (S n) a) ->
                  {auto prf : Elem value xs} -> Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf

removeElem_alt : (value : a) -> (xs : Vect (S n) a) ->
                 {auto prf: Elem value xs} ->
                 Vect n a
removeElem_alt value (value :: ys) {prf = Here}= ys
removeElem_alt {n = Z} value (y :: []) {prf = (There later)} = absurd later
removeElem_alt {n = (S k)} value (y :: ys) {prf = (There later)}
                                                = y :: removeElem_alt value ys


