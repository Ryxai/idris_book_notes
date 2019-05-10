# Chapter 9
1. The definition of *Elem* for *List* follows:
```idris
data Elem : a -> List a -> Type where
  Here : Elem x (x :: xs)
  There : (later : Elem x xs) -> Elem x (y :: xs)
```
2. The definition of *isLast* follows:
```idris
isNotNil : Last [] value -> Void
isNotNil LastOne impossible
isNotNil (LastCons _) impossible

isLastSingleElement : (contra : (x = value) -> Void) -> Last [x] value -> Void
isLastSingleElement contra LastOne = contra Refl
isLastSingleElement _ (LastCons LastOne) impossible
isLastSingleElement _ (LastCons (LastCons _)) impossible

isLastAppend : (contra : Last (y :: xs) value -> Void) -> Last (x :: (y :: xs)) value -> Void
isLastAppend contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No isNotNil
isLast (x :: []) value = case decEq x value of
                              (Yes Refl) => Yes LastOne
                              (No contra) => No (isLastSingleElement contra)
isLast (x :: (y :: xs)) value = case isLast (y :: xs) value of
                                     (Yes LastOne) => Yes (LastCons LastOne)
                                     (Yes (LastCons prf)) => Yes (LastCons (LastCons prf))
                                     (No contra) => No (isLastAppend contra)
```
