1. The definition of *every_other* follows:
```idris
every_other : Stream a -> Stream a
every_other (value1 :: (value2 :: xs)) = value2 :: every_other xs 
```
2. The definition of *Functor* for *InfList* follows:
```idris
Functor InfList where
  map func (value :: xs) = (func value) :: map func xs
```
3. The definition of *coinFlips* follows:
```idris
coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips Z xs = []
coinFlips (S k) (value :: xs) = getFace value :: coinFlips k xs 
  where
    getFace : Int -> Face
    getFace x with (divides x 2)
      getFace ((2 * div) + rem) | (DivBy prf)
      = case rem of
             0 => Heads
             _ => Tails
```
4. The definition of *square_root_approx* follows:
```idris
square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx
  = approx :: square_root_approx number ((approx + (number / approx)) / 2)
```
5. The definition of *square_root_bound* follows:
```idris
square_root_bound : (max : Nat) -> (number : Double) -> (bound : Double) -> 
                    (approxs : Stream Double) -> Double
square_root_bound Z number bound (value :: xs) = value
square_root_bound (S k) number bound (value :: xs)
  = case compare (number - (value * value)) bound of
      LT => square_root_bound k number bound xs
      _ => value 
```
