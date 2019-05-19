import Data.Primitives.Views
data InfList : Type -> Type where
     (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

countFrom : Integer -> InfList Integer
countFrom x = x :: Delay (countFrom (x + 1))

getPrefix : (count : Nat) -> InfList a -> List a
getPrefix Z xs = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs

every_other : Stream a -> Stream a
every_other (value1 :: (value2 :: xs)) = value2 :: every_other xs 

Functor InfList where
  map func (value :: xs) = (func value) :: map func xs

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in 
                   (shiftR seed' 2) :: randoms seed'

data Face = Heads | Tails

total
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

square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx
  = approx :: square_root_approx number ((approx + (number / approx)) / 2)

square_root_bound : (max : Nat) -> (number : Double) -> (bound : Double) -> 
                    (approxs : Stream Double) -> Double
square_root_bound Z number bound (value :: xs) = value
square_root_bound (S k) number bound (value :: xs)
  = case compare (number - (value * value)) bound of
      LT => square_root_bound k number bound xs
      _ => value 

square_root : (number : Double) -> Double
square_root number = square_root_bound 100 number 0.00000000001
                                (square_root_approx number number)
