import Data.Vect

tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case integerToFin i n of
                         Nothing => Nothing
                         (Just idx) => Just (index idx xs)

vectTake : (n : Nat) -> Vect (n + m) a -> Vect n a
vectTake Z xs = []
vectTake (S k) (x :: xs) = x :: vectTake k xs

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries pos [] [] = Nothing
sumEntries 0 (x :: xs) (y :: ys) = Just (x + y)
sumEntries pos (x :: xs) (y :: ys) = sumEntries (pos - 1) xs ys

altSumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
altSumEntries {n} pos xs ys = case integerToFin pos n of
                                   Nothing => Nothing
                                   (Just x) => Just (index x xs + index x ys)

