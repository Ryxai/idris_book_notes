import Data.Vect

{-myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse {n = S k} (x :: xs) = let result = myReverse xs ++ [x] in
                                    rewrite plusCommutative 1 k in result-}



{-myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse (x :: xs) = reverseProof (myReverse xs ++ [x])
  where
    reverseProof : Vect (len + 1) elem -> Vect (S len) elem
    reverseProof {len} result = rewrite plusCommutative 1 len in result-}

myAppend_nil : Vect m elem -> Vect (plus m 0) elem
myAppend_nil {m} xs = rewrite plusZeroRightNeutral m in xs

myAppend_xs : Vect (S (m + len)) elem -> Vect (plus m (S len)) elem
myAppend_xs {m} {len} xs = rewrite sym (plusSuccRightSucc m len) in xs

myAppend : Vect n elem -> Vect m elem -> Vect (m + n) elem
myAppend [] ys = myAppend_nil ys
myAppend (x :: xs) ys = myAppend_xs (x :: myAppend xs ys)

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = sym (plusZeroRightNeutral m)
myPlusCommutes (S k) m = rewrite myPlusCommutes k m in plusSuccRightSucc m k

myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
  where reverse' : Vect n a -> Vect m a -> Vect (n + m) a
        reverse' {n} acc [] = rewrite (plusZeroRightNeutral n) in acc
        reverse' {n} {m = S k} acc (x :: xs) =
          rewrite sym (plusSuccRightSucc n k) in (reverse' (x::acc) xs)

