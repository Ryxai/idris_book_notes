1. The definition for *takeN* follows:
```idris
takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) with (takeN k xs)
  takeN (S k) (x :: xs) | Fewer = Fewer
  takeN (S k) (x :: (n_xs ++ rest)) | (Exact n_xs) = Exact (x :: n_xs)
```
2. The definition of *halves* follows:
```idris
halves : List a -> (List a, List a)
halves xs with (takeN (div (length xs) 2) xs)
  halves xs | Fewer = (xs, [])
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)
```
3.
