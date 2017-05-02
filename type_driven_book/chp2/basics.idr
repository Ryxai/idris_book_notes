double : Num ty => ty -> ty
double x = x + x

add : Num ty => ty -> ty -> ty
add x y = x + y

identity : ty -> ty
identity x = x

twice: (a -> a) -> a -> a
twice f x = f (f x)

quadruple : Num a => a -> a
quadruple = twice double

longer : String -> String -> Nat
longer word1 word2
  = let len1 = length word1
        len2 = length word2 in
        if len1 > len2 then len1 else len2

palindrome : Nat -> String -> Bool
palindrome delim str
  = let len = length str
        forwards = toLower str
        backwards = reverse (toLower str) in
    if len > delim then forwards == backwards else False

counts : String -> (Nat, Nat)
counts str = (length (words str), length str)

top_ten : Ord a => List a -> List a
top_ten lst = take 10 (reverse (sort lst))

over_length : Nat -> List String -> Nat
over_length delim strs = length (
  filter (\x : String => length x > delim) strs) 
