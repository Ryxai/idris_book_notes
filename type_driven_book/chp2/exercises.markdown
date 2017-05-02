# Chapter 2 Exercises
1. The types of the given examples are
 ```idris
  ("A", "B", "C") : (String, String, String)
  ["A", "B", "C"] : List String
  (('A', "B"), 'C') : ((Char, String), Char)
```

2. The *palindrome* function defined below
```idris
palindrome : String -> Bool
palindrome str = str == reverse str
```
3.  The modified function for ignoring case sensitivity is below
```idris
palindrome : String -> Bool
palindrome str = (toLower str) == reverse (toLower str)
```

4.  The modified function for ignoring small strings is below
```idris
palindrome : String -> Bool
palindrome str
  = let len = length str
        forwards = toLower str
        backwards = reverse (toLower str) in
    if len > 10 then forwards == backwards else False
```

5. The modified function for ignoring strings of user defined length is
below
```idris
palindrome : Nat -> String -> Bool
palindrome delim str
  = let len = length str
        forwards = toLower str
        backwards = reverse (toLower str) in
    if len > delim then forwards == backwards else False
```

6. A function that gets the word and character count as a tuple
defined below
```idris
counts : String -> (Nat, Nat)
counts str = (length (words str), length str)
```

7. A function that gets the top ten values from a list defined below
```idris
top_ten : Ord a => List a -> List a
top_ten lst = take 10 (reverse (sort lst))
```

8. A function that returns the number of strings longer than the given
number of characters defined below
```idris
over_length : Nat -> List String -> Nat
over_length delim strs = length (
  filter (\x : String => length x > delim) strs)
```
