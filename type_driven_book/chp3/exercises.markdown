# Section 1
1. A function definition *length* defined
```idris
my_length : List a -> Nat
my_length [] = 0
my_length (x :: xs) = 1 + my_length xs
```

2. A function definition for *reverse* defined
```idris
my_reverse : List a -> List a
my_reverse [] = []
my_reverse (x :: xs) = reverse xs ++ [x]
```

3. A function definition for *map* for *Lists* defined
```idris
my_map : (a -> b) -> List a -> List b
my_map f [] = []
my_map f (x :: xs) = f x :: map f xs
```
4. A function definition for *map* for *Vectors* defined
```idris
my_vect_map : (a -> b) -> Vect k a -> Vect k b
my_vect_map f [] = []
my_vect_map f (x :: xs) = f x :: map f xs
```
# Section 2
1. Reimplementing *transposeMat* with *zipWith* defined below
```idris
createEmpties : Vect n (Vect 0 elem)
createEmpties = replicate _ []

transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = createEmpties
transposeMat (x :: xs) = let xsTrans = transposeMat xs in
                         zipWith (\x, y => x :: y) x xsTrans
```

2. The implementation for *addMatrix* follows
```idris
addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = zipWith (\x, y => x + y) x y :: addMatrix xs ys
```

3. The implementation for *multMatrix* follows
```idris
multMatrix : Num a => Vect n (Vect m a) ->
                      Vect m (Vect p a) ->
                      Vect n (Vect p a)
multMatrix xs ys = multHelper xs (transposeMat ys)
  where
        dot : Num a => Vect k a -> Vect k a -> a
        dot xs ys = sum $ map (\ (s1, s2) => s1 * s2) (zip xs ys)

        multHelper : Num a => Vect n (Vect m a) ->
                              Vect p (Vect m a) ->
                              Vect n (Vect p a)
        multHelper [] _ = []
        multHelper (x :: xs) ys = map (dot x) ys:: multHelper xs ys
```
