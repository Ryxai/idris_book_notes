# Chapter 7
1. The definition of the *Eq* implementation for *Shape* follows:
```idris
Eq Shape where
  (==) (Triangle a b) (Triangle j k) = a == j && b == k
  (==) (Rectangle a b) (Rectangle j k) = a == j && b == k
  (==) (Circle a) (Circle b) = a == b
  (==) _ _ = False
```
2. The definition of the *Ord* implementation for *Shape* using the
are follows:
```idris
Ord Shape where
  compare shape_l shape_r = compare (area shape_l) (area shape_r)
```
3. The definition of *Show* for *Expr* follows:
```idris
Show ty => Show (Expr ty) where
  show (Val x) = show x
  show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
  show (Div x y) = "(" ++ show x ++ " / " ++ show y ++ ")"
  show (Abs x) = " |" ++ show x ++ "| "
```
4. The definition of *Eq* for *Expr* follows:
```idris
(Eq ty, Abs ty, Integral ty, Neg ty)=> Eq (Expr ty) where
  (==) x y = eval x == eval y
```
5. The definition of *Cast* for *Expr* follows:
```idris
Cast ty ty where
  cast orig = orig

(Eq tx, Abs tx, Integral tx, Neg tx, Cast tx ty) => Cast (Expr tx) ty where
  cast orig = cast (eval orig)
```
6. The definition of *Functor* for *Expr* follows:
```idris
Functor Expr where
  map func (Val x) = Val (func x)
  map func (Add x y) = Add (map func x) (map func y)
  map func (Sub x y) = Sub (map func x) (map func y)
  map func (Mul x y) = Mul (map func x) (map func y)
  map func (Div x y) = Div (map func x) (map func y)
  map func (Abs x) = Abs (map func x)
```
7. The definition of *Eq* and *Foldable* for *Vect* follow:
```idris
Eq elem => Eq (Vect n elem) where
  (==) [] [] = True 
  (==) (x :: xs) (y :: ys) = x == y && xs == ys 
  (==) _ _ = False

Foldable (Vect n) where
  foldr func acc [] = acc
  foldr func acc (x :: xs) = func x (foldr func acc xs)
```
