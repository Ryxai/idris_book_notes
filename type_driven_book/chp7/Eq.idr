
data Matter = Solid | Liquid | Gas

Eq Matter where
  (==) Solid Solid = True 
  (==) Liquid Liquid = True 
  (==) Gas Gas = True 
  (==) _ _ = False

  (/=) x y = not (x == y)

occurences : Eq ty => (item : ty) -> (values : List ty) -> Nat
occurences item [] = 0
occurences item (value :: values) = case value == item of
                                         False => occurences item values
                                         True => 1 + occurences item values

data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

Eq elem => Eq (Tree elem) where
  (==) Empty Empty = True
  (==) (Node left e right) (Node left' e' right')
      = left == left' && e == e' && right == right'
  (==) _ _ = False
