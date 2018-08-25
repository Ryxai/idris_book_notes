data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

Eq Shape where
  (==) (Triangle a b) (Triangle j k) = a == j && b == k
  (==) (Rectangle a b) (Rectangle j k) = a == j && b == k
  (==) (Circle a) (Circle b) = a == b
  (==) _ _ = False

Ord Shape where
  compare shape_l shape_r = compare (area shape_l) (area shape_r)

testShapes : List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4, Rectangle 2 7]
