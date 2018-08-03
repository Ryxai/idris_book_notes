data Bool = False | True

data Direction = North | South | East | West

turnClockwize : Direction -> Direction
turnClockwize North = East
turnClockwize South = South
turnClockwize East = West
turnClockwize West = North

||| Represents shapes
data Shape = |||A triangle with its base length and height
             Triangle Double Double
           | ||| A rectangle, with its length and height
             Rectangle Double Double
           | ||| A circle with its radius
             Circle Double

{-
data Shape : Type where
     Triangle : Double -> Double -> Shape
     Rectangle : Double -> Double -> Shape
     Circle : Double -> Shape
-}

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture

rectangle : Picture
rectangle = Primitive (Rectangle 20 10)

circle : Picture
circle = Primitive (Circle 5)

triangle : Picture
triangle = Primitive (Triangle 10 10)

testPicture : Picture
testPicture = Combine (Translate 5 5 rectangle)
                      (Combine (Translate 35 5 circle)
                      (Translate 15 25 triangle))

pictureArea : Picture -> Double
pictureArea (Primitive shape) = area shape
pictureArea (Combine pic pic1) = pictureArea pic + pictureArea pic1
pictureArea (Rotate x pic) = pictureArea pic
pictureArea (Translate x y pic) = pictureArea pic

data Infinite = Forever Infinite

safeDivide : Double -> Double -> Maybe Double
safeDivide x y = if y == 0 then Nothing
                           else Just (x / y)

data Either a b = Left a | Right b

data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)
%name Tree tree, tree1

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe Nothing (Just x) = Just x
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) = Just (max x y)

biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive triangle@(Triangle x y)) = Just (area triangle)
biggestTriangle (Primitive (Rectangle x y)) = Nothing
biggestTriangle (Primitive (Circle x)) = Nothing
biggestTriangle (Combine x y) = maxMaybe (biggestTriangle x) (biggestTriangle y)
biggestTriangle (Rotate x y) = biggestTriangle y
biggestTriangle (Translate x y z) = biggestTriangle z

testPic1 : Picture
testPic1 = Combine (Primitive (Triangle 2 3))
                   (Primitive (Triangle 2 4))

testPic2 : Picture
testPic2 = Combine (Primitive (Rectangle 1 3))
                   (Primitive (Circle 4))

