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
