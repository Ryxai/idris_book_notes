# Chapter 4 Exercises
1. The *listToTree* function is defined below
```idris
listToTree : Ord a => List a -> Tree a
listToTree [] = Empty
listToTree (x :: xs) = insert x (listToTree xs)
```

2. The *treeToList* function is defined below
```idris
treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node left x right) = treeToList left ++ [x] ++ treeToList right
```

3. The *Expr* type is defined below
```idris
data Expr : Type where
     Val : Int -> Expr
     Add : Expr -> Expr -> Expr
     Sub : Expr -> Expr -> Expr
     Mult : Expr -> Expr -> Expr ``` 4. The *evaluate* function is defined below
```idris
evaluate : Expr -> Int
evaluate (Val x) = x
evaluate (Add x y) = evaluate x + evaluate y
evaluate (Sub x y) = evaluate x - evaluate y
evaluate (Mult x y) = evaluate x * evaluate y
```

5. The *maxMaybe* function is defined below
```idris
maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe Nothing (Just x) = Just x
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) = Just (max x y)
```

6. The *biggestTriangle* function is defined below
```idris
biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive triangle@(Triangle x y)) = Just (area triangle)
biggestTriangle (Primitive (Rectangle x y)) = Nothing
biggestTriangle (Primitive (Circle x)) = Nothing
biggestTriangle (Combine x y) = maxMaybe (biggestTriangle x) (biggestTriangle y)
biggestTriangle (Rotate x y) = biggestTriangle y
biggestTriangle (Translate x y z) = biggestTriangle z
```

7. The updated definition for *Vehicle* and the *wheels* and *refuel* function
follow:
```idris
data Vehicle : PowerSource -> Type where
  Unicycle : Vehicle Pedal
  Bicycle : Vehicle Pedal
  Motorcycle : (fuel : Nat) -> Vehicle Petrol
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol

wheels : Vehicle power -> Nat
wheels Unicycle = 1
wheels Bicycle = 2
wheels (Motorcycle fuel) = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Motorcycle fuel) = Motorcycle 50
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
```

8. The updated definition for *Vehicle* and the *wheels* and *refuel* function
follow:
```idris
data Vehicle : PowerSource -> Type where
  Unicycle : Vehicle Pedal
  Bicycle : Vehicle Pedal
  Motorcycle : (fuel : Nat) -> Vehicle Petrol
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol
  Tram : (battery : Nat) -> Vehicle Electic
  ElectricCar : (battery : nat) -> Vehicle Electic

wheels : Vehicle power -> Nat
wheels Unicycle = 1
wheels Bicycle = 2
wheels (Motorcycle fuel) = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels (Tram battery) = 16
wheels (ElectricCar battery) = 4

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Motorcycle fuel) = Motorcycle 50
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel (Tram battery) = Tram 1000
refuel (ElectricCar battery) = ElectricCar 300
```

9. The type of the *take* function for a *Vect* is as follows:
```idris
vectTake : (n : Nat) -> Vect (n + m) a -> Vect n a
```

10. The definition of the *vectTake* function is as follows:
```idris
vectTake : (n : Nat) -> Vect (n + m) a -> Vect n a
vectTake Z xs = []
vectTake (S k) (x :: xs) = x :: vectTake k xs
```

11. The *sumEntries* function is defined as follows:
```idris
sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries pos [] [] = Nothing
sumEntries 0 (x :: xs) (y :: ys) = Just (x + y)
sumEntries pos (x :: xs) (y :: ys) = sumEntries (pos - 1) xs ys
```
Or alternatively as
```idris
altSumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
altSumEntries {n} pos xs ys = case integerToFin pos n of
                                   Nothing => Nothing
                                   (Just x) => Just (index x xs + index x ys)
```
12. Adding a *size* command to the DataStore application we have:
```idris
module Main
import Data.Vect

data DataStore : Type where
     MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size' items') = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size store) newitem = MkData _ (addToData store)
  where
    addToData : Vect oldsize String -> Vect (S oldsize) String
    addToData [] = [newitem]
    addToData (x :: xs) = x :: addToData xs

data Command = Add String
             | Get Integer
             | Size
             | Quit

parseCommand : String -> String -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just (Get (cast val))
parseCommand "size" _ = Just Size
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) ->
           Maybe (String, DataStore)
getEntry pos store
    = let store_items = items store in
          case integerToFin pos (size store) of
               Nothing => Just ("Out of range\n", store)
               Just id => Just (index id (items store) ++ "\n", store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
    = case parse input of
           Nothing => Just ("Invalid command\n", store)
           Just (Add item) =>
              Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
           Just (Get pos) => getEntry pos store
           Just Size => Just ("Size: " ++ show (size store) ++ "\n", store)
           Just Quit => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
```
13. Adding a *search* command to the *DataStore* application we have:
```idris
module Main
import Data.Vect

data DataStore : Type where
     MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size' items') = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size store) newitem = MkData _ (addToData store)
  where
    addToData : Vect oldsize String -> Vect (S oldsize) String
    addToData [] = [newitem]
    addToData (x :: xs) = x :: addToData xs

data Command = Add String
             | Get Integer
             | Size
             | Search String
             | Quit

parseCommand : String -> String -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just (Get (cast val))
parseCommand "size" _ = Just Size
parseCommand "search" val = Just (Search val)
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) ->
           Maybe (String, DataStore)
getEntry pos store
    = let store_items = items store in
          case integerToFin pos (size store) of
               Nothing => Just ("Out of range\n", store)
               Just id => Just (index id (items store) ++ "\n", store)

displayItems : String -> Vect _ String -> String
displayItems substr [] = ""
displayItems substr (str :: strs) = if isInfixOf substr str
                              then str ++ "\n" ++ displayItems substr strs
                              else displayItems substr strs

getMatchingItems : (val : String) -> (store : DataStore) -> Maybe (String, DataStore)
getMatchingItems val store = Just (displayItems val (items store), store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
    = case parse input of
           Nothing => Just ("Invalid command\n", store)
           Just (Add item) =>
              Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
           Just (Get pos) => getEntry pos store
           Just Size => Just ("Size: " ++ show (size store) ++ "\n", store)
           Just (Search val) => getMatchingItems val store
           Just Quit => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
```
14. Updating the *search* function to include the index of the element we get:
```idris
module Main
import Data.Vect

data DataStore : Type where
     MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size' items') = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size store) newitem = MkData _ (addToData store)
  where
    addToData : Vect oldsize String -> Vect (S oldsize) String
    addToData [] = [newitem]
    addToData (x :: xs) = x :: addToData xs

data Command = Add String
             | Get Integer
             | Size
             | Search String
             | Quit

parseCommand : String -> String -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just (Get (cast val))
parseCommand "size" _ = Just Size
parseCommand "search" val = Just (Search val)
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) ->
           Maybe (String, DataStore)
getEntry pos store
    = let store_items = items store in
          case integerToFin pos (size store) of
               Nothing => Just ("Out of range\n", store)
               Just id => Just (index id (items store) ++ "\n", store)

displayItems : String -> Vect n String -> String
displayItems {n = Z} x [] = ""
displayItems {n = (S len)} substr (str :: strs) =
  if isInfixOf substr str then
    (show len) ++ ": " ++ str ++ "\n" ++ (displayItems substr strs) else
    displayItems substr strs


getMatchingItems : (val : String) -> (store : DataStore) -> Maybe (String, DataStore)
getMatchingItems val store = Just (displayItems val (reverse (items store)), store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
    = case parse input of
           Nothing => Just ("Invalid command\n", store)
           Just (Add item) =>
              Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
           Just (Get pos) => getEntry pos store
           Just Size => Just ("Size: " ++ show (size store) ++ "\n", store)
           Just (Search val) => getMatchingItems val store
           Just Quit => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
```

