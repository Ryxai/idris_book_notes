allLengths : List String -> List Nat
allLengths strs = map length strs

invert : Bool- > Bool
invert False = True
invert True = False

describeList : List Int -> String
describeList [] = "Empty"
describeList (x :: xs) = "Non-empty, tail = " ++ show xsS
