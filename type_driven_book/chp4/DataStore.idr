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
