# Chapter 6
1. The definition of the *Matrix* type synonym follows:
```idris
Matrix : Nat -> Nat -> Type
Matrix n m = Vect n (Vect m Double)
```
2. The updated definitions for *printf* follow:
```idris
data Format = Number Format
            | Str Format
            | Dble Format
            | Chr Format
            | Lit String Format
            | End

PrintfType : Format -> Type
PrintfType (Number fmt) = (i : Int) -> PrintfType fmt
PrintfType (Dble fmt) = (i : Double) -> PrintfType fmt
PrintfType (Str fmt) = (str: String) -> PrintfType fmt
PrintfType (Chr fmt) = (char : Char) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

printfFmt : (fmt : Format) -> (acc: String) -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Dble fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \str =>  printfFmt fmt (acc ++ str)
printfFmt (Chr fmt) acc = \char => printfFmt fmt (acc ++ show char)
printfFmt (Lit lit fmt) acc = printfFmt fmt (acc ++ lit)
printfFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Dble (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Chr (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
                             Lit lit chars' => Lit (strCons c lit) chars'
                             fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""
```
3. The definition for *TupleVect* follows:
```idris
TupleVect : (length : Nat) -> (ty : Type) -> Type
TupleVect Z _ = ()
TupleVect (S k) x = (x, TupleVect k x)
```
4. The updated definition of *DataStore* to support *Char* follows:
```idris
module Main

import Data.Vect

infixr 5 .+.

data Schema = SString | SInt | SChar | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size store) newitem = MkData schema _ (addToData store)
  where
    addToData : Vect oldsize (SchemaType schema) -> Vect (S oldsize) (SchemaType schema)
    addToData [] = [newitem]
    addToData (x :: xs) = x :: addToData xs

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                              Z => Just (MkData schema _ [])
                              S k => Nothing

data Command : Schema -> Type where
     SetSchema : Schema -> Command schema
     Add : SchemaType schema -> Command schema
     Get : Integer -> Command schema
     Quit : Command schema


parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString input = getQuoted (unpack input)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs)
        = case span (/= '"') xs of
               (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
               _ => Nothing
    getQuoted _ = Nothing
parsePrefix SChar input = case unpack input of
                           [] => Nothing
                           (char :: rest) => Just (char, ltrim (pack rest))
parsePrefix SInt input = case span isDigit input of
                              ("", rest) => Nothing
                              (num, rest) => Just (cast num, ltrim rest)
parsePrefix (schemal .+. schemar) input
    = case parsePrefix schemal input of
           Nothing => Nothing
           Just (l_val, input') =>
                case parsePrefix schemar input' of
                     Nothing => Nothing
                     Just (r_val, input'') => Just ((l_val, r_val), input'')
```
```idris

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema x = case parsePrefix schema x of
                              Nothing => Nothing
                              Just (res, "") => Just res
                              Just _ => Nothing

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs)
    = case xs of
           [] => Just SString
           _ => case parseSchema xs of
                     Nothing => Nothing
                     Just xs_sch => Just (SString .+. xs_sch)
parseSchema ("Int" :: xs)
    = case xs of
           [] => Just SInt
           _ => case parseSchema xs of
                     Nothing => Nothing
                     Just xs_sch => Just (SInt .+. xs_sch)
parseSchema ("Char" :: xs)
    = case xs of
           [] => Just SChar
           _ => case parseSchema xs of
                     Nothing => Nothing
                     Just xs_sch => Just (SChar .+. xs_sch)
parseSchema _ = Nothing

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "add" rest = case parseBySchema schema rest of
                                      Nothing => Nothing
                                      Just restok => Just (Add restok)
parseCommand schema "get" val = case all isDigit (unpack val) of
                                    False => Nothing
                                    True => Just (Get (cast val))
parseCommand schema "quit" "" = Just Quit
parseCommand schema "schema" rest
    = case parseSchema (words rest) of
           Nothing => Nothing
           Just schemaok => Just (SetSchema schemaok)
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = SChar} item = show item
display {schema = (y .+. z)} (iteml, itemr) = display iteml ++ ", " ++
                                              display itemr

getEntry : (pos : Integer) -> (store : DataStore) ->
           Maybe (String, DataStore)
getEntry pos store
    = let store_items = items store in
          case integerToFin pos (size store) of
               Nothing => Just ("Out of range\n", store)
               Just id => Just (display (index id (items store)) ++ "\n", store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
    = case parse (schema store) input of
           Nothing => Just ("Invalid command\n", store)
           Just (Add item) =>
              Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
           Just (SetSchema schema') =>
              case setSchema store schema' of
                   Nothing => Just ("Can't update schema when entries in store\n", store)
                   Just store' => Just ("OK\n", store')
           Just (Get pos) => getEntry pos store
           Just Quit => Nothing

main : IO ()
main = replWith (MkData (SString .+. SString .+. SInt .+. SChar) _ []) "Command: " processInput
```

5.  The updated form of the *DataStore* is defined below:
```idris
module Main

import Data.Vect

infixr 5 .+.

data Schema = SString | SInt | SChar | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size store) newitem = MkData schema _ (addToData store)
  where
    addToData : Vect oldsize (SchemaType schema) -> Vect (S oldsize) (SchemaType schema)
    addToData [] = [newitem]
    addToData (x :: xs) = x :: addToData xs

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                              Z => Just (MkData schema _ [])
                              S k => Nothing

data Command : Schema -> Type where
     SetSchema : Schema -> Command schema
     Add : SchemaType schema -> Command schema
     Get : Integer -> Command schema
     All : Command schema
     Quit : Command schema


parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString input = getQuoted (unpack input)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs)
        = case span (/= '"') xs of
               (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
               _ => Nothing
    getQuoted _ = Nothing
parsePrefix SChar input = case unpack input of
                           [] => Nothing
                           (char :: rest) => Just (char, ltrim (pack rest))
parsePrefix SInt input = case span isDigit input of
                              ("", rest) => Nothing
                              (num, rest) => Just (cast num, ltrim rest)
parsePrefix (schemal .+. schemar) input
    = case parsePrefix schemal input of
           Nothing => Nothing
           Just (l_val, input') =>
                case parsePrefix schemar input' of
                     Nothing => Nothing
                     Just (r_val, input'') => Just ((l_val, r_val), input'')
```
```idris
parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema x = case parsePrefix schema x of
                              Nothing => Nothing
                              Just (res, "") => Just res
                              Just _ => Nothing

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs)
    = case xs of
           [] => Just SString
           _ => case parseSchema xs of
                     Nothing => Nothing
                     Just xs_sch => Just (SString .+. xs_sch)
parseSchema ("Int" :: xs)
    = case xs of
           [] => Just SInt
           _ => case parseSchema xs of
                     Nothing => Nothing
                     Just xs_sch => Just (SInt .+. xs_sch)
parseSchema ("Char" :: xs)
    = case xs of
           [] => Just SChar
           _ => case parseSchema xs of
                     Nothing => Nothing
                     Just xs_sch => Just (SChar .+. xs_sch)
parseSchema _ = Nothing

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "add" rest = case parseBySchema schema rest of
                                      Nothing => Nothing
                                      Just restok => Just (Add restok)
parseCommand schema "get" "" = Just All
parseCommand schema "get" val = case all isDigit (unpack val) of
                                    False => Nothing
                                    True => Just (Get (cast val))
parseCommand schema "quit" "" = Just Quit
parseCommand schema "schema" rest
    = case parseSchema (words rest) of
           Nothing => Nothing
           Just schemaok => Just (SetSchema schemaok)
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = SChar} item = show item
display {schema = (y .+. z)} (iteml, itemr) = display iteml ++ ", " ++
                                              display itemr

getEntry : (pos : Integer) -> (store : DataStore) ->
           Maybe (String, DataStore)
getEntry pos store
    = let store_items = items store in
          case integerToFin pos (size store) of
               Nothing => Just ("Out of range\n", store)
               Just id => Just (display (index id (items store)) ++ "\n", store)



getAllEntries : (store : DataStore) -> Maybe (String, DataStore)
getAllEntries store = Just (getEntries 0 (items store), store)
    where getEntries : Integer -> Vect n (SchemaType schema) -> String
          getEntries _ [] = ""
          getEntries index (entry :: rest) = (show index) ++ ": " ++
                        (display entry) ++ "\n" ++ getEntries (index + 1) rest

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
    = case parse (schema store) input of
           Nothing => Just ("Invalid command\n", store)
           Just (Add item) =>
              Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
           Just (SetSchema schema') =>
              case setSchema store schema' of
                   Nothing => Just ("Can't update schema when entries in store\n", store)
                   Just store' => Just ("OK\n", store')
           Just (Get pos) => getEntry pos store
           Just All => getAllEntries store
           Just Quit => Nothing

main : IO ()
main = replWith (MkData (SString .+. SString .+. SInt .+. SChar) _ []) "Command: " processInput
```
6. The fullyy updated *DataStore* with *do* notation follows:
```idris
module Main

import Data.Vect

infixr 5 .+.

data Schema = SString | SInt | SChar | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size store) newitem = MkData schema _ (addToData store)
  where
    addToData : Vect oldsize (SchemaType schema) -> Vect (S oldsize) (SchemaType schema)
    addToData [] = [newitem]
    addToData (x :: xs) = x :: addToData xs

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                              Z => Just (MkData schema _ [])
                              S k => Nothing

data Command : Schema -> Type where
     SetSchema : Schema -> Command schema
     Add : SchemaType schema -> Command schema
     Get : Integer -> Command schema
     All : Command schema
     Quit : Command schema


parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString input = getQuoted (unpack input)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs)
        = case span (/= '"') xs of
               (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
               _ => Nothing
    getQuoted _ = Nothing
parsePrefix SChar input = case unpack input of
                           [] => Nothing
                           (char :: rest) => Just (char, ltrim (pack rest))
parsePrefix SInt input = case span isDigit input of
                              ("", rest) => Nothing
                              (num, rest) => Just (cast num, ltrim rest)
parsePrefix (schemal .+. schemar) input = do
          (l_val, input') <- parsePrefix schemal input
          (r_val, input'') <- parsePrefix schemar input'
          pure ((l_val, r_val), input'')
```
```idris

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema x = case parsePrefix schema x of
                              Just (res, "") => Just res
                              _ => Nothing

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs)
    = case xs of
           [] => Just SString
           _ => case parseSchema xs of
                     Nothing => Nothing
                     Just xs_sch => Just (SString .+. xs_sch)
parseSchema ("Int" :: xs)
    = case xs of
           [] => Just SInt
           _ => case parseSchema xs of
                     Nothing => Nothing
                     Just xs_sch => Just (SInt .+. xs_sch)
parseSchema ("Char" :: xs)
    = case xs of
           [] => Just SChar
           _ => case parseSchema xs of
                     Nothing => Nothing
                     Just xs_sch => Just (SChar .+. xs_sch)
parseSchema _ = Nothing

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "add" rest = case parseBySchema schema rest of
                                      Nothing => Nothing
                                      Just restok => Just (Add restok)
parseCommand schema "get" "" = Just All
parseCommand schema "get" val = case all isDigit (unpack val) of
                                    False => Nothing
                                    True => Just (Get (cast val))
parseCommand schema "quit" "" = Just Quit
parseCommand schema "schema" rest
    = case parseSchema (words rest) of
           Nothing => Nothing
           Just schemaok => Just (SetSchema schemaok)
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = SChar} item = show item
display {schema = (y .+. z)} (iteml, itemr) = display iteml ++ ", " ++
                                              display itemr

getEntry : (pos : Integer) -> (store : DataStore) ->
           Maybe (String, DataStore)
getEntry pos store
    = let store_items = items store in
          case integerToFin pos (size store) of
               Nothing => Just ("Out of range\n", store)
               Just id => Just (display (index id (items store)) ++ "\n", store)



getAllEntries : (store : DataStore) -> Maybe (String, DataStore)
getAllEntries store = Just (getEntries 0 (items store), store)
    where getEntries : Integer -> Vect n (SchemaType schema) -> String
          getEntries _ [] = ""
          getEntries index (entry :: rest) = (show index) ++ ": " ++
                        (display entry) ++ "\n" ++ getEntries (index + 1) rest

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
    = case parse (schema store) input of
           Nothing => Just ("Invalid command\n", store)
           Just (Add item) =>
              Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
           Just (SetSchema schema') =>
              case setSchema store schema' of
                   Nothing => Just ("Can't update schema when entries in store\n", store)
                   Just store' => Just ("OK\n", store')
           Just (Get pos) => getEntry pos store
           Just All => getAllEntries store
           Just Quit => Nothing

main : IO ()
main = replWith (MkData (SString .+. SString .+. SInt .+. SChar) _ []) "Command: " processInput
```
