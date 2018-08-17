# Chapter 5
1. The definition of *printLonger* follows below
```idris
printLonger : IO ()
printLonger = do putStr "Input string 1: "
                 firstInput <- getLine
                 putStr "Input string 2: "
                 secondInput <- getLine
                 let longer = max (length firstInput) (length secondInput)
                 putStrLn (show longer)
```

2. The definition of the alternative *printLonger* function follows below:
```idris
printLongerAlt : IO ()
printLongerAlt = putStr "Input string 1: " >>= \_ =>
                 getLine >>= \input1 =>
                 putStr "Input string 2: " >>= \_=>
                 getLine >>= \input2 => 
                 let longer = max (length input1) (length input2) in
                     putStrLn (show longer)
```
3. The definition of the *guess* function follows:
```idris
guess : (target : Nat) -> IO ()
guess target = do putStrLn "Input guess: "
                  Just guessResult <- readNumber
                  | Nothing => do putStrLn "Invalid input"
                                  guess target
                  (case compare guessResult target of
                        LT => do putStrLn "Guess is too low" 
                                 guess target
                        EQ => do putStrLn "Guess is correct!" 
                        GT => do putStrLn "Guess is to high"
                                 guess target)
```
4. The definition of the *main* function follows
```idris
main : IO ()
main = do t <- time
          guess (cast (mod t 100))
```
5. The updated *guess* function follows:
```idris
altGuess : (target : Nat) -> (guesses : Nat) -> IO ()
altGuess target guesses = do putStrLn ((show guesses) ++ " guesses thus far") 
                             putStrLn "Input guess: "
                             Just guessResult <- readNumber
                             | Nothing => do putStrLn "Invalid input"
                                             altGuess target guesses
                             (case compare guessResult target of
                                   LT => do putStrLn "Guess is too low" 
                                            altGuess target (guesses + 1)
                                   EQ => do putStrLn "Guess is correct!" 
                                   GT => do putStrLn "Guess is too high"
                                            altGuess target (guesses + 1))
```
6. The *replWith* and *repl* functions are defined below:
```idris
replWithAlt : (state : a) -> (prompt : String) ->
           (onInput: a -> String -> Maybe(String, a)) -> IO ()
replWithAlt state prompt onInput = do putStrLn prompt
                                      input <- getLine
                                      (case onInput state input of
                                            Nothing => pure () 
                                            (Just (output, resultState)) => do putStrLn output
                                                                               replWithAlt resultState prompt onInput)

replAlt : (prompt : String) -> (onInput : String -> String) -> IO ()
replAlt prompt onInput = replWithAlt () prompt (\st, str => Just (onInput str, ()))
```
7. The definition for *readToBlank* follows:
```idris
readToBlank : IO (List String)
readToBlank = do putStrLn "Enter text (end with a blank line):"
                 line <- getLine
                 if line == ""
                    then pure [] 
                    else do lines <- readToBlank
                            pure (line :: lines)
```
8. The definition for *readAndSave* follows:
```idris
readAndSave : IO () 
readAndSave = do contents <- readToBlank
                 putStrLn "Enter a filename:"
                 fileName <- getLine
                 Right () <- writeFile fileName (unlines contents)
                 | Left err => putStrLn (show err)
                 pure () 
```
9. The definition for *readVectFile* follows (derived from ruippeixotog):
```idris
readVectFileHelper : (file: File) -> IO (Maybe (n ** Vect n String))
readVectFileHelper file = do 
  False <- fEOF file
  | True => pure (Just (_ ** []))
  Right line <- fGetLine file
  | Left err => pure Nothing
  Just (_ ** lines)<- readVectFileHelper file
  | Nothing => pure Nothing
  pure (Just (_ ** (line :: lines)))

readVectFile : (fileName : String) -> IO (n ** Vect n String)
readVectFile fileName = do 
  Right file <- openFile fileName Read
  | Left err => pure (_ ** [])
  Just vec <- readVectFileHelper file
  | Nothing => pure (_ ** [])
  closeFile file
  pure vec
```
