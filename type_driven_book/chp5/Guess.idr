module Main

import System

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input)
     then pure (Just (cast input))
     else pure Nothing


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


main : IO ()
main = do t <- time
          guess (cast (mod t 100))

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

