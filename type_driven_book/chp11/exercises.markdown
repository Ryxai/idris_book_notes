1. The definition of *every_other* follows:
```idris every_other : Stream a -> Stream a
every_other (value1 :: (value2 :: xs)) = value2 :: every_other xs 
```
2. The definition of *Functor* for *InfList* follows:
```idris
Functor InfList where
  map func (value :: xs) = (func value) :: map func xs
```
3. The definition of *coinFlips* follows:
```idris
coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips Z xs = []
coinFlips (S k) (value :: xs) = getFace value :: coinFlips k xs 
  where
    getFace : Int -> Face
    getFace x with (divides x 2)
      getFace ((2 * div) + rem) | (DivBy prf)
      = case rem of
             0 => Heads
             _ => Tails
```
4. The definition of *square_root_approx* follows:
```idris
square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx
  = approx :: square_root_approx number ((approx + (number / approx)) / 2)
```
5. The definition of *square_root_bound* follows:
```idris
square_root_bound : (max : Nat) -> (number : Double) -> (bound : Double) -> 
                    (approxs : Stream Double) -> Double
square_root_bound Z number bound (value :: xs) = value
square_root_bound (S k) number bound (value :: xs)
  = case compare (number - (value * value)) bound of
      LT => square_root_bound k number bound xs
      _ => value 
```
6. The definition of *totalRepl* follows:
```idris
data InfIO : Type where
  Do : IO a
      -> (a -> Inf InfIO)
      -> InfIO

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

totalRepl  : (prompt : String) -> (action : String -> String) -> InfIO
totalRepl prompt action = do putStrLn prompt
                             input <- getLine
                             output <- pure (action input)
                             putStrLn output
                             totalRepl prompt action

data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

run : Fuel -> InfIO -> IO ()
run Dry y = putStrLn "Out of fuel"
run (More fuel) (Do c f) = do res <- c
                              run fuel (f res)
```
7. The definition of *quiz* supporting questions follows:
```idris
import Data.Primitives.Views
import System

data Input = Answer Int
           | QuitCmd

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure val) = pure val
runCommand (Bind c f) = do res <- runCommand c
                           runCommand (f res)

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                         then Pure QuitCmd
                         else Pure (Answer (cast answer))


mutual
  correct : Stream Int -> (score : Nat) -> (questions : Nat) 
              -> ConsoleIO (Nat, Nat)
  correct nums score questions
    = do PutStr "Correct!\n"
         quiz nums (score + 1) (questions + 1)

  wrong : Stream Int -> Int -> (score : Nat) -> (questions : Nat)
            -> ConsoleIO (Nat, Nat)
  wrong nums ans score questions
    = do PutStr ("Wrong the answer is " ++ show ans ++ "\n")
         quiz nums score (questions + 1)

  quiz : Stream Int -> (score : Nat) -> (questions : Nat) -> ConsoleIO (Nat, Nat)
  quiz (num1 :: num2 :: nums) score questions
    = do PutStr ("Score so far: " ++ show score  
                ++ " / " ++ show questions ++ "\n")
         input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ") 
         case input of
              Answer answer => if answer == num1 * num2
                                  then correct nums score questions
                                  else wrong nums (num1 * num2) score questions
              QuitCmd => Quit (score, questions)


randoms : Int -> Stream Int
randoms seed  = let seed' = 1664525 * seed + 1013904223 in
                    (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy prf) = abs rem + 1

namespace InfIODo
  data InfIO : Type where
    Do : IO a
        -> (a -> Inf InfIO)
        -> InfIO

  (>>=) : IO a -> (a -> Inf InfIO) -> InfIO
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run Dry _ = pure Nothing
run (More fuel) (Quit val) = pure (Just val)
run (More fuel) (Do c f) = do res <- runCommand c
                              run fuel (f res)

main : IO ()
main = do seed <- time
          Just (score, questions) <- run forever (quiz (arithInputs 
               (fromInteger seed)) 0 0)
          | Nothing => putStrLn "Quiz failed"
          putStrLn ("Final score: " ++ show score ++ " / " ++ show questions)
```
8. The updated definition of *Command* follows:
```idris
data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b
  ReadFile : String -> Command (Either FileError String) 
  WriteFile : String -> String -> Command (Either FileError ())
```
9. The definition of *shell* follows:
```idris
data Action: Type where
  Cat : String -> Action 
  Copy : String -> String -> Action
  Exit : Action 
  Invalid : Action
%name Action action, action1, action2, action3

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b
  ReadFile : String -> Command (Either FileError String) 
  WriteFile : String -> String -> Command (Either FileError ())

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b


runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure val) = pure val
runCommand (Bind c f) = do res <- runCommand c
                           runCommand (f res)
runCommand (ReadFile filepath) = readFile filepath
runCommand (WriteFile filepath contents) = writeFile filepath contents 

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run fuel (Quit val) = do pure (Just val)
run Dry (Do c f) = pure Nothing
run (More fuel) (Do c f) = do res <- runCommand c
                              run fuel (f res)

parseInput : (input : String) -> List String
parseInput input = parseInputHelper 3 input where
  parseInputHelper : (iterations: Nat) -> (input : String) -> List String
  parseInputHelper Z x = []
  parseInputHelper (S k) "" = []
  parseInputHelper (S k) input = let (arg, rest) = span (/= ' ') input in
                                     arg :: parseInputHelper k (ltrim rest)

parseAction: (input : String) -> Action
parseAction input = case parseInput input of
                         ("cat" :: fp :: []) => Cat fp 
                         ("copy" :: s :: d :: []) => Copy s d
                         ("quit" :: []) => Exit
                         _ => Invalid 

getInput : (prompt : String) -> Command Action
getInput prompt = do PutStr prompt
                     input <- GetLine
                     Pure (parseAction input)


shell : ConsoleIO ()
shell = do action <-  getInput (">:")
           (case action of
                 (Cat filePath) => do Right contents <- ReadFile filePath
                                      | Left error => do PutStr ("Cannot read "
                                                                 ++ "file: "
                                                                 ++ show error
                                                                 ++ "\n")
                                                         shell
                                      PutStr contents
                                      shell
                 (Copy sourcePath destinationPath) 
                  => do Right contents <- ReadFile sourcePath
                        | Left error => do PutStr ("Cannot read file: "
                                                  ++ show error
                                                  ++ "\n")
                                           shell
                        Right _ <- WriteFile destinationPath contents
                        | Left error => do PutStr ("Cannot write file: " 
                                                  ++ show error
                                                  ++ "\n")
                                           shell
                        PutStr (sourcePath ++ " copied to " ++ destinationPath
                               ++ "\n")
                        shell
                 Exit => do PutStr "Exiting\n"
                            Quit ()
                 Invalid => do PutStr "Invalid Command\n"
                               shell)
           
partial
forever : Fuel
forever = More forever

partial 
main : IO ()
main = do Just _ <- run forever shell
          | Nothing => putStrLn "Shell failure"
          pure ()
```
