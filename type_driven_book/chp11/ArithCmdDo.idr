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
  correct : Stream Int -> (score : Nat) -> (questions : Nat) -> ConsoleIO Nat
  correct nums score questions
    = do PutStr "Correct!\n"
         quiz nums (score + 1) (questions + 1)

  wrong : Stream Int -> Int -> (score : Nat) -> (questions : Nat)
    -> ConsoleIO Nat
  wrong nums ans score questions
    = do PutStr ("Wrong the answer is " ++ show ans ++ "\n")
         quiz nums score (questions + 1)

  quiz : Stream Int -> (score : Nat) -> (questions : Nat) -> ConsoleIO Nat
  quiz (num1 :: num2 :: nums) score questions
    = do PutStr ("Score so far: " ++ show score ++ "\n")
         input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ") 
         case input of
              Answer answer => if answer == num1 * num2
                                  then correct nums score questions
                                  else wrong nums (num1 * num2) score questions
              QuitCmd => Quit score
