# Chapter 13
1. The definition of the updated *DoorCmd* follows:
```idris
data DoorCmd : Type -> 
               DoorState ->
               DoorState ->
               Type where
  Open : DoorCmd () DoorClosed DoorOpen
  Close : DoorCmd () DoorOpen DoorClosed
  RingBell : DoorCmd () state state

  Pure : ty -> DoorCmd ty state state
  (>>=) : DoorCmd a state1 state2 ->
       (a -> DoorCmd b state2 state3) ->
       DoorCmd b state1 state3
```
2. The definition of *GuessCmd* follows:
```idris
data GuessCmd : Type -> Nat -> Nat -> Type where
  Try : Integer -> GuessCmd Ordering (S k) k

  Pure : ty -> GuessCmd ty state state
  (>>=) : GuessCmd a state1 state2 ->
         (a -> GuessCmd b state2 state3) ->
         GuessCmd b state1 state3
```
3. The definition of *MatterCmd* follows:
```idris
data MatterCmd : Type -> Matter -> Matter -> Type where
  Melt : MatterCmd () Solid Liquid
  Boil : MatterCmd () Liquid Gas
  Condense : MatterCmd () Gas Liquid
  Freeze : MatterCmd () Liquid Solid

  Pure : ty -> MatterCmd ty state state
  (>>=) : MatterCmd a state1 state2 ->
          (a -> MatterCmd b state2 state3) ->
          MatterCmd b state1 state3
```
4. The updated definition of *StackIO* to support *Subtract* and *Multiply* 
follows:
```idris
import Data.Vect

data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)

  GetStr : StackCmd String height height
  PutStr : String -> StackCmd () height height

  Pure : ty -> StackCmd ty height height
  (>>=) : StackCmd a height1 height2 ->
          (a -> StackCmd b height2 height3) ->
          StackCmd b height1 height3

data StackIO : Nat -> Type where
   Do : StackCmd a height1 height2 ->
        (a -> Inf (StackIO height2)) -> StackIO height1

namespace StackDo
  (>>=) : StackCmd a height1 height2 ->
         (a -> Inf (StackIO height2)) -> StackIO height1
  (>>=) = Do

runStack : (stk: Vect inHeight Integer) ->
            StackCmd ty inHeight outHeight ->
            IO (ty, Vect outHeight Integer)
runStack stk (Push val) = pure ((), val :: stk)
runStack (val :: stk) Pop = pure (val, stk)
runStack (val :: stk) Top = pure (val, val :: stk)
runStack stk GetStr = do x <- getLine
                         pure (x, stk)
runStack stk (PutStr x) = do putStr x
                             pure (() , stk)
runStack stk (Pure x) = pure (x, stk)
runStack stk (cmd >>= next)
  = do (cmdRes, newStk) <- runStack stk cmd
       runStack newStk (next cmdRes)

testAdd : StackCmd Integer 0 0
testAdd = do Push 10
             Push 20
             val1 <- Pop
             val2 <- Pop
             Pure (val1 + val2)

doAdd : StackCmd () (S (S height)) (S height)
doAdd = do val1 <- Pop
           val2 <- Pop
           Push (val1 + val2)

doSubtract : StackCmd () (S (S height))  (S height)
doSubtract = do val1 <- Pop
                val2 <- Pop
                Push (val1 - val2)

doMultiply : StackCmd () (S (S height)) (S height)
doMultiply = do val1 <- Pop
                val2 <- Pop
                Push (val1 * val2)

data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run Dry stk p = pure ()
run (More fuel) stk (Do c f) = do (res, newStk) <- runStack stk c
                                  run fuel newStk (f res)

data StkInput = Number Integer
              | Add
              | Subtract
              | Multiply


strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "subtract" = Just Subtract
strToInput "multiply" = Just Multiply
strToInput x = if all isDigit (unpack x)
                  then Just (Number (cast x))
                  else Nothing

mutual
  tryAdd : StackIO height
  tryAdd {height = S(S h)}= do doAdd
                               result <- Top
                               PutStr (show result ++ "\n")
                               stackCalc
  tryAdd = do PutStr "Fewer than two items on the stack \n"
              stackCalc

  trySubtract: StackIO height
  trySubtract {height = S(S h)}= do doSubtract
                                    result <- Top
                                    PutStr (show result ++ "\n")
                                    stackCalc
  trySubtract = do PutStr "Fewer than two items on the stack \n"
                   stackCalc

  tryMultiply : StackIO height
  tryMultiply {height = S(S h)}= do doMultiply
                                    result <- Top
                                    PutStr (show result ++ "\n")
                                    stackCalc
  tryMultiply = do PutStr "Fewer than two items on the stack \n"
                   stackCalc

  stackCalc : StackIO height
  stackCalc = do PutStr "> "
                 input <- GetStr case strToInput input of Nothing => do PutStr "Invalid input\n"
                                    stackCalc
                      Just (Number x) => do Push x
                                            stackCalc
                      Just Add => tryAdd
                      Just Subtract => trySubtract
                      Just Multiply => tryMultiply

main: IO ()
main = run forever [] stackCalc
```
5. The updated definition of *StackIO* for *Negate* follows:
```idris
import Data.Vect

data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)

  GetStr : StackCmd String height height
  PutStr : String -> StackCmd () height height

  Pure : ty -> StackCmd ty height height
  (>>=) : StackCmd a height1 height2 ->
          (a -> StackCmd b height2 height3) ->
          StackCmd b height1 height3

data StackIO : Nat -> Type where
   Do : StackCmd a height1 height2 ->
        (a -> Inf (StackIO height2)) -> StackIO height1

namespace StackDo
  (>>=) : StackCmd a height1 height2 ->
         (a -> Inf (StackIO height2)) -> StackIO height1
  (>>=) = Do

runStack : (stk: Vect inHeight Integer) ->
            StackCmd ty inHeight outHeight ->
            IO (ty, Vect outHeight Integer)
runStack stk (Push val) = pure ((), val :: stk)
runStack (val :: stk) Pop = pure (val, stk)
runStack (val :: stk) Top = pure (val, val :: stk)
runStack stk GetStr = do x <- getLine
                         pure (x, stk)
runStack stk (PutStr x) = do putStr x
                             pure (() , stk)
runStack stk (Pure x) = pure (x, stk)
runStack stk (cmd >>= next)
  = do (cmdRes, newStk) <- runStack stk cmd
       runStack newStk (next cmdRes)

testAdd : StackCmd Integer 0 0
testAdd = do Push 10
             Push 20
             val1 <- Pop
             val2 <- Pop
             Pure (val1 + val2)

doAdd : StackCmd () (S (S height)) (S height)
doAdd = do val1 <- Pop
           val2 <- Pop
           Push (val1 + val2)

doSubtract : StackCmd () (S (S height))  (S height)
doSubtract = do val1 <- Pop
                val2 <- Pop
                Push (val1 - val2)

doMultiply : StackCmd () (S (S height)) (S height)
doMultiply = do val1 <- Pop
                val2 <- Pop
                Push (val1 * val2)

doNegate : StackCmd () (S height) (S height)
doNegate = do val <- Pop
              Push (negate 5)

data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run Dry stk p = pure ()
run (More fuel) stk (Do c f) = do (res, newStk) <- runStack stk c
                                  run fuel newStk (f res)

data StkInput = Number Integer
              | Add
              | Subtract
              | Multiply
              | Negate

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "subtract" = Just Subtract
strToInput "multiply" = Just Multiply
strToInput "negate" = Just Negate
strToInput x = if all isDigit (unpack x)
                  then Just (Number (cast x))
                  else Nothing

mutual
  tryAdd : StackIO height
  tryAdd {height = S(S h)}= do doAdd
                               result <- Top
                               PutStr (show result ++ "\n")
                               stackCalc
  tryAdd = do PutStr "Fewer than two items on the stack \n"
              stackCalc

  trySubtract: StackIO height
  trySubtract {height = S(S h)}= do doSubtract
                                    result <- Top
                                    PutStr (show result ++ "\n")
                                    stackCalc
  trySubtract = do PutStr "Fewer than two items on the stack \n"
                   stackCalc

  tryMultiply : StackIO height
  tryMultiply {height = S(S h)}= do doMultiply
                                    result <- Top
                                    PutStr (show result ++ "\n")
                                    stackCalc
  tryMultiply = do PutStr "Fewer than two items on the stack \n"
                   stackCalc

  tryNegate : StackIO height
  tryNegate {height = (S h)} = do doNegate
                                  result <- Top
                                  PutStr (show result ++ "\n")
                                  stackCalc
  tryNegate = do PutStr "Fewer than one item on the stack \n"
                 stackCalc


  stackCalc : StackIO height
  stackCalc = do PutStr "> "
                 input <- GetStr
                 case strToInput input of
                      Nothing => do PutStr "Invalid input\n"
                                    stackCalc
                      Just (Number x) => do Push x
                                            stackCalc
                      Just Add => tryAdd
                      Just Subtract => trySubtract
                      Just Multiply => tryMultiply
                      Just Negate => tryNegate

main: IO ()
main = run forever [] stackCalc
```
6. The definition of *StackIO* for *Discard* follows:
```idris
import Data.Vect

data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)

  GetStr : StackCmd String height height
  PutStr : String -> StackCmd () height height

  Pure : ty -> StackCmd ty height height
  (>>=) : StackCmd a height1 height2 ->
          (a -> StackCmd b height2 height3) ->
          StackCmd b height1 height3

data StackIO : Nat -> Type where
   Do : StackCmd a height1 height2 ->
        (a -> Inf (StackIO height2)) -> StackIO height1

namespace StackDo
  (>>=) : StackCmd a height1 height2 ->
         (a -> Inf (StackIO height2)) -> StackIO height1
  (>>=) = Do

runStack : (stk: Vect inHeight Integer) ->
            StackCmd ty inHeight outHeight ->
            IO (ty, Vect outHeight Integer)
runStack stk (Push val) = pure ((), val :: stk)
runStack (val :: stk) Pop = pure (val, stk)
runStack (val :: stk) Top = pure (val, val :: stk)
runStack stk GetStr = do x <- getLine
                         pure (x, stk)
runStack stk (PutStr x) = do putStr x
                             pure (() , stk)
runStack stk (Pure x) = pure (x, stk)
runStack stk (cmd >>= next)
  = do (cmdRes, newStk) <- runStack stk cmd
       runStack newStk (next cmdRes)

testAdd : StackCmd Integer 0 0
testAdd = do Push 10
             Push 20
             val1 <- Pop
             val2 <- Pop
             Pure (val1 + val2)

doAdd : StackCmd () (S (S height)) (S height)
doAdd = do val1 <- Pop
           val2 <- Pop
           Push (val1 + val2)

doSubtract : StackCmd () (S (S height))  (S height)
doSubtract = do val1 <- Pop
                val2 <- Pop
                Push (val1 - val2)

doMultiply : StackCmd () (S (S height)) (S height)
doMultiply = do val1 <- Pop
                val2 <- Pop
                Push (val1 * val2)

doNegate : StackCmd () (S height) (S height)
doNegate = do val <- Pop
              Push (negate 5)

doDiscard : StackCmd Integer (S height) height
doDiscard = do val <- Pop
               Pure val

data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run Dry stk p = pure ()
run (More fuel) stk (Do c f) = do (res, newStk) <- runStack stk c
                                  run fuel newStk (f res)

data StkInput = Number Integer
              | Add
              | Subtract
              | Multiply
              | Negate
              | Discard


strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "subtract" = Just Subtract
strToInput "multiply" = Just Multiply
strToInput "negate" = Just Negate
strToInput "discard" = Just Discard
strToInput x = if all isDigit (unpack x)
                  then Just (Number (cast x))
                  else Nothing

mutual
  tryAdd : StackIO height
  tryAdd {height = S(S h)}= do doAdd
                               result <- Top
                               PutStr (show result ++ "\n")
                               stackCalc
  tryAdd = do PutStr "Fewer than two items on the stack \n"
              stackCalc

  trySubtract: StackIO height
  trySubtract {height = S(S h)}= do doSubtract
                                    result <- Top
                                    PutStr (show result ++ "\n")
                                    stackCalc
  trySubtract = do PutStr "Fewer than two items on the stack \n"
                   stackCalc

  tryMultiply : StackIO height
  tryMultiply {height = S(S h)}= do doMultiply
                                    result <- Top
                                    PutStr (show result ++ "\n")
                                    stackCalc
  tryMultiply = do PutStr "Fewer than two items on the stack \n"
                   stackCalc

  tryNegate : StackIO height
  tryNegate {height = (S h)} = do doNegate
                                  result <- Top
                                  PutStr (show result ++ "\n")
                                  stackCalc
  tryNegate = do PutStr "Fewer than one item on the stack \n"
                 stackCalc

  tryDiscard : StackIO height
  tryDiscard {height = (S h)} = do result <- doDiscard
                                   PutStr ("Discarded " ++ show result ++ "\n")
                                   stackCalc
  tryDiscard = do PutStr "Fewer than one item on the stack \n"
                  stackCalc


  stackCalc : StackIO height
  stackCalc = do PutStr "> "
                 input <- GetStr
                 case strToInput input of
                      Nothing => do PutStr "Invalid input\n"
                                    stackCalc
                      Just (Number x) => do Push x
                                            stackCalc
                      Just Add => tryAdd
                      Just Subtract => trySubtract
                      Just Multiply => tryMultiply
                      Just Negate => tryNegate
                      Just Discard => tryDiscard

main: IO ()
main = run forever [] stackCalc
```
7. The definition of *StackIO* for *Duplicate* follows:
```idris
import Data.Vect

data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)

  GetStr : StackCmd String height height
  PutStr : String -> StackCmd () height height

  Pure : ty -> StackCmd ty height height
  (>>=) : StackCmd a height1 height2 ->
          (a -> StackCmd b height2 height3) ->
          StackCmd b height1 height3

data StackIO : Nat -> Type where
   Do : StackCmd a height1 height2 ->
        (a -> Inf (StackIO height2)) -> StackIO height1

namespace StackDo
  (>>=) : StackCmd a height1 height2 ->
         (a -> Inf (StackIO height2)) -> StackIO height1
  (>>=) = Do

runStack : (stk: Vect inHeight Integer) ->
            StackCmd ty inHeight outHeight ->
            IO (ty, Vect outHeight Integer)
runStack stk (Push val) = pure ((), val :: stk)
runStack (val :: stk) Pop = pure (val, stk)
runStack (val :: stk) Top = pure (val, val :: stk)
runStack stk GetStr = do x <- getLine
                         pure (x, stk)
runStack stk (PutStr x) = do putStr x
                             pure (() , stk)
runStack stk (Pure x) = pure (x, stk)
runStack stk (cmd >>= next)
  = do (cmdRes, newStk) <- runStack stk cmd
       runStack newStk (next cmdRes)

testAdd : StackCmd Integer 0 0
testAdd = do Push 10
             Push 20
             val1 <- Pop
             val2 <- Pop
             Pure (val1 + val2)

doAdd : StackCmd () (S (S height)) (S height)
doAdd = do val1 <- Pop
           val2 <- Pop
           Push (val1 + val2)

doSubtract : StackCmd () (S (S height))  (S height)
doSubtract = do val1 <- Pop
                val2 <- Pop
                Push (val1 - val2)

doMultiply : StackCmd () (S (S height)) (S height)
doMultiply = do val1 <- Pop
                val2 <- Pop
                Push (val1 * val2)

doNegate : StackCmd () (S height) (S height)
doNegate = do val <- Pop
              Push (negate 5)

doDiscard : StackCmd Integer (S height) height
doDiscard = do val <- Pop
               Pure val

doDuplicate : StackCmd () (S height) (S (S height))
doDuplicate = do val <- Top
                 Push val

data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run Dry stk p = pure ()
run (More fuel) stk (Do c f) = do (res, newStk) <- runStack stk c
                                  run fuel newStk (f res)

data StkInput = Number Integer
              | Add
              | Subtract
              | Multiply
              | Negate
              | Discard
              | Duplicate


strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "subtract" = Just Subtract
strToInput "multiply" = Just Multiply
strToInput "negate" = Just Negate
strToInput "discard" = Just Discard
strToInput "duplicate" = Just Duplicate
strToInput x = if all isDigit (unpack x)
                  then Just (Number (cast x))
                  else Nothing

mutual
  tryAdd : StackIO height
  tryAdd {height = S(S h)}= do doAdd
                               result <- Top
                               PutStr (show result ++ "\n")
                               stackCalc
  tryAdd = do PutStr "Fewer than two items on the stack \n"
              stackCalc

  trySubtract: StackIO height
  trySubtract {height = S(S h)}= do doSubtract
                                    result <- Top
                                    PutStr (show result ++ "\n")
                                    stackCalc
  trySubtract = do PutStr "Fewer than two items on the stack \n"
                   stackCalc

  tryMultiply : StackIO height
  tryMultiply {height = S(S h)}= do doMultiply
                                    result <- Top
                                    PutStr (show result ++ "\n")
                                    stackCalc
  tryMultiply = do PutStr "Fewer than two items on the stack \n"
                   stackCalc

  tryNegate : StackIO height
  tryNegate {height = (S h)} = do doNegate
                                  result <- Top
                                  PutStr (show result ++ "\n")
                                  stackCalc
  tryNegate = do PutStr "Fewer than one item on the stack \n"
                 stackCalc

  tryDiscard : StackIO height
  tryDiscard {height = (S h)} = do result <- doDiscard
                                   PutStr ("Discarded " ++ show result ++ "\n")
                                   stackCalc
  tryDiscard = do PutStr "Fewer than one item on the stack \n"
                  stackCalc

  tryDuplicate : StackIO height
  tryDuplicate {height = (S h)} = do doDuplicate
                                     result <- Top
                                     PutStr ("Duplicated " ++
                                              show result ++
                                              "\n")
                                     stackCalc
  tryDuplicate = do PutStr "Fewer then one item on the stack"
                    stackCalc


  stackCalc : StackIO height
  stackCalc = do PutStr "> "
                 input <- GetStr
                 case strToInput input of
                      Nothing => do PutStr "Invalid input\n"
                                    stackCalc
                      Just (Number x) => do Push x
                                            stackCalc
                      Just Add => tryAdd
                      Just Subtract => trySubtract
                      Just Multiply => tryMultiply
                      Just Negate => tryNegate
                      Just Discard => tryDiscard
                      Just Duplicate => tryDuplicate

main: IO ()
main = run forever [] stackCalc
```
