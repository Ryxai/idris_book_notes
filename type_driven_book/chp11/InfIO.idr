data InfIO : Type where
  Do : IO a
      -> (a -> Inf InfIO)
      -> InfIO

{-loopPrint : String -> InfIO
loopPrint msg = Do (putStrLn msg)
                   (\_ => loopPrint msg)-}

{-run : InfIO -> IO ()
run (Do action cont) = do res <- action
                          run (cont res)-}

{-data Fuel = Dry | More Fuel-}
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

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do
loopPrint : String -> InfIO
loopPrint msg = do putStrLn msg
                   loopPrint msg
