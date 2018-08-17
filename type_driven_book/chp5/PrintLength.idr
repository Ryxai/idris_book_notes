printLength : IO ()
printLength = do putStr "Input string: "
                 input <- getLine
                 let len = length input
                 putStrLn (show len)

printLonger : IO ()
printLonger = do putStr "Input string 1: "
                 firstInput <- getLine
                 putStr "Input string 2: "
                 secondInput <- getLine
                 let longer = max (length firstInput) (length secondInput)
                 putStrLn (show longer)

printLongerAlt : IO ()
printLongerAlt = putStr "Input string 1: " >>= \_ =>
                 getLine >>= \input1 =>
                 putStr "Input string 2: " >>= \_=>
                 getLine >>= \input2 => 
                 let longer = max (length input1) (length input2) in
                     putStrLn (show longer)
