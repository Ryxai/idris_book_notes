import Data.Vect

readToBlank : IO (List String)
readToBlank = do putStrLn "Enter text (end with a blank line):"
                 line <- getLine
                 if line == ""
                    then pure [] 
                    else do lines <- readToBlank
                            pure (line :: lines)

readAndSave : IO () 
readAndSave = do contents <- readToBlank
                 putStrLn "Enter a filename:"
                 fileName <- getLine
                 Right () <- writeFile fileName (unlines contents)
                 | Left err => putStrLn (show err)
                 pure () 


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
