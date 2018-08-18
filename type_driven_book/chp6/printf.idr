import Data.Vect 

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

Matrix : Nat -> Nat -> Type
Matrix n m = Vect n (Vect m Double)

