labelWith : Stream labelType -> List a -> List (labelType, a)
labelWith lbs [] = []
labelWith (lbl :: lbs) (val :: vals) = (lbl, val) :: labelWith lbs vals
label : List a -> List (Integer, a)
label = labelWith (iterate (+1) 0)
