# Chapter 1
1. The definition of *update* follows:
```idris
update : (stateType -> stateType) -> State stateType ()
update f = do curr <- get
              put (f curr)
              pure ()
```
2. The definition of *countEmpty* follows:
```idris
countEmpty: Tree a -> State Nat ()
countEmpty Empty = do curr <- get
                      put (curr + (fromIntegerNat 1))
                      pure ()
countEmpty (Node left val right) = do countEmpty left
                                      countEmpty right
                                      pure ()
```
3. The definition of *countEmptyNode* follows:
```idris
countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = do (empty, node) <- get
                          put (empty + (fromIntegerNat 1), node)
                          pure ()
countEmptyNode (Node left val right) = do (empty, node) <- get
                                          put (empty,
                                              node + (fromIntegerNat 1))
                                          countEmptyNode left
                                          countEmptyNode right
                                          pure ()
```
