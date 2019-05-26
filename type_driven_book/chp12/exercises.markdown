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
4. The definition of *updateGameState* follows:
```idris
updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = do st <- GetGameState
                       PutGameState (f st)
```
5. The definition of *Functor*, *Applicative* and *Monad* for *Command* follows:
```idris
mutual
  Functor Command where
    map func val = do res <- val
                      Pure (func res)

  Applicative Command where
    pure = Pure 
    (<*>) f a = do f' <- f
                   a' <- a
                   Pure (f' a')

  Monad Command where
    (>>=) = Bind
```
6. The definition for *getScore* follows:
```idris
getScore : Article -> Integer
getScore (MkArticle _ _ (MkVotes upvotes downvotes)) = upvotes - downvotes 

getScoreAlt : Article -> Integer 
getScoreAlt article = (upvotes (score article)) - (downvotes (score article))
```
7. The definition of *addUpVote* and *addDownVote* follows:
```idris
addUpVote : Article -> Article
addUpVote article = record {score->upvotes $= (+1)} article

downVotes : Article -> Article 
downVotes article = record {score->downvotes $= (+1)} article
```
