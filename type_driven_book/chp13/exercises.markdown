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
