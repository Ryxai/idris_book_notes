# Chapter 14
1. The definition of *ShellCmd* follows:
```idris
data Access = LoggedOut | LoggedIn
data PwdCheck = Correct | Incorrect

data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
  Password : String -> ShellCmd PwdCheck LoggedOut (\check => (case check of
                                                                    Correct => LoggedIn 
                                                                    Incorrect => LoggedOut)) 
  Logout : ShellCmd () LoggedIn (const LoggedOut)
  GetSecret : ShellCmd String LoggedIn (const LoggedIn) 

  PutStr : String -> ShellCmd () state (const state)
  Pure : (res : ty) -> ShellCmd ty (state_fn res) state_fn
  (>>=) : ShellCmd a state1 state2_fn ->
          ((res : a) -> ShellCmd b (state2_fn res) state3_fn) -> 
          ShellCmd b state1 state3_fn

session : ShellCmd () LoggedOut (const LoggedOut)
session = do Correct <- Password "wurzel"
             | Incorrect => PutStr "Wrong Password"
             msg <- GetSecret
             PutStr ("Secret code: " ++ show msg ++ "\n")
             Logout

{-sessionBad : ShellCmd () LoggedOut (const LoggedOut)
sessionBad = do Password "wurzel"
                msg <- GetSecret
                PutStr ("Secret code: " ++ show msg ++ "\n")
                Logout-}

{-noLogout : ShellCmd () LoggedOut (const LoggedOut)
noLogout = do Correct <- Password "wurzel"
              | Incorrect => PutStr "Wrong Password"
              msg <- GetSecret
              PutStr ("Secret code: " ++ show msg ++ "\n")-}
```
2. The updated definition of *MachineCmd* follows:
```idris
VendState : Type
VendState = (Nat, Nat)

data CoinResult = Inserted | Rejected

data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

data MachineCmd : Type ->
                  VendState ->
                  (ty -> VendState) ->
                  Type where
     InsertCoin : MachineCmd CoinResult (pounds, chocs) 
                             (\res => case res of 
                                           Inserted => (S pounds, chocs)
                                           Rejected => (pounds, chocs))
     Vend       : MachineCmd () (S pounds, S chocs) (const (pounds, chocs))
     GetCoins   : MachineCmd () (pounds, chocs) (const (Z, chocs))
     Refill     : (bars : Nat) -> MachineCmd () (Z, chocs) (const (Z, bars + chocs))

     Display    : String -> MachineCmd () state (const state)
     GetInput   : MachineCmd (Maybe Input) state (const state)

     Pure       : ty -> MachineCmd ty state (const state)
     (>>=)      : MachineCmd a state1 state2_fn ->
                  ((res : a) -> MachineCmd b (state2_fn a) state3_fn) ->
                  MachineCmd b state1 state3_fn

data MachineIO : VendState -> Type where
  Do : MachineCmd a state1 state2_fn ->
       ((res : a) -> Inf (MachineIO (state2_fn res))) -> MachineIO state1

namespace MachineDo
  (>>=) : MachineCmd a state1 state2_fn -> ((res : a) ->
          Inf (MachineIO (state2_fn res))) ->
          MachineIO state1
  (>>=) = Do


mutual
  vend : MachineIO (pounds, chocs)
  vend {pounds = Z} = do Display "Insert a coin"
                         machineLoop
  vend {chocs = Z} = do Display "Out of stock" 
                        machineLoop
  vend {pounds = (S k)} {chocs = (S j)} = do Vend
                                             Display "Enjoy!"
                                             machineLoop

  refill : (num : Nat) -> MachineIO (pounds, chocs)
  refill {pounds = Z} num =  do Refill num
                                machineLoop
  refill _ = do Display "Can't refill: Coins in machine"
                machineLoop

  machineLoop : MachineIO (pounds, chocs)
  machineLoop =
    do Just x <- GetInput
       | Nothing => do Display "Invalid input"
                       machineLoop
       case x of
            COIN => do result <- InsertCoin
                       (case result of
                             Inserted => do Display "Coin Inserted"
                                            machineLoop
                             Rejected => do Display "Coin Rejected"
                                            machineLoop)
            VEND => vend
            CHANGE => do GetCoins
                         Display "Change returned"
                         machineLoop
            REFILL num => refill num
```
