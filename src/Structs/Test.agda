module Structs.Test where

-- bracketed syntax for free monoid

data T : Set where
  ! : T

data _*_ (A B : Set) : Set where
  _,_ : (a : A) -> (b : B) -> A * B

data Nat : Set where
  zero : Nat
  suc  : (n : Nat) → Nat

{-# BUILTIN NATURAL Nat #-}

infixr 0 _,_
infix 1 _]
infix -1 [_

data List (A : Set) : Set where
  [] : List A
  _,_ : A -> List A -> List A

_] : {A : Set} -> A -> List A
a ] = a , []

[_ : {A : Set} -> List A -> List A
[ as = as

🎄 : List Nat
🎄 = []

🎅 : List Nat
🎅 = [ 0 ]

𓅓 : List Nat
𓅓 = [ 0 , 1 ]

𓆉 : List Nat
𓆉 = [ 0 , 1 , 2 ]
