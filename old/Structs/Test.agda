{-# OPTIONS --type-in-type --copatterns #-}

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

-----------------------------------------------------------------------

record A-Class (X : Set) : Set where
  constructor Mk
  field fiber : X -> Set
open A-Class {{...}}

-----------------------------------------------------------------------

record B-Class {X : Set} (iax : A-Class X) : Set where
  constructor Mk
  field point : (x : X) -> fiber x
open B-Class {{...}}

-----------------------------------------------------------------------

record B'-Class (X : Set) : Set where
  constructor Mk
  field fax : A-Class X
  field fbx : B-Class fax
open B'-Class {{...}}

{-
instance
  B'ax : {X : Set} -> {{ib'x : B'-Class X}} -> A-Class X
  B'ax = fax
  B'bx : {X : Set} -> {{ib'x : B'-Class X}} -> B-Class fax
  B'bx = fbx
-}
-----------------------------------------------------------------------

testA : {X : Set} -> {{iax : A-Class X}} -> X -> Set
testA = fiber

testB : {X : Set} -> {{iax : A-Class X}} -> {{ibx : B-Class iax}} -> (x : X) -> Set --testA x
testB = fiber --point

testB'A : {X : Set} -> {{ib'x : B'-Class X}} -> X -> Set
testB'A = fiber {{fax}}

testB'B : {X : Set} -> {{ib'x : B'-Class X}} -> (x : X) -> fiber {{fax}} x
testB'B = point {{fbx}}

-----------------------------------------------------------------------

record A-Record : Set where
  constructor Mk
  field ob : Set
  field {{iaob}} : A-Class ob
open A-Record

testRA : (ar : A-Record) -> ob ar -> Set
testRA ar = fiber {{iaob ar}}

------------------------------------------------------------------------

record C-Class (X Y : Set) : Set where
  constructor Mk
  field value : X
open C-Class {{...}}

testC : {X Y : Set} -> {{ic : C-Class X Y}} -> X
testC = value

instance 
  T-C : C-Class T T
  T-C = Mk !

testCT : T
testCT = value

_∣_ : (X : Set) -> X -> X
_∣_ X x = x

-------------------------------------------

record R1 : Set where
  field ff1 : T
open R1

record R2 : Set where
  field ff2 : T
open R2
