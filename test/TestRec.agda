{-# OPTIONS --type-in-type --copatterns #-}

module TestRec where

----------------------------------------------------

Type : Set
Type = Set

record T : Type 
  where
    constructor !

record T' : Type 
  where
    constructor !'

----------------------------------------------------

record E {Base : Type} (Fiber : Base -> Type) : Type
  where
    constructor e
    field {base} : Base
    field fiber : Fiber base
open E

----------------------------------------------------

record 1-Class (X : Type) : Type
  where
    constructor Mk
    field fiber1 : X -> Type

1-Record : Type
1-Record = E 1-Class

fiber1/ : {{x1 : 1-Record}} -> (base x1 -> Type)
fiber1/ {{x1}} = 1-Class.fiber1 (fiber x1)

T-is-1 : 1-Class T
1-Class.fiber1 T-is-1 _ = T

T'-is-1 : 1-Class T'
1-Class.fiber1 T'-is-1 _ = T'

T-1 : 1-Record
T-1 = e T-is-1

T'-1 : 1-Record
T'-1 = e T'-is-1

----------------------------------------------------

record 2-Class (x1 : 1-Record) : Type
  where
    constructor Mk
    X = base x1
    instance ix1 = x1
    field section2 : (x : X) -> fiber1/ x

2-Record : Type
2-Record = E 2-Class

instance
  2Rec-to-1Rec : {{2r : 2-Record}} -> 1-Record
  2Rec-to-1Rec {{2r}} = base 2r

section2/ : 
  {{x2 : 2-Record}} -> 
  (x : base (base x2)) -> fiber1/ x
section2/ {{x2}} = 2-Class.section2 (fiber x2)

T-is-2 : 2-Class T-1
2-Class.section2 T-is-2 x = !

T'-is-2 : 2-Class T'-1
2-Class.section2 T'-is-2 x = !'

instance
  T-2 : 2-Record
  T-2 = e T-is-2

instance
  T'-2 : 2-Record
  T'-2 = e T'-is-2

----------------------------------------------------

test1/ : Type
test1/ = fiber1/ !'

=fiber1/ : {{x1 : 1-Record}} -> (base x1 -> Type)
=fiber1/ = fiber1/

test2/ : test1/
test2/ = section2/ !'

=section2/ : {{x2 : 2-Record}} -> (x : base (base x2)) -> =fiber1/ x
=section2/ = section2/
