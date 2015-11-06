{-# OPTIONS --type-in-type #-}

module CategoryTheory.Test where

record T : Set where
    constructor !

infixr 1 _*_
infixr -1 _,_
record _*_ (A B : Set) : Set where
    constructor _,_
    field fst : A
    field snd : B
open _*_

data Nat' : Set where
    Z' : Nat'
    S' : Nat' → Nat'

Vect : Set → Nat' → Set
Vect X Z' = X
Vect X (S' n) = X * (Vect X n)

data List (X : Set) : Set where
    [] : List X
    _/_ : (len : Nat') → (items : Vect X len) → List X

[_] : {X : Set} → {n : Nat'} → Vect X n → List X
[_] {X} {n} v = n / v

test1 : List T
test1 = [ ! ]
