{-# OPTIONS --type-in-type --copatterns #-}

module Structs.SetoidDef where

open import Structs.Common
open import Structs.RelationDef

record 0-Category-Class 
    {X : Type} 
    (relX : Relation-Class X) : 
    Type  
  where
    constructor Mk
    field
      get-0-Id : {x : X} → (x ⟶ x)
      get-0-Mul : {x y z : X} → (x ⟶ y) → (y ⟶ z) → (x ⟶ z)
open 0-Category-Class public

0-Id : 
    {X : Type} → 
    {relX : Relation-Class X} → 
    {{catX : 0-Category-Class relX}} → 
    {x : X} → (x ⟶ x)
0-Id {{catX}} = get-0-Id catX 

_0-Mul_ :
    {X : Type} → 
    {relX : Relation-Class X} → 
    {{catX : 0-Category-Class relX}} → 
    {x y z : X} → (x ⟶ y) → (y ⟶ z) → (x ⟶ z)
_0-Mul_ {{catX}} = get-0-Mul catX 

record 0-Category-Record 
    : Type
  where
    constructor Mk
    field
      get-ob : Type
      get-rel : Relation-Class get-ob
      get-cat : 0-Category-Class get-rel

instance
  0-Category-Record-Ob : Ob-Class 0-Category-Record
  0-Category-Record-Ob = Mk 0-Category-Record.get-ob
