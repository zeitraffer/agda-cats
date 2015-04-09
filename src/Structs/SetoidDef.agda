{-# OPTIONS --type-in-type --copatterns #-}

module Structs.SetoidDef where

open import Structs.RelationDef

record 0-Category-Class 
    {X : Type} 
    (relX : Relation-Class X) : 
    Set  
  where
    constructor Mk-0-Category
    field
      get-0-Id : {x : X} → (x ⟶ x)
      get-0-Mul : {x y z : X} → (x ⟶ y) → (y ⟶ z) → (x ⟶ z)

0-Id : 
    {X : Type} → 
    {{relX : Relation-Class X}} → 
    {{catX : 0-Category-Class relX}} → 
    (x : X) → (x ⟶ x)
0-Id x = 0-Category-Class.get-0-Id catX {x}
