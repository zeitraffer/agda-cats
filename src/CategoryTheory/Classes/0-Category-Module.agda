{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Classes.0-Category-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Classes.Relation-Module

--------------------------------------
-- `0-Category-Class` to be a preorder
--

record 0-Category-Class 
    {X : Type} 
    (relX : Relation-Class X) 
    : Type  
  where
    constructor Mk
    field
      get-cat-0-Id 
        : {x : X} → (x ⟶ x)
      get-cat-0-Mul 
        : {x y z : X} → (x ⟶ y) → (y ⟶ z) → (x ⟶ z)
open 0-Category-Class public

-- identity method
0-Id : 
    {X : Type} → 
    {relX : Relation-Class X} → 
    ⦃ catX : 0-Category-Class relX ⦄ → 
    {x : X} → (x ⟶ x)
0-Id ⦃ catX ⦄ = get-cat-0-Id catX 

-- multiplication method
_0-Mul_ :
    {X : Type} → 
    {relX : Relation-Class X} → 
    ⦃ catX : 0-Category-Class relX ⦄ → 
    {x y z : X} → (x ⟶ y) → (y ⟶ z) → (x ⟶ z)
_0-Mul_ ⦃ catX ⦄ = get-cat-0-Mul catX 

-- a couple of carriers and operations
record 0-Category-Record 
    : Type
  where
    constructor Mk
    field
      get-cat-rel-rec 
        : Relation-Record

    -- and helpers
    get-cat-ob-type : Type
    get-cat-ob-type = get-rel-ob-type get-cat-rel-rec
    get-cat-rel-inst : Relation-Class get-cat-ob-type
    get-cat-rel-inst = get-rel-rel-inst get-cat-rel-rec

    field
      ⦃ get-cat-cat-inst ⦄
        : 0-Category-Class get-cat-rel-inst

open 0-Category-Record public

instance
  0-Category-Record-Ob : Ob-Class 0-Category-Record
  0-Category-Record-Ob = Mk get-cat-ob-type

