{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Classes.0-Groupoid-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Classes.Relation-Module
open import CategoryTheory.Classes.0-Category-Module

--------------------------------------
-- `0-Groupoid-Class` to be a setoid
--

record 0-Groupoid-Class 
    {X : Type} 
    {relX : Relation-Class X} 
    (catX : 0-Category-Class relX) : 
    Type  
  where
    constructor Mk
    field
      get-grp-0-Inv : 
          {x y : X} → (x ⟶ y) → (y ⟶ x)
open 0-Groupoid-Class public

-- inverse method
_0-Inv_ :
    {X : Type} → 
    {relX : Relation-Class X} → 
    {catX : 0-Category-Class relX} → 
    ⦃ grpX : 0-Groupoid-Class catX ⦄ → 
    {x y : X} → (x ⟶ y) → (y ⟶ x)
_0-Inv_ ⦃ grpX ⦄ = get-grp-0-Inv grpX 

-- a couple of carriers and operations
record 0-Groupoid-Record 
    : Type
  where
    constructor Mk
    field
      get-grp-cat-rec
        : 0-Category-Record
    -- and helpers
    get-grp-rel-rec : Relation-Record
    get-grp-rel-rec = get-cat-rel-rec get-grp-cat-rec
    get-grp-ob-type : Type
    get-grp-ob-type = get-rel-ob-type get-grp-rel-rec
    get-grp-rel-inst : Relation-Class get-grp-ob-type
    get-grp-rel-inst = get-rel-rel-inst get-grp-rel-rec
    get-grp-cat-inst : 0-Category-Class get-grp-rel-inst
    get-grp-cat-inst = get-cat-cat-inst get-grp-cat-rec

    field
      ⦃ get-grp-grp-inst ⦄
        : 0-Groupoid-Class get-grp-cat-inst

open 0-Groupoid-Record public

instance
  0-Groupoid-Record-Ob : Ob-Class 0-Groupoid-Record
  0-Groupoid-Record-Ob = Mk get-grp-ob-type

