{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Classes.0-Relation-Module where

open import CategoryTheory.Common-Module

-----------------------------
-- `Relation` type-synonym
--

0-Relation-Type : (src dst : Type) → Type
0-Relation-Type X Y = X → Y → Type

-------------------------------------------------------
-- `0-Relation-Class` - the major default relation over carrier
-- 
-- `_⟶_` - wrapped relation
--

record 0-Relation-Class 
    (X : Type) 
    : Type
  where
    constructor Mk
    field 
      get-it 
        : 0-Relation-Type X X

instance  
  0-Relation-Class-Wrap : 
      {X : Type} → 
      Wrap-Class (0-Relation-Type X X) (0-Relation-Class X)
  0-Relation-Class-Wrap {X} = Mk 0-Relation-Class.get-it Mk

-- the only method
_⟶_ : {X : Type} → ⦃ rel : 0-Relation-Class X ⦄ → 0-Relation-Type X X
_⟶_ ⦃ rel ⦄ = get rel

-- the only method wrapper
record _`⟶`_ 
    {X : Type} 
    ⦃ rel : 0-Relation-Class X ⦄
    (src dst : X) 
    : Type
  where
    constructor Mk
    field 
      get-it 
        : 0-Relation-Class.get-it rel src dst

instance
  ⟶-Wrap : 
      {X : Type} → 
      ⦃ rel : 0-Relation-Class X ⦄ → 
      {src dst : X} → 
      Wrap-Class (0-Relation-Class.get-it rel src dst) (src `⟶` dst)
  ⟶-Wrap = Mk _`⟶`_.get-it Mk

--------------------------------------------------------------
-- `0-Relation-Class'` - the minor default relation over carrier
-- 
-- `_⇸_` - wrapped relation
--

record 
    0-Relation-Class' (X : Type) 
    : Type
  where
    constructor Mk
    field 
      get-it 
        : 0-Relation-Type X X

instance  
  0-Relation-Class'-Wrap : 
      {X : Type} → 
      Wrap-Class (0-Relation-Type X X) (0-Relation-Class' X)
  0-Relation-Class'-Wrap {X} = Mk 0-Relation-Class'.get-it Mk

-- the only method
_⇸_ : {X : Type} → ⦃ rel : 0-Relation-Class' X ⦄ → 0-Relation-Type X X
_⇸_ ⦃ rel ⦄ = get rel

record _`⇸`_ 
    {X : Type} 
    ⦃ rel : 0-Relation-Class' X ⦄ 
    (src dst : X) 
    : Type
  where
    constructor Mk
    field 
      get-it 
        : 0-Relation-Class'.get-it rel src dst

instance
  ⇸-Wrap : 
      {X : Type} → 
      ⦃ rel : 0-Relation-Class' X ⦄ → 
      {src dst : X} → 
      Wrap-Class (0-Relation-Class'.get-it rel src dst) (src `⇸` dst)
  ⇸-Wrap = Mk _`⇸`_.get-it Mk

-----------------------------------------------------------
-- `0-Relation-Record` - a couple of a carrier and a relation
--

record 
    0-Relation-Record 
    : Type
  where
    constructor Mk
    field
      get-rel-ob-type 
        : Type
      ⦃ get-rel-rel-inst ⦄
        : 0-Relation-Class get-rel-ob-type
open 0-Relation-Record public

instance
  0-Relation-Record-Ob : Ob-Class 0-Relation-Record
  0-Relation-Record-Ob = Mk get-rel-ob-type

