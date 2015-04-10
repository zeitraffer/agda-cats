{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Classes.Relation-Module where

open import CategoryTheory.Common-Module

-----------------------------
-- `Relation` type-synonym
--

Relation-Type : (src dst : Type) → Type
Relation-Type X Y = X → Y → Type

-------------------------------------------------------
-- `Relation-Class` - the major default relation over carrier
-- 
-- `_⟶_` - wrapped relation
--

record Relation-Class 
    (X : Type) 
    : Type
  where
    constructor Mk
    field 
      get-it 
        : Relation-Type X X

instance  
  Relation-Class-Wrap : 
      {X : Type} → 
      Wrap-Class (Relation-Type X X) (Relation-Class X)
  Relation-Class-Wrap {X} = Mk Relation-Class.get-it Mk

-- the only method
_⟶_ : {X : Type} → ⦃ rel : Relation-Class X ⦄ → Relation-Type X X
_⟶_ ⦃ rel ⦄ = get rel

-- the only method wrapper
record _`⟶`_ 
    {X : Type} 
    ⦃ rel : Relation-Class X ⦄
    (src dst : X) 
    : Type
  where
    constructor Mk
    field 
      get-it 
        : Relation-Class.get-it rel src dst

instance
  ⟶-Wrap : 
      {X : Type} → 
      ⦃ rel : Relation-Class X ⦄ → 
      {src dst : X} → 
      Wrap-Class (Relation-Class.get-it rel src dst) (src `⟶` dst)
  ⟶-Wrap = Mk _`⟶`_.get-it Mk

--------------------------------------------------------------
-- `Relation-Class'` - the minor default relation over carrier
-- 
-- `_⇸_` - wrapped relation
--

record 
    Relation-Class' (X : Type) 
    : Type
  where
    constructor Mk
    field 
      get-it 
        : Relation-Type X X

instance  
  Relation-Class'-Wrap : 
      {X : Type} → 
      Wrap-Class (Relation-Type X X) (Relation-Class' X)
  Relation-Class'-Wrap {X} = Mk Relation-Class'.get-it Mk

-- the only method
_⇸_ : {X : Type} → ⦃ rel : Relation-Class' X ⦄ → Relation-Type X X
_⇸_ ⦃ rel ⦄ = get rel

record _`⇸`_ 
    {X : Type} 
    ⦃ rel : Relation-Class' X ⦄ 
    (src dst : X) 
    : Type
  where
    constructor Mk
    field 
      get-it 
        : Relation-Class'.get-it rel src dst

instance
  ⇸-Wrap : 
      {X : Type} → 
      ⦃ rel : Relation-Class' X ⦄ → 
      {src dst : X} → 
      Wrap-Class (Relation-Class'.get-it rel src dst) (src `⇸` dst)
  ⇸-Wrap = Mk _`⇸`_.get-it Mk

-----------------------------------------------------------
-- `Relation-Record` - a couple of a carrier and a relation
--

record 
    Relation-Record 
    : Type
  where
    constructor Mk
    field
      get-rel-ob-type 
        : Type
      ⦃ get-rel-rel-inst ⦄
        : Relation-Class get-rel-ob-type
open Relation-Record public

instance
  Relation-Record-Ob : Ob-Class Relation-Record
  Relation-Record-Ob = Mk get-rel-ob-type

