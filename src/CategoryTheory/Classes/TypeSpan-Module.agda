{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Classes.TypeSpan-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Operations.TypeSpan-Module

-------------------------------------------------------
-- `TypeEndoSpan-Class` - the major default relation over carrier
-- 
-- `_⟶_` - wrapped relation
--

record TypeEndoSpan-Class (X : Type) : Type
  where
    constructor Mk
    field 
      it : TypeSpan-Type X X

instance  
  TypeEndoSpan-Class-is-Wrap : 
      {X : Type} → 
      Wrap-Class (TypeSpan-Type X X) (TypeEndoSpan-Class X)
  TypeEndoSpan-Class-is-Wrap = Mk TypeEndoSpan-Class.it Mk

-- the only method
_⟶_ : 
    {X : Type} → 
    ⦃ rel : TypeEndoSpan-Class X ⦄ → 
    TypeSpan-Type X X
_⟶_ ⦃ rel ⦄ = get rel

-- the only method wrapper
record _`⟶`_ 
    {X : Type} 
    ⦃ rel : TypeEndoSpan-Class X ⦄
    (src dst : X) 
    : Type
  where
    constructor Mk
    field 
      it : src ⟶ dst

instance
  ⟶-is-Wrap : 
      {X : Type} → 
      ⦃ rel : TypeEndoSpan-Class X ⦄ → 
      {src dst : X} → 
      Wrap-Class (src ⟶ dst) (src `⟶` dst)
  ⟶-is-Wrap = Mk _`⟶`_.it Mk

--------------------------------------------------------------
-- `TypeEndoSpan-Class'` - the minor default relation over carrier
-- 
-- `_⇸_` - wrapped relation
--

record TypeEndoSpan-Class' (X : Type) : Type
  where
    constructor Mk
    field 
      it : TypeSpan-Type X X

instance  
  TypeEndoSpan-Class'-is-Wrap : 
      {X : Type} → 
      Wrap-Class (TypeSpan-Type X X) (TypeEndoSpan-Class' X)
  TypeEndoSpan-Class'-is-Wrap = Mk TypeEndoSpan-Class'.it Mk

-- the only method
_⇸_ : 
    {X : Type} → 
    ⦃ rel : TypeEndoSpan-Class' X ⦄ → 
    TypeSpan-Type X X
_⇸_ ⦃ rel ⦄ = get rel

record _`⇸`_ 
    {X : Type} 
    ⦃ rel : TypeEndoSpan-Class' X ⦄ 
    (src dst : X) 
    : Type
  where
    constructor Mk
    field 
      it : src ⇸ dst

instance
  ⇸-is-Wrap : 
      {X : Type} → 
      ⦃ rel : TypeEndoSpan-Class' X ⦄ → 
      {src dst : X} → 
      Wrap-Class (src ⇸ dst) (src `⇸` dst)
  ⇸-is-Wrap = Mk _`⇸`_.it Mk

-----------------------------------------------------------
-- `TypeEndoSpan-Record` - a couple of a carrier and a relation
--

record TypeEndoSpan-Record : Type
  where
    constructor Mk
    field
      ob-type : Type
      ⦃ rel-inst ⦄ : TypeEndoSpan-Class ob-type

instance
  TypeEndoSpan-Record-is-Ob : Ob-Class TypeEndoSpan-Record
  TypeEndoSpan-Record-is-Ob = Mk TypeEndoSpan-Record.ob-type

-----------------------------------------------------------
-- `TypeEndoSpan-Record` - a couple of a carrier and a relation
--

record TypeEndoSpan-Record' : Type
  where
    constructor Mk
    field
      ob-type : Type
      ⦃ rel-inst ⦄ : TypeEndoSpan-Class' ob-type

instance
  TypeEndoSpan-Record'-is-Ob : Ob-Class TypeEndoSpan-Record'
  TypeEndoSpan-Record'-is-Ob = Mk TypeEndoSpan-Record'.ob-type

