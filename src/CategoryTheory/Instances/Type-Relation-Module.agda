{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Instances.Type-Relation-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Classes.Relation-Module

-----------------------------
-- `X ⟶ Y` mapping of types
--

instance
  Type-Relation-Inst : Relation-Class Type
  Type-Relation-Inst = Mk λ a b → (a → b)

-----------------------------
-- `X ⇸ Y` - mapping of types
--

instance
  Type-Relation'-Inst : Relation-Class' Type
  Type-Relation'-Inst = Mk λ a b → Relation-Type a b

Type-Relation : Relation-Record
Type-Relation = Mk Type
