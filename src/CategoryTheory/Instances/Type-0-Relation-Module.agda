{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Instances.Type-0-Relation-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Classes.0-Relation-Module

-----------------------------
-- `X ⟶ Y` mapping of types
--

instance
  Type-0-Relation-Inst : 0-Relation-Class Type
  Type-0-Relation-Inst = Mk λ a b → (a → b)

-----------------------------
-- `X ⇸ Y` - mapping of types
--

instance
  Type-0-Relation'-Inst : 0-Relation-Class' Type
  Type-0-Relation'-Inst = Mk λ a b → 0-Relation-Type a b

Type-0-Relation : 0-Relation-Record
Type-0-Relation = Mk Type
