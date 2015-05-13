{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Instances.Type-TypeEndoSpan-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Operations.TypeSpan-Module
open import CategoryTheory.Classes.TypeSpan-Module

-----------------------------
-- `X ⟶ Y` - mappings between types
--

instance
  Type-is-TypeEndoSpan : TypeEndoSpan-Class Type
  Type-is-TypeEndoSpan = Mk TypeMap-Type

Type-TypeEndoSpan : TypeEndoSpan-Record
Type-TypeEndoSpan = Mk Type

-----------------------------
-- `X ⇸ Y` - spans between types
--

instance
  Type-is-TypeEndoSpan' : TypeEndoSpan-Class' Type
  Type-is-TypeEndoSpan' = Mk TypeSpan-Type

Type-TypeEndoSpan' : TypeEndoSpan-Record'
Type-TypeEndoSpan' = Mk Type
