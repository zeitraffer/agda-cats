{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Operations.TypeSpan-Module where

open import CategoryTheory.Common-Module

-----------------------------
-- `TypeMap` type-synonym
--

TypeMap-Type : (src dst : Type) → Type
TypeMap-Type X Y = X → Y

-----------------------------
-- `TypeSpan` type-synonym
--

TypeSpan-Type : (src dst : Type) → Type
TypeSpan-Type X Y = X → Y → Type

