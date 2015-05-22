{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Common.Wrap-Class-Module where

open import CategoryTheory.Common.Type-Type-Module 
open import CategoryTheory.Common.Existential-Type-Module 

------------------------------------------
-- `Wrap` class - for isomorphic wrappers
--
-- `wrap x` method - wrap `x` into wrapped value
-- `get w` method - extract from wrapped value `w`
--

record Wrap-Class (X WX : Type) : Type
  where
    constructor Mk-Wrap
    field
      unwrap : WX → X
      wrap : X → WX

Wrap-Record : Type
Wrap-Record = ∃² Wrap-Class

unwrap : 
  {X WX : Type} → 
  ⦃ w-cl : Wrap-Class X WX ⦄ → 
  (WX → X)
unwrap ⦃ w-cl ⦄ = Wrap-Class.unwrap w-cl

wrap : 
  {X WX : Type} → 
  ⦃ w-cl : Wrap-Class X WX ⦄ → 
  (X → WX)
wrap ⦃ w-cl ⦄ = Wrap-Class.wrap w-cl

