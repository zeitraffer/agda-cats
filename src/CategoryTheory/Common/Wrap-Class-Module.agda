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
      get : WX → X
      wrap : X → WX

Wrap-Record : Type
Wrap-Record = ∃² Wrap-Class

get : ⦃ w-rec : Wrap-Record ⦄ → (∃².base₂ w-rec → ∃².base₁ w-rec)
get ⦃ w-rec ⦄ = Wrap-Class.get (∃².fiber w-rec)

wrap : ⦃ w-rec : Wrap-Record ⦄ → (∃².base₁ w-rec → ∃².base₂ w-rec)
wrap ⦃ w-rec ⦄ = Wrap-Class.wrap (∃².fiber w-rec)

