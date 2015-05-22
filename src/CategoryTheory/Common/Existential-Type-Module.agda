{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Common.Existential-Type-Module where

open import CategoryTheory.Common.Type-Type-Module 

-------------------------------------------
-- (∃) type - for: 
-- dependent sums (dependent type theory)
-- existential types (System F, etc)
-- total space of fibration (topology)
-- quantifier of existence (logics)
--

record ∃¹ 
    {Base : Type} 
    (Fiber : Base → Type) 
    : Type 
  where
    constructor ℯ¹
    field
      {base} : Base
      fiber : Fiber base

record ∃² 
    {Base₁ Base₂ : Type} 
    (Fiber : Base₁ → Base₂ → Type) 
    : Type 
  where
    constructor ℯ²
    field
      {base₁} : Base₁
      {base₂} : Base₂
      fiber : Fiber base₁ base₂

