{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Common.Carrier-Class-Module where

open import CategoryTheory.Common.Type-Type-Module 
open import CategoryTheory.Common.Existential-Type-Module 

-------------------------------------------
-- (Carrier) class - for structures over carrier
--
-- (Carrier) method - forget structure
--

record Carrier-Class (X C : Type) : Type
  where
    constructor Mk-Carrier
    field 
      carrier : X → C

Carrier-Record : Type
Carrier-Record = ∃² Carrier-Class

Carrier : ⦃ c-rec : Carrier-Record ⦄ → (∃².base₁ c-rec → ∃².base₂ c-rec)
Carrier ⦃ c-rec ⦄ = Carrier-Class.carrier (∃².fiber c-rec)

