{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Common.Ob-Class-Module where

open import CategoryTheory.Common.Type-Type-Module 
open import CategoryTheory.Common.Existential-Type-Module 

-------------------------------------------
-- (Ob) class - for structures over carrier
--
-- (Ob) method - forget structure
--

record Ob-Class (X : Type) : Type
  where
    constructor Mk-Ob
    field 
      ob : X → Type

Ob-Record : Type
Ob-Record = ∃¹ Ob-Class

Ob : 
    {X : Type} → 
    ⦃ o-cl : Ob-Class X ⦄ → 
    (X → Type)
Ob ⦃ o-cl ⦄ = Ob-Class.ob o-cl

