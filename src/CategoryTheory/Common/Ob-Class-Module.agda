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
Ob-Record = ∃ Ob-Class

Ob : ⦃ o-rec : Ob-Record ⦄ → (∃.base o-rec → Type)
Ob ⦃ o-rec ⦄ = Ob-Class.ob (∃.fiber o-rec)

