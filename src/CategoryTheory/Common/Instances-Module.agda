{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Common.Instances-Module where

open import CategoryTheory.Common.Type-Type-Module 
open import CategoryTheory.Common.Existential-Type-Module 
open import CategoryTheory.Common.Ob-Class-Module 
open import CategoryTheory.Common.Carrier-Class-Module 
open import CategoryTheory.Common.Wrap-Class-Module 

-------------------------------
-- sample instances
--

instance
  Ob-Record-is-Ob : Ob-Class Ob-Record
  Ob-Record-is-Ob = Mk-Ob ∃¹.base

Ob-Record-Ob : Ob-Record
Ob-Record-Ob = ℯ¹ Ob-Record-is-Ob

instance
  Carrier-Record-is-Ob : Ob-Class Carrier-Record
  Carrier-Record-is-Ob = Mk-Ob ∃².base₁

Carrier-Record-Ob : Ob-Record
Carrier-Record-Ob = ℯ¹ Carrier-Record-is-Ob

instance
  Wrap-Record-is-Ob : Ob-Class Wrap-Record
  Wrap-Record-is-Ob = Mk-Ob ∃².base₂

Wrap-Record-Ob : Ob-Record
Wrap-Record-Ob = ℯ¹ Wrap-Record-is-Ob

instance
  Ob-Class-is-Wrap : {X : Type} → Wrap-Class (X → Type) (Ob-Class X)
  Ob-Class-is-Wrap = Mk-Wrap Ob-Class.ob Mk-Ob

Ob-Class-Wrap : {X : Type} → Wrap-Record
Ob-Class-Wrap {X} = ℯ² (Ob-Class-is-Wrap {X})

instance
  Carrier-Class-is-Wrap : {X C : Type} → Wrap-Class (X → C) (Carrier-Class X C)
  Carrier-Class-is-Wrap = Mk-Wrap Carrier-Class.carrier Mk-Carrier

Carrier-Class-Wrap : {X C : Type} → Wrap-Record
Carrier-Class-Wrap {X} {C} = ℯ² (Carrier-Class-is-Wrap {X} {C})
