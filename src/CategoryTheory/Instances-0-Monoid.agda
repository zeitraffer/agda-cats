{-# OPTIONS --type-in-type #-}

module CategoryTheory.Instances-0-Monoid where

open import CategoryTheory.Common
open import CategoryTheory.Classes-Common
open import CategoryTheory.Instances-Common
open import CategoryTheory.Operations-List
open import CategoryTheory.Operations-Type-Complete
open import CategoryTheory.Operations-Arrow-Monoid
open import CategoryTheory.Classes-0-Monoid

-- monoid of types wrt cartesian product
instance
    Type/0-Monoid : 0-Monoidᴿ Typeᵀ
    Type/0-Monoid = Mk (List/cata' ⊤ᵀ _×ᵀ_)
instance
    Typeᴹ : 0-Monoidᵀ
    Typeᴹ = ℯ Typeᵀ Type/0-Monoid

-- monoid of relations (arrows) wrt composition
instance
    Arrow/0-Monoid : {ob : Typeᵀ} → 0-Monoidᴿ (ob ↠ Typeᵀ)
    Arrow/0-Monoid = Mk (List/cata' ①ᴬ _⊗ᴬ_)
instance
    Arrowᴹ : {ob : Typeᵀ} → 0-Monoidᵀ
    Arrowᴹ {ob} = ℯ (ob ↠ Typeᵀ) Arrow/0-Monoid

-- "List" is monoid
instance
    List/0-Monoid : {Item : Typeᵀ} → 0-Monoidᴿ (Listᵀ Item)
    List/0-Monoid = Mk List/flatten
