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
Typeᴹ : 0-Monoidᵀ
Typeᴹ = 𝞂 Typeᵀ Type/0-Monoid

-- monoid of relations (arrows) wrt composition
instance
    Arrow/0-Monoid : {ob : Typeᵀ} → 0-Monoidᴿ (ob ↠ Typeᵀ)
    Arrow/0-Monoid = Mk (List/cata' ①ᴬ _⊗ᴬ_)
Arrowᴹ : (ob : Typeᵀ) → 0-Monoidᵀ
Arrowᴹ ob = 𝞂 (ob ↠ Typeᵀ) Arrow/0-Monoid

-- monoid of lists wrt concatenations (the free monoid)
instance
    List/0-Monoid : {Item : Typeᵀ} → 0-Monoidᴿ (Listᵀ Item)
    List/0-Monoid = Mk List/flatten
Listᴹ : (Item : Typeᵀ) → 0-Monoidᵀ
Listᴹ Item = 𝞂 (Listᵀ Item) List/0-Monoid

ℕᵀ : Typeᵀ
ℕᵀ = Listᵀ ⊤ᵀ

0ᴺ : ℕᵀ
0ᴺ = []
1ᴺ : ℕᵀ
1ᴺ = ! ∙ 0ᴺ
2ᴺ : ℕᵀ
2ᴺ = ! ∙ 1ᴺ
3ᴺ : ℕᵀ
3ᴺ = ! ∙ 2ᴺ

private
  module Test where
    test0 : ⟪⟫ ≡ 0ᴺ
    test0 = Refl
    test1 : ⟪ 1ᴺ ⟫ ≡ 1ᴺ
    test1 = Refl
    test2 : ⟪ 1ᴺ ∙ 1ᴺ ⟫ ≡ 2ᴺ
    test2 = Refl
    test3 : ⟪ ⟪⟫ ∙ (⟪ 1ᴺ ⟫) ∙ (⟪ 1ᴺ ∙ 1ᴺ ⟫) ⟫ ≡ 3ᴺ
    test3 = Refl
