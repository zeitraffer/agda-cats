{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Type-Category where

open import CategoryTheory.Common

-- identity function
ᵀ⟨⟩ : {X : Typeᵀ} → X −ᵀ→ X
ᵀ⟨⟩ = x ⟼ x

-- function composition
_ᵀ∘_ : {X Y Z : Typeᵀ} → X −ᵀ→ Y → Y −ᵀ→ Z → X −ᵀ→ Z
f ᵀ∘ g = x ⟼ g (f x)
