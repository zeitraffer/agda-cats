{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Type-Category where

open import CategoryTheory.Common

-- identity function
ᵀ⟨⟩ : {X : Typeᵀ} → X −ᵀ→ X
ᵀ⟨⟩ = x ⟼ x

-- function composition
infixl 5 _ᵀ∘_
_ᵀ∘_ : {X Y Z : Typeᵀ} → X −ᵀ→ Y → Y −ᵀ→ Z → X −ᵀ→ Z
f ᵀ∘ g = x ⟼ g (f x)

−ᵀ→/map² : _−ᵀ→_ −ᴬ→ (_−ᵀ→_ ⟜ᴬ− _−ᵀ→_)
−ᵀ→/map² β φ = a ⟼ β (φ (a))

−ᵀ→/map¹ : _−ᵀ→_ −ᴬ→  (_−ᵀ→_ −ᴬ⊸ _−ᵀ→_)
−ᵀ→/map¹ α φ = a ⟼ φ (α (a))
