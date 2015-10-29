{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Endo-Category where

open import CategoryTheory.Common

-- identity function
ᴱ⟨⟩ : {X : Endoᵀ} → X −ᴱ→ X
ᴱ⟨⟩ = x ⟼ x

-- function composition
_ᴱ∘_ : {X Y Z : Endoᵀ} → X −ᴱ→ Y → Y −ᴱ→ Z → X −ᴱ→ Z
f ᴱ∘ g = x ⟼ g (f x)
