{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Arrow-Category where

open import CategoryTheory.Common

↠/map² :
    {U₁ U₂ : Typeᵀ} →  (U₁ → U₂) →
    {ob : Typeᵀ} →
    ob ↠ U₁ → ob ↠ U₂
↠/map² f _⇒_ a b = f (a ⇒ b)

↠/map¹ :
    {U : Typeᵀ} →
    {ob₁ ob₂ : Typeᵀ} → (ob₁ → ob₂) →
    ob₂ ↠ U → ob₁ ↠ U
↠/map¹ f _⇒_ a b = (f a ⇒ f b)

-- identity mapping
ᴬ⟨⟩ : {ob : Typeᵀ} → {A : relᵀ ob} → A −ᴬ→ A
ᴬ⟨⟩ = x ⟼ x

-- function composition
infixl 5 _ᴬ∘_
_ᴬ∘_ :
    {ob : Typeᵀ} → {X Y Z : relᵀ ob} → 
    X −ᴬ→ Y → Y −ᴬ→ Z → X −ᴬ→ Z
f ᴬ∘ g = x ⟼ g (f x)
