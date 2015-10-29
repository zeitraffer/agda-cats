{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Arrow-Category where

open import CategoryTheory.Common

↠/co-map :
    {U₁ U₂ : Typeᵀ} →  (U₁ → U₂) →
    {ob : Typeᵀ} →
    ob ↠ U₁ → ob ↠ U₂
↠/co-map f _⇒_ a b = f (a ⇒ b)

↠/contra-map :
    {U : Typeᵀ} →
    {ob₁ ob₂ : Typeᵀ} → (ob₁ → ob₂) →
    ob₂ ↠ U → ob₁ ↠ U
↠/contra-map f _⇒_ a b = (f a ⇒ f b)

_−ᴬ→_ : {ob : Typeᵀ} → (ob ↠ Typeᵀ) ↠ Typeᵀ
_−ᴬ→_ {ob} _⇒₁_ _⇒₂_ = {a b : ob} → (a ⇒₁ b) −ᵀ→ (a ⇒₂ b)
