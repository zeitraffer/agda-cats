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

_−ᴬ→_ : {A B : Typeᵀ} → relᵀ (A ⇸ B)
_−ᴬ→_ {A} {B} _⇒₁_ _⇒₂_ = {a : A} → {b : B} → (a ⇒₁ b) −ᵀ→ (a ⇒₂ b)
