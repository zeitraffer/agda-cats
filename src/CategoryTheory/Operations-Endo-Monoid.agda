{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Endo-Monoid where

open import CategoryTheory.Common
open import CategoryTheory.Operations-Type

ᴱ⟪⟫ : ᵀ0-ary' Endoᵀ
ᴱ⟪⟫ = A ⟼ A

_ᴱ∙_ : ᵀ2-ary' Endoᵀ
F ᴱ∙ G = A ⟼ G (F A)
