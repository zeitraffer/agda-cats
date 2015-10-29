{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Endo where

open import CategoryTheory.Common
open import CategoryTheory.Operations-Type
open import CategoryTheory.Operations-Endo-Monoid

ᴱneutral' : ᵀ0-ary' Endoᵀ
ᴱneutral' = ᴱ⟪⟫

ᴱneutral : ᵀ0-ary Endoᵀ
ᴱneutral = ᵀ0-wrap ᴱneutral'

ᴱcompose' : ᵀ2-ary' Endoᵀ
ᴱcompose' = _ᴱ∙_

ᴱcompose : ᵀ2-ary Endoᵀ
ᴱcompose = ᵀ2-wrap ᴱcompose'

ᴱ0-ary : preᵀ Endoᵀ
ᴱ0-ary A = ᴱ⟪⟫ −ᴱ→ A

ᴱ2-ary : preᵀ Endoᵀ
ᴱ2-ary A = (A ᴱ∙ A) −ᴱ→ A
