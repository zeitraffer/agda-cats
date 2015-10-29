{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Type where

open import CategoryTheory.Common
open import CategoryTheory.Operations-Type-Complete

ᵀ0-ary : Endoᵀ
ᵀ0-ary A = ⊤ᵀ −ᵀ→ A

ᵀ0-ary' : Endoᵀ
ᵀ0-ary' A = A

ᵀ0-wrap : ᵀ0-ary' −ᴱ→ ᵀ0-ary
ᵀ0-wrap = uncurry0

ᵀ0-unwrap : ᵀ0-ary −ᴱ→ ᵀ0-ary'
ᵀ0-unwrap = curry0

ᵀ2-ary : Endoᵀ
ᵀ2-ary A = (A ×ᵀ A) −ᵀ→ A

ᵀ2-ary' : Endoᵀ
ᵀ2-ary' A = A → A → A

ᵀ2-wrap : ᵀ2-ary' −ᴱ→ ᵀ2-ary
ᵀ2-wrap = uncurry2

ᵀ2-unwrap : ᵀ2-ary −ᴱ→ ᵀ2-ary'
ᵀ2-unwrap = curry2

ᵀneutral' : ᵀ0-ary' Typeᵀ
ᵀneutral' = ⊤ᵀ

ᵀneutral : ᵀ0-ary Typeᵀ
ᵀneutral = ᵀ0-wrap ᵀneutral'

ᵀcompose' : ᵀ2-ary' Typeᵀ
ᵀcompose' = _×ᵀ_

ᵀcompose : ᵀ2-ary Typeᵀ
ᵀcompose = ᵀ2-wrap ᵀcompose'
