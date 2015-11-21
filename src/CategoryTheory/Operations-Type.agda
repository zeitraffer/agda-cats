{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Type where

open import CategoryTheory.Common
open import CategoryTheory.Operations-Type-Complete

ᵀ0-ary : Endoᵀ
ᵀ0-ary A = ⊤ᵀ −ᵀ→ A

ᵀ0-ary' : Endoᵀ
ᵀ0-ary' A = A

ᵀ0-wrap : ᵀ0-ary' −ᴾ→ ᵀ0-ary
ᵀ0-wrap = uncurry0

ᵀ0-unwrap : ᵀ0-ary −ᴾ→ ᵀ0-ary'
ᵀ0-unwrap = curry0

ᵀ2-ary : Endoᵀ
ᵀ2-ary A = (A ×ᵀ A) −ᵀ→ A

ᵀ2-ary' : Endoᵀ
ᵀ2-ary' A = A → A → A

ᵀ2-wrap : ᵀ2-ary' −ᴾ→ ᵀ2-ary
ᵀ2-wrap = uncurry2

ᵀ2-unwrap : ᵀ2-ary −ᴾ→ ᵀ2-ary'
ᵀ2-unwrap = curry2

ᵀL-act : Relᵀ
ᵀL-act A M = (A ×ᵀ M) −ᵀ→ M

ᵀL-act' : Relᵀ
ᵀL-act' A M = A → M → M

ᵀL-wrap : ᵀL-act' −ᴬ→ ᵀL-act
ᵀL-wrap = uncurry2

ᵀL-unwrap : ᵀL-act −ᴬ→ ᵀL-act'
ᵀL-unwrap = curry2

ᵀneutral' : ᵀ0-ary' Typeᵀ
ᵀneutral' = ⊤ᵀ

ᵀneutral : ᵀ0-ary Typeᵀ
ᵀneutral = ᵀ0-wrap ᵀneutral'

ᵀcompose' : ᵀ2-ary' Typeᵀ
ᵀcompose' = _×ᵀ_

ᵀcompose : ᵀ2-ary Typeᵀ
ᵀcompose = ᵀ2-wrap ᵀcompose'
