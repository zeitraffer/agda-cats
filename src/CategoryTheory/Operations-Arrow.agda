{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Arrow where

open import CategoryTheory.Common
open import CategoryTheory.Operations-Arrow-Category
open import CategoryTheory.Operations-Arrow-Monoid

ᴬ0-ary : {ob : Typeᵀ} → preᵀ (relᵀ ob)
ᴬ0-ary R = ①ᴬ −ᴬ→ R

ᴬ0-ary' : {ob : Typeᵀ} → preᵀ (relᵀ ob)
ᴬ0-ary' {ob} _⇛_ = {a : ob} → a ⇛ a

ᴬ0-wrap : {ob : Typeᵀ} → ᴬ0-ary' {ob} −ᴱ→ ᴬ0-ary {ob}
ᴬ0-wrap f ! = f

ᴬ0-unwrap : {ob : Typeᵀ} → ᴬ0-ary {ob} −ᴱ→ ᴬ0-ary' {ob}
ᴬ0-unwrap f = f !

ᴬ2-ary : {ob : Typeᵀ} → preᵀ (relᵀ ob)
ᴬ2-ary A = (A ⊗ᴬ A) −ᴬ→ A

ᴬ2-ary' : {ob : Typeᵀ} → preᵀ (relᵀ ob)
ᴬ2-ary' A = A −ᴬ→ (A −ᴬ⊸ A)
