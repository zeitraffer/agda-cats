{-# OPTIONS --type-in-type #-}

module CategoryTheory.Classes-0-Monoid where

open import CategoryTheory.Common
open import CategoryTheory.Classes-Common
open import CategoryTheory.Instances-Common
open import CategoryTheory.Operations-List

-- "Monoid" is a capability of reducing "List"

0-Monoid-applyᵀ : Endoᵀ
0-Monoid-applyᵀ carrier = Listᵀ carrier → carrier

record 0-Monoidᴿ (carrier : Typeᵀ) : Typeᵀ where
    constructor Mk
    field apply : 0-Monoid-applyᵀ carrier
0-Monoidᵀ = 𝝨 0-Monoidᴿ

instance
    0-Monoid/Wrapper :
        {carrier : Typeᵀ} →
        Wrapperᴿ (0-Monoid-applyᵀ carrier) (0-Monoidᴿ carrier)
    Wrapperᴿ.get-Get 0-Monoid/Wrapper = 0-Monoidᴿ.apply
    Wrapperᴿ.get-Put 0-Monoid/Wrapper = Mk

0-Concat' :
    {carrier : Typeᵀ} →
    ⦃ 𝕄 : 0-Monoidᴿ carrier ⦄ →
    0-Monoid-applyᵀ carrier
0-Concat' ⦃ 𝕄 ⦄ = Get 𝕄

0-Concat :
    ⦃ 𝕄 : 0-Monoidᵀ ⦄ →
    0-Monoid-applyᵀ (Arg 𝕄)
0-Concat ⦃ 𝕄 ⦄ = Get (App 𝕄)

--------------------------------------------------------------- syntax

infix 0 ⟪_
infix 100 _⟫

-- ⟪ a ∙ b ∙ c ⟫ denote monoid concatenation, see tests

⟪⟫ : ⦃ 𝕄 : 0-Monoidᵀ ⦄ → Arg 𝕄
⟪⟫ = 0-Concat List/neutral'

⟪'⟫ : {carrier : Typeᵀ} → ⦃ 𝕄 : 0-Monoidᴿ carrier ⦄ → carrier
⟪'⟫ = 0-Concat' List/neutral'

⟪_ : ⦃ 𝕄 : 0-Monoidᵀ ⦄ → 0-Monoid-applyᵀ (Arg 𝕄)
⟪_ = 0-Concat

⟪'_ : {carrier : Typeᵀ} → ⦃ 𝕄 : 0-Monoidᴿ carrier ⦄ → 0-Monoid-applyᵀ carrier
⟪'_ = 0-Concat'

_⟫ : {carrier : Typeᵀ} → carrier → Listᵀ (carrier)
_⟫ = List/return
