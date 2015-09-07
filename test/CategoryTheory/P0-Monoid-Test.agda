{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.P0-Monoid-Test where

open import CategoryTheory.Common-Module
open import CategoryTheory.Continuous-Module

data Nᵀ : Typeᵀ
  where
    0ᴺ : Nᵀ
    _+1ᴺ : Nᵀ → Nᵀ

N/cata : {Rᵀ : Typeᵀ} → Rᵀ → (Rᵀ → Rᵀ) → Nᵀ → Rᵀ
N/cata {Rᵀ} zero succ = cata
  where
    cata : Nᵀ → Rᵀ
    cata 0ᴺ = zero
    cata (n +1ᴺ) = succ (cata n)

1ᴺ : Nᵀ
1ᴺ = 0ᴺ +1ᴺ

_+ᴺ_ : Nᵀ → Nᵀ → Nᵀ
_+ᴺ_ n = N/cata n _+1ᴺ

instance
  N:P0-Monoid : P0-Monoidᴿ
  N:P0-Monoid = Mk Nᵀ (List/cata 0ᴺ _+ᴺ_)

test-0ᴺ : Nᵀ
test-0ᴺ = ⟪⟫

test-1ᴺ : Nᵀ
test-1ᴺ = ⟪ 1ᴺ ⟫

test-2ᴺ : Nᵀ
test-2ᴺ = ⟪ 1ᴺ , 1ᴺ ⟫

test-3ᴺ : Nᵀ
test-3ᴺ = ⟪ test-0ᴺ , test-1ᴺ , test-2ᴺ ⟫

---------------------------------------------------------------

data ⊤ᵀ : Typeᵀ
  where
    ! : ⊤ᵀ

record _⨯ᵀ_ (Lᵀ Rᵀ : Typeᵀ) : Typeᵀ
  where
    constructor _,_
    field pr-L : Lᵀ
    field pr-R : Rᵀ
open _⨯ᵀ_

instance
  Type:P0-Monoid : P0-Monoidᴿ
  Type:P0-Monoid = Mk Typeᵀ (List/cata ⊤ᵀ _⨯ᵀ_)
