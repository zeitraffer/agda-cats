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

_+ᴺ_ : Nᵀ → Nᵀ → Nᵀ
_+ᴺ_ n = N/cata n _+1ᴺ

-- additive instance (default)
instance
  N:Monoid:+ : P0-Monoidᴿ
  N:Monoid:+ = Mk Nᵀ (List/cata 0ᴺ _+ᴺ_)

1ᴺ : Nᵀ
1ᴺ = 0ᴺ +1ᴺ

_⨯ᴺ_ : Nᵀ → Nᵀ → Nᵀ
_⨯ᴺ_ n = N/cata 0ᴺ (_+ᴺ_ n)

-- multiplicative instance (non-default)
N:Monoid:⨯ : P0-Monoidᴿ
N:Monoid:⨯ = Mk Nᵀ (List/cata 0ᴺ _+ᴺ_)

---------------------------------------------------------------

test-0ᴺ : Nᵀ
test-0ᴺ = ⟪⟫

test-1ᴺ : Nᵀ
test-1ᴺ = ⟪ 1ᴺ ⟫

test-2ᴺ : Nᵀ
test-2ᴺ = ⟪ 1ᴺ , 1ᴺ ⟫

test-3ᴺ : Nᵀ
test-3ᴺ = ⟪ test-0ᴺ , test-1ᴺ , test-2ᴺ ⟫

---------------------------------------------------------------

data 0ᵀ : Typeᵀ
  where

data _+ᵀ_ (Lᵀ Rᵀ : Typeᵀ) : Typeᵀ
  where
    incl-L : Lᵀ → Lᵀ +ᵀ Rᵀ
    incl-R : Rᵀ → Lᵀ +ᵀ Rᵀ

record 1ᵀ : Typeᵀ
  where
    constructor !

record _⨯ᵀ_ (Lᵀ Rᵀ : Typeᵀ) : Typeᵀ
  where
    constructor _::_
    field proj-L : Lᵀ
    field proj-R : Rᵀ

instance
  Type:Monoid:+ : P0-Monoidᴿ
  Type:Monoid:+ = Mk Typeᵀ (List/cata 0ᵀ _+ᵀ_)

Type:Monoid:⨯ : P0-Monoidᴿ
Type:Monoid:⨯ = Mk Typeᵀ (List/cata 1ᵀ _⨯ᵀ_)

---------------------------------------------------------------

test-0ᵀ : Typeᵀ
test-0ᵀ = ⟪⟫

test-1ᵀ : Typeᵀ
test-1ᵀ = ⟪ 1ᵀ ⟫

test-2ᵀ : Typeᵀ
test-2ᵀ = ⟪ 1ᵀ , 1ᵀ ⟫

test-3ᵀ : Typeᵀ
test-3ᵀ = ⟪ test-0ᵀ , test-1ᵀ , test-2ᵀ ⟫

---------------------------------------------------------------
