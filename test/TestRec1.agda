{-# OPTIONS --type-in-type --copatterns #-}

module TestRec1 where

---------------------------

-- synonym for the type of types
Typeᵀ : Set
Typeᵀ = Set

-- synomym for lambda syntax
λ-syntax : {A : Typeᵀ} → {B : A → Typeᵀ} → ((a : A) → B a) → ((a : A) → B a)
λ-syntax f = f
syntax λ-syntax (λ a → b) = [ a ↦ b ]

---------------------------
-- definitions of type-classes

record Baseᴿ : Typeᵀ where
  constructor Mk
  field fBase : Typeᵀ

Baseᴹ : ⦃ B : Baseᴿ ⦄ → Typeᵀ
Baseᴹ ⦃ B ⦄ = Baseᴿ.fBase B

record Fiberᴿ : Typeᵀ where
  constructor Mk
  field fBase : Baseᴿ
  field fFiber : Baseᴹ → Typeᵀ

instance
  F→B : ⦃ F : Fiberᴿ ⦄ → Baseᴿ
  F→B ⦃ F ⦄ = Fiberᴿ.fBase F

Fiberᴹ : ⦃ F : Fiberᴿ ⦄ → Baseᴹ → Typeᵀ
Fiberᴹ ⦃ F ⦄ = Fiberᴿ.fFiber F

---------------------------
-- generic usage

useBase : ⦃ B : Baseᴿ ⦄ → Typeᵀ
useBase = Baseᴹ

useFiber : ⦃ F : Fiberᴿ ⦄ → Baseᴹ → Typeᵀ
useFiber = Fiberᴹ

useFB : ⦃ F : Fiberᴿ ⦄ → Typeᵀ
useFB = Baseᴹ

---------------------------
-- concrete usage

instance
  iFiber : Fiberᴿ
  iFiber = Mk (Mk Typeᵀ) [ type ↦ (type → Typeᵀ) ]

getBase : Typeᵀ
getBase = Baseᴹ

getFiber : Baseᴹ → Typeᵀ
getFiber = Fiberᴹ
