{-# OPTIONS --type-in-type --copatterns #-}

module TestRecᴹ where

Type : Set
Type = Set

λ-syntax : {A B : Type} → (A → B) → (A → B)
λ-syntax f = f

syntax λ-syntax (λ x → B) = ℓ x ↦ B

---------------------------
-- definitions of type-classes




---------------------------
-- generic usage

useBase : ⦃ base : BaseRec ⦄ → Type
useBase = Base

useFiber : ⦃ fiber : FiberRec ⦄ → Base → Type
useFiber = Fiber

useFB : ⦃ fiber : FiberRec ⦄ → Type
useFB = Base

---------------------------
-- concrete usage

instance
  iFiber : FiberRec
  iFiber = Mk (Mk Type) (𝝺 type ↦ (type → Type))

getBase : Type
getBase = Base

getFiber : Base → Type
getFiber = Fiber
