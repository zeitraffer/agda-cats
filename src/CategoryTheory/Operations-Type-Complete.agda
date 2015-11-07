{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Type-Complete where

open import CategoryTheory.Common

infixr 8 _×ᵀ_
infixr -999 _,_

-- terminal object in "Type"
data ⊤ᵀ : Typeᵀ where
    ! : ⊤ᵀ

-- product in "Type"
data _×ᵀ_ (L R : Typeᵀ) : Typeᵀ where
    _,_ : (l : L) → (r : R) → L ×ᵀ R

-- nullary curring
curry0 : {X : Typeᵀ} → (⊤ᵀ −ᵀ⊸ X) −ᵀ→ (X)
curry0 x = x !

-- nullary uncurring
uncurry0 : {X : Typeᵀ} → (X) −ᵀ→ (⊤ᵀ −ᵀ⊸ X)
uncurry0 x t = x

-- binary curring
curry2 : {A B C : Typeᵀ} → ((A ×ᵀ B) −ᵀ⊸ C) −ᵀ→ (A −ᵀ⊸ (B −ᵀ⊸ C))
curry2 f a b = f (a , b)

-- binary uncurring
uncurry2 : {A B C : Typeᵀ} → (A −ᵀ⊸ (B −ᵀ⊸ C)) −ᵀ→ ((A ×ᵀ B) −ᵀ⊸ C)
uncurry2 f (a , b) = f a b
