{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-List where

open import CategoryTheory.Common
open import CategoryTheory.Operations-Type
open import CategoryTheory.Operations-Type-Category
open import CategoryTheory.Operations-Endo

infixr 5 _∙_

-- "List" as free monoid
data Listᵀ (X : Typeᵀ) : Typeᵀ where
    [] : Listᵀ X
    _∙_ : X → Listᵀ X → Listᵀ X

-- catamorphism
List/cata' : {X R : Typeᵀ} → R → (X → R → R) → Listᵀ X → R
List/cata' {X} {R} nil cons = cata
  where
    cata : Listᵀ X → R
    cata [] = nil
    cata (head ∙ tail) = cons head (cata tail)

-- functor acts on morphisms
List/map : {A B : Typeᵀ} → (A −ᵀ→ B) → (Listᵀ A −ᵀ→ Listᵀ B)
List/map f = List/cata' [] (a ⟼ bs ⟼ f a ∙ bs)

-- monoid neutral element
List/neutral' : {X : Typeᵀ} → ᵀ0-ary' (Listᵀ X)
List/neutral' = []

-- monoid composition
List/compose' : {X : Typeᵀ} → ᵀ2-ary' (Listᵀ X)
List/compose' = List/cata' ᵀ⟨⟩ (x ⟼ f ⟼ l ⟼ x ∙ f l)

-- monad identity
List/return : ᴱ0-ary Listᵀ
List/return x = x ∙ []

-- monad multiplication
List/flatten : ᴱ2-ary Listᵀ
List/flatten = List/cata' List/neutral' List/compose'
