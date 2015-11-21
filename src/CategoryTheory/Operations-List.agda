{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-List where

open import CategoryTheory.Common
open import CategoryTheory.Operations-Type
open import CategoryTheory.Operations-Type-Category
open import CategoryTheory.Operations-Type-Complete
open import CategoryTheory.Operations-Endo
open import CategoryTheory.Classes-0-Graph
open import CategoryTheory.Instances-0-Graph

infixr 5 _∙_

-- "List" as free monoid
data Listᵀ (X : Typeᵀ) : Typeᵀ where
    [] : Listᵀ X
    _∙_ : X → Listᵀ X → Listᵀ X

-- catamorphism (curried)
List/cata' : {X R : Typeᵀ} → ᵀ0-ary' R → ᵀL-act' X R → Listᵀ X ⟶ R
List/cata' {X} {R} nil cons = cata
  where
    cata : Listᵀ X → R
    cata [] = nil
    cata (head ∙ tail) = cons head (cata tail)

-- catamorphism (uncurried)
List/cata : {X R : Typeᵀ} → ᵀ0-ary R → ᵀL-act X R → Listᵀ X ⟶ R
List/cata nil cons = List/cata' (ᵀ0-unwrap nil) (ᵀL-unwrap cons)

-- functor acts on morphisms
List/map : {A B : Typeᵀ} → A ⟶ B → Listᵀ A ⟶ Listᵀ B
List/map f = List/cata' [] (f ᵀ∘ _∙_)

-- (a ⟼ bs ⟼ f a ∙ bs)

-- monoid neutral element
List/neutral' : {X : Typeᵀ} → ᵀ0-ary' (Listᵀ X)
List/neutral' = []

-- monoid composition
List/compose' : {X : Typeᵀ} → ᵀ2-ary' (Listᵀ X)
List/compose' = List/cata' ᵀ⟨⟩ (_∙_ ᵀ∘ −ᵀ→/map²)

-- monad identity
List/return : ᴱ0-ary Listᵀ
List/return x = x ∙ []

-- monad multiplication
List/flatten : ᴱ2-ary Listᵀ
List/flatten = List/cata' List/neutral' List/compose'
