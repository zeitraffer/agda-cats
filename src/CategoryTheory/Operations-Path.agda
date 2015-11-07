{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Path where

open import CategoryTheory.Common
open import CategoryTheory.Operations-Type
open import CategoryTheory.Operations-Type-Category
open import CategoryTheory.Operations-Endo
open import CategoryTheory.Operations-Arrow-Category
open import CategoryTheory.Operations-Arrow-Monoid
open import CategoryTheory.Classes-0-Graph
open import CategoryTheory.Instances-0-Graph

module Path {ob : Typeᵀ} (_⇒_ : relᵀ ob) where
  infixr 5 _∘_
  data _⇛_ : relᵀ ob where
    [] : {a : ob} → a ⇛ a
    _∘_ : {a b c : ob} → a ⇒ b → b ⇛ c → a ⇛ c

open Path using ([]; _∘_) renaming (_⇛_ to Pathᴬ) public

-- catamorphism
Path/cata :
    {ob : Typeᵀ} → {X R : relᵀ ob} →
    ①ᴬ ⟶ R → (X ⊗ᴬ R) ⟶ R → Pathᴬ X ⟶ R
Path/cata {ob} {X} {R} nil cons = cata
  where
    cata : Pathᴬ X ⟶ R
    cata [] = nil !
    cata (head ∘ tail) = cons (head , (cata tail))

-- functor acts on morphisms
Path/map :
    {ob : Typeᵀ} → {A B : relᵀ ob} →
    (A ⟶ B) → (Pathᴬ A ⟶ Pathᴬ B)
Path/map f = Path/cata (! ᴬ⟼ []) (a ⟼ bs ⟼ f a ∙ bs)

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
