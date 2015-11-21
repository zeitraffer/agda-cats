{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Path where

open import CategoryTheory.Common
open import CategoryTheory.Operations-Type
open import CategoryTheory.Operations-Type-Category
open import CategoryTheory.Operations-Endo
open import CategoryTheory.Operations-Arrow-Category
open import CategoryTheory.Operations-Arrow-Monoid
open import CategoryTheory.Operations-Arrow
open import CategoryTheory.Classes-0-Graph
open import CategoryTheory.Instances-0-Graph

infixr 5 _∘_
data Pathᴬ {ob : Typeᵀ} (A : relᵀ ob) : relᵀ ob where
    [] : ᴬ0-ary' (Pathᴬ A)
    _∘_ : ᴬL-act' A (Pathᴬ A)

-- catamorphism (uncurried)
Path/cata' :
    {ob : Typeᵀ} → {X R : relᵀ ob} →
    ᴬ0-ary' R → ᴬL-act' X R → Pathᴬ X ⟶ R
Path/cata' {ob} {X} {R} nil cons = cata
  where
    cata : Pathᴬ X ⟶ R
    cata [] = nil
    cata (head ∘ tail) = cons head (cata tail)

-- catamorphism (uncurried)
Path/cata :
    {ob : Typeᵀ} → {X R : relᵀ ob} →
    ᴬ0-ary R → ᴬL-act X R → Pathᴬ X ⟶ R
Path/cata nil cons = Path/cata' (ᴬ0-unwrap nil) (ᴬL-unwrap cons)

-- functor acts on morphisms
Path/map :
    {ob : Typeᵀ} → {A B : relᵀ ob} →
    (A ⟶ B) → (Pathᴬ A ⟶ Pathᴬ B)
Path/map {ob} {A} {B} f = Path/cata' [] mapp
  where
    mapp : ᴬL-act' A (Pathᴬ B)
    mapp a bs = f a ∘ bs

-- Path/neutral' : {ob : Typeᵀ} → {A : relᵀ ob} → ᴬ0-ary' (Pathᴬ A)
-- Path/neutral' = []

-- Path/compose' : {ob : Typeᵀ} → {A : relᵀ ob} → ᴬ2-ary' (Pathᴬ A)
-- Path/compose' {ob} {A} = Path/cata' ᴬ⟨⟩ compp
--   where
--     compp : ᴬL-act' A (Pathᴬ A)
--     compp a f p = a ∘ f p

-- -- monad identity
-- List/return : ᴱ0-ary Listᵀ
-- List/return x = x ∙ []
--
-- -- monad multiplication
-- List/flatten : ᴱ2-ary Listᵀ
-- List/flatten = List/cata' List/neutral' List/compose'
