{-# OPTIONS --type-in-type #-}

module CategoryTheory.Instances-0-Graph where

open import CategoryTheory.Common
open import CategoryTheory.Classes-Common
open import CategoryTheory.Instances-Common
open import CategoryTheory.Classes-0-Graph
open import CategoryTheory.Operations-Arrow-Category

instance
    Type/0-Graph : 0-Graphᴿ Typeᵀ
    0-Graphᴿ.apply Type/0-Graph = _−ᵀ→_
Typeᴳ : 0-Graphᵀ
Typeᴳ = Typeᵀ , Type/0-Graph

instance
    Arrow/0-Graph : {ob : Typeᵀ} → 0-Graphᴿ (relᵀ ob)
    0-Graphᴿ.apply Arrow/0-Graph = _−ᴬ→_
Arrowᴳ : (ob : Typeᵀ) → 0-Graphᵀ
Arrowᴳ ob = relᵀ ob , Arrow/0-Graph

private
  module Test where
    open import CategoryTheory.Operations-Type-Category
    test1 : Typeᵀ ⟶ Typeᵀ
    test1 = ᵀ⟨⟩
