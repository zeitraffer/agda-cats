{-# OPTIONS --type-in-type #-}

module CategoryTheory.Classes-01-Category where

open import CategoryTheory.Common
open import CategoryTheory.Classes-Common
open import CategoryTheory.Instances-Common
open import CategoryTheory.Operations-Path
open import CategoryTheory.Classes-0-Graph
open import CategoryTheory.Instances-0-Graph

-- "Category" is a capability of reducing "Path"

01-Category-applyᵀ : {ob : Typeᵀ} → preᵀ (relᵀ ob)
01-Category-applyᵀ carrier = Pathᵀ carrier ⟶ carrier

record 01-Categoryᴿ (carrier : Typeᵀ) : Typeᵀ where
    constructor Mk
    field apply : 0-Monoid-applyᵀ carrier
0-Monoidᵀ : Typeᵀ
0-Monoidᵀ = 𝝨 0-Monoidᴿ
