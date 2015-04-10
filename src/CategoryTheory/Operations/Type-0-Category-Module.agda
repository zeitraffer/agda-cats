{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Operations.Type-0-Category-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Classes.0-Relation-Module
open import CategoryTheory.Instances.Type-0-Relation-Module

0-Id-Map : {X : Type} → X ⟶ X
0-Id-Map x = x

0-Mul-Map : {x y z : Type} → (x ⟶ y) → (y ⟶ z) → (x ⟶ z)
0-Mul-Map f g = λ x → g (f x)
