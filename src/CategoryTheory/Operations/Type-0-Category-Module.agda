{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Operations.Type-0-Category-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Classes.Relation-Module
open import CategoryTheory.Instances.Type-Relation-Module

0-Id-Map : {X : Type} → X ⟶ X
0-Id-Map x = x

_0-Mul-Map_ : {x y z : Type} → (x ⟶ y) → (y ⟶ z) → (x ⟶ z)
f 0-Mul-Map g = λ x → g (f x)
