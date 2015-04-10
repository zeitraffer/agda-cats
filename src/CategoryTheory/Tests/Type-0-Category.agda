{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Tests.Type-0-Category where

open import CategoryTheory.Common-Module
open import CategoryTheory.Classes.0-Relation-Module
open import CategoryTheory.Classes.0-Category-Module
open import CategoryTheory.Operations.Type-0-Category-Module
open import CategoryTheory.Operations.Terminal-Type-Module
open import CategoryTheory.Instances.Type-0-Relation-Module
open import CategoryTheory.Instances.Type-0-Category-Module

testId : Terminal-Type ⟶ Terminal-Type
testId = 0-Id

testMul : Terminal-Type ⟶ Terminal-Type
testMul = testId 0-Mul testId
