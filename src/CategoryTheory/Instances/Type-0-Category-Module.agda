{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Instances.Type-0-Category-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Classes.0-Category-Module
open import CategoryTheory.Instances.Type-Relation-Module
open import CategoryTheory.Operations.Type-0-Category-Module

instance
  Type-0-Category-Inst : 0-Category-Class Type-Relation-Inst
  Type-0-Category-Inst = Mk 0-Id-Map _0-Mul-Map_

Type-0-Category : 0-Category-Record
Type-0-Category = Mk Type-Relation

