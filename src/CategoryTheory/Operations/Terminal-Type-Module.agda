{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Operations.Terminal-Type-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Classes.0-Relation-Module
open import CategoryTheory.Instances.Type-0-Relation-Module

data Terminal-Type : Type
  where
    ! : Terminal-Type

const-Map : {X Y : Type} → Y → X ⟶ Y
const-Map y = λ x → y

final-Map : {X : Type} → X ⟶ Terminal-Type 
final-Map = const-Map !
