{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Operations.Terminal-Type-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Classes.0-Relation-Module
open import CategoryTheory.Instances.Type-0-Relation-Module

data Terminal-Type 
    : Type
  where
    Mk-Terminal 
      : Terminal-Type

data Terminal-Equ-Type
    : 0-Relation-Type Terminal-Type Terminal-Type
  where
    Mk-Terminal-Equ 
      : Terminal-Equ-Type Mk-Terminal Mk-Terminal

const-Map : {X Y : Type} → Y → X ⟶ Y
const-Map y = λ x → y

final-Map : {X : Type} → X ⟶ Terminal-Type 
final-Map = const-Map Mk-Terminal
