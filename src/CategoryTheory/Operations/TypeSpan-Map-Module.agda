{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Operations.TypeSpan-Map-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Operations.TypeSpan-Module
open import CategoryTheory.Classes.TypeSpan-Module
open import CategoryTheory.Instances.Type-TypeEndoSpan-Module

TypeSpan-MapType : {X Y : Type} → (X ⇸ Y) ⇸ (X ⇸ Y)
TypeSpan-MapType {X} {Y} _↝₁_ _↝₂_ = 
    {x : X}{y : Y} → (x ↝₁ y) ⟶ (x ↝₂ y)

TypeSpan-SpanType : {X Y : Type} → (X ⇸ Y) ⇸ (X ⇸ Y)
TypeSpan-SpanType {X} {Y} _↝₁_ _↝₂_ = 
    {x : X}{y : Y} → (x ↝₁ y) ⇸ (x ↝₂ y)

