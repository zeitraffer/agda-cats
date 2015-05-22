{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Instances.TypeSpan-TypeEndoSpan-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Classes.TypeSpan-Module
open import CategoryTheory.Operations.TypeSpan-Map-Module

-----------------------------
-- `X ⟶ Y` - mappings between spans
--

instance
  TypeSpan-is-TypeEndoSpan : {X Y : Type} → TypeEndoSpan-Class (X ⇸ Y)
  TypeSpan-is-TypeEndoSpan = Mk-TypeEndoSpan TypeSpan-MapType

TypeSpan-TypeEndoSpan : (X Y : Type) → TypeEndoSpan-Record
TypeSpan-TypeEndoSpan X Y = ℯ¹ (TypeSpan-is-TypeEndoSpan {X} {Y})

-----------------------------
-- `X ⇸ Y` - spans between spans
--

instance
  TypeSpan-is-TypeEndoSpan' : {X Y : Type} → TypeEndoSpan'-Class (X ⇸ Y)
  TypeSpan-is-TypeEndoSpan' = Mk-TypeEndoSpan' TypeSpan-SpanType

TypeSpan-TypeEndoSpan' : (X Y : Type) → TypeEndoSpan'-Record
TypeSpan-TypeEndoSpan' X Y = ℯ¹ (TypeSpan-is-TypeEndoSpan' {X} {Y})

