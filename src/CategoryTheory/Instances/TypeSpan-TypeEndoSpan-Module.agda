{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Instances.TypeSpan-TypeEndoSpan-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Classes.TypeSpan-Module
open import CategoryTheory.Operations.TypeSpan-Map-Module
--open import CategoryTheory.

-----------------------------
-- `X ⟶ Y` - mappings between spans
--

instance
  TypeSpan-is-TypeEndoSpan : {X Y : Type} → TypeEndoSpan-Class (X ⇸ Y)
  TypeSpan-is-TypeEndoSpan = Mk TypeSpan-MapType

TypeSpan-TypeEndoSpan : (X Y : Type) → TypeEndoSpan-Record
TypeSpan-TypeEndoSpan X Y = Mk (X ⇸ Y)

-----------------------------
-- `X ⇸ Y` - spans between spans
--

instance
  Type-is-TypeEndoSpan' : {X Y : Type} → TypeEndoSpan-Class' (X ⇸ Y)
  Type-is-TypeEndoSpan' = Mk TypeSpan-MapType

TypeSpan-TypeEndoSpan' : (X Y : Type) → TypeEndoSpan-Record'
TypeSpan-TypeEndoSpan' X Y = Mk (X ⇸ Y)

