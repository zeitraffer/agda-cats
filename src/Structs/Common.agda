{-# OPTIONS --type-in-type --copatterns #-}

module Structs.Common where

------------------------------
-- `Type` - an obvious synonym
--

Type : Set
Type = Set

------------------------------------------
-- `Wrap-Class` class - for isomorphic wrappers
--
-- `wrap x` method - wrap `x` into wrapper type
-- `get w` method - extract from wrapped value `w`
--

record Wrap-Class 
    (X WX : Type)
    : Type
  where
    constructor Mk
    field
      get-get : 
          WX → X
      get-wrap : 
          X → WX
open Wrap-Class

get : 
    {X WX : Type} → 
    ⦃ w : Wrap-Class X WX ⦄ → 
    WX → X
get ⦃ w ⦄ = get-get w

wrap : 
    {X WX : Type} → 
    ⦃ w : Wrap-Class X WX ⦄ → 
    X → WX
wrap ⦃ w ⦄ = get-wrap w

-------------------------------------------
-- `Ob-Class` class - for structures over carrier
--
-- `Ob` method - forget structure
--

record Ob-Class
    (X : Type) 
    : Type
  where
    constructor Mk
    field 
      get-ob : 
          X → Type
open Ob-Class

Ob : 
    {X : Type} →
    ⦃ ob : Ob-Class X ⦄ →
    X → Type
Ob ⦃ ob ⦄ = get-ob ob

