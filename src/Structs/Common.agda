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

record Wrap-Type-Class 
    (X : Type) 
    : Type 
  where
    constructor Mk
    field
      get-it : 
          Type

record Wrap-Class 
    {X : Type}
    (type : Wrap-Type-Class X)
    : Type
  where
    constructor Mk
    field
      get-get : 
          X → Wrap-Type-Class.get-it type
      get-wrap : 
          Wrap-Type-Class.get-it type → X

get : 
    {X : Type} → 
    {type : Wrap-Type-Class X} →
    ⦃ wrapper : Wrap-Class type ⦄ → 
    X → Wrap-Type-Class.get-it type
get ⦃ wrapper ⦄ = Wrap-Class.get-get wrapper

wrap : 
    {X : Type} → 
    {type : Wrap-Type-Class X} →
    ⦃ getter : Wrap-Class type ⦄ → 
    Wrap-Type-Class.get-it type → X
wrap ⦃ wrapper ⦄ = Wrap-Class.get-wrap wrapper

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

Ob : 
    {X : Type} →
    ⦃ ob : Ob-Class X ⦄ →
    X → Type
Ob ⦃ ob ⦄ = Ob-Class.get-ob ob

