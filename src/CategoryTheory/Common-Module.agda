{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Common-Module where

------------------------------
-- (Type) - an obvious synonym
--

Type : Set
Type = Set

------------------------------------------
-- `Wrap` class - for isomorphic wrappers
--
-- `wrap x` method - wrap `x` into wrapped value
-- `get w` method - extract from wrapped value `w`
--

record Wrap-Class (X WX : Type) : Type
  where
    constructor Mk
    field
      get : WX → X
      wrap : X → WX

get : 
    {X WX : Type} → 
    ⦃ w : Wrap-Class X WX ⦄ → 
    WX → X
get ⦃ w ⦄ = Wrap-Class.get w

wrap : 
    {X WX : Type} → 
    ⦃ w : Wrap-Class X WX ⦄ → 
    X → WX
wrap ⦃ w ⦄ = Wrap-Class.wrap w

-------------------------------------------
-- (Ob) class - for structures over carrier
--
-- (Ob) method - forget structure
--

record Ob-Class (X : Type) : Type
  where
    constructor Mk
    field 
      ob : X → Type

Ob : 
    {X : Type} →
    ⦃ ob : Ob-Class X ⦄ →
    X → Type
Ob ⦃ ob ⦄ = Ob-Class.ob ob

-------------------------------------------
-- (Carrier) class - for structures over carrier
--
-- (Carrier) method - forget structure
--

record Carrier-Class (X : Type) : Type
  where
    constructor Mk
    field 
      carrier : X → Type

Ob : 
    {X : Type} →
    ⦃ ob : Ob-Class X ⦄ →
    X → Type
Ob ⦃ ob ⦄ = Ob-Class.ob ob

-------------------------------------------
-- (∃) type - for: 
-- dependent sums (dependent type theory)
-- existential types (System F, etc)
-- total space of fibration (topology)
-- quantifier of existence (logics)

record ∃ {Base : Type} (Fiber : base → Type) : Type 
  where
    constructor Mk
    field
      base : Base
      fiber : Fiber base

instance 
  ∃- : {Base : Type} {Fiber : base → Type} → Ob-Class (∃ Fiber)
  ∃-Ob = 