{-# OPTIONS --type-in-type --copatterns #-}

module 0-Arrow where

---------------------------------------------------------------

Type : Set
Type = Set

record Ob-Record : Type
  where
    constructor Mk
    field {ob} : Type
    field apply : ob → Type

Ob : {{rec : Ob-Record}} → Ob-Record.ob rec → Type
Ob {{rec}} = Ob-Record.apply rec

instance
  Ob:Ob : Ob-Record
  Ob:Ob = Mk Ob-Record.ob

---------------------------------------------------------------

_↠_ : (ob U : Type) → Type
ob ↠ U = (a b : ob) → U

---------------------------------------------------------------

record Plain-0-Arrow-Record : Type
  where
    constructor Mk
    field {ob} : Type
    field arrow : ob ↠ Type

instance
  Plain-0-Arrow:Ob : Ob-Record
  Plain-0-Arrow:Ob = Mk Plain-0-Arrow-Record.ob

_⟶_ :
    {{rec : Plain-0-Arrow-Record}} →
    Ob rec ↠ Type
_⟶_ {{rec}} = Plain-0-Arrow-Record.arrow rec

Type/Arrow : Type ↠ Type
Type/Arrow a b = a → b

instance
  Type:0-Arrow : Plain-0-Arrow-Record
  Type:0-Arrow = Mk Type/Arrow

Arrow/Arrow :
    {ob : Type} →
    {{U : Plain-0-Arrow-Record}} →
    (ob ↠ Ob U) ↠ Type
Arrow/Arrow {ob} _⇒₁_ _⇒₂_ = (a b : ob) → (a ⇒₁ b) ⟶ (a ⇒₂ b)

instance
  Arrow:0-Arrow :
      {ob : Type} →
      {{U : Plain-0-Arrow-Record}} →
      Plain-0-Arrow-Record
  Arrow:0-Arrow {ob} {{U}} = Mk {ob ↠ Ob U} Arrow/Arrow

---------------------------------------------------------------

record Rich-0-Arrow-Record (U : Plain-0-Arrow-Record) : Type
  where
    constructor Mk
    field ob : Type
    field arrow : ob ↠ Ob U

instance
  Rich-0-Arrow:Ob : {U : Plain-0-Arrow-Record} → Ob-Record
  Rich-0-Arrow:Ob {U} = Mk (Rich-0-Arrow-Record.ob {U})

_⟹_ :
    {{U : Plain-0-Arrow-Record}} →
    {{rec : Rich-0-Arrow-Record U}} →
    Ob rec ↠ Ob U
_⟹_ {{U}} {{rec}} = Rich-0-Arrow-Record.arrow rec

---------------------------------------------------------------

co-map/Arrow :
    {U₁ U₂ : Type} →  (U₁ → U₂) →
    {ob : Type} →
    ob ↠ U₁ → ob ↠ U₂
co-map/Arrow f _⇒_ a b = f (a ⇒ b)

contra-map/Arrow :
    {U : Type} →
    {ob₁ ob₂ : Type} → (ob₁ → ob₂) →
    ob₂ ↠ U → ob₁ ↠ U
contra-map/Arrow f _⇒_ a b = (f a ⇒ f b)

---------------------------------------------------------------

Invertible-Arrow-Type :
    {ob : Type} →
    {{U : Plain-0-Arrow-Record}} →
    (_⇒_ : ob ↠ Ob U) → Type
Invertible-Arrow-Type {ob} _⇒_ = (a b : ob) → (a ⇒ b) ⟶ (b ⇒ a)

record Plain-0-InvArrow-Record : Type
  where
    constructor Mk
    field arrow : Plain-0-Arrow-Record
    field inverse : Invertible-Arrow-Type {Ob arrow} _⟶_

instance
  Plain-0-InvArrow:Ob : Ob-Record
  Plain-0-InvArrow:Ob = Mk (Rich-0-Arrow-Record.ob {U})
