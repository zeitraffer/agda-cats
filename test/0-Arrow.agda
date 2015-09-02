{-# OPTIONS --type-in-type --copatterns #-}

module 0-Arrow where

---------------------------------------------------------------

Type : Set
Type = Set

λ-syntax : {A B : Type} → (A → B) → (A → B)
λ-syntax f = f

syntax λ-syntax (λ x → B) = 𝝺 x ↦ B

---------------------------------------------------------------

record Ob-Record : Type
  where
    constructor Mk
    field {carrier} : Type
    field apply : carrier → Type

Ob : {{rec : Ob-Record}} → Ob-Record.carrier rec → Type
Ob {{rec}} = Ob-Record.apply rec

record Carrier-Record : Type
  where
    constructor Mk
    field {carrier} : Type
    field apply : carrier → Type

Carrier : {{rec : Carrier-Record}} → Carrier-Record.carrier rec → Type
Carrier {{rec}} = Carrier-Record.apply rec

instance
  Ob:Carrier : Carrier-Record
  Ob:Carrier = Mk Ob-Record.carrier

instance
  Carrier:Carrier : Carrier-Record
  Carrier:Carrier = Mk Carrier-Record.carrier

---------------------------------------------------------------

_↠_ : (ob U : Type) → Type
ob ↠ U = (a b : ob) → U

record Plain-Arrow-Record : Type
  where
    constructor Mk
    field {carrier-rec} : Ob-Record
    carrier = Carrier carrier-rec
    field arrow : (c : carrier) → Ob c ↠ Type

instance
  Plain-Arrow:Carrier : Carrier-Record
  Plain-Arrow:Carrier = Mk Plain-Arrow-Record.carrier

instance
  Plain-Arrow→Ob : {{rec : Plain-Arrow-Record}} → Ob-Record
  Plain-Arrow→Ob {{rec}} = Plain-Arrow-Record.carrier-rec rec

PArrow : {{rec : Plain-Arrow-Record}} → (c : Carrier rec) → Ob c ↠ Type
PArrow {{rec}} = Plain-Arrow-Record.arrow rec

---------------------------------------------------------------

record Plain-0-Graph-Record : Type
  where
    constructor Mk
    field {ob} : Type
    field arrow : ob ↠ Type

Plain-0-Graph:Ob : Ob-Record
Plain-0-Graph:Ob = Mk Plain-0-Graph-Record.ob

instance
  Plain-0-Graph:Arrow : Plain-Arrow-Record
  Plain-0-Graph:Arrow = Mk Plain-0-Graph-Record.arrow

_⟶_ :
    {{rec : Plain-0-Graph-Record}} →
    Ob rec ↠ Type
_⟶_ {{rec}} = Plain-0-Graph-Record.arrow rec

Type/↠ : Type ↠ Type
Type/↠ a b = a → b

instance
  Type:Plain-0-Graph : Plain-0-Graph-Record
  Type:Plain-0-Graph = Mk Type/↠

Arrow/↠ :
    {{U : Plain-0-Graph-Record}} →
    {ob : Type} →
    (ob ↠ Ob U) ↠ Type
Arrow/↠ {ob} _⇒₁_ _⇒₂_ = (a b : ob) → (a ⇒₁ b) ⟶ (a ⇒₂ b)

instance
  Arrow:Plain-0-Graph :
      {{U : Plain-0-Graph-Record}} →
      {ob : Type} →
      Plain-0-Graph-Record
  Arrow:Plain-0-Graph {{U}} {ob} = Mk {ob ↠ Ob U} Arrow/↠

---------------------------------------------------------------

record Rich-0-Graph-Record (U : Plain-0-Graph-Record) : Type
  where
    constructor Mk
    field {ob} : Type
    field arrow : ob ↠ Ob U

instance
  Rich-0-Graph:Ob : {U : Plain-0-Graph-Record} → Ob-Record
  Rich-0-Graph:Ob {U} = Mk (Rich-0-Graph-Record.ob {U})

_⟹_ :
    {{U : Plain-0-Graph-Record}} →
    {{rec : Rich-0-Graph-Record U}} →
    Ob rec ↠ Ob U
_⟹_ {{U}} {{rec}} = Rich-0-Graph-Record.arrow rec

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
    {{U : Plain-0-Graph-Record}} →
    ob ↠ Ob U → Type
Invertible-Arrow-Type {ob} _⇒_ = {a b : ob} → (a ⇒ b) ⟶ (b ⇒ a)

record Plain-0-InvGraph-Record : Type
  where
    constructor Mk
    field {arrow-rec} : Plain-0-Graph-Record
    ob = Ob arrow-rec
    arrow = PArrow arrow-rec
    field inverse : Invertible-Arrow-Type arrow

instance
  Plain-0-InvGraph:Ob : Ob-Record
  Plain-0-InvGraph:Ob = Mk Plain-0-InvGraph-Record.ob

instance
  Plain-0-InvGraph→Plain-0-Graph : {{rec : Plain-0-InvGraph-Record}} → Plain-0-Graph-Record
  Plain-0-InvGraph→Plain-0-Graph {{rec}} = Plain-0-InvGraph-Record.arrow-rec rec
