{-# OPTIONS --type-in-type --copatterns #-}

module Continuous where

--------------------------------------------------------------- Common-Oper

-- synonym for the type of types
Typeᵀ : Set
Typeᵀ = Set

-- synomym for lambda syntax
λ-syntax : {Aᵀ Bᵀ : Typeᵀ} → (Aᵀ → Bᵀ) → (Aᵀ → Bᵀ)
λ-syntax f = f
syntax λ-syntax (λ a → b) = [ a ↦ b ]

-- declare type in subexpression: prefix (the), postfix (as)
the : (Aᵀ : Typeᵀ) → Aᵀ → Aᵀ
the Aᵀ a = a
syntax the A a = a as A

--------------------------------------------------------------- Common-Classes

-- `Apply` class (previous)

Projectᵀ : (result arg : Typeᵀ) → Typeᵀ
Projectᵀ result arg = arg → result

-- `Arg` class

record Argᴿ (Resultᵀ : Typeᵀ) : Typeᵀ
  where
    constructor Mk
    field argᵀ : Typeᵀ
    field apply : Projectᵀ Resultᵀ argᵀ

Arg :
    {Resultᵀ : Typeᵀ} →
    {{arg-rec : Argᴿ Resultᵀ}} →
    Applyᵀ Resultᵀ (Argᴿ.argᵀ arg-rec)
Arg {{arg-rec}} = Argᴿ.apply arg-rec

-- `Apply` class

Apply-ofᵀ : {Argᵀ : Typeᵀ} → (argᵀ : Argᵀ) → (argᵀ → Typeᵀ) → Typeᵀ
Apply-ofᵀ argᵀ fiberᵀ = (a : argᵀ) → fiberᵀ a

record Apply-ofᴿ (Argᵀ : Typeᵀ) : Typeᵀ
  where
    constructor Mk
    field argᵀ : Argᵀ
    field fiberᵀ : argᵀ → Typeᵀ
    field apply-of : Apply-ofᵀ argᵀ fiberᵀ

Apply-of :
    {Argᵀ : Typeᵀ} →
    {{apply-rec : Apply-ofᴿ Argᵀ}} →
    Apply-ofᵀ resultᵀ (Apply-ofᴿ.argᵀ apply-rec) (Apply-ofᴿ.proj apply-rec)
Apply-of {{arg-rec}} = Apply-ofᴿ.apply-of arg-rec

-- `Ob` class

record Obᴿ (Resultᵀ : Typeᵀ) : Typeᵀ
  where
    constructor Mk
    field argᵀ : Typeᵀ
    field apply : Applyᵀ Resultᵀ argᵀ

Ob :
    {resultᵀ : Typeᵀ} →
    {{ob-rec : Obᴿ resultᵀ}} →
    Applyᵀ resultᵀ (Obᴿ.argᵀ ob-rec)
Ob {{ob-rec}} = Obᴿ.apply ob-rec

-- `Carrier` class

record Carrierᴿ (Resultᵀ : Typeᵀ) : Typeᵀ
  where
    constructor Mk
    field argᵀ : Typeᵀ
    field apply : Applyᵀ Resultᵀ argᵀ

Carrier :
    {resultᵀ : Typeᵀ} →
    {{carrier-rec : Carrierᴿ resultᵀ}} →
    Applyᵀ resultᵀ (Carrierᴿ.argᵀ carrier-rec)
Carrier {{carrier-rec}} = Carrierᴿ.apply carrier-rec

--------------------------------------------------------------- Common-Instances

-- Arg

instance
  Arg:Arg : {resultᵀ : Typeᵀ} → Argᴿ Typeᵀ
  Arg:Arg {resultᵀ} = Mk (Argᴿ resultᵀ) Argᴿ.argᵀ

-- instance
--   Arg:Apply-of : {Resultᵀ : Typeᵀ} → Apply-ofᵀ Resultᵀ
--   Arg:Apply-of {Resultᵀ} = Mk Argᴿ.apply

-- Apply

-- Ob

instance
  Ob:Arg : {resultᵀ : Typeᵀ} → Argᴿ Typeᵀ
  Ob:Arg {resultᵀ} = Mk (Obᴿ resultᵀ) Obᴿ.argᵀ

-- Carrier

instance
  Carrier:Arg : {resultᵀ : Typeᵀ} → Argᴿ Typeᵀ
  Carrier:Arg {resultᵀ} = Mk (Carrierᴿ resultᵀ) Carrierᴿ.argᵀ

---------------------------------------------------------------

data P0-Listᵀ (X : Typeᵀ) : Typeᵀ
  where
    0-Nil : P0-Listᵀ X
    0-Cons : (head : X) → (tail : P0-Listᵀ X) → P0-Listᵀ X

Concatᵀ : Typeᵀ → Typeᵀ
Concatᵀ carrierᵀ = P0-Listᵀ carrierᵀ → carrierᵀ

record P0-Monoidᴿ : Typeᵀ
  where
    constructor Mk
    field carrierᵀ : Typeᵀ
    field apply : Concatᵀ carrierᵀ

instance
  P0-Monoid:Carrier : Carrierᴿ Typeᵀ
  P0-Monoid:Carrier = Mk _ P0-Monoidᴿ.carrierᵀ

P0-Concat : {{rec : P0-Monoidᴿ}} → Concatᵀ (Carrier rec)
P0-Concat {{rec}} = P0-Monoidᴿ.apply rec

--------------------------------------------------------------- Common-Oper

_↠_ : (ob U : Typeᵀ) → Typeᵀ
ob ↠ U = (a b : ob) → U

co-map/Arrow :
    {U₁ U₂ : Typeᵀ} →  (U₁ → U₂) →
    {ob : Typeᵀ} →
    ob ↠ U₁ → ob ↠ U₂
co-map/Arrow f _⇒_ a b = f (a ⇒ b)

contra-map/Arrow :
    {U : Typeᵀ} →
    {ob₁ ob₂ : Typeᵀ} → (ob₁ → ob₂) →
    ob₂ ↠ U → ob₁ ↠ U
contra-map/Arrow f _⇒_ a b = (f a ⇒ f b)

--------------------------------------------------------------- Classes

-- plain (non-enriched) graph

record P0-Graphᴿ : Typeᵀ
  where
    constructor Mk
    field {obᵀ} : Typeᵀ
    field apply : obᵀ ↠ Typeᵀ

instance
  P0-Graph:Ob : Obᴿ Typeᵀ
  P0-Graph:Ob = Mk _ P0-Graphᴿ.obᵀ

_⟶_ :
    {{rec : P0-Graphᴿ}} →
    Ob rec ↠ Typeᵀ
_⟶_ {{rec}} = P0-Graphᴿ.apply rec

Type/↠ : Typeᵀ ↠ Typeᵀ
Type/↠ a b = a → b

instance
  Type:P0-Graph : P0-Graphᴿ
  Type:P0-Graph = Mk Type/↠

Arrow/↠ :
    {{U : P0-Graphᴿ}} →
    {ob : Typeᵀ} →
    (ob ↠ Ob U) ↠ Typeᵀ
Arrow/↠ {ob} _⇒₁_ _⇒₂_ = (a b : ob) → (a ⇒₁ b) ⟶ (a ⇒₂ b)

instance
  Arrow:P0-Graph :
      {{U : P0-Graphᴿ}} →
      {ob : Typeᵀ} →
      P0-Graphᴿ
  Arrow:P0-Graph {{U}} {ob} = Mk {ob ↠ Ob U} Arrow/↠

---------------------------------------------------------------

-- U-enriched graph

record E0-Graphᴿ (U : P0-Graphᴿ) : Typeᵀ
  where
    constructor Mk
    field {obᵀ} : Typeᵀ
    field apply : obᵀ ↠ Ob U

instance
  R0-Graph:Ob : {U : P0-Graphᴿ} → Obᴿ Typeᵀ
  R0-Graph:Ob {U} = Mk _ (E0-Graphᴿ.obᵀ {U})

_⟹_ :
    {{U : P0-Graphᴿ}} →
    {{rec : E0-Graphᴿ U}} →
    Ob rec ↠ Ob U
_⟹_ {{U}} {{rec}} = E0-Graphᴿ.apply rec

---------------------------------------------------------------

data P0-Path {ob : Typeᵀ} (rel : ob ↠ Typeᵀ) : (a b : ob) → Typeᵀ
  where
    0Nil : {a : ob} → P0-Path rel a a
    0Cons : {a b c : ob} → rel a b → P0-Path rel b c → P0-Path rel a c

--
