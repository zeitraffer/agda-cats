{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Continuous-Module where

open import CategoryTheory.Common-Module

---------------------------------------------------------------

-- capability of reducing `List` -> `Monoid`

data P0-Listᵀ (Xᵀ : Typeᵀ) : Typeᵀ
  where
    [∙] : P0-Listᵀ Xᵀ
    _∙_ : Xᵀ → P0-Listᵀ Xᵀ → P0-Listᵀ Xᵀ

List/cata : {Xᵀ Rᵀ : Typeᵀ} → Rᵀ → (Xᵀ → Rᵀ → Rᵀ) → P0-Listᵀ Xᵀ → Rᵀ
List/cata {Xᵀ} {Rᵀ} nil cons = cata
  where
    cata : P0-Listᵀ Xᵀ → Rᵀ
    cata [∙] = nil
    cata (head ∙ tail) = cons head (cata tail)

P0-Monoidᵀ : Typeᵀ → Typeᵀ
P0-Monoidᵀ carrierᵀ = P0-Listᵀ carrierᵀ → carrierᵀ

-- plain (non-enriched) 0-dimensional (non-categorified) monoid

record P0-Monoidᴿ : Typeᵀ
  where
    constructor Mk
    field carrierᵀ : Typeᵀ
    field apply : P0-Monoidᵀ carrierᵀ

P0-Monoid:Arg : Argᴿ Typeᵀ
P0-Monoid:Arg = Mk _ P0-Monoidᴿ.carrierᵀ

instance
  P0-Monoid:Apply : Applyᴿ Typeᵀ P0-Monoidᵀ
  P0-Monoid:Apply = Mk P0-Monoid:Arg P0-Monoidᴿ.apply

instance
  P0-Monoid:Carrier : Carrierᴿ Typeᵀ
  P0-Monoid:Carrier = Mk _ P0-Monoidᴿ.carrierᵀ

P0-Concat : {{rec : P0-Monoidᴿ}} → P0-Monoidᵀ (Carrier rec)
P0-Concat {{rec}} = P0-Monoidᴿ.apply rec

--------------------------------------------------------------- syntax

infixr 5 _∙_
infix 10 _⟫
infix 0 ⟪_

-- ⟪a,b,c⟫ to be monoid concatenation, see tests

⟪⟫ : {{M : P0-Monoidᴿ}} → Carrier M
⟪⟫ = P0-Concat [∙]

⟪_ : {{M : P0-Monoidᴿ}} → P0-Monoidᵀ (Carrier M)
⟪_ = P0-Concat

_⟫ : {{M : P0-Monoidᴿ}} → Carrier M → P0-Listᵀ (Carrier M)
_⟫ m = m ∙ [∙]

--------------------------------------------------------------- Common-Oper

_↠_ : (ob U : Typeᵀ) → Typeᵀ
ob ↠ U = (a b : ob) → U

↠/co-map :
    {U₁ U₂ : Typeᵀ} →  (U₁ → U₂) →
    {ob : Typeᵀ} →
    ob ↠ U₁ → ob ↠ U₂
↠/co-map f _⇒_ a b = f (a ⇒ b)

↠/contra-map :
    {U : Typeᵀ} →
    {ob₁ ob₂ : Typeᵀ} → (ob₁ → ob₂) →
    ob₂ ↠ U → ob₁ ↠ U
↠/contra-map f _⇒_ a b = (f a ⇒ f b)

Arrow/↠ :
    {ob : Typeᵀ} →
    (ob ↠ Typeᵀ) ↠ Typeᵀ
Arrow/↠ {ob} _⇒₁_ _⇒₂_ = (a b : ob) → (a ⇒₁ b) → (a ⇒₂ b)

--------------------------------------------------------------- Classes

-- plain (non-enriched) graph

record P0-Graphᴿ : Typeᵀ
  where
    constructor Mk
    field obᵀ : Typeᵀ
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
  Type:P0-Graph = Mk _ Type/↠

instance
  Arrow:P0-Graph : {ob : Typeᵀ} → P0-Graphᴿ
  Arrow:P0-Graph {ob} = Mk (ob ↠ Typeᵀ) Arrow/↠

---------------------------------------------------------------

-- U-enriched graph

record E0-Graphᴿ (U : P0-Graphᴿ) : Typeᵀ
  where
    constructor Mk
    field obᵀ : Typeᵀ
    field apply : obᵀ ↠ Ob U

instance
  E0-Graph:Ob : {U : P0-Graphᴿ} → Obᴿ Typeᵀ
  E0-Graph:Ob {U} = Mk _ (E0-Graphᴿ.obᵀ {U})

_⟹_ :
    {U : P0-Graphᴿ} →
    {{rec : E0-Graphᴿ U}} →
    Ob rec ↠ Ob U
_⟹_ {{rec}} = E0-Graphᴿ.apply rec

instance
  Type:E0-Graph : E0-Graphᴿ Type:P0-Graph
  Type:E0-Graph = Mk _ Type/↠

Arrow/↠' :
    {ob : Typeᵀ} →
    {{U : E0-Graphᴿ Type:P0-Graph}} →
    (ob ↠ Ob U) ↠ Typeᵀ
Arrow/↠' {ob} _⇒₁_ _⇒₂_ = (a b : ob) → (a ⇒₁ b) ⟹ (a ⇒₂ b)

instance
  Arrow:E0-Graph :
    {ob : Typeᵀ} →
    {{U : E0-Graphᴿ Type:P0-Graph}} →
    E0-Graphᴿ Type:P0-Graph
  Arrow:E0-Graph {ob} {{U}} = Mk (ob ↠ Ob U) Arrow/↠'

---------------------------------------------------------------

-- capability of reducing `Path` is `Category`

module Pathᴹ {ob : Typeᵀ} (_⇒_ : ob ↠ Typeᵀ) where
  data _⇛_ : ob ↠ Typeᵀ where
    [∘] : {a : ob} → a ⇛ a
    _∘_ : {a b c : ob} → a ⇒ b → b ⇛ c → a ⇛ c

P0-Pathᵀ : {ob : Typeᵀ} → ob ↠ Typeᵀ → ob ↠ Typeᵀ
P0-Pathᵀ _⇒_ = let open Pathᴹ _⇒_ in _⇛_

{-
List/cata : {Xᵀ Rᵀ : Typeᵀ} → Rᵀ → (Xᵀ → Rᵀ → Rᵀ) → P0-Listᵀ Xᵀ → Rᵀ
List/cata {Xᵀ} {Rᵀ} nil cons = cata
  where
    cata : P0-Listᵀ Xᵀ → Rᵀ
    cata [] = nil
    cata (head , tail) = cons head (cata tail)
-}

P0-Categoryᵀ : {ob : Typeᵀ} → (ob ↠ Typeᵀ) → Typeᵀ
P0-Categoryᵀ carrier = P0-Pathᵀ carrier ⟶ carrier

P0-Categoryᵀ- : {ob : Typeᵀ} → (ob ↠ Typeᵀ) → Typeᵀ
P0-Categoryᵀ- carrier = P0-Pathᵀ carrier ⟹ carrier
