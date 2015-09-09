{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Continuous-Module where

open import CategoryTheory.Common-Module

--------------------------------------------------------------- morphisms

List/cata : {X R : Typeᵀ} → R → (X → R → R) → 0-Listᵀ X → R
List/cata {X} {R} nil cons = cata
  where
    cata : 0-Listᵀ X → R
    cata [∙] = nil
    cata (head ∙ tail) = cons head (cata tail)

List/unit : {X : Typeᵀ} → X → 0-Listᵀ X
List/unit x = x ∙ [∙]

---------------------------------------------------------------

-- capability of reducing `List` -> `Monoid`

0-Monoidᵀ : Typeᵀ → Typeᵀ
0-Monoidᵀ carrier = 0-Listᵀ carrier → carrier

-- plain (non-enriched) 0-dimensional (non-categorified) monoid

record 0-Monoidᴿ : Typeᵀ
  where
    constructor Mk
    field carrier : Typeᵀ
    field apply : 0-Monoidᵀ carrier

0-Monoid:Arg : Argᴿ Typeᵀ
0-Monoid:Arg = Mk _ 0-Monoidᴿ.carrier

instance
  0-Monoid:Apply : Applyᴿ Typeᵀ 0-Monoidᵀ
  0-Monoid:Apply = Mk 0-Monoid:Arg 0-Monoidᴿ.apply

instance
  0-Monoid:Carrier : Carrierᴿ Typeᵀ
  0-Monoid:Carrier = Mk _ 0-Monoidᴿ.carrier

0-Concat : {{M : 0-Monoidᴿ}} → 0-Monoidᵀ (Carrier M)
0-Concat {{M}} = 0-Monoidᴿ.apply M

--------------------------------------------------------------- syntax

infix 6 _⟫
infix 4 ⟪_

-- ⟪a∙b∙c⟫ denote monoid concatenation, see tests

⟪⟫ : {{M : 0-Monoidᴿ}} → Carrier M
⟪⟫ = 0-Concat [∙]

⟪_ : {{M : 0-Monoidᴿ}} → 0-Monoidᵀ (Carrier M)
⟪_ = 0-Concat

_⟫ : {{M : 0-Monoidᴿ}} → Carrier M → 0-Listᵀ (Carrier M)
_⟫ m = m ∙ [∙]

-- monoid of types wrt cartesian product
instance
  Typeᴹ : 0-Monoidᴿ
  Typeᴹ = Mk Typeᵀ (List/cata ⊤ᵀ _×ᵀ_)

-- monoid of relations (arrows) wrt composition
instance
  Arrowᴹ : {ob : Typeᵀ} → 0-Monoidᴿ
  Arrowᴹ {ob} = Mk (ob ↠ Typeᵀ) (List/cata 0-Idᴬ 0-Mulᴬ)

--------------------------------------------------------------- Common-Oper

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

_-ᴬ→_ : {ob : Typeᵀ} → (ob ↠ Typeᵀ) ↠ Typeᵀ
_-ᴬ→_ {ob} _⇒₁_ _⇒₂_ = {a b : ob} → (a ⇒₁ b) → (a ⇒₂ b)

--------------------------------------------------------------- Classes

-- plain (non-enriched) graph

0-Graphᵀ : Typeᵀ → Typeᵀ
0-Graphᵀ ob = ob ↠ Typeᵀ

record 0-Graphᴿ : Typeᵀ
  where
    constructor Mk
    field ob : Typeᵀ
    field apply : 0-Graphᵀ ob

instance
  0-Graph:Ob : Obᴿ Typeᵀ
  0-Graph:Ob = Mk _ 0-Graphᴿ.ob

0-Graph:Arg : Argᴿ Typeᵀ
0-Graph:Arg = Mk _ 0-Graphᴿ.ob

instance
  0-Graph:Apply : Applyᴿ Typeᵀ 0-Graphᵀ
  0-Graph:Apply = Mk 0-Graph:Arg 0-Graphᴿ.apply

-- plain `arrow` operator
infix 0 _⟶_
_⟶_ : {{G : 0-Graphᴿ}} → 0-Graphᵀ (Ob G)
_⟶_ {{G}} = Apply G

instance
  Typeᴳ : 0-Graphᴿ
  Typeᴳ = Mk _ _-ᵀ→_

instance
  Arrowᴳ : {ob : Typeᵀ} → 0-Graphᴿ
  Arrowᴳ {ob} = Mk (ob ↠ Typeᵀ) _-ᴬ→_

---------------------------------------------------------------

-- U-enriched graph - `E0-Graph` class

E0-Graphᵀ : 0-Graphᴿ → Typeᵀ → Typeᵀ
E0-Graphᵀ U ob = ob ↠ Ob U

record E0-Graphᴿ (U : 0-Graphᴿ) : Typeᵀ
  where
    constructor Mk
    field ob : Typeᵀ
    field apply : E0-Graphᵀ U ob

instance
  E0-Graph:Ob : {U : 0-Graphᴿ} → Obᴿ Typeᵀ
  E0-Graph:Ob {U} = Mk _ (E0-Graphᴿ.ob {U})

-- enriched `arrow` operator
infix 0 _⟹_
_⟹_ : {U : 0-Graphᴿ} → {{G : E0-Graphᴿ U}} → E0-Graphᵀ U (Ob G)
_⟹_ {{G}} = E0-Graphᴿ.apply G

instance
  Typeᴳ' : E0-Graphᴿ Typeᴳ
  Typeᴳ' = Mk _ _-ᵀ→_

_=ᴬ⇒_ :
    {{U : E0-Graphᴿ Typeᴳ}} →
    {ob : Typeᵀ} →
    (ob ↠ Ob U) ↠ Typeᵀ
_=ᴬ⇒_ {ob} _⇒₁_ _⇒₂_ = (a b : ob) → (a ⇒₁ b) ⟹ (a ⇒₂ b)

instance
  Arrowᴳ' :
    {{U : E0-Graphᴿ Typeᴳ}} →
    {ob : Typeᵀ} → E0-Graphᴿ Typeᴳ
  Arrowᴳ' {{U}} {ob} = Mk (ob ↠ Ob U) _=ᴬ⇒_

---------------------------------------------------------------

Diagᵀ : {ob : Typeᵀ} → ob ↠ Typeᵀ → Typeᵀ
Diagᵀ {ob} _⇒_ = {x : ob} → x ⇒ x

Path/cata :
    {ob : Typeᵀ} → {X R : ob ↠ Typeᵀ} →
    0-Idᴬ ⟶ R → 0-Mulᴬ X R ⟶ R → 0-Pathᴬ X ⟶ R
Path/cata {ob} {X} {R} nil cons = cata
  where
    cata : 0-Pathᴬ X ⟶ R
    cata [∘] = nil !
    cata (head ∘ tail) = cons (head , cata tail)

---------------------------------------------------------------

-- capability of reducing `Path` is `Category`
-- `category` is monoid enriched in category of `arrows over Ob`

0-Categoryᵀ : 0-Graphᴿ → Typeᵀ
0-Categoryᵀ G = 0-Pathᴬ (Apply G) ⟶ (Apply G)

-- plain (non-enriched) 0-dimensional category (preorder)

record 0-Categoryᴿ : Typeᵀ
  where
    constructor Mk
    field G : 0-Graphᴿ
    ob = Ob G
    arrow = Apply G
    field apply : 0-Categoryᵀ G

0-Category:Arg : Argᴿ 0-Graphᴿ
0-Category:Arg = Mk _ 0-Categoryᴿ.G

instance
  0-Category:Apply : Applyᴿ 0-Graphᴿ 0-Categoryᵀ
  0-Category:Apply = Mk 0-Category:Arg 0-Categoryᴿ.apply

instance
  0-Category:Ob : Obᴿ Typeᵀ
  0-Category:Ob = Mk _ 0-Categoryᴿ.ob

instance
  0-Category:Carrier : Carrierᴿ 0-Graphᴿ
  0-Category:Carrier = Mk _ 0-Categoryᴿ.G

0-Paste : {{C : 0-Categoryᴿ}} → 0-Categoryᵀ (Carrier C)
0-Paste {{C}} = 0-Categoryᴿ.apply C

--------------------------------------------------------------- syntax

infix 6 _⟩
infix 4 ⟨_

-- ⟨a∘b∘c⟩ denote morphism pasting, see tests

⟨⟩ : {{C : 0-Categoryᴿ}} → Diagᵀ (Apply (Carrier C))
⟨⟩ = 0-Paste [∘]

⟨_ : {{C : 0-Categoryᴿ}} → 0-Categoryᵀ (Carrier C)
⟨_ = 0-Paste

_⟩ : {{C : 0-Categoryᴿ}} → Apply (Carrier C) ⟶ 0-Pathᴬ (Apply (Carrier C))
_⟩ m = m ∘ [∘]

{-
-- monoid of types wrt cartesian product
instance
  Typeᴹ : 0-Monoidᴿ
  Typeᴹ = Mk Typeᵀ (List/cata ⊤ᵀ _×ᵀ_)

-- monoid of relations (arrows) wrt composition
instance
  Arrowᴹ : {ob : Typeᵀ} → 0-Monoidᴿ
  Arrowᴹ {ob} = Mk (ob ↠ Typeᵀ) (List/cata 0-Idᴬ 0-Mulᴬ)
-}

---------------------------------------------------------------
