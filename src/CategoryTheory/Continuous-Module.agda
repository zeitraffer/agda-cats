{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Continuous-Module where

open import CategoryTheory.Common-Module

--------------------------------------------------------------- Data

data ⊤ᵀ : Typeᵀ where
  ! : ⊤ᵀ

data _×ᵀ_ (L R : Typeᵀ) : Typeᵀ where
  _,_ : (l : L) → (r : R) → L ×ᵀ R

data 0-Listᵀ (X : Typeᵀ) : Typeᵀ where
    [∙] : 0-Listᵀ X
    _∙_ : X → 0-Listᵀ X → 0-Listᵀ X

module 0-Idᴹ {X : Typeᵀ} where
  data _⇛_ : X ⇸ X where
    ! : {x : X} → x ⇛ x

module 0-Mulᴹ {X Y Z : Typeᵀ} (_⇒₁_ : X ⇸ Y) (_⇒₂_ : Y ⇸ Z) where
  data _⇛_ : X ⇸ Z where
    _,_ : {x : X} → {y : Y} → {z : Z} → x ⇒₁ y → y ⇒₂ z → x ⇛ z

module 0-Pathᴹ {ob : Typeᵀ} (_⇒_ : ob ↠ Typeᵀ) where
  data _⇛_ : ob ↠ Typeᵀ where
    [∘] : {a : ob} → a ⇛ a
    _∘_ : {a b c : ob} → a ⇒ b → b ⇛ c → a ⇛ c

open 0-Idᴹ using (!) renaming (_⇛_ to 0-Idᴬ) public
open 0-Mulᴹ using (_,_) renaming (_⇛_ to 0-Mulᴬ) public
open 0-Pathᴹ using ([∘]; _∘_) renaming (_⇛_ to 0-Pathᴬ) public

--------------------------------------------------------------- morphisms

List/cata : {X R : Typeᵀ} → R → (X → R → R) → 0-Listᵀ X → R
List/cata {X} {R} nil cons = cata
  where
    cata : 0-Listᵀ X → R
    cata [∙] = nil
    cata (head ∙ tail) = cons head (cata tail)

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

infixr 5 _∙_
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

record 0-Graphᴿ : Typeᵀ
  where
    constructor Mk
    field ob : Typeᵀ
    field apply : ob ↠ Typeᵀ

instance
  0-Graph:Ob : Obᴿ Typeᵀ
  0-Graph:Ob = Mk _ 0-Graphᴿ.ob

-- plain `arrow` operator
infix 0 _⟶_
_⟶_ :
    {{rec : 0-Graphᴿ}} →
    Ob rec ↠ Typeᵀ
_⟶_ {{rec}} = 0-Graphᴿ.apply rec

instance
  Typeᴳ : 0-Graphᴿ
  Typeᴳ = Mk _ _-ᵀ→_

instance
  Arrowᴳ : {ob : Typeᵀ} → 0-Graphᴿ
  Arrowᴳ {ob} = Mk (ob ↠ Typeᵀ) _-ᴬ→_

---------------------------------------------------------------

-- U-enriched graph

record E0-Graphᴿ (U : 0-Graphᴿ) : Typeᵀ
  where
    constructor Mk
    field ob : Typeᵀ
    field apply : ob ↠ Ob U

instance
  E0-Graph:Ob : {U : 0-Graphᴿ} → Obᴿ Typeᵀ
  E0-Graph:Ob {U} = Mk _ (E0-Graphᴿ.ob {U})

-- enriched `arrow` operator
_⟹_ :
    {U : 0-Graphᴿ} →
    {{rec : E0-Graphᴿ U}} →
    Ob rec ↠ Ob U
_⟹_ {{rec}} = E0-Graphᴿ.apply rec

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

0-Categoryᵀ : {ob : Typeᵀ} → ob ↠ Typeᵀ → Typeᵀ
0-Categoryᵀ carrier = 0-Pathᴬ carrier ⟶ carrier
