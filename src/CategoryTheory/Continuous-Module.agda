{-# OPTIONS --type-in-type #-}

module CategoryTheory.Continuous-Module where

open import CategoryTheory.Common

--------------------------------------------------------------- Classes


instance
  Typeᴳ : 0-Graphᴿ
  Typeᴳ = Mk _ _−ᵀ→_

instance
  Arrowᴳ : {ob : Typeᵀ} → 0-Graphᴿ
  Arrowᴳ {ob} = Mk (0-Graphᵀ ob) _−ᴬ→_

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
  E0-Graph:Ob : {U : 0-Graphᴿ} → Obᴿ
  E0-Graph:Ob {U} = Mk _ (E0-Graphᴿ.ob {U})

-- enriched `arrow` operator
infix 0 _⟹_
_⟹_ : {U : 0-Graphᴿ} → {{G : E0-Graphᴿ U}} → E0-Graphᵀ U (Ob G)
_⟹_ {{G}} = E0-Graphᴿ.apply G

instance
  Typeᴳ' : E0-Graphᴿ Typeᴳ
  Typeᴳ' = Mk _ _−ᵀ→_

_=ᴬ⇒_ : {{U : 0-Graphᴿ}} → {ob : Typeᵀ} → 0-Graphᵀ (E0-Graphᵀ U ob)
_=ᴬ⇒_ {ob} _⇒₁_ _⇒₂_ = (a b : ob) → (a ⇒₁ b) ⟶ (a ⇒₂ b)

instance
  Arrowᴳ' : {{U : 0-Graphᴿ}} → {ob : Typeᵀ} → E0-Graphᴿ Typeᴳ
  Arrowᴳ' {{U}} {ob} = Mk (E0-Graphᵀ U ob) _=ᴬ⇒_

---------------------------------------------------------------

-- global elements
Arrow/neutralᵀ : {ob : Typeᵀ} → 0-Graphᵀ ob → Typeᵀ
Arrow/neutralᵀ {ob} _⇒_ = {a : ob} → a ⇒ a

Arrow/neutral'ᵀ : {ob : Typeᵀ} → 0-Graphᵀ ob → Typeᵀ
Arrow/neutral'ᵀ {ob} _⇒_ = {a : ob} → a ⇒ a

Arrow/binop'ᵀ : {ob : Typeᵀ} → 0-Graphᵀ ob → Typeᵀ
Arrow/binop'ᵀ {ob} _⇒_ = {a b c : ob} → a ⇒ b → b ⇒ c → a ⇒ c

Arrow/L-action'ᵀ : {ob : Typeᵀ} → 0-Graphᵀ ob → 0-Graphᵀ ob → Typeᵀ
Arrow/L-action'ᵀ {ob} _⇒_ _⇛_ = {a b c : ob} → a ⇒ b → b ⇛ c → a ⇛ c

Arrow/R-action'ᵀ : {ob : Typeᵀ} → 0-Graphᵀ ob → 0-Graphᵀ ob → Typeᵀ
Arrow/R-action'ᵀ {ob} _⇛_ _⇒_ = {a b c : ob} → a ⇛ b → b ⇒ c → a ⇛ c

-- uncurried version
Path/cata :
    {ob : Typeᵀ} → {X R : 0-Graphᵀ ob} →
    ⟪⟫ ⟶ R → ⟪ X ∙ R ⟫ ⟶ R → 0-Pathᴬ X ⟶ R
Path/cata {ob} {X} {R} nil cons = cata
  where
    cata : 0-Pathᴬ X ⟶ R
    cata [∘] = nil !
    cata (head ∘ tail) = cons (head , cata tail , !)

Path/neutral' : {ob : Typeᵀ} → {X R : 0-Graphᵀ ob} → ⟪⟫ ⟶ 0-Pathᴬ R
Path/neutral' ! = [∘]


--- TODO

---------------------------------------------------------------

-- `Category` is acapability of reducing `Path`
-- `category` is also a monoid enriched in category of `arrows over Ob`

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
  0-Category:Ob : Obᴿ
  0-Category:Ob = Mk _ 0-Categoryᴿ.ob

instance
  0-Category:0-Arrow-of : 0-Arrow-ofᴿ
  0-Category:0-Arrow-of = Mk 0-Category:Ob 0-Categoryᴿ.arrow

instance
  0-Category:Carrier : Carrierᴿ 0-Graphᴿ
  0-Category:Carrier = Mk _ 0-Categoryᴿ.G

0-Paste : {{C : 0-Categoryᴿ}} → 0-Categoryᵀ (Carrier C)
0-Paste {{C}} = Apply C

--------------------------------------------------------------- syntax

infix 6 _⟩
infix 4 ⟨_

-- ⟨a∘b∘c⟩ denote morphism pasting, see tests

⟨⟩ : {{C : 0-Categoryᴿ}} → Arrow/neutralᵀ (Arrow-of C)
⟨⟩ = 0-Paste [∘]

⟨_ : {{C : 0-Categoryᴿ}} → 0-Categoryᵀ (Carrier C)
⟨_ = 0-Paste

_⟩ : {{C : 0-Categoryᴿ}} → Arrow-of C ⟶ 0-Pathᴬ (Arrow-of C)
_⟩ m = m ∘ [∘]

-- category of types
-- instance
--   Type⁰ᶜ : 0-Categoryᴿ
--   Type⁰ᶜ = Mk Typeᴳ

-- TODO getArrow
-- TODO get neutral binop return flatten
-- TODO record for classes

---------------------------------------------------------------
