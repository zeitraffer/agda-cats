{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Common-Module where

--------------------------------------------------------------- Common-Oper

-- synonym for the type of types
Typeᵀ : Set
Typeᵀ = Set

-- synomym for lambda syntax
infixr -100 λ-syntax
λ-syntax : {A : Typeᵀ} → {B : A → Typeᵀ} → ((a : A) → B a) → ((a : A) → B a)
λ-syntax f = f
syntax λ-syntax (λ a → b) = a ↦ b

-- declare type in subexpression: prefix (the), postfix (as)
the : (A : Typeᵀ) → A → A
the A a = a
syntax the A a = a :: A

--------------------------------------------------------------- Common-Classes

-- `Arg` class

Argᵀ : (result arg : Typeᵀ) → Typeᵀ
Argᵀ result arg = arg → result

record Argᴿ (Resultᵀ : Typeᵀ) : Typeᵀ
  where
    constructor Mk
    field arg : Typeᵀ
    field apply : Argᵀ Resultᵀ arg

Arg :
    {result : Typeᵀ} →
    {{A : Argᴿ result}} →
    Argᵀ result (Argᴿ.arg A)
Arg {{A}} = Argᴿ.apply A

-- `Apply` class

Applyᵀ :
    {result : Typeᵀ} →
    (class : result → Typeᵀ) →
    Argᴿ result → Typeᵀ
Applyᵀ class A = (a : Argᴿ.arg A) → class (Arg a)

record Applyᴿ (Resultᵀ : Typeᵀ) (Classᵀ : Resultᵀ → Typeᵀ) : Typeᵀ
  where
    constructor Mk
    field A : Argᴿ Resultᵀ
    field apply : Applyᵀ Classᵀ A

Apply :
    {result : Typeᵀ} →
    {class : result → Typeᵀ} →
    {{A : Applyᴿ result class}} →
    Applyᵀ class (Applyᴿ.A A)
Apply {{A}} = Applyᴿ.apply A

instance
  Apply→Arg :
    {result : Typeᵀ} →
    {class : result → Typeᵀ} →
    {{A : Applyᴿ result class}} →
    Argᴿ result
  Apply→Arg {{A}} = Applyᴿ.A A


-- `Ob` class

Obᵀ : Typeᵀ → Typeᵀ
Obᵀ arg = arg → Typeᵀ

record Obᴿ : Typeᵀ
  where
    constructor Mk
    field arg : Typeᵀ
    field apply : Obᵀ arg

Ob : {{O : Obᴿ}} → Obᵀ (Obᴿ.arg O)
Ob {{O}} = Obᴿ.apply O

-- `Carrier` class

record Carrierᴿ (Resultᵀ : Typeᵀ) : Typeᵀ
  where
    constructor Mk
    field arg : Typeᵀ
    field apply : Argᵀ Resultᵀ arg

Carrier :
    {result : Typeᵀ} →
    {{C : Carrierᴿ result}} →
    Argᵀ result (Carrierᴿ.arg C)
Carrier {{C}} = Carrierᴿ.apply C

--------------------------------------------------------------- Common-Instances

-- Arg

Arg:Arg : {result : Typeᵀ} → Argᴿ Typeᵀ
Arg:Arg {result} = Mk (Argᴿ result) Argᴿ.arg

instance
  Arg:Apply : {result : Typeᵀ} → Applyᴿ _ (Argᵀ result)
  Arg:Apply = Mk Arg:Arg Argᴿ.apply

-- Apply

Apply:Arg : {result : Typeᵀ} → {class : result → Typeᵀ} → Argᴿ (Argᴿ result)
Apply:Arg {result} {class} = Mk (Applyᴿ result class) Applyᴿ.A

instance
  Apply:Apply :
    {result : Typeᵀ} →
    {class : result → Typeᵀ} →
    Applyᴿ _ (Applyᵀ class)
  Apply:Apply {result} {class} = Mk (Apply:Arg {result} {class}) Applyᴿ.apply

-- Ob

Ob:Arg : Argᴿ Typeᵀ
Ob:Arg = Mk _ Obᴿ.arg

instance
  Ob:Apply : Applyᴿ _ Obᵀ
  Ob:Apply = Mk _ Obᴿ.apply

-- Carrier

Carrier:Arg : {result : Typeᵀ} → Argᴿ Typeᵀ
Carrier:Arg {result} = Mk (Carrierᴿ result) Carrierᴿ.arg

instance
  Carrier:Apply : {result : Typeᵀ} → Applyᴿ _ (Argᵀ result)
  Carrier:Apply {result} = Mk (Carrier:Arg {result}) Carrierᴿ.apply

---------------------------------------------------------------

_↠_ : Typeᵀ → Typeᵀ → Typeᵀ
ob ↠ U = ob → ob → U

_⇸_ : Typeᵀ → Typeᵀ → Typeᵀ
source ⇸ target = source → target → Typeᵀ

_−ᵀ→_ : Typeᵀ ↠ Typeᵀ
a −ᵀ→ b = a → b

-- identity function
ᵀ⟨⟩ : {X : Typeᵀ} → X −ᵀ→ X
ᵀ⟨⟩ = x ↦ x

-- function composition
_ᵀ∘_ : {X Y Z : Typeᵀ} → X −ᵀ→ Y → Y −ᵀ→ Z → X −ᵀ→ Z
f ᵀ∘ g = x ↦ g (f x)

--------------------------------------------------------------- Data

data ⊤ᵀ : Typeᵀ where
    ! : ⊤ᵀ

infixr 10 _×ᵀ_
infixr 0 _,_
data _×ᵀ_ (L R : Typeᵀ) : Typeᵀ where
    _,_ : (l : L) → (r : R) → L ×ᵀ R

infixr 5 _∙_
data 0-Listᵀ (X : Typeᵀ) : Typeᵀ where
    [] : 0-Listᵀ X
    _∙_ : X → 0-Listᵀ X → 0-Listᵀ X

module 0-Id {X : Typeᵀ} where
  data _⇛_ : X ⇸ X where
    ! : {x : X} → x ⇛ x

module 0-Mul {X Y Z : Typeᵀ} (_⇒₁_ : X ⇸ Y) (_⇒₂_ : Y ⇸ Z) where
  infixr 0 _,_
  data _⇛_ : X ⇸ Z where
    _,_ : {x : X} → {y : Y} → {z : Z} → x ⇒₁ y → y ⇒₂ z → x ⇛ z

module 0-Path {ob : Typeᵀ} (_⇒_ : ob ↠ Typeᵀ) where
  infixr 5 _∘_
  data _⇛_ : ob ↠ Typeᵀ where
    [] : {a : ob} → a ⇛ a
    _∘_ : {a b c : ob} → a ⇒ b → b ⇛ c → a ⇛ c

-- TODO just []

open 0-Id using (!) renaming (_⇛_ to ①ᴬ) public
open 0-Mul using (_,_) renaming (_⇛_ to _⊗ᴬ_) public
open 0-Path using ([]; _∘_) renaming (_⇛_ to 0-Pathᴬ) public

-- propositional equality to be the identity relation
_≡_ : {X : Typeᵀ} → X ↠ Typeᵀ
_≡_ = ①ᴬ



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

_−ᴬ→_ : {ob : Typeᵀ} → (ob ↠ Typeᵀ) ↠ Typeᵀ
_−ᴬ→_ {ob} _⇒₁_ _⇒₂_ = {a b : ob} → (a ⇒₁ b) −ᵀ→ (a ⇒₂ b)

TypeEndoᵀ : Typeᵀ
TypeEndoᵀ = Typeᵀ → Typeᵀ

-- plain part of natural transformation
_−ᴺ→_ : TypeEndoᵀ ↠ Typeᵀ
F −ᴺ→ G = {x : Typeᵀ} → F x −ᵀ→ G x
-- TODO use general 0-NatTrans

--------------------------------------------------------------- morphisms

Type/neutral' : Typeᵀ
Type/neutral' = ⊤ᵀ

Type/compose' : Typeᵀ → Typeᵀ → Typeᵀ
Type/compose' = _×ᵀ_

Type/0-aryᵀ : TypeEndoᵀ
Type/0-aryᵀ X = Type/neutral' −ᵀ→ X

Type/0-ary'ᵀ : TypeEndoᵀ
Type/0-ary'ᵀ X = X

Type/0-ary/wrap : Type/0-ary'ᵀ −ᴺ→ Type/0-aryᵀ
Type/0-ary/wrap x u = x

Type/0-ary/unwrap : Type/0-aryᵀ −ᴺ→ Type/0-ary'ᵀ
Type/0-ary/unwrap ξ = ξ !

Type/2-aryᵀ : TypeEndoᵀ
Type/2-aryᵀ X = Type/compose' X X −ᵀ→ X

Type/2-ary'ᵀ : TypeEndoᵀ
Type/2-ary'ᵀ X = X → X → X

Type/2-ary/wrap : Type/2-ary'ᵀ −ᴺ→ Type/2-aryᵀ
Type/2-ary/wrap b p =

Type/2-ary/unwrap : Type/2-aryᵀ −ᴺ→ Type/2-ary'ᵀ
Type/2-ary/unwrap {X} ξ = ξ !

TypeEndo/neutral' : Type/0-ary'ᵀ TypeEndoᵀ
TypeEndo/neutral' = X ↦ X

TypeEndo/compose' : Type/2-ary'ᵀ TypeEndoᵀ
TypeEndo/compose' F G = X ↦ G (F X)

TypeEndo/neutralᵀ : TypeEndoᵀ → Typeᵀ
TypeEndo/neutralᵀ F = TypeEndo/neutral' −ᴺ→ F

TypeEndo/composeᵀ : TypeEndoᵀ → Typeᵀ
TypeEndo/composeᵀ F = TypeEndo/compose' F F −ᴺ→ F

---------------------------------------------------------------

List/cata' : {X R : Typeᵀ} → R → (X → R → R) → 0-Listᵀ X → R
List/cata' {X} {R} nil cons = cata
  where
    cata : 0-Listᵀ X → R
    cata [] = nil
    cata (head ∙ tail) = cons head (cata tail)

List/neutral' : {X : Typeᵀ} → Type/0-ary'ᵀ (0-Listᵀ X)
List/neutral' = []

List/compose' : {X : Typeᵀ} → Type/2-ary'ᵀ (0-Listᵀ X)
List/compose' = List/cata' ᵀ⟨⟩ (x ↦ f ↦ l ↦ x ∙ f l)

List/return : TypeEndo/neutralᵀ 0-Listᵀ
List/return x = x ∙ []

List/flatten : TypeEndo/composeᵀ 0-Listᵀ
List/flatten = List/cata' List/neutral' List/compose'

---------------------------------------------------------------
-- TODO [,,,] overloaded HList
-- TODO Wrap class
