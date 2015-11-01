{-# OPTIONS --type-in-type #-}

module CategoryTheory.Common-Module where

--------------------------------------------------------------- Common-Classes


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

--------------------------------------------------------------- Data

module 0-Path {ob : Typeᵀ} (_⇒_ : ob ↠ Typeᵀ) where
  infixr 5 _∘_
  data _⇛_ : ob ↠ Typeᵀ where
    [] : {a : ob} → a ⇛ a
    _∘_ : {a b c : ob} → a ⇒ b → b ⇛ c → a ⇛ c

-- TODO just []

open 0-Path using ([]; _∘_) renaming (_⇛_ to 0-Pathᴬ) public

---------------------------------------------------------------
-- TODO Wrap class
