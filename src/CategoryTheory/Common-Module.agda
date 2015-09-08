{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Common-Module where

--------------------------------------------------------------- Common-Oper

-- synonym for the type of types
Typeᵀ : Set
Typeᵀ = Set

-- synomym for lambda syntax
λ-syntax : {A : Typeᵀ} → {B : A → Typeᵀ} → ((a : A) → B a) → ((a : A) → B a)
λ-syntax f = f
syntax λ-syntax (λ a → b) = [ a ↦ b ]

-- declare type in subexpression: prefix (the), postfix (as)
the : (A : Typeᵀ) → A → A
the A a = a
syntax the A a = a as A

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

record Obᴿ (Resultᵀ : Typeᵀ) : Typeᵀ
  where
    constructor Mk
    field arg : Typeᵀ
    field apply : Argᵀ Resultᵀ arg

Ob :
    {result : Typeᵀ} →
    {{O : Obᴿ result}} →
    Argᵀ result (Obᴿ.arg O)
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
  Arg:Apply : {result : Typeᵀ} → Applyᴿ Typeᵀ (Argᵀ result)
  Arg:Apply = Mk Arg:Arg Argᴿ.apply

-- Apply

Apply:Arg : {result : Typeᵀ} → {class : result → Typeᵀ} → Argᴿ (Argᴿ result)
Apply:Arg {result} {class} = Mk (Applyᴿ result class) Applyᴿ.A

instance
  Apply:Apply :
    {result : Typeᵀ} →
    {class : result → Typeᵀ} →
    Applyᴿ (Argᴿ result) (Applyᵀ class)
  Apply:Apply {result} {class} = Mk (Apply:Arg {result} {class}) Applyᴿ.apply

-- Ob

Ob:Arg : {result : Typeᵀ} → Argᴿ Typeᵀ
Ob:Arg {result} = Mk (Obᴿ result) Obᴿ.arg

instance
  Ob:Apply : {result : Typeᵀ} → Applyᴿ Typeᵀ (Argᵀ result)
  Ob:Apply {result} = Mk (Ob:Arg {result}) Obᴿ.apply

-- Carrier

Carrier:Arg : {result : Typeᵀ} → Argᴿ Typeᵀ
Carrier:Arg {result} = Mk (Carrierᴿ result) Carrierᴿ.arg

instance
  Carrier:Apply : {result : Typeᵀ} → Applyᴿ Typeᵀ (Argᵀ result)
  Carrier:Apply {result} = Mk (Carrier:Arg {result}) Carrierᴿ.apply

---------------------------------------------------------------
