{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Common-Module where

--------------------------------------------------------------- Common-Oper

-- synonym for the type of types
Typeᵀ : Set
Typeᵀ = Set

-- synomym for lambda syntax
λ-syntax : {Aᵀ : Typeᵀ} → {Bᵀ : Aᵀ → Typeᵀ} → ((a : Aᵀ) → Bᵀ a) → ((a : Aᵀ) → Bᵀ a)
λ-syntax f = f
syntax λ-syntax (λ a → b) = [ a ↦ b ]

-- declare type in subexpression: prefix (the), postfix (as)
the : (Aᵀ : Typeᵀ) → Aᵀ → Aᵀ
the Aᵀ a = a
syntax the A a = a as A

--------------------------------------------------------------- Common-Classes

-- `Apply` class (previous)

Argᵀ : (result arg : Typeᵀ) → Typeᵀ
Argᵀ result arg = arg → result

-- `Arg` class

record Argᴿ (Resultᵀ : Typeᵀ) : Typeᵀ
  where
    constructor Mk
    field argᵀ : Typeᵀ
    field apply : Argᵀ Resultᵀ argᵀ

Arg :
    {Resultᵀ : Typeᵀ} →
    {{arg-rec : Argᴿ Resultᵀ}} →
    Argᵀ Resultᵀ (Argᴿ.argᵀ arg-rec)
Arg {{arg-rec}} = Argᴿ.apply arg-rec

-- `Apply` class

Applyᵀ :
    {resultᵀ : Typeᵀ} →
    (classᵀ : resultᵀ → Typeᵀ) →
    (Argᴿ resultᵀ) →
    Typeᵀ
Applyᵀ classᵀ arg-rec = (arg : Argᴿ.argᵀ arg-rec) → classᵀ (Arg arg)

record Applyᴿ (Resultᵀ : Typeᵀ) (Classᵀ : Resultᵀ → Typeᵀ) : Typeᵀ
  where
    constructor Mk
    field arg-rec : Argᴿ Resultᵀ
    field apply : Applyᵀ Classᵀ arg-rec

Apply :
    {resultᵀ : Typeᵀ} →
    {classᵀ : resultᵀ → Typeᵀ} →
    {{apply-rec : Applyᴿ resultᵀ classᵀ}} →
    Applyᵀ classᵀ (Applyᴿ.arg-rec apply-rec)
Apply {{apply-rec}} = Applyᴿ.apply apply-rec

instance
  Apply→Arg :
    {resultᵀ : Typeᵀ} →
    {classᵀ : resultᵀ → Typeᵀ} →
    {{apply-rec : Applyᴿ resultᵀ classᵀ}} →
    Argᴿ resultᵀ
  Apply→Arg {{apply-rec}} = Applyᴿ.arg-rec apply-rec


-- `Ob` class

record Obᴿ (Resultᵀ : Typeᵀ) : Typeᵀ
  where
    constructor Mk
    field argᵀ : Typeᵀ
    field apply : Argᵀ Resultᵀ argᵀ

Ob :
    {resultᵀ : Typeᵀ} →
    {{ob-rec : Obᴿ resultᵀ}} →
    Argᵀ resultᵀ (Obᴿ.argᵀ ob-rec)
Ob {{ob-rec}} = Obᴿ.apply ob-rec

-- `Carrier` class

record Carrierᴿ (Resultᵀ : Typeᵀ) : Typeᵀ
  where
    constructor Mk
    field argᵀ : Typeᵀ
    field apply : Argᵀ Resultᵀ argᵀ

Carrier :
    {resultᵀ : Typeᵀ} →
    {{carrier-rec : Carrierᴿ resultᵀ}} →
    Argᵀ resultᵀ (Carrierᴿ.argᵀ carrier-rec)
Carrier {{carrier-rec}} = Carrierᴿ.apply carrier-rec

--------------------------------------------------------------- Common-Instances

-- Arg

Arg:Arg : {resultᵀ : Typeᵀ} → Argᴿ Typeᵀ
Arg:Arg {resultᵀ} = Mk (Argᴿ resultᵀ) Argᴿ.argᵀ

instance
  Arg:Apply : {Resultᵀ : Typeᵀ} → Applyᴿ Typeᵀ (Argᵀ Resultᵀ)
  Arg:Apply = Mk Arg:Arg Argᴿ.apply

-- Apply

Apply:Arg : {resultᵀ : Typeᵀ} → {classᵀ : resultᵀ → Typeᵀ} → Argᴿ (Argᴿ resultᵀ)
Apply:Arg {resultᵀ} {classᵀ} = Mk (Applyᴿ resultᵀ classᵀ) Applyᴿ.arg-rec

instance
  Apply:Apply :
    {resultᵀ : Typeᵀ} →
    {classᵀ : resultᵀ → Typeᵀ} →
    Applyᴿ (Argᴿ resultᵀ) (Applyᵀ classᵀ)
  Apply:Apply {resultᵀ} {classᵀ} = Mk (Apply:Arg {resultᵀ} {classᵀ}) Applyᴿ.apply

-- Ob

Ob:Arg : {resultᵀ : Typeᵀ} → Argᴿ Typeᵀ
Ob:Arg {resultᵀ} = Mk (Obᴿ resultᵀ) Obᴿ.argᵀ

instance
  Ob:Apply : {resultᵀ : Typeᵀ} → Applyᴿ Typeᵀ (Argᵀ resultᵀ)
  Ob:Apply {resultᵀ} = Mk (Ob:Arg {resultᵀ}) Obᴿ.apply

-- Carrier

Carrier:Arg : {resultᵀ : Typeᵀ} → Argᴿ Typeᵀ
Carrier:Arg {resultᵀ} = Mk (Carrierᴿ resultᵀ) Carrierᴿ.argᵀ

instance
  Carrier:Apply : {resultᵀ : Typeᵀ} → Applyᴿ Typeᵀ (Argᵀ resultᵀ)
  Carrier:Apply {resultᵀ} = Mk (Carrier:Arg {resultᵀ}) Carrierᴿ.apply

---------------------------------------------------------------
