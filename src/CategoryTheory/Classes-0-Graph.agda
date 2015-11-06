{-# OPTIONS --type-in-type #-}

module CategoryTheory.Classes-0-Graph where

open import CategoryTheory.Common
open import CategoryTheory.Classes-Common
open import CategoryTheory.Instances-Common

record Obᴿ (carrier : Typeᵀ) : Typeᵀ where
    constructor Mk
    field apply : preᵀ carrier
Obᵀ : Typeᵀ
Obᵀ = 𝝨 Obᴿ

instance
    Ob/WrapperGet : {carrier : Typeᵀ} → WrapperGetᴿ (preᵀ carrier) (Obᴿ carrier)
    WrapperGetᴿ.apply Ob/WrapperGet = Obᴿ.apply
instance
    Ob/WrapperPut : {carrier : Typeᵀ} → WrapperPutᴿ (preᵀ carrier) (Obᴿ carrier)
    WrapperPutᴿ.apply Ob/WrapperPut = Mk
instance
    Type/Ob : Obᴿ Typeᵀ
    Obᴿ.apply Type/Ob X = X

Ob : ⦃ 𝕆 : Obᵀ ⦄ → preᵀ (Arg 𝕆)
Ob ⦃ 𝕆 ⦄ = Get (App 𝕆)
Ob' : {carrier : Typeᵀ} → ⦃ 𝕆 : Obᴿ carrier ⦄ → preᵀ carrier
Ob' = Ob

-- plain (non-enriched) graph

record 0-Graphᴿ (ob : Typeᵀ) : Typeᵀ where
    constructor Mk
    field apply : relᵀ ob
0-Graphᵀ : Typeᵀ
0-Graphᵀ = 𝝨 0-Graphᴿ

instance
    0-Graph/WrapperGet : {ob : Typeᵀ} → WrapperGetᴿ (relᵀ ob) (0-Graphᴿ ob)
    WrapperGetᴿ.apply 0-Graph/WrapperGet = 0-Graphᴿ.apply
instance
    0-Graph/WrapperPut : {ob : Typeᵀ} → WrapperPutᴿ (relᵀ ob) (0-Graphᴿ ob)
    WrapperPutᴿ.apply 0-Graph/WrapperPut = Mk
instance
    0-Graph/Ob : Obᴿ 0-Graphᵀ
    Obᴿ.apply 0-Graph/Ob = Arg

Arrow-applyᵀ : (ob carrier : Typeᵀ) → Typeᵀ
Arrow-applyᵀ ob carrier = carrier → relᵀ ob

record Arrowᴿ (ob carrier : Typeᵀ) : Typeᵀ where
    constructor Mk
    field apply : Arrow-applyᵀ ob carrier
Arrowᵀ : Endoᵀ
Arrowᵀ ob = 𝝨 (Arrowᴿ ob)

instance
    Arrow/WrapperGet :
        {ob carrier : Typeᵀ} →
        WrapperGetᴿ (Arrow-applyᵀ ob carrier) (Arrowᴿ ob carrier)
    WrapperGetᴿ.apply Arrow/WrapperGet = Arrowᴿ.apply
instance
    Arrow/WrapperPut :
        {ob carrier : Typeᵀ} →
        WrapperPutᴿ (Arrow-applyᵀ ob carrier) (Arrowᴿ ob carrier)
    WrapperPutᴿ.apply Arrow/WrapperPut = Mk

Arrow :
    {ob : Typeᵀ} → ⦃ 𝔸 : Arrowᵀ ob ⦄ →
    Arrow-applyᵀ ob (Arg 𝔸)
Arrow ⦃ 𝔸 ⦄ = Get (App 𝔸)

Arrow' :
    {ob carrier : Typeᵀ} → ⦃ 𝔸 : Arrowᴿ ob carrier ⦄ →
    Arrow-applyᵀ ob carrier
Arrow' = Arrow

-- plain "arrow" operator
infix 0 _⟶_
_⟶_ : ⦃ 𝔾 : 0-Graphᵀ ⦄ → relᵀ (Ob 𝔾)
_⟶_ ⦃ 𝔾 ⦄ = Get (App 𝔾)
_⟶'_ : {ob : Typeᵀ} → ⦃ 𝔾 : 0-Graphᴿ ob ⦄ → relᵀ ob
_⟶'_ = _⟶_
