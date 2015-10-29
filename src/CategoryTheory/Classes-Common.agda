{-# OPTIONS --type-in-type #-}

module CategoryTheory.Classes-Common where

open import CategoryTheory.Common

-------------- `Arg` class

Argᵀ : (result arg : Typeᵀ) → Typeᵀ
Argᵀ result arg = arg → result

record Argᴿ (result arg : Typeᵀ) : Typeᵀ
  where
    constructor Mk
    field get : Argᵀ result arg

Arg𝝨 (Res : Typeᵀ) : Typeᵀ
Arg𝝨 Res = 𝝨 (Argᵀ Res)

Arg :
    {result : Typeᵀ} →
    {{A : Argᴿ result}} →
    Argᵀ result (Argᴿ.arg A)
Arg {{A}} = Argᴿ.apply A
