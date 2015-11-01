{-# OPTIONS --type-in-type #-}

module CategoryTheory.Classes-Common where

open import CategoryTheory.Common

-------------- "Wrapper" class

Wrapper-Getᵀ : (arg carrier : Typeᵀ) → Typeᵀ
Wrapper-Getᵀ arg carrier = carrier → arg
Wrapper-Putᵀ : (arg carrier : Typeᵀ) → Typeᵀ
Wrapper-Putᵀ arg carrier = arg → carrier

record Wrapperᴿ (arg carrier : Typeᵀ) : Typeᵀ where
    constructor Mk
    field get-Get : Wrapper-Getᵀ arg carrier
    field get-Put : Wrapper-Putᵀ arg carrier
Wrapperᵀ : Endoᵀ
Wrapperᵀ arg = 𝝨 (Wrapperᴿ arg)

Get :
    {arg carrier : Typeᵀ} → ⦃ 𝕎 : Wrapperᴿ arg carrier ⦄ →
    Wrapper-Getᵀ arg carrier
Get ⦃ 𝕎 ⦄ = Wrapperᴿ.get-Get 𝕎

Put :
    {arg carrier : Typeᵀ} → ⦃ 𝕎 : Wrapperᴿ arg carrier ⦄ →
    Wrapper-Getᵀ arg carrier
Put ⦃ 𝕎 ⦄ = Wrapperᴿ.get-Get 𝕎

Sigma-Argᵀ :
    (Base : Typeᵀ) →
    (carrier : Typeᵀ) →
    Typeᵀ
Sigma-Argᵀ Base carrier = carrier → Base

Sigma-Appᵀ :
    (Base : Typeᵀ) → (Base → Typeᵀ) →
    (carrier : Typeᵀ) →
    Sigma-Argᵀ Base carrier →
    Typeᵀ
Sigma-Appᵀ Base Fiber carrier arg = (elem : carrier) → Fiber (arg elem)

Arg :
    {Base : Typeᵀ} → {Fiber : Base → Typeᵀ} → {carrier : Typeᵀ} →
    ⦃ 𝕎 : Wrapperᴿ (𝝨 Fiber) carrier ⦄ →
    Sigma-Argᵀ Base carrier
Arg elem = 𝝨.base (Get elem)

App :
    {Base : Typeᵀ} → {Fiber : Base → Typeᵀ} → {carrier : Typeᵀ} →
    ⦃ 𝕎 : Wrapperᴿ (𝝨 Fiber) carrier ⦄ →
    Sigma-Appᵀ Base Fiber carrier Arg
App elem = 𝝨.fiber (Get elem)
