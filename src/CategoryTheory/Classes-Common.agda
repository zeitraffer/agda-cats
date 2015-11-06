{-# OPTIONS --type-in-type #-}

module CategoryTheory.Classes-Common where

open import CategoryTheory.Common

-------------- "Wrapper" class

WrapperGet-applyᵀ : (arg carrier : Typeᵀ) → Typeᵀ
WrapperGet-applyᵀ arg carrier = carrier → arg
WrapperPut-applyᵀ : (arg carrier : Typeᵀ) → Typeᵀ
WrapperPut-applyᵀ arg carrier = arg → carrier

record WrapperGetᴿ (arg carrier : Typeᵀ) : Typeᵀ where
    constructor Mk
    field apply : WrapperGet-applyᵀ arg carrier
WrapperGetᵀ : Endoᵀ
WrapperGetᵀ arg = 𝝨 (WrapperGetᴿ arg)

Get' :
    {arg carrier : Typeᵀ} → ⦃ 𝕎 : WrapperGetᴿ arg carrier ⦄ →
    WrapperGet-applyᵀ arg carrier
Get' ⦃ 𝕎 ⦄ = WrapperGetᴿ.apply 𝕎

Get :
    {arg : Typeᵀ} → ⦃ 𝕎 : WrapperGetᵀ arg ⦄ →
    WrapperGet-applyᵀ arg (𝝨.base 𝕎)
Get ⦃ 𝕎 ⦄ = WrapperGetᴿ.apply (𝝨.fiber 𝕎)

record WrapperPutᴿ (arg carrier : Typeᵀ) : Typeᵀ where
    constructor Mk
    field apply : WrapperPut-applyᵀ arg carrier
WrapperPutᵀ : Endoᵀ
WrapperPutᵀ arg = 𝝨 (WrapperPutᴿ arg)

Put' :
    {arg carrier : Typeᵀ} → ⦃ 𝕎 : WrapperPutᴿ arg carrier ⦄ →
    WrapperPut-applyᵀ arg carrier
Put' ⦃ 𝕎 ⦄ = WrapperPutᴿ.apply 𝕎

Put :
    {arg : Typeᵀ} → ⦃ 𝕎 : WrapperPutᵀ arg ⦄ →
    WrapperPut-applyᵀ arg (𝝨.base 𝕎)
Put ⦃ 𝕎 ⦄ = WrapperPutᴿ.apply (𝝨.fiber 𝕎)

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

Arg' :
    {Base : Typeᵀ} → {Fiber : Base → Typeᵀ} → {carrier : Typeᵀ} →
    ⦃ 𝕎 : WrapperGetᴿ (𝝨 Fiber) carrier ⦄ →
    Sigma-Argᵀ Base carrier
Arg' elem = 𝝨.base (Get' elem)

Arg :
    {Base : Typeᵀ} → {Fiber : Base → Typeᵀ} →
    ⦃ 𝕎 : WrapperGetᵀ (𝝨 Fiber) ⦄ →
    Sigma-Argᵀ Base (𝝨.base 𝕎)
Arg elem = 𝝨.base (Get elem)

App' :
    {Base : Typeᵀ} → {Fiber : Base → Typeᵀ} → {carrier : Typeᵀ} →
    ⦃ 𝕎 : WrapperGetᴿ (𝝨 Fiber) carrier ⦄ →
    Sigma-Appᵀ Base Fiber carrier Arg'
App' elem = 𝝨.fiber (Get' elem)

App :
    {Base : Typeᵀ} → {Fiber : Base → Typeᵀ} →
    ⦃ 𝕎 : WrapperGetᵀ (𝝨 Fiber) ⦄ →
    Sigma-Appᵀ Base Fiber (𝝨.base 𝕎) Arg
App elem = 𝝨.fiber (Get elem)
