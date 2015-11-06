{-# OPTIONS --type-in-type #-}

module CategoryTheory.Instances-Common where

open import CategoryTheory.Common
open import CategoryTheory.Classes-Common

-- any type is a wrapper for itself
instance
    identity/WrapperGet : {T : Typeᵀ} → WrapperGetᴿ T T
    WrapperGetᴿ.apply identity/WrapperGet x = x
instance
    identity/WrapperPut : {T : Typeᵀ} → WrapperPutᴿ T T
    WrapperPutᴿ.apply identity/WrapperPut x = x

instance
    Get/WrapperGet :
        {arg carrier : Typeᵀ} →
        WrapperGetᴿ (WrapperGet-applyᵀ arg carrier) (WrapperGetᴿ arg carrier)
    WrapperGetᴿ.apply Get/WrapperGet = WrapperGetᴿ.apply
instance
    Get/WrapperPut :
        {arg carrier : Typeᵀ} →
        WrapperPutᴿ (WrapperGet-applyᵀ arg carrier) (WrapperGetᴿ arg carrier)
    WrapperPutᴿ.apply Get/WrapperPut = Mk

instance
    Put/WrapperGet :
        {arg carrier : Typeᵀ} →
        WrapperGetᴿ (WrapperPut-applyᵀ arg carrier) (WrapperPutᴿ arg carrier)
    WrapperGetᴿ.apply Put/WrapperGet = WrapperPutᴿ.apply
instance
    Put/WrapperPut :
        {arg carrier : Typeᵀ} →
        WrapperPutᴿ (WrapperPut-applyᵀ arg carrier) (WrapperPutᴿ arg carrier)
    WrapperPutᴿ.apply Put/WrapperPut = Mk

-- implicit conversion to curried type-class instance
instance
    promoteSigma :
        {Base : Typeᵀ} → {Fiber : Base → Typeᵀ} →
        {base : Base} → ⦃ 𝔽 : Fiber base ⦄ →
        𝝨 Fiber
    promoteSigma {base = base} ⦃ 𝔽 ⦄ = 𝞂 base 𝔽
