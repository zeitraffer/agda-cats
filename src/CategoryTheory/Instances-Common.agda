{-# OPTIONS --type-in-type #-}

module CategoryTheory.Instances-Common where

open import CategoryTheory.Common
open import CategoryTheory.Classes-Common

instance
    identity/Wrapper : {T : Typeᵀ} → Wrapperᴿ T T
    Wrapperᴿ.get-Get identity/Wrapper x = x
    Wrapperᴿ.get-Put identity/Wrapper x = x
