module Structs.NaturalModule where

open import Agda.Primitive public

0ᴸ : Level
0ᴸ = lzero

_+1ᴸ : Level → Level
_+1ᴸ = lsuc

Type : (ℓ : Level) → Set (ℓ +1ᴸ)
Type ℓ = Set ℓ

Type0 = Type 0ᴸ

record LiftType 
    {ℓ : Level} 
    (ℓ⁺ : Level) 
    (T : Type ℓ) : 
    Type (ℓ ⊔ ℓ⁺)
  where
    constructor MkLiftType
    field 
      unLift : T
open LiftType public

data ℕᵀ : 
    Type 0ᴸ
  where
    0ᴺ : ℕᵀ
    _+1ᴺ : ℕᵀ → ℕᵀ

1ᴺ : ℕᵀ
1ᴺ = 0ᴺ +1ᴺ

_+ᴺ_ : (n m : ℕᵀ) → ℕᵀ
0ᴺ +ᴺ m = m
(n +1ᴺ) +ᴺ m = (n +ᴺ m) +1ᴺ
