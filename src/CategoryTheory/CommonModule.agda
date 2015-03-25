module CategoryTheory.CommonModule where

open import Agda.Primitive public

ZeroLevel : Level
ZeroLevel = lzero

SuccLevel : (ℓ : Level) → Level
SuccLevel = lsuc

_JoinLevel_ : (ℓ₁ ℓ₂ : Level) → Level
_JoinLevel_ = _⊔_ 
