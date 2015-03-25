module CategoryTheory.Operations.PlainArrowModule where

open import CategoryTheory.CommonModule
open import CategoryTheory.Operations.TypeModule

record PlainArrowType
    {ℓO : Level} 
    (ℓA : Level)
    (ob : Set ℓO) :
    Set (ℓO ⊔ lsuc ℓA)
  where
    constructor MkPlainArrow
    field
      ❪_❫ₐ : 
        
open PlainArrowType public

record _←PlainArrow-_ 
    {ℓO ℓA : Level} 
    {ob : Set ℓO} 
    (a₂ a₁ : PlainArrowType ℓA ob) :
    Set (ℓO ⊔ ℓA)
  where
    constructor MkPlainArrowMor
    field
      ❪_❫ₐₘ :
        (o₂ o₁ : ob) → 
        (❪ a₁ ❫ₐ o₂ o₁ → ❪ a₂ ❫ₐ o₂ o₁)
open _←PlainArrow-_ public

BackwardPlainArrow : 
    {ℓO ℓA : Level} →
    {O1 O2 : Set ℓO} →
    (O1 → O2) →
    PlainArrowType ℓA O2 → 
    PlainArrowType ℓA O1
❪ BackwardPlainArrow f arrow ❫ₐ target source = ❪ arrow ❫ₐ (f target) (f source)

-- TODO Forward, Backward as functors
