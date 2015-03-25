module CategoryTheory.Operations.OperationsModule where

open import CategoryTheory.CommonModule

--
-- basic
--

-- mappings or functions
_←_ : {ℓ : Level} (X Y : Set ℓ) → Set ℓ
X ← Y = Y → X

-- identity function
IdFun : {ℓ : Level} (X : Set ℓ) → (X ← X)
IdFun _ x = x

-- multiplication (composition) of function
_MulFun_ : {ℓ : Level} {X Y Z : Set ℓ} (X←Y : X ← Y) (Y←Z : Y ← Z) → (X ← Z)
(X←Y MulFun Y←Z) z = X←Y (Y←Z (z))

-- product of types
record _ProdType_ {ℓ : Level} (L R : Set ℓ) : Set ℓ
  where
    constructor _,_
    field TypeProjL : L
    field TypeProjR : R
open _ProdType_ public

_ProdTypePair_ : {ℓ : Level} {X L R : Set ℓ} (lf : L ← X) (rf : R ← X) → (L ProdType R) ← X
TypeProjL ((lf ProdTypePair rf) x) = lf x
TypeProjR ((lf ProdTypePair rf) x) = rf x

-- sum of types
data _SumType_ {ℓ : Level} (L R : Set ℓ) : Set ℓ
  where
    TypeInclL : L → L SumType R
    TypeInclR : R → L SumType R

_SumTypePair_ : {ℓ : Level} {L R Y : Set ℓ} (lf : Y ← L) (rf : Y ← R) → Y ← (L SumType R)
(lf SumTypePair rf) (TypeInclL l) = lf l
(lf SumTypePair rf) (TypeInclR r) = rf r
