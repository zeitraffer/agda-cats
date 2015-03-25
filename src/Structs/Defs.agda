module Structs.Defs where

open import Structs.RelModule

record 0CategoryType 
    (ℓ ℓᴬ : Level) : 
    Type (SuccLev ℓ ⊔ SuccLev ℓᴬ)
  where
    constructor Mk0Category
    field 
      fOb : 
        Type ℓ
      fQuiver : 
        RelationType ℓᴬ fOb fOb
      fPaste : 
        {n : NaturalType} → 
          fQuiver ← powerRel n fQuiver
open 0CategoryType public

-- record 1CatType (lev : Level) : Set where
-- record _<-1Cat-_ {lev} (src trg : 1CatType lev) : Set where
