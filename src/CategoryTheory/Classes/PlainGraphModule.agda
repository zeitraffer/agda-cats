module CategoryTheory.Classes.PlainGraphModule where

open import CategoryTheory.CommonModule

record PlainGraphLevelClass 
    {ℓ : Level} 
    (ob : Set ℓ) :
    Set
  where
    constructor MkPlainGraphLevelClass
    field
      getℓ : Level
open PlainGraphLevelClass {{...}}

record PlainGraphClass 
    {ℓ : Level} 
    (ob : Set ℓ) :
    Set
  where
    constructor MkPlainGraphClass
    field
      {{∫Level}} : PlainGraphLevelClass ob
open PlainGraphClass {{...}}
