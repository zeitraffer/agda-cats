{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Initial.Smart.FiniteComplete-Module where

------------------------------------------
-- `Layer` - level in categorical syntax
-- 

data Layer 
    : Set 
  where
    LZero 
      : Layer
    LSucc 
      : Layer → Layer

Cat : Layer
Cat = LZero

Fun : Layer
Fun = LSucc Cat

Mor : Layer
Mor = LSucc Fun

Equ : Layer
Equ = LSucc Mor  

type-syntax : (X : Set) -> X -> X
type-syntax X x = x

syntax type-syntax X x = x ∣ X

infix 1 _∙_∙_

--------------------------------
-- `_↠_` - styles of morphisms
-- 

data _↠_
    : (arg res : Layer) → Set 
  where
    ↦ -- functor
      : Cat ↠ Fun
    ⇄ -- adjunction
      : Cat ↠ Fun
    ⇒ -- morphism = natural transformation
      : Fun ↠ Mor
    ⇔ -- isomorphism
      : Fun ↠ Mor
    ≡ -- equality
      : Mor ↠ Equ

mutual

  ---------------------------------------
  -- internal 'types' of terms
  ---------------------------------------
  data “_” 
      : Layer 
      → Set 
    where

      TheCat
        : “ Cat ”

      -- creates a morphism type of a given style from two objects
      _∙_∙_ 

        : {layer-ob layer-to : Layer} 
        → {ob : “ layer-ob ”} 
        → « ob » 
        → layer-ob ↠ layer-to
        → « ob » 
        ---------------
        → “ layer-to ”


  ---------------------------------------
  -- terms of internal 'types'
  ---------------------------------------
  data «_» 
      : {layer : Layer} 
      → “ layer ” 
      → Set 
    where

    --=============================================
    -- bicategory structure
    --=============================================

      IdEqu
        : {mor : “ Mor ”}
        → (m : « mor »)
        → {≈ : Mor ↠ Equ }
        → « m ∙ ≈ ∙ m »

      MulEqu
        : {mor : “ Mor ”}
        → (m₁ m₂ m₃ : « mor »)
        → {≈ : Mor ↠ Equ }
        → « m₁ ∙ ≈ ∙ m₂ »
        → « m₂ ∙ ≈ ∙ m₃ »
        → « m₁ ∙ ≈ ∙ m₃ »

      InvEqu
        : {mor : “ Mor ”}
        → (m₁ m₂ : « mor »)
        → {≈ : Mor ↠ Equ }
        → « m₁ ∙ ≈ ∙ m₂ »
        → « m₂ ∙ ≈ ∙ m₁ »

      IdMor
        : {fun : “ Fun ”}
        → (f : « fun »)
        → {⟹ : Fun ↠ Mor }
        → « f ∙ ⟹ ∙ f »

      MulMor
        : {fun : “ Fun ”}
        → (f₁ f₂ f₃ : « fun »)
        → {⟹ : Fun ↠ Mor }
        → « f₁ ∙ ⟹ ∙ f₂ »
        → « f₂ ∙ ⟹ ∙ f₃ »
        → « f₁ ∙ ⟹ ∙ f₃ »

      MulMorEqu
        : {fun : “ Fun ”}
        → (f₁ f₂ f₃ : « fun »)
        → {⟹ : Fun ↠ Mor }
        → {≈ : Mor ↠ Equ }
        → {m₁₂ m₁₂' : « f₁ ∙ ⟹ ∙ f₂ »}
        → {m₂₃ m₂₃' : « f₂ ∙ ⟹ ∙ f₃ »}

        → «  »

      IdFun
        : {cat : “ Cat ”}
        → (c : « cat »)
        → {⟶ : Cat ↠ Fun }
        → « c ∙ ⟶ ∙ c »
