module InitSmart.Category where

data Layer : Set where
  Ob : Layer
  Mor_ : Layer → Layer

data Arrow : Set
  where
    ⇒ : Arrow
    _* : Arrow → Arrow

mutual

  data “_” : Layer → Set 
    where
      It : “ Ob ”
      _∙_∙_ : 
          {layer : Layer} → {type : “ layer ”} → 
          « type » → Arrow → « type » → 
          “ Mor layer ”

  data «_» : {layer : Layer} → “ layer ” → Set 
    where

      Empty : 
          {layer : Layer} → {type : “ layer ”} → {⟹ : Arrow} → 
          (x : « type ») → 
          « x ∙ ⟹ * ∙ x »

      _∷_ : 
          {layer : Layer} → {type : “ layer ”} → {⟹ : Arrow} → 
          {x y z : « type »} → 
          « x ∙ ⟹ ∙ y » → « y ∙ ⟹ * ∙ z » → 
          « x ∙ ⟹ * ∙ z »

      Empty' : 
          {layer : Layer} → {type : “ layer ”} → {⟹ ⟹' : Arrow} → 
          (x : « type ») → 
          « Empty x ∙ ⟹' ∙ Empty x »

      _∷'_ : 
          {layer : Layer} → {type : “ layer ”} → {⟹ ⟹' : Arrow} → 
          {x y z : « type »} → 
          {f g : « x ∙ ⟹ ∙ y »} → {fs gs : « y ∙ ⟹ * ∙ z »} → 
          « f ∙ ⟹' ∙ g » → « fs ∙ ⟹' ∙ gs » → 
          « (f ∷ fs) ∙ ⟹' ∙ (g ∷ gs) »
