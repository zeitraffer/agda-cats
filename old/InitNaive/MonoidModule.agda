module InitNaive.MonoidModule where

mutual

  data Tag : Set where
    El : Tag
    _≡_ : « El » → « El » → Tag

  data «_» : Tag → Set where  
    -- setoid structure
    𝟙 : (e : « El ») → « e ≡ e »
    ∘ : {e₁ e₂ e₃ : « El »} → « e₁ ≡ e₂ » → « e₂ ≡ e₃ » → « e₁ ≡ e₃ »
    ⁻ : {e₁ e₂ : « El »} → « e₁ ≡ e₂ » → « e₂ ≡ e₁ »
    -- monoid structure
    ! : « El »
    _*_ : « El » → « El » → « El »
    NeutralityLeftEqu : (e : « El ») → « (! * e) ≡ e »
    NeutralityRightEqu : (e : « El ») → « (e * !) ≡ e »
    AssociativityEqu : (x y z : « El ») → « ((x * y) * z) ≡ (x * (y * z)) »

