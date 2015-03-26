module InitSmart.MonoidNormal where

mutual

  data ‹› : Set where
    Ob : ‹›
    _⇒_ : (x y : ‹ Ob ›) → ‹›
    _≡_ : {x y : ‹ Ob ›} → (f g : ‹ x ⇒ y ›) → ‹›

  data ‹_› : ‹› → Set where
    0ᴼ : ‹ Ob ›
    Sᴼ : ‹ Ob › → ‹ Ob ›
    Nilᴹ : ‹ 0ᴼ ⇒ 0ᴼ › 
    Zᴹ : {n m : ‹ Ob ›} → ‹ n ⇒ m › → ‹ n ⇒ (Sᴼ m) › 
    Sᴹ : {n m : ‹ Ob ›} → ‹ n ⇒ (Sᴼ m) › → ‹ (Sᴼ n) ⇒ (Sᴼ m) ›
    idᴱ : {n m : ‹ Ob ›} → {f : ‹ n ⇒ m ›} → ‹ f ≡ f ›
