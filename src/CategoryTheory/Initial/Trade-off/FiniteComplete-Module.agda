{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Initial.Trade-off.FiniteComplete-Module where

------------------------------------------
-- `Layer` - level in categorical syntax
-- 

data Layer : Set where
  LZero : Layer
  LSucc : Layer → Layer

Ob : Layer
Ob = LZero

Mor : Layer
Mor = LSucc Ob

Equ : Layer
Equ = LSucc Mor  

mutual

  infix 1 _⊠_ _⇒_ _≡_
  infixl 10 _MulMor_ _MulEqu_ _MulMorEqu_ 

  ---------------------------------------
  -- internal 'types' of terms
  ---------------------------------------
  data “_” 
      : Layer 
      → Set 
    where

      -- objects
      ∗ 
        : “ Ob ”

      -- pairs of objects
      _⊠_ 
        : (left right : “ Ob ”) 
        → “ Ob ”

      -- morphisms
      _⇒_ 
        : {t : “ Ob ”} 
        → (source target : « t ») 
        → “ Mor ”

      -- isomorphisms
      _⇔_ 
        : {t : “ Ob ”} 
        → (source target : « t ») 
        → “ Mor ”

      -- equalities
      _≡_ 
        : {t : “ Mor ”} 
        → (source target : « t ») 
        → “ Equ ”


  ---------------------------------------
  -- terms of internal 'types'
  ---------------------------------------
  data «_» 
      : {layer : Layer} 
      → “ layer ” 
      → Set 
    where

    --=============================================
    -- category structure
    --=============================================

      IdMor 
        : {ob : “ Ob ”} 
        → {x : « ob »} 
        → « x ⇒ x »

      _MulMor_ 
        : {ob : “ Ob ”} 
        → {x y z : « ob »} 
        → « x ⇒ y »
        → « y ⇒ z »
        → « x ⇒ z »

      IdEqu 
        : {mor : “ Mor ”} 
        → {f : « mor »}
        → « f ≡ f »

      _MulEqu_ 
        : {mor : “ Mor ”} 
        → {f g h : « mor »} 
        → « f ≡ g »
        → « g ≡ h »
        → « f ≡ h »

      InvEqu 
        : {mor : “ Mor ”} 
        → {f g : « mor »} 
        → « f ≡ g »
        → « g ≡ f »

      _MulMorEqu_
        : {ob : “ Ob ”}
        → {x y z : « ob »} 
        → {f f' : « x ⇒ y »} 
        → {g g' : « y ⇒ z »} 
        → « f ≡ f' »
        → « g ≡ g' »
        → « f MulMor g ≡ f' MulMor g' »

    --=============================================
    -- isomorphisms
    --=============================================

      -- an isomorphism consists of a pair of morphisms endowed by a pair of equations
      MkIso
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {forward : « x ⇒ y »}
        → {backward : « y ⇒ x »}
        → « forward MulMor backward ≡ IdMor »
        → « IdMor ≡ backward MulMor forward »
        → « x ⇔ y »

      -- forward component of isomorphism
      IsoForwardMor
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → « x ⇔ y »
        → « x ⇒ y »

      -- backward component of isomorphism
      IsoBackwardMor
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → « x ⇔ y »
        → « y ⇒ x »

      -- equation of isomorphism at the begin object
      IsoBeginEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → (i : « x ⇔ y »)
        → « (IsoForwardMor i) MulMor (IsoBackwardMor i) ≡ IdMor »

      -- equation of isomorphism at the end object
      IsoEndEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → (i : « x ⇔ y »)
        → « IdMor ≡ (IsoBackwardMor i) MulMor (IsoForwardMor i) »

      -- decompose and than compose isomorphism 
      MkIsoCorrectEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → (i : « x ⇔ y »)
        → « i ≡ MkIso (IsoBeginEqu i) (IsoEndEqu i) »

      -- compose and decompose isomorphism, at forward
      IsoForwardMorCorrectEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {forward : « x ⇒ y »}
        → {backward : « y ⇒ x »}
        → (ex : « forward MulMor backward ≡ IdMor »)
        → (ey : « IdMor ≡ backward MulMor forward »)
        → « IsoForwardMor (MkIso ex ey) ≡ forward »

      -- compose and decompose isomorphism, at backward
      IsoBackwardMorCorrectEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {forward : « x ⇒ y »}
        → {backward : « y ⇒ x »}
        → (ex : « forward MulMor backward ≡ IdMor »)
        → (ey : « IdMor ≡ backward MulMor forward »)
        → « IsoBackwardMor (MkIso ex ey) ≡ backward »

      -- morphism constructor acts on equalities
      MkIsoEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {forward forward' : « x ⇒ y »}
        → {backward backward' : « y ⇒ x »}
        → (ex : « forward MulMor backward ≡ IdMor »)
        → (ey : « IdMor ≡ backward MulMor forward »)
        → (ex' : « forward' MulMor backward' ≡ IdMor »)
        → (ey' : « IdMor ≡ backward' MulMor forward' »)
        → (eforw : « forward ≡ forward' »)
        → (eback : « backward ≡ backward' »)
        → « MkIso ex ey ≡ MkIso ex' ey' »

      -- forward projection acts on equalities
      IsoForwardMorEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {i i' : « x ⇔ y »}
        → « i ≡ i' »
        → « IsoForwardMor i ≡ IsoForwardMor i' »

      -- backward projection acts on equalities
      IsoBackwardMorEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {i i' : « x ⇔ y »}
        → « i ≡ i' »
        → « IsoBackwardMor i ≡ IsoBackwardMor i' »

      InvIso
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → « x ⇔ y »
        → « y ⇔ x »

      InvIsoEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {i i' : « x ⇔ y »}
        → « i ≡ i' »
        → « InvIso i ≡ InvIso i' »

      InvForwardIsoEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → (i : « x ⇔ y »)
        → « IsoForwardMor (InvIso i) ≡ IsoBackwardMor i »

      InvBackwardIsoEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → (i : « x ⇔ y »)
        → « IsoBackwardMor (InvIso i) ≡ IsoForwardMor i »

    --=============================================
    -- product category structure
    --=============================================

      _CatPairOb_ 
        : {obl obr : “ Ob ”}
        → « obl »
        → « obr »
        → « obl ⊠ obr »

      _CatPairMor_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → « l ⇒ l' »
        → « r ⇒ r' »
        → « l CatPairOb r ⇒ l' CatPairOb r' »

      _CatPairEqu_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → (fl fl' : « l ⇒ l' »)
        → (fr fr' : « r ⇒ r' »)
        → « fl ≡ fl' »
        → « fr ≡ fr' »
        → « fl CatPairMor fr ≡ fl' CatPairMor fr' »

      CatProjLeftOb
        : {obl obr : “ Ob ”}
        → « obl ⊠ obr »
        → « obl »

      CatProjRightOb
        : {obl obr : “ Ob ”}
        → « obl ⊠ obr »
        → « obr »

      CatProjLeftMor
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → « l CatPairOb r ⇒ l' CatPairOb r' »
        → « l ⇒ l' »

      CatProjRightMor
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → « l CatPairOb r ⇒ l' CatPairOb r' »
        → « r ⇒ r' »

      _CatProjLeftEqu_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → (fl fl' : « l ⇒ l' »)
        → (fr fr' : « r ⇒ r' »)
        → « fl CatPairMor fr ≡ fl' CatPairMor fr' »
        → « fl ≡ fl' »

      _CatProjRightEqu_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → (fl fl' : « l ⇒ l' »)
        → (fr fr' : « r ⇒ r' »)
        → « fl CatPairMor fr ≡ fl' CatPairMor fr' »
        → « fr ≡ fr' »

