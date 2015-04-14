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

  infix 1 _⊠_ _⇒_ _⇔_ _≡_
  infixl 10 _MulMor_ _MulEqu_ _MulMorEqu_ 
  infixl 10 _CatPairOb_ _CatPairMor_ _CatPairEqu_ 

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

      NeutrLeftEqu
        : {ob : “ Ob ”}
        → {x y : « ob »} 
        → {f : « x ⇒ y »} 
        → « IdMor MulMor f ≡ f »

      NeutrRightEqu
        : {ob : “ Ob ”}
        → {x y : « ob »} 
        → {f : « x ⇒ y »} 
        → « f MulMor IdMor ≡ f »

      AssocEqu
        : {ob : “ Ob ”}
        → {x y z t : « ob »} 
        → {f : « x ⇒ y »} 
        → {g : « y ⇒ z »} 
        → {h : « z ⇒ t »} 
        → « (f MulMor g) MulMor h ≡ f MulMor (g MulMor h) »

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
    -- product of categories structure
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
        → {fl fl' : « l ⇒ l' »}
        → {fr fr' : « r ⇒ r' »}
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
        → {p q : « obl ⊠ obr »}
        → « p ⇒ q »
        → « CatProjLeftOb p ⇒ CatProjLeftOb q »

      CatProjRightMor
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊠ obr »}
        → « p ⇒ q »
        → « CatProjRightOb p ⇒ CatProjRightOb q »

      CatProjLeftEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊠ obr »}
        → {f g : « p ⇒ q »}
        → « f ≡ g »
        → « CatProjLeftMor f ≡ CatProjLeftMor g »

      CatProjRightEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊠ obr »}
        → {f g : « p ⇒ q »}
        → « f ≡ g »
        → « CatProjRightMor f ≡ CatProjRightMor g »

      CatPairIdEqu
        : {obl obr : “ Ob ”}
        → {l : « obl »}
        → {r : « obr »}
        → « IdMor CatPairMor IdMor ≡ IdMor {x = l CatPairOb r} »

      CatPairMorEqu
        : {obl obr : “ Ob ”}
        → {al bl cl : « obl »}
        → {ar br cr : « obr »}
        → {fl : « al ⇒ bl »}
        → {gl : « bl ⇒ cl »}
        → {fr : « ar ⇒ br »}
        → {gr : « br ⇒ cr »}
        → « (fl MulMor gl) CatPairMor (fr MulMor gr) ≡ 
            (fl CatPairMor fr) MulMor (gl CatPairMor gr) »

      CatProjLeftIdEqu
        : {obl obr : “ Ob ”}
        → {p : « obl ⊠ obr »}
        → « CatProjLeftMor (IdMor {x = p}) ≡ IdMor {x = CatProjLeftOb p} »

      CatProjRightIdEqu
        : {obl obr : “ Ob ”}
        → {p : « obl ⊠ obr »}
        → « CatProjRightMor (IdMor {x = p}) ≡ IdMor {x = CatProjRightOb p} »

      CatProjLeftMulEqu
        : {obl obr : “ Ob ”}
        → {p q r : « obl ⊠ obr »}
        → {f : « p ⇒ q »}
        → {g : « q ⇒ r »}
        → « CatProjLeftMor (f MulMor g) ≡ CatProjLeftMor f MulMor CatProjLeftMor g »

      CatProjRightMulEqu
        : {obl obr : “ Ob ”}
        → {p q r : « obl ⊠ obr »}
        → {f : « p ⇒ q »}
        → {g : « q ⇒ r »}
        → « CatProjRightMor (f MulMor g) ≡ CatProjRightMor f MulMor CatProjRightMor g »

      CatPairIso
        : {obl obr : “ Ob ”}
        → {p : « obl ⊠ obr »}
        → « CatProjLeftOb p CatPairOb CatProjRightOb p ⇔ p »

      CatProjLeftIso
        : {obl obr : “ Ob ”}
        → {l : « obl »}
        → {r : « obr »}
        → « CatProjLeftOb (l CatPairOb r) ⇔ l »

      CatProjRightIso
        : {obl obr : “ Ob ”}
        → {l : « obl »}
        → {r : « obr »}
        → « CatProjRightOb (l CatPairOb r) ⇔ r »

      CatPairIsoFrwNatEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊠ obr »}
        → {f : « p ⇒ q »}
        → « (CatProjLeftMor f CatPairMor CatProjRightMor f) MulMor IsoForwardMor CatPairIso 
             ≡ 
            IsoForwardMor CatPairIso MulMor f »

      CatPairIsoBckNatEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊠ obr »}
        → {f : « p ⇒ q »}
        → « IsoBackwardMor CatPairIso MulMor (CatProjLeftMor f CatPairMor CatProjRightMor f) 
             ≡ 
            f MulMor IsoBackwardMor CatPairIso »

      CatProjLeftIsoFrwNatEqu
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → {fl : « l ⇒ l' »}
        → {fr : « r ⇒ r' »}
        → « CatProjLeftMor (fl CatPairMor fr) MulMor IsoForwardMor CatProjLeftIso 
             ≡ 
            IsoForwardMor CatProjLeftIso MulMor fl »

      CatProjLeftIsoBckNatEqu
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → {fl : « l ⇒ l' »}
        → {fr : « r ⇒ r' »}
        → « IsoBackwardMor CatProjLeftIso MulMor CatProjLeftMor (fl CatPairMor fr) 
             ≡ 
            fl MulMor IsoBackwardMor CatProjLeftIso »

      CatProjRightIsoFrwNatEqu
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → {fl : « l ⇒ l' »}
        → {fr : « r ⇒ r' »}
        → « CatProjRightMor (fl CatPairMor fr) MulMor IsoForwardMor CatProjRightIso 
             ≡ 
            IsoForwardMor CatProjRightIso MulMor fr »

      CatProjRightIsoBckNatEqu
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → {fl : « l ⇒ l' »}
        → {fr : « r ⇒ r' »}
        → « IsoBackwardMor CatProjRightIso MulMor CatProjRightMor (fl CatPairMor fr) 
             ≡ 
            fr MulMor IsoBackwardMor CatProjRightIso »

