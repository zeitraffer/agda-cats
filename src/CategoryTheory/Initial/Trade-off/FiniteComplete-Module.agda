{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Initial.Trade-off.FiniteComplete-Module where

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

Ob : Layer
Ob = LZero

Mor : Layer
Mor = LSucc Ob

Equ : Layer
Equ = LSucc Mor  

--------------------------------
-- `_↠_` - styles of morphisms
-- 

data _↠_
    : (arg res : Layer) → Set 
  where
    ⇒ 
      : Ob ↠ Mor
    ⇔ 
      : Ob ↠ Mor
    ≡ 
      : Mor ↠ Equ

------------------------------------------
mutual

  infix 1 _⊗_ _∙_∙_
  infixl 10 _MulMor_ _MulEqu_ _MulMorEqu_ 
  infixl 10 _CatPairOb_ _CatPairMor_ _CatPairEqu_ 

  ---------------------------------------
  -- internal 'types' of terms
  ---------------------------------------
  data “_” 
      : Layer 
      → Set 
    where

      -- type of objects of the specified category
      ⋆ 

        --------
        : “ Ob ”

      -- type of objects of terminal category
      ① 

        --------
        : “ Ob ”

      -- type of pairs of objects
      _⊗_ 

        : “ Ob ”
        → “ Ob ”
        ---------
        → “ Ob ”

      -- creates a morphism type of a given style from two objects
      _∙_∙_ 

        : {layer-ob layer-mor : Layer} 
        → {ob : “ layer-ob ”} 
        → « ob » 
        → layer-ob ↠ layer-mor
        → « ob » 
        ---------------
        → “ layer-mor ”

      -- type of commutative squares
      Square

        : {layer-ob layer-mor layer-equ : Layer} 
        → layer-mor ↠ layer-equ
        → {⟹ : layer-ob ↠ layer-mor }
        → {ob : “ layer-ob ”} 
        → {x11 x12 x21 x22 : « ob »}
        → « x11 ∙ ⟹ ∙ x12 »
        → « x21 ∙ ⟹ ∙ x22 »
        → « x11 ∙ ⟹ ∙ x21 »
        → « x12 ∙ ⟹ ∙ x22 »
        ----------------------
        → “ layer-equ ”


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
        → {⟹ : Ob ↠ Mor }
        → (x : « ob »)
        → « x ∙ ⟹ ∙ x »

      _MulMor_ 
        : {ob : “ Ob ”} 
        → {⟹ : Ob ↠ Mor }
        → {x y z : « ob »} 
        → « x ∙ ⟹ ∙ y »
        → « y ∙ ⟹ ∙ z »
        → « x ∙ ⟹ ∙ z »

      IdEqu 
        : {mor : “ Mor ”} 
        → {≡≡ : Mor ↠ Equ }
        → (f : « mor »)
        → « f ∙ ≡≡ ∙ f »

      _MulEqu_ 
        : {mor : “ Mor ”} 
        → {≡≡ : Mor ↠ Equ }
        → {f g h : « mor »} 
        → « f ∙ ≡≡ ∙ g »
        → « g ∙ ≡≡ ∙ h »
        → « f ∙ ≡≡ ∙ h »

      InvEqu 
        : {mor : “ Mor ”} 
        → {f g : « mor »} 
        → « f ∙ ≡ ∙ g »
        → « g ∙ ≡ ∙ f »

      _MulMorEqu_
        : {ob : “ Ob ”}
        → {⟹ : Ob ↠ Mor }
        → {≡≡ : Mor ↠ Equ }
        → {x y z : « ob »} 
        → {f f' : « x ∙ ⟹ ∙ y »} 
        → {g g' : « y ∙ ⟹ ∙ z »} 
        → « f ∙ ≡≡ ∙ f' »
        → « g ∙ ≡≡ ∙ g' »
        → « f MulMor g ∙ ≡≡ ∙ f' MulMor g' »

      NeutrLeftEqu
        : {ob : “ Ob ”}
        → {⟹ : Ob ↠ Mor }
        → {x y : « ob »} 
        → (f : « x ∙ ⟹ ∙ y »)
        → « IdMor x MulMor f ∙ ≡ ∙ f »

      NeutrRightEqu
        : {ob : “ Ob ”}
        → {⟹ : Ob ↠ Mor }
        → {x y : « ob »} 
        → (f : « x ∙ ⟹ ∙ y »)
        → « f MulMor IdMor y ∙ ≡ ∙ f »

      AssocEqu
        : {ob : “ Ob ”}
        → {⟹ : Ob ↠ Mor }
        → {x y z t : « ob »} 
        → (f : « x ∙ ⟹ ∙ y ») 
        → (g : « y ∙ ⟹ ∙ z ») 
        → (h : « z ∙ ⟹ ∙ t ») 
        → « (f MulMor g) MulMor h ∙ ≡ ∙ f MulMor (g MulMor h) »

    --=============================================
    -- isomorphisms
    --=============================================

      -- an isomorphism consists of a pair of morphisms endowed by a pair of equations
      MkIso
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {forward : « x ∙ ⇒ ∙ y »}
        → {backward : « y ∙ ⇒ ∙ x »}
        → « forward MulMor backward ∙ ≡ ∙ IdMor x »
        → « IdMor y ∙ ≡ ∙ backward MulMor forward »
        → « x ∙ ⇔ ∙ y »

      -- forward component of isomorphism
      IsoForwardMor
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → « x ∙ ⇔ ∙ y »
        → « x ∙ ⇒ ∙ y »

      -- backward component of isomorphism
      IsoBackwardMor
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → « x ∙ ⇔ ∙ y »
        → « y ∙ ⇒ ∙ x »

      -- equation of isomorphism at the begin object
      IsoBeginEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → (i : « x ∙ ⇔ ∙ y »)
        → « (IsoForwardMor i) MulMor (IsoBackwardMor i) ∙ ≡ ∙ IdMor x »

      -- equation of isomorphism at the end object
      IsoEndEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → (i : « x ∙ ⇔ ∙ y »)
        → « IdMor y ∙ ≡ ∙ (IsoBackwardMor i) MulMor (IsoForwardMor i) »

      -- decompose and than compose isomorphism 
      MkIsoCorrectEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → (i : « x ∙ ⇔ ∙ y »)
        → « i ∙ ≡ ∙ MkIso (IsoBeginEqu i) (IsoEndEqu i) »

      -- compose and decompose isomorphism, at forward
      IsoForwardMorCorrectEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {forward : « x ∙ ⇒ ∙ y »}
        → {backward : « y ∙ ⇒ ∙ x »}
        → (ex : « forward MulMor backward ∙ ≡ ∙ IdMor x »)
        → (ey : « IdMor y ∙ ≡ ∙ backward MulMor forward »)
        → « IsoForwardMor (MkIso ex ey) ∙ ≡ ∙ forward »

      -- compose and decompose isomorphism, at backward
      IsoBackwardMorCorrectEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {forward : « x ∙ ⇒ ∙ y »}
        → {backward : « y ∙ ⇒ ∙ x »}
        → (ex : « forward MulMor backward ∙ ≡ ∙ IdMor x »)
        → (ey : « IdMor y ∙ ≡ ∙ backward MulMor forward »)
        → « IsoBackwardMor (MkIso ex ey) ∙ ≡ ∙ backward »

      -- morphism constructor acts on equalities
      MkIsoEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {forward forward' : « x ∙ ⇒ ∙ y »}
        → {backward backward' : « y ∙ ⇒ ∙ x »}
        → {ex : « forward MulMor backward ∙ ≡ ∙ IdMor x »}
        → {ey : « IdMor y ∙ ≡ ∙ backward MulMor forward »}
        → {ex' : « forward' MulMor backward' ∙ ≡ ∙ IdMor x »}
        → {ey' : « IdMor y ∙ ≡ ∙ backward' MulMor forward' »}
        → (eforw : « forward ∙ ≡ ∙ forward' »)
        → (eback : « backward ∙ ≡ ∙ backward' »)
        → « MkIso ex ey ∙ ≡ ∙ MkIso ex' ey' »

      -- forward projection acts on equalities
      IsoForwardMorEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {i i' : « x ∙ ⇔ ∙ y »}
        → « i ∙ ≡ ∙ i' »
        → « IsoForwardMor i ∙ ≡ ∙ IsoForwardMor i' »

      -- backward projection acts on equalities
      IsoBackwardMorEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {i i' : « x ∙ ⇔ ∙ y »}
        → « i ∙ ≡ ∙ i' »
        → « IsoBackwardMor i ∙ ≡ ∙ IsoBackwardMor i' »

      InvIso
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → « x ∙ ⇔ ∙ y »
        → « y ∙ ⇔ ∙ x »

      InvIsoEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {i i' : « x ∙ ⇔ ∙ y »}
        → « i ∙ ≡ ∙ i' »
        → « InvIso i ∙ ≡ ∙ InvIso i' »

      InvDefEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → (i : « x ∙ ⇔ ∙ y »)
        → « InvIso i ∙ ≡ ∙ MkIso (InvEqu (IsoEndEqu i)) (InvEqu (IsoBeginEqu i)) »

    --
    --
    --

      -- square as equation
      MkSquare

          : {≡≡ : Mor ↠ Equ}
          → {⟹ : Ob ↠ Mor }
          → {ob : “ Ob ”} 
          → {x11 x12 x21 x22 : « ob »}
          → {f1x : « x11 ∙ ⟹ ∙ x12 »}
          → {f2x : « x21 ∙ ⟹ ∙ x22 »}
          → {fx1 : « x11 ∙ ⟹ ∙ x21 »}
          → {fx2 : « x12 ∙ ⟹ ∙ x22 »}
          → « (f1x MulMor fx2) ∙ ≡≡ ∙ (fx1 MulMor f2x) »
          ---------------------------------
          → « Square ≡≡ f1x f2x fx1 fx2 »


    --=============================================
    -- the terminal category structure
    --=============================================

      CatOneOb
        : « ① »

      CatOneCorrectIso
        : (x : « ① »)
        → « x ∙ ⇔ ∙ CatOneOb »

--      TerminalCorrectIsoFrwNatEqu
--      TerminalCorrectIsoBckNatEqu

--      OneCorrectOkEqu      
--        → « OneCorrectIso MkOneOb ∙ ≡ ∙ IdIso »

    --=============================================
    -- product of categories structure
    --=============================================

      _CatPairOb_ 
        : {obl obr : “ Ob ”}
        → « obl »
        → « obr »
        → « obl ⊗ obr »

      _CatPairMor_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → « l ∙ ⇒ ∙ l' »
        → « r ∙ ⇒ ∙ r' »
        → « l CatPairOb r ∙ ⇒ ∙ l' CatPairOb r' »

      _CatPairEqu_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → {fl fl' : « l ∙ ⇒ ∙ l' »}
        → {fr fr' : « r ∙ ⇒ ∙ r' »}
        → « fl ∙ ≡ ∙ fl' »
        → « fr ∙ ≡ ∙ fr' »
        → « fl CatPairMor fr ∙ ≡ ∙ fl' CatPairMor fr' »

      CatProjLeftOb
        : {obl obr : “ Ob ”}
        → « obl ⊗ obr »
        → « obl »

      CatProjRightOb
        : {obl obr : “ Ob ”}
        → « obl ⊗ obr »
        → « obr »

      CatProjLeftMor
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → « p ∙ ⇒ ∙ q »
        → « CatProjLeftOb p ∙ ⇒ ∙ CatProjLeftOb q »

      CatProjRightMor
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → « p ∙ ⇒ ∙ q »
        → « CatProjRightOb p ∙ ⇒ ∙ CatProjRightOb q »

      CatProjLeftEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → {f g : « p ∙ ⇒ ∙ q »}
        → « f ∙ ≡ ∙ g »
        → « CatProjLeftMor f ∙ ≡ ∙ CatProjLeftMor g »

      CatProjRightEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → {f g : « p ∙ ⇒ ∙ q »}
        → « f ∙ ≡ ∙ g »
        → « CatProjRightMor f ∙ ≡ ∙ CatProjRightMor g »

      CatPairIdEqu
        : {obl obr : “ Ob ”}
        → {l : « obl »}
        → {r : « obr »}
        → « IdMor l CatPairMor IdMor r ∙ ≡ ∙ IdMor (l CatPairOb r) »

      CatPairMorEqu
        : {obl obr : “ Ob ”}
        → {al bl cl : « obl »}
        → {ar br cr : « obr »}
        → {fl : « al ∙ ⇒ ∙ bl »}
        → {gl : « bl ∙ ⇒ ∙ cl »}
        → {fr : « ar ∙ ⇒ ∙ br »}
        → {gr : « br ∙ ⇒ ∙ cr »}
        → « (fl MulMor gl) CatPairMor (fr MulMor gr) ∙ ≡ ∙ 
            (fl CatPairMor fr) MulMor (gl CatPairMor gr) »

      CatProjLeftIdEqu
        : {obl obr : “ Ob ”}
        → {p : « obl ⊗ obr »}
        → « CatProjLeftMor (IdMor p) ∙ ≡ ∙ IdMor (CatProjLeftOb p) »

      CatProjRightIdEqu
        : {obl obr : “ Ob ”}
        → {p : « obl ⊗ obr »}
        → « CatProjRightMor (IdMor p) ∙ ≡ ∙ IdMor (CatProjRightOb p) »

      CatProjLeftMulEqu
        : {obl obr : “ Ob ”}
        → {p q r : « obl ⊗ obr »}
        → {f : « p ∙ ⇒ ∙ q »}
        → {g : « q ∙ ⇒ ∙ r »}
        → « CatProjLeftMor (f MulMor g) ∙ ≡ ∙ CatProjLeftMor f MulMor CatProjLeftMor g »

      CatProjRightMulEqu
        : {obl obr : “ Ob ”}
        → {p q r : « obl ⊗ obr »}
        → {f : « p ∙ ⇒ ∙ q »}
        → {g : « q ∙ ⇒ ∙ r »}
        → « CatProjRightMor (f MulMor g) ∙ ≡ ∙ CatProjRightMor f MulMor CatProjRightMor g »

      CatPairCorrectIso
        : {obl obr : “ Ob ”}
        → {p : « obl ⊗ obr »}
        → « CatProjLeftOb p CatPairOb CatProjRightOb p ∙ ⇔ ∙ p »

      CatProjLeftCorrectIso
        : {obl obr : “ Ob ”}
        → {l : « obl »}
        → {r : « obr »}
        → « CatProjLeftOb (l CatPairOb r) ∙ ⇔ ∙ l »

      CatProjRightCorrectIso
        : {obl obr : “ Ob ”}
        → {l : « obl »}
        → {r : « obr »}
        → « CatProjRightOb (l CatPairOb r) ∙ ⇔ ∙ r »

      CatPairCorrectIsoFrwNatEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → {f : « p ∙ ⇒ ∙ q »}
        → « (CatProjLeftMor f CatPairMor CatProjRightMor f) MulMor IsoForwardMor CatPairCorrectIso 
             ∙ ≡ ∙ 
            IsoForwardMor CatPairCorrectIso MulMor f »

      CatPairCorrectIsoBkwNatEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → {f : « p ∙ ⇒ ∙ q »}
        → « IsoBackwardMor CatPairCorrectIso MulMor (CatProjLeftMor f CatPairMor CatProjRightMor f) 
             ∙ ≡ ∙ 
            f MulMor IsoBackwardMor CatPairCorrectIso »

      CatProjLeftCorrectIsoFrwNatEqu
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → {fl : « l ∙ ⇒ ∙ l' »}
        → {fr : « r ∙ ⇒ ∙ r' »}
        → « CatProjLeftMor (fl CatPairMor fr) MulMor IsoForwardMor CatProjLeftCorrectIso 
             ∙ ≡ ∙ 
            IsoForwardMor CatProjLeftCorrectIso MulMor fl »

      CatProjLeftCorrectIsoBkwNatEqu
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → {fl : « l ∙ ⇒ ∙ l' »}
        → {fr : « r ∙ ⇒ ∙ r' »}
        → « IsoBackwardMor CatProjLeftCorrectIso MulMor CatProjLeftMor (fl CatPairMor fr) 
             ∙ ≡ ∙ 
            fl MulMor IsoBackwardMor CatProjLeftCorrectIso »

      CatProjRightCorrectIsoFrwNatEqu
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → {fl : « l ∙ ⇒ ∙ l' »}
        → {fr : « r ∙ ⇒ ∙ r' »}
        → « CatProjRightMor (fl CatPairMor fr) MulMor IsoForwardMor CatProjRightCorrectIso 
             ∙ ≡ ∙ 
            IsoForwardMor CatProjRightCorrectIso MulMor fr »

      CatProjRightCorrectIsoBkwNatEqu
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → {fl : « l ∙ ⇒ ∙ l' »}
        → {fr : « r ∙ ⇒ ∙ r' »}
        → « IsoBackwardMor CatProjRightCorrectIso MulMor CatProjRightMor (fl CatPairMor fr) 
             ∙ ≡ ∙ 
            fr MulMor IsoBackwardMor CatProjRightCorrectIso »

