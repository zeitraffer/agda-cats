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
  infixl 10 _MkPairOb_ _MkPairMor_ _MkPairEqu_ 

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
        → {⟹ₕ : layer-ob ↠ layer-mor }
        → {⟹ᵥ : layer-ob ↠ layer-mor }
        → {ob : “ layer-ob ”} 
        → {x11 x12 x21 x22 : « ob »}
        → layer-mor ↠ layer-equ
        → « x11 ∙ ⟹ₕ ∙ x12 »
        → « x21 ∙ ⟹ₕ ∙ x22 »
        → « x11 ∙ ⟹ᵥ ∙ x21 »
        → « x12 ∙ ⟹ᵥ ∙ x22 »
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

      -- redundant
      NeutrBothEqu
        : {ob : “ Ob ”}
        → {⟹ : Ob ↠ Mor }
        → (x : « ob »)
        → « IdMor x MulMor IdMor x ∙ ≡ ∙ IdMor {⟹ = ⟹} x »

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

      IdIsoEqu      
        : {ob : “ Ob ”} 
        → {x : « ob »} 
        → « IdMor x ∙ ≡ ∙ MkIso (NeutrBothEqu x) (InvEqu (NeutrBothEqu x)) »

    --=============================================
    -- commutative squares
    --=============================================

      -- square as equation
      MkSquareMorMor

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

      MkOneOb
        : « ① »

      OneCorrectIso
        : (x : « ① »)
        → « MkOneOb ∙ ⇔ ∙ x »

      OneCorrectIsoFrwNatEqu
        : {x y : « ① »}
        → (f : « x ∙ ⇒ ∙ y »)
        → « Square ≡ 
            (IdMor MkOneOb) f 
            (OneCorrectIso x) (OneCorrectIso y) »

      OneOkEqu      
        : « OneCorrectIso MkOneOb ∙ ≡ ∙ IdMor MkOneOb »

    --=============================================
    -- product of categories structure
    --=============================================

      _MkPairOb_ 
        : {obl obr : “ Ob ”}
        → « obl »
        → « obr »
        → « obl ⊗ obr »

      _MkPairMor_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → « l ∙ ⇒ ∙ l' »
        → « r ∙ ⇒ ∙ r' »
        → « l MkPairOb r ∙ ⇒ ∙ l' MkPairOb r' »

      _MkPairEqu_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → {fl fl' : « l ∙ ⇒ ∙ l' »}
        → {fr fr' : « r ∙ ⇒ ∙ r' »}
        → « fl ∙ ≡ ∙ fl' »
        → « fr ∙ ≡ ∙ fr' »
        → « fl MkPairMor fr ∙ ≡ ∙ fl' MkPairMor fr' »

      PairLeftOb
        : {obl obr : “ Ob ”}
        → « obl ⊗ obr »
        → « obl »

      PairRightOb
        : {obl obr : “ Ob ”}
        → « obl ⊗ obr »
        → « obr »

      PairLeftMor
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → « p ∙ ⇒ ∙ q »
        → « PairLeftOb p ∙ ⇒ ∙ PairLeftOb q »

      PairRightMor
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → « p ∙ ⇒ ∙ q »
        → « PairRightOb p ∙ ⇒ ∙ PairRightOb q »

      PairLeftEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → {f g : « p ∙ ⇒ ∙ q »}
        → « f ∙ ≡ ∙ g »
        → « PairLeftMor f ∙ ≡ ∙ PairLeftMor g »

      PairRightEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → {f g : « p ∙ ⇒ ∙ q »}
        → « f ∙ ≡ ∙ g »
        → « PairRightMor f ∙ ≡ ∙ PairRightMor g »

      _MkPairIdEqu_
        : {obl obr : “ Ob ”}
        → (l : « obl »)
        → (r : « obr »)
        → « IdMor l MkPairMor IdMor r ∙ ≡ ∙ IdMor (l MkPairOb r) »

      MkPairMorEqu
        : {obl obr : “ Ob ”}
        → {al bl cl : « obl »}
        → {ar br cr : « obr »}
        → (fl : « al ∙ ⇒ ∙ bl »)
        → (gl : « bl ∙ ⇒ ∙ cl »)
        → (fr : « ar ∙ ⇒ ∙ br »)
        → (gr : « br ∙ ⇒ ∙ cr »)
        → « (fl MulMor gl) MkPairMor (fr MulMor gr) ∙ ≡ ∙ 
            (fl MkPairMor fr) MulMor (gl MkPairMor gr) »

      PairLeftIdEqu
        : {obl obr : “ Ob ”}
        → (p : « obl ⊗ obr »)
        → « PairLeftMor (IdMor p) ∙ ≡ ∙ IdMor (PairLeftOb p) »

      PairRightIdEqu
        : {obl obr : “ Ob ”}
        → (p : « obl ⊗ obr »)
        → « PairRightMor (IdMor p) ∙ ≡ ∙ IdMor (PairRightOb p) »

      _PairLeftMulEqu_
        : {obl obr : “ Ob ”}
        → {p q r : « obl ⊗ obr »}
        → (f : « p ∙ ⇒ ∙ q »)
        → (g : « q ∙ ⇒ ∙ r »)
        → « PairLeftMor (f MulMor g) ∙ ≡ ∙ PairLeftMor f MulMor PairLeftMor g »

      _PairRightMulEqu_
        : {obl obr : “ Ob ”}
        → {p q r : « obl ⊗ obr »}
        → (f : « p ∙ ⇒ ∙ q »)
        → (g : « q ∙ ⇒ ∙ r »)
        → « PairRightMor (f MulMor g) ∙ ≡ ∙ PairRightMor f MulMor PairRightMor g »

      MkPairCorrectIso
        : {obl obr : “ Ob ”}
        → (p : « obl ⊗ obr »)
        → « PairLeftOb p MkPairOb PairRightOb p ∙ ⇔ ∙ p »

      _PairLeftCorrectIso_
        : {obl obr : “ Ob ”}
        → (l : « obl »)
        → (r : « obr »)
        → « PairLeftOb (l MkPairOb r) ∙ ⇔ ∙ l »

      _PairRightCorrectIso_
        : {obl obr : “ Ob ”}
        → (l : « obl »)
        → (r : « obr »)
        → « PairRightOb (l MkPairOb r) ∙ ⇔ ∙ r »

      MkPairCorrectIsoNatEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → (f : « p ∙ ⇒ ∙ q »)
        → « Square ≡
            (PairLeftMor f MkPairMor PairRightMor f) f
            (MkPairCorrectIso p) (MkPairCorrectIso q) »

      _PairLeftCorrectIsoNatEqu_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → (fl : « l ∙ ⇒ ∙ l' »)
        → (fr : « r ∙ ⇒ ∙ r' »)
        → « Square ≡
            (PairLeftMor (fl MkPairMor fr)) fl
            (l PairLeftCorrectIso r) (l' PairLeftCorrectIso r') »

      _PairRightCorrectIsoNatEqu_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → (fl : « l ∙ ⇒ ∙ l' »)
        → (fr : « r ∙ ⇒ ∙ r' »)
        → « Square ≡ 
            (PairRightMor (fl MkPairMor fr)) fr
            (l PairRightCorrectIso r) (l' PairRightCorrectIso r') »

