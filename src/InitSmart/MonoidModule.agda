module InitSmart.MonoidModule where

mutual

  -- 'types'
  data Tag : Set where
    Ob : Tag
    _⇒_ : (x y : « Ob ») → Tag
    _≡_ : {x y : « Ob »} → (f g : « x ⇒ y ») → Tag

  -- terms
  data «_» : Tag → Set where

    --≡≡≡≡≡≡≡≡=
    -- system : category structure
    --≡≡≡≡≡≡≡≡=

    -- identity morphism
    IdMor : 

      {x : « Ob »} → 
      --------------
      « x ⇒ x »

    -- composition of morphisms
    _MulMor_ : 

      {x y z : « Ob »} → 
      « x ⇒ y » → 
      « y ⇒ z » → 
      ---------------
      « x ⇒ z »

    -- identity equality / reflixivity
    IdEqu : 

      {x y : « Ob »} → 
      {f : « x ⇒ y »} → 
      -----------------
      « f ≡ f »

    -- composition of equalities / transitivity
    _MulEqu_ : 

      {x y : « Ob »} → 
      {f g h : « x ⇒ y »} → 
      « f ≡ g » → 
      « g ≡ h » → 
      ---------------
      « f ≡ h »

    -- inverse equality / symmetry
    InvEqu : 

      {x y : « Ob »} → 
      {f g : « x ⇒ y »} → 
      « f ≡ g » → 
      --------------
      « g ≡ f »

    -- composition of morphisms is congruence
    _MulMorEqu_ : 

      {x y z : « Ob »} → 
      {f f' : « x ⇒ y »} → 
      {g g' : « y ⇒ z »} → 
      « f ≡ f' » → 
      « g ≡ g' » → 
      -------------------------------------------
      « (f MulMor g) ≡ (f' MulMor g') »

    --≡≡≡≡≡≡≡≡≡≡≡≡=
    -- system : monoidal category structure
    --≡≡≡≡≡≡≡≡≡≡≡≡=

    -- identity object
    IdOb : 

      -------
      « Ob »

    -- monoidal operation in category, action on objects
    _MulOb_ : 

      (l r : « Ob ») → 
      -----------------
      « Ob »

    -- monoidal operation in category, action on morphisms
    _MulObMor_ : 

      {l l' r r' : « Ob »} → 
      « l ⇒ l' » → 
      « r ⇒ r' » → 
      ---------------------------------------
      « (l MulOb r) ⇒ (l' MulOb r') »

    -- monoidal operation in category, action on equalities
    _MulObEqu_ : 

      {l l' r r' : « Ob »} → 
      {fl fl' : « l ⇒ l' »} → 
      {fr fr' : « r ⇒ r' »} → 
      « fl ≡ fl' » → 
      « fr ≡ fr' » → 
      ------------------------------------------------------
      « (fl MulObMor fr) ≡ (fl' MulObMor fr') »

    -- monoidal operation in category, functoriality at identity
    _MulObIdEqu_ : 

      (l r : « Ob ») →
      ------------------
      « (IdMor MulObMor IdMor) ≡ IdMor {l MulOb r} »

    -- monoidal operation in category, functoriality at composition
    MulObMulEqu : 

      {l l' l'' r r' r'' : « Ob »} →
      (f : « l ⇒ l' ») → (f' : « l' ⇒ l'' ») →
      (g : « r ⇒ r' ») → (g' : « r' ⇒ r'' ») →
      -----------------------------------------
      « ((f MulMor f') MulObMor (g MulMor g')) ≡ 
        ((f MulObMor g) MulMor (f' MulObMor g')) »

    -- left neutrality of identity object transformation, top-down direction
    NeutrLeftDownMor : 

      {x : « Ob »} → 
      ------------------------------
      « (IdOb MulOb x) ⇒ x »

    -- left neutrality of identity object transformation, bottom-up direction
    NeutrLeftUpMor : 

      {x : « Ob »} → 
      ------------------------------
      « x ⇒ (IdOb MulOb x) »      

    -- isomorphism
    NeutrLeftDownUpIsoEqu : 

      {x : « Ob »} → 
      ------------------------------
      «(NeutrLeftDownMor MulMor NeutrLeftUpMor) ≡ 
        IdMor {IdOb MulOb x}»

    -- isomorphism
    NeutrLeftUpDownIsoEqu : 

      {x : « Ob »} → 
      ------------------------------
      «(NeutrLeftUpMor MulMor NeutrLeftDownMor) ≡ 
        IdMor {x} »

    -- naturality of `NeutrLeftDownMor`
    NeutrLeftDownMorNatEqu : 

      {x y : « Ob »} → 
      (f : « x ⇒ y ») → 
      --------------------
      « (NeutrLeftDownMor MulMor f) ≡ 
        ((IdMor MulObMor f) MulMor NeutrLeftDownMor) »

    -- naturality of `NeutrLeftUpMor`
    NeutrLeftUpMorNatEqu : 

      {x y : « Ob »} → 
      (f : « x ⇒ y ») → 
      --------------------
      « (NeutrLeftUpMor MulMor (IdMor MulObMor f)) ≡ 
        (f MulMor NeutrLeftUpMor) »

    -- left neutrality of identity object transformation, top-down direction
    NeutrRightDownMor : 

      {x : « Ob »} → 
      ------------------------------
      « (x MulOb IdOb) ⇒ x »

    -- left neutrality of identity object transformation, bottom-up direction
    NeutrRightUpMor : 

      {x : « Ob »} → 
      ------------------------------
      « x ⇒ (x MulOb IdOb) »      

    -- isomorphism
    NeutrRightDownUpIsoEqu : 

      {x : « Ob »} → 
      ------------------------------
      «(NeutrRightDownMor MulMor NeutrRightUpMor) ≡ 
        IdMor {x MulOb IdOb}»

    -- isomorphism
    NeutrRightUpDownIsoEqu : 

      {x : « Ob »} → 
      ------------------------------
      «(NeutrRightUpMor MulMor NeutrRightDownMor) ≡ 
        IdMor {x} »

    -- naturality of `NeutrRightDownMor`
    NeutrRightDownMorNatEqu : 

      {x y : « Ob »} → 
      (f : « x ⇒ y ») → 
      --------------------
      « (NeutrRightDownMor MulMor f) ≡ 
        ((f MulObMor IdMor) MulMor NeutrRightDownMor) »

    -- naturality of `NeutrRightUpMor`
    NeutrRightUpMorNatEqu : 

      {x y : « Ob »} → 
      (f : « x ⇒ y ») → 
      --------------------
      « (NeutrRightUpMor MulMor (f MulObMor IdMor)) ≡ 
        (f MulMor NeutrRightUpMor) »

    -- associativity transformation, left-to-right
    AssocLRMor : 

      {x y z : « Ob »} →
      ---------------------
      «((x MulOb y) MulOb z) ⇒ (x MulOb (y MulOb z))»

    -- associativity transformation, right-to-left
    AssocRLMor : 

      {x y z : « Ob »} →
      ---------------------
      «(x MulOb (y MulOb z)) ⇒ ((x MulOb y) MulOb z)»

    -- associativity transformation, left isomorphism equation
    AssocLeftIsoEqu : 

      {x y z : « Ob »} →
      ---------------------
      « (AssocLRMor MulMor AssocRLMor) ≡
        IdMor {(x MulOb y) MulOb z} »

    -- associativity transformation, right isomorphism equation
    AssocRightIsoEqu : 

      {x y z : « Ob »} →
      ---------------------
      « (AssocRLMor MulMor AssocLRMor) ≡
        IdMor {x MulOb (y MulOb z)} »

    -- associativity transformation, left-to-right, naturality of
    AssocLRMorNatEqu : 

      {x y z x' y' z' : « Ob »} → 
      (f : « x ⇒ x' ») → 
      (g : « y ⇒ y' ») → 
      (h : « z ⇒ z' ») → 
      --------------------------
      « (AssocLRMor MulMor (f MulObMor (g MulObMor h))) ≡
        (((f MulObMor g) MulObMor h) MulMor AssocLRMor) »

    -- associativity transformation, right-to-left, naturality of
    AssocRLMorNatEqu : 

      {x y z x' y' z' : « Ob »} → 
      (f : « x ⇒ x' ») → 
      (g : « y ⇒ y' ») → 
      (h : « z ⇒ z' ») → 
      --------------------------
      « (AssocRLMor MulMor ((f MulObMor g) MulObMor h)) ≡
        ((f MulObMor (g MulObMor h)) MulMor AssocRLMor) »

    --====================
    -- applied : monoid structure
    --====================

    -- the carrier object
    El : 
      « Ob »

    -- the unity of the monoid
    IdEl : 
      « IdOb ⇒ El »

    -- the binary operation of the monoid
    MulEl : 
      « (El MulOb El) ⇒ El »

    -- left neutrality
    NeutralityLeftEqu : 
      « ((IdEl MulObMor (IdMor)) MulMor MulEl) ≡ 
        NeutrLeftDownMor »

    -- right neutrality
    NeutralityRightEqu : 
      « (((IdMor) MulObMor IdEl) MulMor MulEl) ≡ 
        NeutrRightDownMor »

    -- associativity
    AssociativityEqu : 
      « ((MulEl MulObMor IdMor) MulMor MulEl) ≡ 
        (AssocLRMor MulMor ((IdMor MulObMor MulEl) MulMor MulEl)) »

