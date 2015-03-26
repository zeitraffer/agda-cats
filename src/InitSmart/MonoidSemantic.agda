module InitSmart.MonoidSemantic where

open import InitSmart.MonoidModule
open import InitSmart.MonoidNormal

------------------------------------
-- helper functions
------------------------------------

1ᴼ : ‹ Ob ›
1ᴼ = Sᴼ 0ᴼ

_+ᴼ_ : (n m : ‹ Ob ›) → ‹ Ob ›
0ᴼ +ᴼ m = m
(Sᴼ n) +ᴼ m = Sᴼ (n +ᴼ m)

SZ : {n m : ‹ Ob ›} → ‹ n ⇒ m › → ‹ (Sᴼ n) ⇒ (Sᴼ m) ›
SZ f = Sᴹ (Zᴹ f)

idᴹ : {n : ‹ Ob ›} → ‹ n ⇒ n ›
idᴹ {0ᴼ} = Nilᴹ
idᴹ {Sᴼ _} = SZ idᴹ

_mulᴹ_ : {m n k : ‹ Ob ›} → ‹ m ⇒ n › → ‹ n ⇒ k › → ‹ m ⇒ k ›
Nilᴹ mulᴹ Nilᴹ = Nilᴹ
Nilᴹ mulᴹ (Zᴹ g) = Zᴹ (Nilᴹ mulᴹ g)
(Zᴹ f) mulᴹ (Zᴹ g) = Zᴹ ((Zᴹ f) mulᴹ g)
(Sᴹ f) mulᴹ (Zᴹ g) = Zᴹ ((Sᴹ f) mulᴹ g)
(Zᴹ f) mulᴹ (Sᴹ g) = f mulᴹ g
(Sᴹ f) mulᴹ (Sᴹ g) = Sᴹ (f mulᴹ Sᴹ g)

_+ᴼᴹ_ : {m m' n n' : ‹ Ob ›} → ‹ m ⇒ m' › → ‹ n ⇒ n' › → ‹ (m +ᴼ n) ⇒ (m' +ᴼ n') ›
Nilᴹ +ᴼᴹ g = g
(Zᴹ f) +ᴼᴹ g = Zᴹ (f +ᴼᴹ g)
(Sᴹ f) +ᴼᴹ g = Sᴹ (f +ᴼᴹ g)

neutrDᴹ : {n : ‹ Ob ›} → ‹ (n +ᴼ 0ᴼ) ⇒ n ›
neutrDᴹ {0ᴼ} = Nilᴹ
neutrDᴹ {Sᴼ _} = SZ neutrDᴹ

neutrUᴹ : {n : ‹ Ob ›} → ‹ n ⇒ (n +ᴼ 0ᴼ) ›
neutrUᴹ {0ᴼ} = Nilᴹ
neutrUᴹ {Sᴼ _} = SZ neutrUᴹ

assocLRᴹ : {a b c : ‹ Ob ›} → ‹ ((a +ᴼ b) +ᴼ c) ⇒ (a +ᴼ (b +ᴼ c)) ›
assocLRᴹ {0ᴼ} = idᴹ
assocLRᴹ {Sᴼ n} = SZ (assocLRᴹ {n})

assocRLᴹ : {a b c : ‹ Ob ›} → ‹ (a +ᴼ (b +ᴼ c)) ⇒ ((a +ᴼ b) +ᴼ c) ›
assocRLᴹ {0ᴼ} = idᴹ
assocRLᴹ {Sᴼ n} = SZ (assocRLᴹ {n})

_mulᴱ_ : {x y : ‹ Ob ›} → {f g h : ‹ x ⇒ y ›} → ‹ f ≡ g › → ‹ g ≡ h › → ‹ f ≡ h ›
idᴱ mulᴱ idᴱ = idᴱ

invᴱ : {x y : ‹ Ob ›} → {f g : ‹ x ⇒ y ›} → ‹ f ≡ g › → ‹ g ≡ f ›
invᴱ idᴱ = idᴱ

_mulᴹᴱ_ : {x y z : ‹ Ob ›} → {f f' : ‹ x ⇒ y ›} → {g g' : ‹ y ⇒ z ›} → ‹ f ≡ f' › → ‹ g ≡ g' › → ‹ f mulᴹ g ≡ f' mulᴹ g' ›
idᴱ mulᴹᴱ idᴱ = idᴱ

_+ᴼᴱ_ : 
    {l l' r r' : ‹ Ob ›} → {fl fl' : ‹ l ⇒ l' ›} → {fr fr' : ‹ r ⇒ r' ›} → 
    ‹ fl ≡ fl' › → ‹ fr ≡ fr' › → ‹ fl +ᴼᴹ fr ≡ fl' +ᴼᴹ fr' ›
idᴱ +ᴼᴱ idᴱ = idᴱ

_+ᴼidᴱ_ : (l r : ‹ Ob ›) → ‹ idᴹ +ᴼᴹ idᴹ ≡ idᴹ {l +ᴼ r} ›
0ᴼ +ᴼidᴱ r = idᴱ
(Sᴼ l) +ᴼidᴱ r = idᴱ

{- TODO
+ᴼmulᴱ : {l l' l'' r r' r'' : ‹ Ob ›} →
      (f : ‹ l ⇒ l' ›) → (f' : ‹ l' ⇒ l'' ›) →
      (g : ‹ r ⇒ r' ›) → (g' : ‹ r' ⇒ r'' ›) →
      ‹ (f mulᴹ f') +ᴼᴹ (g mulᴹ g') ≡ 
        (f +ᴼᴹ g) mulᴹ (f' +ᴼᴹ g') ›
+ᴼmulᴱ Nilᴹ Nilᴹ _ _ = idᴱ
-}

------------------------------------
-- semantic functions
------------------------------------
mutual

  -- type mapping
  [_] : «» → ‹›
  [ Ob ] = Ob
  [ x ⇒ y ] = ⟦ x ⟧ ⇒ ⟦ y ⟧
  [ f ≡ g ] = ⟦ f ⟧ ≡ ⟦ g ⟧

  -- main semantic mapping
  ⟦_⟧ : {t : «»} → « t » → ‹ [ t ] ›

  -- category structure
  ⟦ IdMor ⟧ = idᴹ
  ⟦ f MulMor g ⟧ = ⟦ f ⟧ mulᴹ ⟦ g ⟧
  ⟦ IdEqu ⟧ = idᴱ
  ⟦ e MulEqu e' ⟧ = ⟦ e ⟧ mulᴱ ⟦ e' ⟧
  ⟦ InvEqu e ⟧ = invᴱ ⟦ e ⟧
  ⟦ e MulMorEqu e' ⟧ = ⟦ e ⟧ mulᴹᴱ ⟦ e' ⟧

  -- monoidal category structure TODO
  ⟦ IdOb ⟧ = 0ᴼ
  ⟦ a MulOb b ⟧ = ⟦ a ⟧ +ᴼ ⟦ b ⟧
  ⟦ f MulObMor g ⟧ = ⟦ f ⟧ +ᴼᴹ ⟦ g ⟧
  ⟦ e MulObEqu e' ⟧ = ⟦ e ⟧ +ᴼᴱ ⟦ e' ⟧
  ⟦ l MulObIdEqu r ⟧ = ⟦ l ⟧ +ᴼidᴱ ⟦ r ⟧
--  ⟦ MulObMulEqu f f' g g' ⟧ = +ᴼmulᴱ ⟦ f ⟧ ⟦ f' ⟧ ⟦ g ⟧ ⟦ g' ⟧
  ⟦ NeutrLeftDownMor ⟧ = idᴹ
  ⟦ NeutrLeftUpMor ⟧ = idᴹ
  ⟦ NeutrRightDownMor ⟧ = neutrDᴹ
  ⟦ NeutrRightUpMor ⟧ = neutrUᴹ
  ⟦ AssocLRMor {x} {y} {z} ⟧ = assocLRᴹ {⟦ x ⟧} {⟦ y ⟧} {⟦ z ⟧}
  ⟦ AssocRLMor {x} {y} {z} ⟧ = assocRLᴹ {⟦ x ⟧} {⟦ y ⟧} {⟦ z ⟧}

  -- monoid object structure
  ⟦ ElOb ⟧ = 1ᴼ
  ⟦ IdEl ⟧ = Zᴹ Nilᴹ -- list [0]
  ⟦ MulEl ⟧ = Sᴹ (Sᴹ (Zᴹ Nilᴹ)) -- list [2]
  ⟦ NeutralityLeftEqu ⟧ = idᴱ
  ⟦ NeutralityRightEqu ⟧ = idᴱ
  ⟦ AssociativityEqu ⟧ = idᴱ

{-
  ⟦ NeutrLeftEqu {_} {_} {_} ⟧
  ⟦ NeutrRightEqu {_} {_} {_} ⟧
  ⟦ AssocEqu {_} {_} {_} {_} {_} {_} {_} ⟧

  ⟦ NeutrLeftDownUpIsoEqu {_} ⟧
  ⟦ NeutrLeftUpDownIsoEqu {_} ⟧
  ⟦ NeutrLeftDownMorNatEqu {_} {_} _ ⟧
  ⟦ NeutrLeftUpMorNatEqu {_} {_} _ ⟧
  ⟦ NeutrRightDownUpIsoEqu {_} ⟧
  ⟦ NeutrRightUpDownIsoEqu {_} ⟧
  ⟦ NeutrRightDownMorNatEqu {_} {_} _ ⟧
  ⟦ NeutrRightUpMorNatEqu {_} {_} _ ⟧
  ⟦ AssocLeftIsoEqu {_} {_} {_} ⟧
  ⟦ AssocRightIsoEqu {_} {_} {_} ⟧
  ⟦ AssocLRMorNatEqu {_} {_} {_} {_} {_} {_} _ _ _ ⟧
  ⟦ AssocRLMorNatEqu {_} {_} {_} {_} {_} {_} _ _ _ ⟧
-}
