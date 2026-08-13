{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The change of base along a structured functor commutes with the μ-carriers.
-- The change of base keeps index setoids, and sorts and trees are built from
-- index setoids alone, so the two μ-carriers share their trees up to a
-- transport that is the identity at the leaves. The fibre comparison is by
-- recursion on trees: constants and parameters are untouched, products cross
-- the base functor's product comparison, and each root crosses its lifting
-- comparison, whose naturality at the lifted action carries the transports.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ) renaming (suc to sucℕ)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import prop using () renaming (_,_ to _,ₚ_)
open import categories using (Category; HasProducts)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import lifting using (Lifting)
open import functor using (Functor)
open import finite-product-functor
  using (preserve-chosen-products; module preserve-chosen-products-consequences)
open import prop-setoid using (Setoid; IsEquivalence; mk-≃m)
open import indexed-family using (Fam)
import fam
import fam-functor
import polynomial-functor
import fam-mu-lifting.sort
import fam-mu-lifting.fibre

module fam-mu-lifting.fibrewise {o m e o₂ m₂ e₂} (os es : Level)
    {𝒞 : Category o m e} (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    {𝟙c : Category.obj 𝒞} (Lft : Lifting CM 𝟙c)
    {𝒟 : Category o₂ m₂ e₂} (CM' : CMonEnriched 𝒟) (BP' : ∀ x y → Biproduct CM' x y)
    {𝟙d : Category.obj 𝒟} (Lft' : Lifting CM' 𝟙d)
    (F : Functor 𝒞 𝒟)
    (F-prod : preserve-chosen-products F (biproducts→products CM BP) (biproducts→products CM' BP'))
    (F-L : ∀ X → Category.Iso 𝒟 (Functor.fobj F (Lifting.L Lft X)) (Lifting.L Lft' (Functor.fobj F X)))
    (F-L-natural : ∀ {X Y} (f : Category._⇒_ 𝒞 X Y) →
       Category._≈_ 𝒟
         (Category._∘_ 𝒟 (Category.Iso.fwd (F-L Y)) (Functor.fmor F (Lifting.Lmap Lft f)))
         (Category._∘_ 𝒟 (Lifting.Lmap Lft' (Functor.fmor F f)) (Category.Iso.fwd (F-L X))))
    where

private
  module F𝒞 = fam.CategoryOfFamilies os (os ⊔ es) 𝒞
  module F𝒟 = fam.CategoryOfFamilies os (os ⊔ es) 𝒟
  module Sh = fam-mu-lifting.sort os es
  module Fc = fam-mu-lifting.fibre os es CM BP Lft
  module Fd = fam-mu-lifting.fibre os es CM' BP' Lft'
  module 𝒟C = Category 𝒟
  module 𝒟Pm = HasProducts (biproducts→products CM' BP')
  module DL = Lifting Lft'

open Sh using (Sort; mkSort)
open polynomial-functor using (Poly; Poly-map; extend)
open prop-setoid._⇒_
open Functor
open F𝒞.Obj
open F𝒟.Obj
open F𝒟.Mor
open F𝒟._≃_
open indexed-family._⇒f_
open indexed-family._≃f_
open 𝒟C
open Iso

FamF : Functor F𝒞.cat F𝒟.cat
FamF = fam-functor.FamF os (os ⊔ es) F

private
  -- Lifting an isomorphism through the target lifting.
  L-iso : ∀ {a b} → 𝒟C.Iso a b → 𝒟C.Iso (DL.L a) (DL.L b)
  L-iso i .fwd = DL.Lmap (i .fwd)
  L-iso i .bwd = DL.Lmap (i .bwd)
  L-iso i .fwd∘bwd≈id =
    ≈-trans (≈-sym (DL.Lmap-comp _ _)) (≈-trans (DL.Lmap-cong (i .fwd∘bwd≈id)) DL.Lmap-id)
  L-iso i .bwd∘fwd≈id =
    ≈-trans (≈-sym (DL.Lmap-comp _ _)) (≈-trans (DL.Lmap-cong (i .bwd∘fwd≈id)) DL.Lmap-id)

  -- Conjugating a commuting square by isomorphisms on both sides.
  iso-flip : ∀ {a b c d} (i : 𝒟C.Iso a b) (j : 𝒟C.Iso c d)
             {f : a ⇒ c} {g : b ⇒ d} →
             (j .fwd ∘ f) ≈ (g ∘ i .fwd) →
             (f ∘ i .bwd) ≈ (j .bwd ∘ g)
  iso-flip i j {f} {g} sq =
    ≈-trans (≈-sym id-left)
      (≈-trans (∘-cong (≈-sym (j .bwd∘fwd≈id)) ≈-refl)
        (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl (≈-sym (assoc _ _ _)))
            (≈-trans (∘-cong ≈-refl (∘-cong sq ≈-refl))
              (≈-trans (∘-cong ≈-refl (assoc _ _ _))
                (≈-trans (∘-cong ≈-refl
                    (∘-cong ≈-refl (i .fwd∘bwd≈id)))
                  (∘-cong ≈-refl id-right)))))))

  -- One naturality step across a root: the transport under the source lifting is carried through
  -- the lifting comparison, given the inner square under the target lifting.
  root-step : ∀ {a a' b b'} (i' : 𝒟C.Iso (F .fobj a') b') (i : 𝒟C.Iso (F .fobj a) b)
              {s : Category._⇒_ 𝒞 a a'} {t : b ⇒ b'} →
              ((i' .fwd ∘ F .fmor s) ≈ (t ∘ i .fwd)) →
              (((DL.Lmap (i' .fwd) ∘ F-L a' .fwd) ∘ F .fmor (Lifting.Lmap Lft s))
                ≈ (DL.Lmap t ∘ (DL.Lmap (i .fwd) ∘ F-L a .fwd)))
  root-step {a} {a'} i' i {s} {t} inner =
    ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (F-L-natural s))
        (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong
              (≈-trans (≈-sym (DL.Lmap-comp _ _))
                (≈-trans (DL.Lmap-cong inner) (DL.Lmap-comp _ _)))
              ≈-refl)
            (assoc _ _ _))))

ℓk : Level
ℓk = o ⊔ m ⊔ e ⊔ o₂ ⊔ m₂ ⊔ e₂ ⊔ lsuc os ⊔ lsuc es

module Fibrewise {N : ℕ} (δ : Fin N → F𝒞.Obj) where
  module T = Sh.Tree (λ i → δ i .idx)
  module C = Fc.Fibre δ
  module D = Fd.Fibre (λ i → FamF .fobj (δ i))

  P̂ : ∀ {j} → Fc.Poly-C j → Fd.Poly-C j
  P̂ = Poly-map FamF

  -- Relate references and decorated sorts of the two erasures: environment
  -- positions coincide, and sorts relate recursively through the μ-body from
  -- which both are formed.
  mutual
    data SRel : (r₁ r₂ : Fin N ⊎ Sort N) → C.DecoAssign r₁ → D.DecoAssign r₂ → Set ℓk where
      env : ∀ {p} → SRel (inj₁ p) (inj₁ p) (lift tt) (lift tt)
      srt : ∀ {s₁ s₂ e₁ e₂} → SortRel s₁ s₂ e₁ e₂ → SRel (inj₂ s₁) (inj₂ s₂) e₁ e₂

    data SortRel : (s₁ s₂ : Sort N) → C.Deco s₁ → D.Deco s₂ → Set ℓk where
      mk : ∀ {j} (Q : Fc.Poly-C (sucℕ j))
           (ρ₁ ρ₂ : Fin j → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → D.DecoAssign (ρ₂ i)) →
           (∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           SortRel (mkSort Fc.∣ Q ∣ ρ₁) (mkSort Fd.∣ P̂ Q ∣ ρ₂)
                   (C.mkDeco Q d₁) (D.mkDeco (P̂ Q) d₂)

  -- Forward tree transport, by recursion on the polynomial; the leaves are
  -- identities.
  mutual
    cfwd : ∀ {j} (Q : Fc.Poly-C (sucℕ j))
           (ρ₁ ρ₂ : Fin j → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → D.DecoAssign (ρ₂ i))
           (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           T.W Fc.∣ Q ∣ ρ₁ → T.W Fd.∣ P̂ Q ∣ ρ₂
    cfwd Q ρ₁ ρ₂ d₁ d₂ rel (T.sup x) =
      T.sup (shape-cfwd Q (extend ρ₁ (inj₂ (mkSort Fc.∣ Q ∣ ρ₁)))
               (extend ρ₂ (inj₂ (mkSort Fd.∣ P̂ Q ∣ ρ₂)))
               (C.deco-ext Q d₁) (D.deco-ext (P̂ Q) d₂)
               (extend-rel Q ρ₁ ρ₂ d₁ d₂ rel) x)

    extend-rel : ∀ {j} (Q : Fc.Poly-C (sucℕ j))
                 (ρ₁ ρ₂ : Fin j → Fin N ⊎ Sort N)
                 (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → D.DecoAssign (ρ₂ i))
                 (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
                 ∀ i → SRel (extend ρ₁ (inj₂ (mkSort Fc.∣ Q ∣ ρ₁)) i)
                            (extend ρ₂ (inj₂ (mkSort Fd.∣ P̂ Q ∣ ρ₂)) i)
                            (C.deco-ext Q d₁ i)
                            (D.deco-ext (P̂ Q) d₂ i)
    extend-rel Q ρ₁ ρ₂ d₁ d₂ rel Fin.zero    = srt (mk Q ρ₁ ρ₂ d₁ d₂ rel)
    extend-rel Q ρ₁ ρ₂ d₁ d₂ rel (Fin.suc i) = rel i

    shape-cfwd : ∀ {j} (Q : Fc.Poly-C j)
                 (η₁ η₂ : Fin j → Fin N ⊎ Sort N)
                 (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → D.DecoAssign (η₂ i))
                 (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                 T.⟦ Fc.∣ Q ∣ ⟧shape η₁ → T.⟦ Fd.∣ P̂ Q ∣ ⟧shape η₂
    shape-cfwd (Poly.const A) η₁ η₂ d₁ d₂ rel x = x
    shape-cfwd (Poly.var i)   η₁ η₂ d₁ d₂ rel x = el-cfwd (rel i) x
    shape-cfwd (Q Poly.+ R) η₁ η₂ d₁ d₂ rel (inj₁ x) = inj₁ (shape-cfwd Q η₁ η₂ d₁ d₂ rel x)
    shape-cfwd (Q Poly.+ R) η₁ η₂ d₁ d₂ rel (inj₂ y) = inj₂ (shape-cfwd R η₁ η₂ d₁ d₂ rel y)
    shape-cfwd (Q Poly.× R) η₁ η₂ d₁ d₂ rel (x , y) =
      shape-cfwd Q η₁ η₂ d₁ d₂ rel x , shape-cfwd R η₁ η₂ d₁ d₂ rel y
    shape-cfwd (Poly.μ Q')  η₁ η₂ d₁ d₂ rel t = cfwd Q' η₁ η₂ d₁ d₂ rel t

    el-cfwd : ∀ {r₁ r₂ e₁ e₂} → SRel r₁ r₂ e₁ e₂ → T.El r₁ → T.El r₂
    el-cfwd env x = x
    el-cfwd (srt (mk Q ρ₁ ρ₂ d₁ d₂ rel)) x = cfwd Q ρ₁ ρ₂ d₁ d₂ rel x

  -- The forward transport preserves bisimilarity.
  mutual
    c≈fwd : ∀ {j} (Q : Fc.Poly-C (sucℕ j))
            (ρ₁ ρ₂ : Fin j → Fin N ⊎ Sort N)
            (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → D.DecoAssign (ρ₂ i))
            (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
            {x y : T.W Fc.∣ Q ∣ ρ₁} → T.W-≈ x y →
            T.W-≈ (cfwd Q ρ₁ ρ₂ d₁ d₂ rel x) (cfwd Q ρ₁ ρ₂ d₁ d₂ rel y)
    c≈fwd Q ρ₁ ρ₂ d₁ d₂ rel {T.sup x} {T.sup y} p =
      shape≈-cfwd Q (extend ρ₁ (inj₂ (mkSort Fc.∣ Q ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fd.∣ P̂ Q ∣ ρ₂)))
        (C.deco-ext Q d₁) (D.deco-ext (P̂ Q) d₂)
        (extend-rel Q ρ₁ ρ₂ d₁ d₂ rel) p

    shape≈-cfwd : ∀ {j} (Q : Fc.Poly-C j)
                  (η₁ η₂ : Fin j → Fin N ⊎ Sort N)
                  (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → D.DecoAssign (η₂ i))
                  (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                  {x y : T.⟦ Fc.∣ Q ∣ ⟧shape η₁} → T.shape≈ Fc.∣ Q ∣ η₁ x y →
                  T.shape≈ Fd.∣ P̂ Q ∣ η₂ (shape-cfwd Q η₁ η₂ d₁ d₂ rel x) (shape-cfwd Q η₁ η₂ d₁ d₂ rel y)
    shape≈-cfwd (Poly.const A) η₁ η₂ d₁ d₂ rel p = p
    shape≈-cfwd (Poly.var i)   η₁ η₂ d₁ d₂ rel p = elEq-cfwd (rel i) p
    shape≈-cfwd (Q Poly.+ R) η₁ η₂ d₁ d₂ rel {inj₁ _} {inj₁ _} p = shape≈-cfwd Q η₁ η₂ d₁ d₂ rel p
    shape≈-cfwd (Q Poly.+ R) η₁ η₂ d₁ d₂ rel {inj₂ _} {inj₂ _} p = shape≈-cfwd R η₁ η₂ d₁ d₂ rel p
    shape≈-cfwd (Q Poly.× R) η₁ η₂ d₁ d₂ rel {_ , _} {_ , _} (p ,ₚ q) =
      shape≈-cfwd Q η₁ η₂ d₁ d₂ rel p ,ₚ shape≈-cfwd R η₁ η₂ d₁ d₂ rel q
    shape≈-cfwd (Poly.μ Q')  η₁ η₂ d₁ d₂ rel {x} {y} p = c≈fwd Q' η₁ η₂ d₁ d₂ rel {x} {y} p

    elEq-cfwd : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x y : T.El r₁} →
                T.elEq r₁ x y → T.elEq r₂ (el-cfwd r x) (el-cfwd r y)
    elEq-cfwd env p = p
    elEq-cfwd (srt (mk Q ρ₁ ρ₂ d₁ d₂ rel)) {x} {y} p = c≈fwd Q ρ₁ ρ₂ d₁ d₂ rel {x} {y} p

  -- Backward tree transport.
  mutual
    cbwd : ∀ {j} (Q : Fc.Poly-C (sucℕ j))
           (ρ₁ ρ₂ : Fin j → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → D.DecoAssign (ρ₂ i))
           (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           T.W Fd.∣ P̂ Q ∣ ρ₂ → T.W Fc.∣ Q ∣ ρ₁
    cbwd Q ρ₁ ρ₂ d₁ d₂ rel (T.sup x) =
      T.sup (shape-cbwd Q (extend ρ₁ (inj₂ (mkSort Fc.∣ Q ∣ ρ₁)))
               (extend ρ₂ (inj₂ (mkSort Fd.∣ P̂ Q ∣ ρ₂)))
               (C.deco-ext Q d₁) (D.deco-ext (P̂ Q) d₂)
               (extend-rel Q ρ₁ ρ₂ d₁ d₂ rel) x)

    shape-cbwd : ∀ {j} (Q : Fc.Poly-C j)
                 (η₁ η₂ : Fin j → Fin N ⊎ Sort N)
                 (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → D.DecoAssign (η₂ i))
                 (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                 T.⟦ Fd.∣ P̂ Q ∣ ⟧shape η₂ → T.⟦ Fc.∣ Q ∣ ⟧shape η₁
    shape-cbwd (Poly.const A) η₁ η₂ d₁ d₂ rel x = x
    shape-cbwd (Poly.var i)   η₁ η₂ d₁ d₂ rel x = el-cbwd (rel i) x
    shape-cbwd (Q Poly.+ R) η₁ η₂ d₁ d₂ rel (inj₁ x) = inj₁ (shape-cbwd Q η₁ η₂ d₁ d₂ rel x)
    shape-cbwd (Q Poly.+ R) η₁ η₂ d₁ d₂ rel (inj₂ y) = inj₂ (shape-cbwd R η₁ η₂ d₁ d₂ rel y)
    shape-cbwd (Q Poly.× R) η₁ η₂ d₁ d₂ rel (x , y) =
      shape-cbwd Q η₁ η₂ d₁ d₂ rel x , shape-cbwd R η₁ η₂ d₁ d₂ rel y
    shape-cbwd (Poly.μ Q')  η₁ η₂ d₁ d₂ rel t = cbwd Q' η₁ η₂ d₁ d₂ rel t

    el-cbwd : ∀ {r₁ r₂ e₁ e₂} → SRel r₁ r₂ e₁ e₂ → T.El r₂ → T.El r₁
    el-cbwd env x = x
    el-cbwd (srt (mk Q ρ₁ ρ₂ d₁ d₂ rel)) x = cbwd Q ρ₁ ρ₂ d₁ d₂ rel x

  -- The backward transport preserves bisimilarity.
  mutual
    c≈bwd : ∀ {j} (Q : Fc.Poly-C (sucℕ j))
            (ρ₁ ρ₂ : Fin j → Fin N ⊎ Sort N)
            (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → D.DecoAssign (ρ₂ i))
            (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
            {x y : T.W Fd.∣ P̂ Q ∣ ρ₂} → T.W-≈ x y →
            T.W-≈ (cbwd Q ρ₁ ρ₂ d₁ d₂ rel x) (cbwd Q ρ₁ ρ₂ d₁ d₂ rel y)
    c≈bwd Q ρ₁ ρ₂ d₁ d₂ rel {T.sup x} {T.sup y} p =
      shape≈-cbwd Q (extend ρ₁ (inj₂ (mkSort Fc.∣ Q ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fd.∣ P̂ Q ∣ ρ₂)))
        (C.deco-ext Q d₁) (D.deco-ext (P̂ Q) d₂)
        (extend-rel Q ρ₁ ρ₂ d₁ d₂ rel) p

    shape≈-cbwd : ∀ {j} (Q : Fc.Poly-C j)
                  (η₁ η₂ : Fin j → Fin N ⊎ Sort N)
                  (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → D.DecoAssign (η₂ i))
                  (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                  {x y : T.⟦ Fd.∣ P̂ Q ∣ ⟧shape η₂} → T.shape≈ Fd.∣ P̂ Q ∣ η₂ x y →
                  T.shape≈ Fc.∣ Q ∣ η₁ (shape-cbwd Q η₁ η₂ d₁ d₂ rel x) (shape-cbwd Q η₁ η₂ d₁ d₂ rel y)
    shape≈-cbwd (Poly.const A) η₁ η₂ d₁ d₂ rel p = p
    shape≈-cbwd (Poly.var i)   η₁ η₂ d₁ d₂ rel p = elEq-cbwd (rel i) p
    shape≈-cbwd (Q Poly.+ R) η₁ η₂ d₁ d₂ rel {inj₁ _} {inj₁ _} p = shape≈-cbwd Q η₁ η₂ d₁ d₂ rel p
    shape≈-cbwd (Q Poly.+ R) η₁ η₂ d₁ d₂ rel {inj₂ _} {inj₂ _} p = shape≈-cbwd R η₁ η₂ d₁ d₂ rel p
    shape≈-cbwd (Q Poly.× R) η₁ η₂ d₁ d₂ rel {_ , _} {_ , _} (p ,ₚ q) =
      shape≈-cbwd Q η₁ η₂ d₁ d₂ rel p ,ₚ shape≈-cbwd R η₁ η₂ d₁ d₂ rel q
    shape≈-cbwd (Poly.μ Q')  η₁ η₂ d₁ d₂ rel {x} {y} p = c≈bwd Q' η₁ η₂ d₁ d₂ rel {x} {y} p

    elEq-cbwd : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x y : T.El r₂} →
                T.elEq r₂ x y → T.elEq r₁ (el-cbwd r x) (el-cbwd r y)
    elEq-cbwd env p = p
    elEq-cbwd (srt (mk Q ρ₁ ρ₂ d₁ d₂ rel)) {x} {y} p = c≈bwd Q ρ₁ ρ₂ d₁ d₂ rel {x} {y} p

  -- Round trips: the two transports are mutually inverse up to bisimilarity.
  mutual
    c-fb : ∀ {j} (Q : Fc.Poly-C (sucℕ j))
           (ρ₁ ρ₂ : Fin j → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → D.DecoAssign (ρ₂ i))
           (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           (x : T.W Fc.∣ Q ∣ ρ₁) →
           T.W-≈ (cbwd Q ρ₁ ρ₂ d₁ d₂ rel (cfwd Q ρ₁ ρ₂ d₁ d₂ rel x)) x
    c-fb Q ρ₁ ρ₂ d₁ d₂ rel (T.sup x) =
      shape-cfb Q (extend ρ₁ (inj₂ (mkSort Fc.∣ Q ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fd.∣ P̂ Q ∣ ρ₂)))
        (C.deco-ext Q d₁) (D.deco-ext (P̂ Q) d₂)
        (extend-rel Q ρ₁ ρ₂ d₁ d₂ rel) x

    shape-cfb : ∀ {j} (Q : Fc.Poly-C j)
                (η₁ η₂ : Fin j → Fin N ⊎ Sort N)
                (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → D.DecoAssign (η₂ i))
                (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                (x : T.⟦ Fc.∣ Q ∣ ⟧shape η₁) →
                T.shape≈ Fc.∣ Q ∣ η₁ (shape-cbwd Q η₁ η₂ d₁ d₂ rel (shape-cfwd Q η₁ η₂ d₁ d₂ rel x)) x
    shape-cfb (Poly.const A) η₁ η₂ d₁ d₂ rel x = IsEquivalence.refl (Setoid.isEquivalence (A .idx))
    shape-cfb (Poly.var i)   η₁ η₂ d₁ d₂ rel x = el-cfb (rel i) x
    shape-cfb (Q Poly.+ R) η₁ η₂ d₁ d₂ rel (inj₁ x) = shape-cfb Q η₁ η₂ d₁ d₂ rel x
    shape-cfb (Q Poly.+ R) η₁ η₂ d₁ d₂ rel (inj₂ y) = shape-cfb R η₁ η₂ d₁ d₂ rel y
    shape-cfb (Q Poly.× R) η₁ η₂ d₁ d₂ rel (x , y) =
      shape-cfb Q η₁ η₂ d₁ d₂ rel x ,ₚ shape-cfb R η₁ η₂ d₁ d₂ rel y
    shape-cfb (Poly.μ Q')  η₁ η₂ d₁ d₂ rel t = c-fb Q' η₁ η₂ d₁ d₂ rel t

    el-cfb : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (x : T.El r₁) →
             T.elEq r₁ (el-cbwd r (el-cfwd r x)) x
    el-cfb (env {p}) x = T.elEq-refl (inj₁ p) x
    el-cfb (srt (mk Q ρ₁ ρ₂ d₁ d₂ rel)) x = c-fb Q ρ₁ ρ₂ d₁ d₂ rel x

  mutual
    c-bf : ∀ {j} (Q : Fc.Poly-C (sucℕ j))
           (ρ₁ ρ₂ : Fin j → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → D.DecoAssign (ρ₂ i))
           (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           (y : T.W Fd.∣ P̂ Q ∣ ρ₂) →
           T.W-≈ (cfwd Q ρ₁ ρ₂ d₁ d₂ rel (cbwd Q ρ₁ ρ₂ d₁ d₂ rel y)) y
    c-bf Q ρ₁ ρ₂ d₁ d₂ rel (T.sup y) =
      shape-cbf Q (extend ρ₁ (inj₂ (mkSort Fc.∣ Q ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fd.∣ P̂ Q ∣ ρ₂)))
        (C.deco-ext Q d₁) (D.deco-ext (P̂ Q) d₂)
        (extend-rel Q ρ₁ ρ₂ d₁ d₂ rel) y

    shape-cbf : ∀ {j} (Q : Fc.Poly-C j)
                (η₁ η₂ : Fin j → Fin N ⊎ Sort N)
                (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → D.DecoAssign (η₂ i))
                (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                (y : T.⟦ Fd.∣ P̂ Q ∣ ⟧shape η₂) →
                T.shape≈ Fd.∣ P̂ Q ∣ η₂ (shape-cfwd Q η₁ η₂ d₁ d₂ rel (shape-cbwd Q η₁ η₂ d₁ d₂ rel y)) y
    shape-cbf (Poly.const A) η₁ η₂ d₁ d₂ rel y = IsEquivalence.refl (Setoid.isEquivalence (A .idx))
    shape-cbf (Poly.var i)   η₁ η₂ d₁ d₂ rel y = el-cbf (rel i) y
    shape-cbf (Q Poly.+ R) η₁ η₂ d₁ d₂ rel (inj₁ y) = shape-cbf Q η₁ η₂ d₁ d₂ rel y
    shape-cbf (Q Poly.+ R) η₁ η₂ d₁ d₂ rel (inj₂ y) = shape-cbf R η₁ η₂ d₁ d₂ rel y
    shape-cbf (Q Poly.× R) η₁ η₂ d₁ d₂ rel (x , y) =
      shape-cbf Q η₁ η₂ d₁ d₂ rel x ,ₚ shape-cbf R η₁ η₂ d₁ d₂ rel y
    shape-cbf (Poly.μ Q')  η₁ η₂ d₁ d₂ rel t = c-bf Q' η₁ η₂ d₁ d₂ rel t

    el-cbf : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (y : T.El r₂) →
             T.elEq r₂ (el-cfwd r (el-cbwd r y)) y
    el-cbf (env {p}) y = T.elEq-refl (inj₁ p) y
    el-cbf (srt (mk Q ρ₁ ρ₂ d₁ d₂ rel)) y = c-bf Q ρ₁ ρ₂ d₁ d₂ rel y

  -- The fibre isomorphisms: the base functor's image of a fibre against the
  -- target-side fibre at the transported tree. Constants and parameters are
  -- identities, products cross the product comparison, and each root crosses
  -- the lifting comparison.
  mutual
    fib-ciso : ∀ {j} (Q : Fc.Poly-C (sucℕ j))
               (ρ₁ ρ₂ : Fin j → Fin N ⊎ Sort N)
               (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → D.DecoAssign (ρ₂ i))
               (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i))
               (w : T.W Fc.∣ Q ∣ ρ₁) →
               𝒟C.Iso (F .fobj (C.fib Q d₁ w)) (D.fib (P̂ Q) d₂ (cfwd Q ρ₁ ρ₂ d₁ d₂ rel w))
    fib-ciso Q ρ₁ ρ₂ d₁ d₂ rel (T.sup x) =
      fib-shape-ciso Q (extend ρ₁ (inj₂ (mkSort Fc.∣ Q ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fd.∣ P̂ Q ∣ ρ₂)))
        (C.deco-ext Q d₁) (D.deco-ext (P̂ Q) d₂)
        (extend-rel Q ρ₁ ρ₂ d₁ d₂ rel) x

    fib-shape-ciso : ∀ {j} (Q : Fc.Poly-C j)
                     (η₁ η₂ : Fin j → Fin N ⊎ Sort N)
                     (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → D.DecoAssign (η₂ i))
                     (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i))
                     (x : T.⟦ Fc.∣ Q ∣ ⟧shape η₁) →
                     𝒟C.Iso (F .fobj (C.fib-shape Q d₁ x))
                            (D.fib-shape (P̂ Q) d₂ (shape-cfwd Q η₁ η₂ d₁ d₂ rel x))
    fib-shape-ciso (Poly.const A) η₁ η₂ d₁ d₂ rel x = Iso-refl
    fib-shape-ciso (Poly.var i)   η₁ η₂ d₁ d₂ rel x = fib-el-ciso (rel i) x
    fib-shape-ciso (Q Poly.+ R) η₁ η₂ d₁ d₂ rel (inj₁ x) =
      Iso-trans (F-L _) (L-iso (fib-shape-ciso Q η₁ η₂ d₁ d₂ rel x))
    fib-shape-ciso (Q Poly.+ R) η₁ η₂ d₁ d₂ rel (inj₂ y) =
      Iso-trans (F-L _) (L-iso (fib-shape-ciso R η₁ η₂ d₁ d₂ rel y))
    fib-shape-ciso (Q Poly.× R) η₁ η₂ d₁ d₂ rel (x , y) =
      Iso-trans (F-L _)
        (L-iso (Iso-trans (IsIso→Iso F-prod)
                 (𝒟Pm.product-preserves-iso
                   (fib-shape-ciso Q η₁ η₂ d₁ d₂ rel x)
                   (fib-shape-ciso R η₁ η₂ d₁ d₂ rel y))))
    fib-shape-ciso (Poly.μ Q')  η₁ η₂ d₁ d₂ rel t = fib-ciso Q' η₁ η₂ d₁ d₂ rel t

    fib-el-ciso : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (x : T.El r₁) →
                  𝒟C.Iso (F .fobj (C.fib-el r₁ e₁ x)) (D.fib-el r₂ e₂ (el-cfwd r x))
    fib-el-ciso (env {p}) x = Iso-refl
    fib-el-ciso (srt (mk Q ρ₁ ρ₂ d₁ d₂ rel)) x = fib-ciso Q ρ₁ ρ₂ d₁ d₂ rel x

  open preserve-chosen-products-consequences F (biproducts→products CM BP) (biproducts→products CM' BP') F-prod
    using (mul⁻¹-natural)

  -- The fibre isomorphisms commute with transport along bisimilarity.
  mutual
    fib-cnat : ∀ {j} (Q : Fc.Poly-C (sucℕ j))
               (ρ₁ ρ₂ : Fin j → Fin N ⊎ Sort N)
               (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → D.DecoAssign (ρ₂ i))
               (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i))
               {w w' : T.W Fc.∣ Q ∣ ρ₁} (p : T.W-≈ w w') →
               ((fib-ciso Q ρ₁ ρ₂ d₁ d₂ rel w' .fwd)
                 ∘ F .fmor (C.fib-subst Q d₁ {x = w} {y = w'} p))
               ≈ ((D.fib-subst (P̂ Q) d₂
                        {x = cfwd Q ρ₁ ρ₂ d₁ d₂ rel w} {y = cfwd Q ρ₁ ρ₂ d₁ d₂ rel w'}
                        (c≈fwd Q ρ₁ ρ₂ d₁ d₂ rel {w} {w'} p))
                     ∘ (fib-ciso Q ρ₁ ρ₂ d₁ d₂ rel w .fwd))
    fib-cnat Q ρ₁ ρ₂ d₁ d₂ rel {T.sup x} {T.sup x'} p =
      fib-shape-cnat Q (extend ρ₁ (inj₂ (mkSort Fc.∣ Q ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fd.∣ P̂ Q ∣ ρ₂)))
        (C.deco-ext Q d₁) (D.deco-ext (P̂ Q) d₂)
        (extend-rel Q ρ₁ ρ₂ d₁ d₂ rel) {x} {x'} p

    fib-shape-cnat : ∀ {j} (Q : Fc.Poly-C j)
                     (η₁ η₂ : Fin j → Fin N ⊎ Sort N)
                     (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → D.DecoAssign (η₂ i))
                     (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i))
                     {x x' : T.⟦ Fc.∣ Q ∣ ⟧shape η₁} (p : T.shape≈ Fc.∣ Q ∣ η₁ x x') →
                     ((fib-shape-ciso Q η₁ η₂ d₁ d₂ rel x' .fwd)
                       ∘ F .fmor (C.fib-shape-subst Q d₁ p))
                     ≈ ((D.fib-shape-subst (P̂ Q) d₂ (shape≈-cfwd Q η₁ η₂ d₁ d₂ rel {x} {x'} p))
                           ∘ (fib-shape-ciso Q η₁ η₂ d₁ d₂ rel x .fwd))
    fib-shape-cnat (Poly.const A) η₁ η₂ d₁ d₂ rel p = ≈-trans id-left (≈-sym id-right)
    fib-shape-cnat (Poly.var i)   η₁ η₂ d₁ d₂ rel p = fib-el-cnat (rel i) p
    fib-shape-cnat (Q Poly.+ R) η₁ η₂ d₁ d₂ rel {inj₁ x} {inj₁ x'} p =
      root-step (fib-shape-ciso Q η₁ η₂ d₁ d₂ rel x') (fib-shape-ciso Q η₁ η₂ d₁ d₂ rel x)
        (fib-shape-cnat Q η₁ η₂ d₁ d₂ rel p)
    fib-shape-cnat (Q Poly.+ R) η₁ η₂ d₁ d₂ rel {inj₂ y} {inj₂ y'} p =
      root-step (fib-shape-ciso R η₁ η₂ d₁ d₂ rel y') (fib-shape-ciso R η₁ η₂ d₁ d₂ rel y)
        (fib-shape-cnat R η₁ η₂ d₁ d₂ rel p)
    fib-shape-cnat (Q Poly.× R) η₁ η₂ d₁ d₂ rel {x₁ , x₂} {x₁' , x₂'} (p₁ ,ₚ p₂) =
      root-step pI' pI
        (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl (mul⁻¹-natural {f = s₁} {g = s₂}))
            (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong
                  (≈-trans (≈-sym (𝒟Pm.prod-m-comp _ _ _ _))
                    (≈-trans
                      (𝒟Pm.prod-m-cong
                        (fib-shape-cnat Q η₁ η₂ d₁ d₂ rel {x₁} {x₁'} p₁)
                        (fib-shape-cnat R η₁ η₂ d₁ d₂ rel {x₂} {x₂'} p₂))
                      (𝒟Pm.prod-m-comp _ _ _ _)))
                  ≈-refl)
                (assoc _ _ _)))))
      where
        s₁ = C.fib-shape-subst Q d₁ p₁
        s₂ = C.fib-shape-subst R d₁ p₂

        pI : 𝒟C.Iso _ _
        pI = Iso-trans (IsIso→Iso F-prod)
               (𝒟Pm.product-preserves-iso
                 (fib-shape-ciso Q η₁ η₂ d₁ d₂ rel x₁)
                 (fib-shape-ciso R η₁ η₂ d₁ d₂ rel x₂))

        pI' : 𝒟C.Iso _ _
        pI' = Iso-trans (IsIso→Iso F-prod)
                (𝒟Pm.product-preserves-iso
                  (fib-shape-ciso Q η₁ η₂ d₁ d₂ rel x₁')
                  (fib-shape-ciso R η₁ η₂ d₁ d₂ rel x₂'))
    fib-shape-cnat (Poly.μ Q')  η₁ η₂ d₁ d₂ rel {t} {t'} p = fib-cnat Q' η₁ η₂ d₁ d₂ rel {t} {t'} p

    fib-el-cnat : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x x' : T.El r₁} (p : T.elEq r₁ x x') →
                  ((fib-el-ciso r x' .fwd)
                    ∘ F .fmor (C.fib-el-subst r₁ e₁ p))
                  ≈ ((D.fib-el-subst r₂ e₂ (elEq-cfwd r {x} {x'} p))
                        ∘ (fib-el-ciso r x .fwd))
    fib-el-cnat (env {p}) q = ≈-trans id-left (≈-sym id-right)
    fib-el-cnat (srt (mk Q ρ₁ ρ₂ d₁ d₂ rel)) {x} {x'} q = fib-cnat Q ρ₁ ρ₂ d₁ d₂ rel {x} {x'} q

-- The assembled comparison: the change of base commutes with the μ-carriers, as
-- an isomorphism of Fam(𝒟)-objects over shared trees.
module FibrewiseMu {n : ℕ} (P : Fc.Poly-C (sucℕ n)) (δ : Fin n → F𝒞.Obj) where
  open Fibrewise δ
  open Fam

  private
    ρ₀ : Fin n → Fin n ⊎ Sort n
    ρ₀ i = inj₁ i

    d₁₀ : ∀ i → C.DecoAssign (ρ₀ i)
    d₁₀ i = lift tt

    d₂₀ : ∀ i → D.DecoAssign (ρ₀ i)
    d₂₀ i = lift tt

    rel₀ : ∀ i → SRel (ρ₀ i) (ρ₀ i) (d₁₀ i) (d₂₀ i)
    rel₀ i = env

    Fw = cfwd P ρ₀ ρ₀ d₁₀ d₂₀ rel₀
    Bw = cbwd P ρ₀ ρ₀ d₁₀ d₂₀ rel₀
    ci = fib-ciso P ρ₀ ρ₀ d₁₀ d₂₀ rel₀

  fwd-mor : F𝒟.Mor (FamF .fobj (Fc.μObj P δ)) (Fd.μObj (P̂ P) (λ i → FamF .fobj (δ i)))
  fwd-mor .idxf .func = Fw
  fwd-mor .idxf .func-resp-≈ {w} {w'} = c≈fwd P ρ₀ ρ₀ d₁₀ d₂₀ rel₀ {w} {w'}
  fwd-mor .famf .transf w = ci w .fwd
  fwd-mor .famf .natural {w} {w'} q = fib-cnat P ρ₀ ρ₀ d₁₀ d₂₀ rel₀ {w} {w'} q

  bwd-mor : F𝒟.Mor (Fd.μObj (P̂ P) (λ i → FamF .fobj (δ i))) (FamF .fobj (Fc.μObj P δ))
  bwd-mor .idxf .func = Bw
  bwd-mor .idxf .func-resp-≈ {s} {s'} = c≈bwd P ρ₀ ρ₀ d₁₀ d₂₀ rel₀ {s} {s'}
  bwd-mor .famf .transf s =
    ci (Bw s) .bwd ∘
    D.fib-subst (P̂ P) d₂₀ {x = s} {y = Fw (Bw s)}
      (T.W-≈-sym {x = Fw (Bw s)} {y = s} (c-bf P ρ₀ ρ₀ d₁₀ d₂₀ rel₀ s))
  bwd-mor .famf .natural {s₁} {s₂} q =
    ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong₂ (≈-sym (D.fib-trans* (P̂ P) d₂₀
                                           {x = s₁} {y = s₂} {z = Fw (Bw s₂)} _ q)))
        (≈-sym
          (≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong₁ (iso-flip (ci (Bw s₁)) (ci (Bw s₂))
                (fib-cnat P ρ₀ ρ₀ d₁₀ d₂₀ rel₀ {Bw s₁} {Bw s₂}
                  (c≈bwd P ρ₀ ρ₀ d₁₀ d₂₀ rel₀ {s₁} {s₂} q))))
              (≈-trans (assoc _ _ _)
                (∘-cong₂ (≈-sym (D.fib-trans* (P̂ P) d₂₀
                                          {x = s₁} {y = Fw (Bw s₁)} {z = Fw (Bw s₂)} _ _))))))))

  fb-≃ : Category._≈_ F𝒟.cat
           (Category._∘_ F𝒟.cat fwd-mor bwd-mor) (Category.id F𝒟.cat _)
  fb-≃ .idxf-eq =
    mk-≃m (λ s → c-bf P ρ₀ ρ₀ d₁₀ d₂₀ rel₀ s)
  fb-≃ .famf-eq .transf-eq {s} =
    ≈-trans (∘-cong₂ id-left)
      (≈-trans (∘-cong₂ (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong₁ (ci (Bw s) .fwd∘bwd≈id)) id-left)))
        (≈-trans (≈-sym (D.fib-trans* (P̂ P) d₂₀
                                  {x = s} {y = Fw (Bw s)} {z = s} _ _))
          (D.fib-refl* (P̂ P) d₂₀ s)))

  bf-≃ : Category._≈_ F𝒟.cat
           (Category._∘_ F𝒟.cat bwd-mor fwd-mor) (Category.id F𝒟.cat _)
  bf-≃ .idxf-eq =
    mk-≃m (λ w → c-fb P ρ₀ ρ₀ d₁₀ d₂₀ rel₀ w)
  bf-≃ .famf-eq .transf-eq {w} =
    ≈-trans (∘-cong₂ id-left)
      (≈-trans (∘-cong₂ (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong₂ (≈-sym
              (fib-cnat P ρ₀ ρ₀ d₁₀ d₂₀ rel₀ {w} {Bw (Fw w)}
                (T.W-≈-sym {x = Bw (Fw w)} {y = w} (c-fb P ρ₀ ρ₀ d₁₀ d₂₀ rel₀ w)))))
            (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (ci (Bw (Fw w)) .bwd∘fwd≈id)) id-left)))))
        (≈-trans (≈-sym ((FamF .fobj (Fc.μObj P δ)) .fam .trans*
                                  {x = w} {y = Bw (Fw w)} {z = w} _ _))
          ((FamF .fobj (Fc.μObj P δ)) .fam .refl* {x = w})))

  fibrewise-μ-iso : Category.Iso F𝒟.cat
                  (FamF .fobj (Fc.μObj P δ)) (Fd.μObj (P̂ P) (λ i → FamF .fobj (δ i)))
  fibrewise-μ-iso .Category.Iso.fwd = fwd-mor
  fibrewise-μ-iso .Category.Iso.bwd = bwd-mor
  fibrewise-μ-iso .Category.Iso.fwd∘bwd≈id = fb-≃
  fibrewise-μ-iso .Category.Iso.bwd∘fwd≈id = bf-≃
