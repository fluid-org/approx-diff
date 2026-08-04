{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Carrier of μ-types for the Fam construction: nested μ reduced to a single
-- sort-indexed W-type in setoids, with the fibre family computed by structural
-- recursion over trees. The sorts and trees are category-free, built from the
-- index setoids alone; the fibres recover the objects of the original
-- polynomial and environment through a decoration of the sorts.
--
-- Abbott, Altenkirch, Ghani. Containers: constructing strictly positive types. TCS 342(1), 2005.
-- Abbott, Altenkirch, Ghani. Representing nested inductive types using W-types. ICALP 2004.
-- Emmenegger. W-types in setoids. arXiv:1809.02375, 2018.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using () renaming (tt to ttS)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts; HasCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import commutative-monoid using (CommutativeMonoid)
open import lifting using (Lifting)
open import prop-setoid using (IsEquivalence; Setoid; module ≈-Reasoning)
open import indexed-family using (Fam; _⇒f_)
import fam
import polynomial-functor
import fam-mu-types.sort
import fam-mu-lifting.fibre

module fam-mu-lifting.carrier {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    {𝟙c : Category.obj 𝒞} (Lft : Lifting CM 𝟙c) where

open Category 𝒞 public
open IsEquivalence public

P : HasProducts 𝒞
P = biproducts→products CM BP

open HasProducts P public
open Lifting Lft public
open fam.CategoryOfFamilies os (os ⊔ es) 𝒞 public
open Obj public
open Mor public
open Fam public
module Fam𝒞 = Category cat
open products P public  -- Fam-level products
module Fam𝒞-P = HasProducts products
open _⇒f_ public
open polynomial-functor using (extend) public
open polynomial-functor.Poly public
Poly = polynomial-functor.Poly cat
open Setoid using (Carrier; isEquivalence) renaming (_≈_ to _≈s_) public

open import Data.Sum using (_⊎_) public
open import Data.Product using () renaming (_×_ to _×T_) public
open import prop using (_∧_; ⊥) public

-- The category-free sort layer, shared by every base category, and the
-- decorated fibre layer over this one.
module Sh = fam-mu-types.sort os es
open Sh public using (Sort; mkSort)
open fam-mu-lifting.fibre os es CM BP Lft public using (Idx; ∣_∣; module Fibre; μObj)

-- The fibrewise lift of a family: same index, each fibre lifted, transports under the action.
Lf : Obj → Obj
Lf X .idx = X .idx
Lf X .fam .fm x = L (X .fam .fm x)
Lf X .fam .subst e = Lmap (X .fam .subst e)
Lf X .fam .refl* = ≈-trans (Lmap-cong (X .fam .refl*)) Lmap-id
Lf X .fam .trans* q p = ≈-trans (Lmap-cong (X .fam .trans* q p)) (Lmap-comp _ _)

-- The interpretation of a polynomial with a root at every value former: sums are coproducts of
-- lifted summands, products are lifted products, mirroring the fibres of the trees.
fobj : (μ-obj : ∀ {k} → Poly (suc k) → (Fin k → Obj) → Obj) →
       ∀ {n} → Poly n → (Fin n → Obj) → Obj
fobj μ-obj (const A) δ = A
fobj μ-obj (var i)   δ = δ i
fobj μ-obj (P' + Q') δ =
  HasCoproducts.coprod coproducts (Lf (fobj μ-obj P' δ)) (Lf (fobj μ-obj Q' δ))
fobj μ-obj (P' × Q') δ = Lf (Fam𝒞-P.prod (fobj μ-obj P' δ) (fobj μ-obj Q' δ))
fobj μ-obj (μ P')    δ = μ-obj P' δ

-- The context-paired transport across the lifting and its laws, from the engine.
import lifting-fold
open lifting-fold CM BP Lft public
  using (under-root; under-root-cong; under-root-natural; under-root-post; under-root-pre;
         under-root-p₂; under-root-strip; pm; pm-in₁; pm-in₂; bp-ext; cop; cop-cong;
         strip-root; strip-root-cong; strip-root-natural)

-- A family's transports are isomorphisms, inverted along the symmetric proof.
fam-subst-iso₁ : ∀ {I : Setoid os (os ⊔ es)} (F : Fam I 𝒞)
                 {x y : I .Setoid.Carrier} (e : I .Setoid._≈_ x y) →
                 (F .subst e ∘ F .subst (I .Setoid.isEquivalence .sym e)) ≈ id _
fam-subst-iso₁ {I} F e =
  ≈-trans (≈-sym (F .trans* e (I .Setoid.isEquivalence .sym e))) (F .refl*)

fam-subst-iso₂ : ∀ {I : Setoid os (os ⊔ es)} (F : Fam I 𝒞)
                 {x y : I .Setoid.Carrier} (e : I .Setoid._≈_ x y) →
                 (F .subst (I .Setoid.isEquivalence .sym e) ∘ F .subst e) ≈ id _
fam-subst-iso₂ {I} F e =
  ≈-trans (≈-sym (F .trans* (I .Setoid.isEquivalence .sym e) e)) (F .refl*)

pm-iso : ∀ {a₁ a₂ b₁ b₂} {f : a₁ ⇒ a₂} {f' : a₂ ⇒ a₁} {h : b₁ ⇒ b₂} {h' : b₂ ⇒ b₁} →
         (f ∘ f') ≈ id a₂ → (h ∘ h') ≈ id b₂ →
         (prod-m f h ∘ prod-m f' h') ≈ id (prod a₂ b₂)
pm-iso e₁ e₂ = ≈-trans (≈-sym (prod-m-comp _ _ _ _)) (≈-trans (prod-m-cong e₁ e₂) prod-m-id)

-- The transport across the lifting as a family morphism: fibrewise under-root, natural because
-- transports are isomorphisms.
under-rootF : ∀ {Γ X Y : Obj} → Mor (Fam𝒞-P.prod Γ X) Y → Mor (Fam𝒞-P.prod Γ (Lf X)) (Lf Y)
under-rootF f .idxf = f .idxf
under-rootF f .famf ._⇒f_.transf (γ , x) = under-root (f .famf ._⇒f_.transf (γ , x))
under-rootF {Γ} {X} {Y} f .famf ._⇒f_.natural {γ₁ , x₁} {γ₂ , x₂} (γ≈ , x≈) =
  under-root-natural (Γ .fam .subst γ≈)
    (fam-subst-iso₁ (X .fam) x≈) (fam-subst-iso₂ (X .fam) x≈)
    (fam-subst-iso₁ (Y .fam) (f .idxf .prop-setoid._⇒_.func-resp-≈ (γ≈ , x≈)))
    (fam-subst-iso₂ (Y .fam) (f .idxf .prop-setoid._⇒_.func-resp-≈ (γ≈ , x≈)))
    (f .famf ._⇒f_.transf (γ₁ , x₁)) (f .famf ._⇒f_.transf (γ₂ , x₂))
    (f .famf ._⇒f_.natural (γ≈ , x≈))

-- The family-level transport across the lifting is congruent and carries the projection to the
-- projection.
under-rootF-cong : ∀ {Γ X Y : Obj} {f g : Mor (Fam𝒞-P.prod Γ X) Y} →
                   f ≃ g → under-rootF f ≃ under-rootF g
under-rootF-cong {Γ} {X} {Y} {f} {g} E ._≃_.idxf-eq = E ._≃_.idxf-eq
under-rootF-cong {Γ} {X} {Y} {f} {g} E ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , x} =
  ≈-trans (under-root-post
            (fam-subst-iso₁ (Y .fam)
              (E ._≃_.idxf-eq .prop-setoid._≃m_.func-eq
                (Γ .idx .Setoid.isEquivalence .sym (Γ .idx .Setoid.isEquivalence .refl) ,
                 X .idx .Setoid.isEquivalence .refl)))
            (fam-subst-iso₂ (Y .fam)
              (E ._≃_.idxf-eq .prop-setoid._≃m_.func-eq
                (Γ .idx .Setoid.isEquivalence .sym (Γ .idx .Setoid.isEquivalence .refl) ,
                 X .idx .Setoid.isEquivalence .refl)))
            (f .famf ._⇒f_.transf (γ , x)))
          (under-root-cong (E ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , x}))

under-rootF-p₂ : ∀ {Γ X : Obj} →
                 under-rootF (Fam𝒞-P.p₂ {Γ} {X}) ≃ Fam𝒞-P.p₂ {Γ} {Lf X}
under-rootF-p₂ {Γ} {X} ._≃_.idxf-eq .prop-setoid._≃m_.func-eq (γ≈ , x≈) = x≈
under-rootF-p₂ {Γ} {X} ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , x} =
  ≈-trans (∘-cong (≈-trans (Lmap-cong (X .fam .refl*)) Lmap-id) ≈-refl)
          (≈-trans id-left under-root-p₂)

private
  module CME = CMonEnriched CM

-- The fibrewise action of the lifting on a family morphism.
Lf-map : ∀ {X Y : Obj} → Mor X Y → Mor (Lf X) (Lf Y)
Lf-map f .idxf = f .idxf
Lf-map f .famf ._⇒f_.transf x = Lmap (f .famf ._⇒f_.transf x)
Lf-map f .famf ._⇒f_.natural e =
  ≈-trans (≈-sym (Lmap-comp _ _)) (≈-trans (Lmap-cong (f .famf ._⇒f_.natural e)) (Lmap-comp _ _))

-- The payload injection, fibrewise; natural because transports are isomorphisms.
injF : ∀ {X : Obj} → Mor X (Lf X)
injF .idxf = prop-setoid.idS _
injF {X} .famf ._⇒f_.transf x = inj
injF {X} .famf ._⇒f_.natural {x₁} {x₂} e =
  ≈-sym (Lmap-inj (fam-subst-iso₁ (X .fam) e) (fam-subst-iso₂ (X .fam) e))

-- The unit family of the lifting: a single fibre, at the object the roots come from.
𝟙L : Obj
𝟙L = simple[ prop-setoid.𝟙 , 𝟙c ]

-- The zero morphism into a family, at a chosen index.
zeroF : ∀ {A X : Obj} (x : X .idx .Carrier) → Mor A X
zeroF {A} {X} x .idxf .prop-setoid._⇒_.func _ = x
zeroF {A} {X} x .idxf .prop-setoid._⇒_.func-resp-≈ _ = X .idx .isEquivalence .refl
zeroF {A} {X} x .famf ._⇒f_.transf i = CME.εm
zeroF {A} {X} x .famf ._⇒f_.natural e =
  ≈-trans (CME.comp-bilinear-ε₁ _) (≈-sym (CME.comp-bilinear-ε₂ _))

zeroF-p₁ : ∀ {A X Y : Obj} (x : X .idx .Carrier) (y : Y .idx .Carrier) →
           Fam𝒞._≈_ (Fam𝒞._∘_ (Fam𝒞-P.p₁ {X} {Y}) (zeroF {A} (x , y))) (zeroF x)
zeroF-p₁ {A} {X} {Y} x y ._≃_.idxf-eq .prop-setoid._≃m_.func-eq _ = X .idx .isEquivalence .refl
zeroF-p₁ {A} {X} {Y} x y ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans (∘-cong (X .fam .refl*) (≈-trans id-left (CME.comp-bilinear-ε₂ _)))
          id-left

zeroF-p₂ : ∀ {A X Y : Obj} (x : X .idx .Carrier) (y : Y .idx .Carrier) →
           Fam𝒞._≈_ (Fam𝒞._∘_ (Fam𝒞-P.p₂ {X} {Y}) (zeroF {A} (x , y))) (zeroF y)
zeroF-p₂ {A} {X} {Y} x y ._≃_.idxf-eq .prop-setoid._≃m_.func-eq _ = Y .idx .isEquivalence .refl
zeroF-p₂ {A} {X} {Y} x y ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans (∘-cong (Y .fam .refl*) (≈-trans id-left (CME.comp-bilinear-ε₂ _)))
          id-left

-- The support, as a family morphism into the unit family.
sptF : ∀ {X : Obj} → Mor X 𝟙L
sptF .idxf = prop-setoid.to-𝟙
sptF {X} .famf ._⇒f_.transf x = spt
sptF {X} .famf ._⇒f_.natural {x₁} {x₂} e =
  ≈-trans (spt-natural (fam-subst-iso₁ (X .fam) e) (fam-subst-iso₂ (X .fam) e))
          (≈-sym id-left)

-- A map out of a biproduct against a pairing splits into its two legs.
cop-pair : ∀ {a b c d : obj} (f : a ⇒ c) (g : b ⇒ c) (u : d ⇒ a) (v : d ⇒ b) →
           (cop f g ∘ pair u v) ≈ ((f ∘ u) CME.+m (g ∘ v))
cop-pair f g u v =
  ≈-trans (CME.comp-bilinear₂ _ _ _)
    (CME.homCM _ _ .CommutativeMonoid.+-cong
      (≈-trans (≈-sym (assoc _ _ _)) (∘-cong (Biproduct.copair-in₁ (BP _ _) _ _) ≈-refl))
      (≈-trans (≈-sym (assoc _ _ _)) (∘-cong (Biproduct.copair-in₂ (BP _ _) _ _) ≈-refl)))

-- Transporting under a root against an assembled argument: the payload is eliminated in context,
-- and the root it carried joins the support that the elimination charges at the payload.
under-root-pair : ∀ {W Γ X Y : obj} (r : prod Γ X ⇒ Y)
                  (g : W ⇒ Γ) (u : W ⇒ X) (t : W ⇒ 𝟙c) →
                  (under-root r ∘ pair g (cop inj root ∘ pair u t))
                    ≈ (cop inj root ∘ pair (r ∘ pair g u) ((spt ∘ u) CME.+m t))
under-root-pair {W} {Γ} {X} {Y} r g u t = begin
    under-root r ∘ pair g (cop inj root ∘ pair u t)
  ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl (cop-pair _ _ _ _)) ⟩
    under-root r ∘ pair g ((inj ∘ u) CME.+m (root ∘ t))
  ≈⟨ cop-pair _ _ _ _ ⟩
    ((inj ∘ (r ∘ i₁)) ∘ g) CME.+m (affine root (inj ∘ (r ∘ i₂)) ∘ ((inj ∘ u) CME.+m (root ∘ t)))
  ≈⟨ +-cong ≈-refl (CME.comp-bilinear₂ _ _ _) ⟩
    ((inj ∘ (r ∘ i₁)) ∘ g)
      CME.+m ((affine root (inj ∘ (r ∘ i₂)) ∘ (inj ∘ u))
                CME.+m (affine root (inj ∘ (r ∘ i₂)) ∘ (root ∘ t)))
  ≈⟨ +-cong ≈-refl
       (+-cong (≈-trans (≈-sym (assoc _ _ _)) (∘-cong (affine-inj _ _) ≈-refl))
               (≈-trans (≈-sym (assoc _ _ _)) (∘-cong (affine-root _ _) ≈-refl))) ⟩
    ((inj ∘ (r ∘ i₁)) ∘ g)
      CME.+m (((((root ∘ spt) CME.+m (inj ∘ (r ∘ i₂))) ∘ u)) CME.+m (root ∘ t))
  ≈⟨ +-cong ≈-refl (+-cong (CME.comp-bilinear₁ _ _ _) ≈-refl) ⟩
    ((inj ∘ (r ∘ i₁)) ∘ g)
      CME.+m ((((root ∘ spt) ∘ u) CME.+m ((inj ∘ (r ∘ i₂)) ∘ u)) CME.+m (root ∘ t))
  ≈˘⟨ +-assoc ⟩
    (((inj ∘ (r ∘ i₁)) ∘ g)
       CME.+m (((root ∘ spt) ∘ u) CME.+m ((inj ∘ (r ∘ i₂)) ∘ u))) CME.+m (root ∘ t)
  ≈⟨ +-cong (+-cong ≈-refl +-comm) ≈-refl ⟩
    (((inj ∘ (r ∘ i₁)) ∘ g)
       CME.+m (((inj ∘ (r ∘ i₂)) ∘ u) CME.+m ((root ∘ spt) ∘ u))) CME.+m (root ∘ t)
  ≈⟨ +-cong (≈-sym +-assoc) ≈-refl ⟩
    ((((inj ∘ (r ∘ i₁)) ∘ g) CME.+m ((inj ∘ (r ∘ i₂)) ∘ u))
       CME.+m ((root ∘ spt) ∘ u)) CME.+m (root ∘ t)
  ≈⟨ +-assoc ⟩
    (((inj ∘ (r ∘ i₁)) ∘ g) CME.+m ((inj ∘ (r ∘ i₂)) ∘ u))
      CME.+m (((root ∘ spt) ∘ u) CME.+m (root ∘ t))
  ≈˘⟨ +-cong payload-leg root-leg ⟩
    (inj ∘ (r ∘ pair g u)) CME.+m (root ∘ ((spt ∘ u) CME.+m t))
  ≈˘⟨ cop-pair _ _ _ _ ⟩
    cop inj root ∘ pair (r ∘ pair g u) ((spt ∘ u) CME.+m t)
  ∎
  where
  open ≈-Reasoning isEquiv
  i₁ = Biproduct.in₁ (BP Γ X)
  i₂ = Biproduct.in₂ (BP Γ X)

  +-cong = λ {x} {y} {f₁} {f₂} {g₁} {g₂} →
           CME.homCM x y .CommutativeMonoid.+-cong {f₁} {f₂} {g₁} {g₂}
  +-assoc = λ {x} {y} {f₁} {f₂} {f₃} →
            CME.homCM x y .CommutativeMonoid.+-assoc {f₁} {f₂} {f₃}
  +-comm = λ {x} {y} {f₁} {f₂} → CME.homCM x y .CommutativeMonoid.+-comm {f₁} {f₂}

  payload-leg : (inj ∘ (r ∘ pair g u))
                  ≈ (((inj ∘ (r ∘ i₁)) ∘ g) CME.+m ((inj ∘ (r ∘ i₂)) ∘ u))
  payload-leg =
    ≈-trans (∘-cong ≈-refl (CME.comp-bilinear₂ _ _ _))
    (≈-trans (CME.comp-bilinear₂ _ _ _)
             (+-cong (≈-trans (∘-cong ≈-refl (≈-sym (assoc _ _ _))) (≈-sym (assoc _ _ _)))
                     (≈-trans (∘-cong ≈-refl (≈-sym (assoc _ _ _))) (≈-sym (assoc _ _ _)))))

  root-leg : (root ∘ ((spt ∘ u) CME.+m t)) ≈ (((root ∘ spt) ∘ u) CME.+m (root ∘ t))
  root-leg =
    ≈-trans (CME.comp-bilinear₂ _ _ _) (+-cong (≈-sym (assoc _ _ _)) ≈-refl)

-- The action of the lifting commutes with the assembly at an isomorphism: the injection is natural
-- only there, while the root is natural always.
Lmap-assemble : ∀ {X Y : obj} {h : X ⇒ Y} {h' : Y ⇒ X} →
                (h ∘ h') ≈ id Y → (h' ∘ h) ≈ id X →
                (Lmap h ∘ cop inj root) ≈ (cop inj root ∘ pm h (id 𝟙c))
Lmap-assemble {X} {Y} {h} {h'} hi₁ hi₂ =
  bp-ext
    (≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (Biproduct.copair-in₁ (BP _ _) _ _))
        (≈-trans (Lmap-inj hi₁ hi₂)
          (≈-sym (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl (pm-in₁ _ _))
              (≈-trans (≈-sym (assoc _ _ _))
                       (∘-cong (Biproduct.copair-in₁ (BP _ _) _ _) ≈-refl))))))))
    (≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (Biproduct.copair-in₂ (BP _ _) _ _))
        (≈-trans (Lmap-root _)
          (≈-sym (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl (pm-in₂ _ _))
              (≈-trans (≈-sym (assoc _ _ _))
                (≈-trans (∘-cong (Biproduct.copair-in₂ (BP _ _) _ _) ≈-refl) id-right))))))))

-- Assembling a lifted element from a payload and a root over it.
assembleF : ∀ {X : Obj} → Mor (Fam𝒞-P.prod X 𝟙L) (Lf X)
assembleF .idxf = prop-setoid.project₁
assembleF {X} .famf ._⇒f_.transf (x , _) = cop inj root
assembleF {X} .famf ._⇒f_.natural {x₁ , _} {x₂ , _} (e , _) =
  ≈-sym (Lmap-assemble (fam-subst-iso₁ (X .fam) e) (fam-subst-iso₂ (X .fam) e))

-- The zero of a lifted family is the assembly of the zero payload over the zero root.
zeroF-assemble : ∀ {A X : Obj} (x : X .idx .Carrier) →
                 Fam𝒞._≈_ (Fam𝒞._∘_ (assembleF {X}) (zeroF {A} (x , lift ttS))) (zeroF x)
zeroF-assemble {A} {X} x ._≃_.idxf-eq .prop-setoid._≃m_.func-eq _ =
  X .idx .isEquivalence .refl
zeroF-assemble {A} {X} x ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans (∘-cong (≈-trans (Lmap-cong (X .fam .refl*)) Lmap-id)
                  (≈-trans id-left (CME.comp-bilinear-ε₂ _)))
          id-left

-- The injection is the assembly at the payload's own support: the lifting's laws recover any map
-- out of a lifted object from its two restrictions, and the identity is its own assembly.
inj-assemble : ∀ {X : obj} → (cop inj root ∘ pair (id X) spt) ≈ inj
inj-assemble {X} =
  ≈-trans (CME.comp-bilinear₂ _ _ _)
  (≈-trans (CME.homCM _ _ .CommutativeMonoid.+-cong
             (≈-trans (≈-sym (assoc _ _ _))
               (≈-trans (∘-cong (Biproduct.copair-in₁ (BP _ _) _ _) ≈-refl) id-right))
             (≈-trans (≈-sym (assoc _ _ _))
               (∘-cong (Biproduct.copair-in₂ (BP _ _) _ _) ≈-refl)))
  (≈-trans (CME.homCM _ _ .CommutativeMonoid.+-comm)
  (≈-trans (≈-sym (affine-inj root inj))
  (≈-trans (∘-cong (≈-trans (affine-cong (≈-sym id-left) (≈-sym id-left))
                            (affine-η (id (L X))))
                   ≈-refl)
           id-left))))

injF-assemble : ∀ {X : Obj} →
                Fam𝒞._≈_ (Fam𝒞._∘_ (assembleF {X}) (Fam𝒞-P.pair (Fam𝒞.id X) sptF)) (injF {X})
injF-assemble {X} ._≃_.idxf-eq .prop-setoid._≃m_.func-eq p = p
injF-assemble {X} ._≃_.famf-eq .indexed-family._≃f_.transf-eq {x} =
  ≈-trans (∘-cong (Lf X .fam .refl*) ≈-refl)
          (≈-trans id-left (≈-trans id-left inj-assemble))

-- Dropping the root: the assembly at the zero constant, so the root's contribution vanishes.
payloadF : ∀ {X : Obj} → Mor (Lf X) X
payloadF .idxf = prop-setoid.idS _
payloadF {X} .famf ._⇒f_.transf x = affine CME.εm (id _)
payloadF {X} .famf ._⇒f_.natural {x₁} {x₂} e =
  lifting-ext _ _
    (≈-trans (assoc _ _ _)
      (≈-trans (∘-cong₂ (Lmap-root s))
        (≈-trans (affine-root _ _)
          (≈-sym (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong₂ (affine-root _ _)) (CME.comp-bilinear-ε₂ s)))))))
    (≈-trans (assoc _ _ _)
      (≈-trans (∘-cong₂ (Lmap-inj (fam-subst-iso₁ (X .fam) e) (fam-subst-iso₂ (X .fam) e)))
        (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong₁ payload-inj)
            (≈-trans id-left
              (≈-sym (≈-trans (assoc _ _ _)
                (≈-trans (∘-cong₂ payload-inj) id-right))))))))
  where
    s = X .fam .subst e
    payload-inj : ∀ {c} → (affine CME.εm (id c) ∘ inj) ≈ id c
    payload-inj =
      ≈-trans (affine-inj CME.εm (id _))
        (≈-trans (CME.homCM _ _ .CommutativeMonoid.+-cong (CME.comp-bilinear-ε₁ spt) ≈-refl)
          (CME.homCM _ _ .CommutativeMonoid.+-lunit))

-- A chosen constant of every fibre, natural under the transports: what an eliminator produces
-- from a root alone.
record Pointed (X : Obj) : Set (o ⊔ m ⊔ e ⊔ os ⊔ es) where
  field
    pt         : ∀ x → 𝟙c ⇒ X .fam .fm x
    pt-natural : ∀ {x₁ x₂} (e : _≈s_ (X .idx) x₁ x₂) →
                 (X .fam .subst e ∘ pt x₁) ≈ pt x₂

open Pointed public

-- Zero constants: eliminators discard the root, the reading without tags.
zero-pointed : ∀ {X} → Pointed X
zero-pointed .pt x = CME.εm
zero-pointed {X} .pt-natural e = CME.comp-bilinear-ε₂ (X .fam .subst e)

-- The bare root as the constant of a lifted family.
root-pointed : ∀ {X} → Pointed (Lf X)
root-pointed .pt x = root
root-pointed {X} .pt-natural e = Lmap-root (X .fam .subst e)

-- The constant of a lifted family: the root together with the payload's constant beneath it.
Lf-pointed : ∀ {X} → Pointed X → Pointed (Lf X)
Lf-pointed p .pt x = root CME.+m (inj ∘ p .pt x)
Lf-pointed {X} p .pt-natural {x₁} {x₂} e =
  ≈-trans (CME.comp-bilinear₂ _ _ _)
    (CME.homCM _ _ .CommutativeMonoid.+-cong
      (Lmap-root _)
      (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong₁ (Lmap-inj (fam-subst-iso₁ (X .fam) e) (fam-subst-iso₂ (X .fam) e)))
          (≈-trans (assoc _ _ _) (∘-cong₂ (p .pt-natural e))))))

prod-pointed : ∀ {X Y} → Pointed X → Pointed Y → Pointed (Fam𝒞-P.prod X Y)
prod-pointed pX pY .pt (x , y) = pair (pX .pt x) (pY .pt y)
prod-pointed pX pY .pt-natural {x₁ , y₁} {x₂ , y₂} (e₁ , e₂) =
  ≈-trans (pair-natural _ _ _)
    (pair-cong
      (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (pair-p₁ _ _)) (pX .pt-natural e₁)))
      (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (pair-p₂ _ _)) (pY .pt-natural e₂))))

coprod-pointed : ∀ {X Y} → Pointed X → Pointed Y →
                 Pointed (HasCoproducts.coprod coproducts X Y)
coprod-pointed pX pY .pt (inj₁ x) = pX .pt x
coprod-pointed pX pY .pt (inj₂ y) = pY .pt y
coprod-pointed pX pY .pt-natural {inj₁ x₁} {inj₁ x₂} e = pX .pt-natural e
coprod-pointed pX pY .pt-natural {inj₂ y₁} {inj₂ y₂} e = pY .pt-natural e

-- Eliminating a root in context: the payload continues, and the root produces the target's
-- chosen constant.
elimF : ∀ {Γ X C : Obj} → Pointed C → Mor (Fam𝒞-P.prod Γ X) C → Mor (Fam𝒞-P.prod Γ (Lf X)) C
elimF ptC f .idxf = f .idxf
elimF ptC f .famf ._⇒f_.transf (γ , x) =
  strip-root (ptC .pt (f .idxf .prop-setoid._⇒_.func (γ , x))) (f .famf ._⇒f_.transf (γ , x))
elimF {Γ} {X} {C} ptC f .famf ._⇒f_.natural {γ₁ , x₁} {γ₂ , x₂} (γ≈ , x≈) =
  strip-root-natural (Γ .fam .subst γ≈)
    (fam-subst-iso₁ (X .fam) x≈) (fam-subst-iso₂ (X .fam) x≈)
    (ptC .pt-natural (f .idxf .prop-setoid._⇒_.func-resp-≈ (γ≈ , x≈)))
    (f .famf ._⇒f_.transf (γ₁ , x₁)) (f .famf ._⇒f_.transf (γ₂ , x₂))
    (f .famf ._⇒f_.natural (γ≈ , x≈))

-- Transport across the lifting is the elimination at the root constant with the injected map.
under-rootF-elimF : ∀ {Γ X Y : Obj} (h : Mor (Fam𝒞-P.prod Γ X) Y) →
                    under-rootF h ≃ elimF root-pointed (Fam𝒞._∘_ injF h)
under-rootF-elimF h ._≃_.idxf-eq .prop-setoid._≃m_.func-eq e =
  h .idxf .prop-setoid._⇒_.func-resp-≈ e
under-rootF-elimF {Γ} {X} {Y} h ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans (∘-cong (≈-trans (Lmap-cong (Y .fam .refl*)) Lmap-id) ≈-refl)
  (≈-trans id-left
  (≈-trans (under-root-strip _)
           (strip-root-cong ≈-refl (≈-sym id-left))))

-- The lift of an isomorphism of families.
Lf-iso : ∀ {X Y : Obj} → Fam𝒞.Iso X Y → Fam𝒞.Iso (Lf X) (Lf Y)
Lf-iso i .Fam𝒞.Iso.fwd = Lf-map (i .Fam𝒞.Iso.fwd)
Lf-iso i .Fam𝒞.Iso.bwd = Lf-map (i .Fam𝒞.Iso.bwd)
Lf-iso {X} {Y} i .Fam𝒞.Iso.fwd∘bwd≈id ._≃_.idxf-eq =
  i .Fam𝒞.Iso.fwd∘bwd≈id ._≃_.idxf-eq
Lf-iso {X} {Y} i .Fam𝒞.Iso.fwd∘bwd≈id ._≃_.famf-eq .indexed-family._≃f_.transf-eq {y} =
  ≈-trans (∘-cong₂ id-left)
    (≈-trans (∘-cong₂ (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong
            (≈-trans (∘-cong₂ (≈-sym id-left))
              (i .Fam𝒞.Iso.fwd∘bwd≈id ._≃_.famf-eq .indexed-family._≃f_.transf-eq {y})))
          Lmap-id)))
Lf-iso {X} {Y} i .Fam𝒞.Iso.bwd∘fwd≈id ._≃_.idxf-eq =
  i .Fam𝒞.Iso.bwd∘fwd≈id ._≃_.idxf-eq
Lf-iso {X} {Y} i .Fam𝒞.Iso.bwd∘fwd≈id ._≃_.famf-eq .indexed-family._≃f_.transf-eq {x} =
  ≈-trans (∘-cong₂ id-left)
    (≈-trans (∘-cong₂ (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong
            (≈-trans (∘-cong₂ (≈-sym id-left))
              (i .Fam𝒞.Iso.bwd∘fwd≈id ._≃_.famf-eq .indexed-family._≃f_.transf-eq {x})))
          Lmap-id)))

-- Trees over an environment: shapes at its index setoids, fibres by decoration.
module Tree {n} (δ : Fin n → Obj) where
  open Sh.Tree (λ i → δ i .idx) public
  open Fibre δ public
