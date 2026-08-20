{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- μ-types for the Fam construction: the carrier, reindexing of its trees,
-- the strong catamorphism, inMap, Lambek's lemma and the initial-algebra
-- laws, with preservation of sections by each of the maps. The functorial
-- action and μ-map, which need a terminal object, live under WithTerminal.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import commutative-monoid using (CommutativeMonoid)
import lifting
open import prop-setoid using (IsEquivalence; Setoid; module ≈-Reasoning)
import prop-setoid as PS
open import indexed-family using (Fam; _⇒f_)
import fam
import fam-functor
open import functor using (StrongFunctor)
import polynomial-functor
import fam-mu-lifting.sort
import fam-mu-lifting.fibre

module fam-mu-lifting {o m e} (os es : Level) {𝒞 : Category o m e}
    (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    (𝟙c : Category.obj 𝒞) where

------------------------------------------------------------------------------
-- Carrier: nested μ reduced to a single sort-indexed W-type in setoids, with
-- the fibre family computed by structural recursion over trees. The sorts and
-- trees are category-free, built from the index setoids alone; the fibres
-- recover the objects of the original polynomial and environment through a
-- decoration of the sorts.
--
-- Abbott, Altenkirch, Ghani. Containers: constructing strictly positive types. TCS 342(1), 2005.
-- Abbott, Altenkirch, Ghani. Representing nested inductive types using W-types. ICALP 2004.
-- Emmenegger. W-types in setoids. arXiv:1809.02375, 2018.
------------------------------------------------------------------------------

open Category 𝒞 public
open IsEquivalence public

𝒞-products : HasProducts 𝒞
𝒞-products = biproducts→products CM BP

open HasProducts 𝒞-products public

private
  module Lc = lifting CM BP 𝟙c
open Lc public
  using (L; root; inj; copair-root; copair-inj; lifting-ext;
         Lmap; Lmap-cong; Lmap-id; Lmap-comp; Lmap-root; Lmap-inj;
         L-elem; L-elem-cong; L-elem-natural;
         strong-Lmap; strong-Lmap-cong; strong-Lmap-natural; strong-Lmap-pre; strong-Lmap-post; strong-Lmap-co; strong-Lmap-p₂; strong-Lmap-elem; strong-Lmap-inj;
         elim-root; elim-root-cong; elim-root-natural)
open fam.CategoryOfFamilies os (os ⊔ es) 𝒞 public
open Obj public
open Mor public
open Fam public
module Fam𝒞 = Category cat
open products 𝒞-products public  -- Fam-level products
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
module Srt = fam-mu-lifting.sort os es
open Srt public using (Sort; mkSort)
open fam-mu-lifting.fibre os es CM BP 𝟙c public using (Idx; ∣_∣; module Fibre; μ-fam)

-- The lifting on families: the fibrewise strong endofunctor induced by the lifting.
private
  LfS : StrongFunctor products
  LfS = fam-functor.FamF-strong os (os ⊔ es) 𝒞-products Lc.L-strong
  module LfS = StrongFunctor LfS

Lf : Obj → Obj
Lf = LfS.fobj

Lf-map : ∀ {X Y : Obj} → Mor X Y → Mor (Lf X) (Lf Y)
Lf-map = LfS.fmor

open LfS public using () renaming (fmor-cong to Lf-map-cong; fmor-id to Lf-map-id; fmor-comp to Lf-map-comp)

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

prod-m-iso : ∀ {a₁ a₂ b₁ b₂} {f : a₁ ⇒ a₂} {f' : a₂ ⇒ a₁} {h : b₁ ⇒ b₂} {h' : b₂ ⇒ b₁} →
             (f ∘ f') ≈ id a₂ → (h ∘ h') ≈ id b₂ → (prod-m f h ∘ prod-m f' h') ≈ id (prod a₂ b₂)
prod-m-iso e₁ e₂ = ≈-trans (≈-sym (prod-m-comp _ _ _ _)) (≈-trans (prod-m-cong e₁ e₂) prod-m-id)

open polynomial-functor.Interp products strongCoproducts LfS public
  using (fobj; extend-mor; HasMu; HasMuLaws; _∘co_) renaming (strong-Lmap to strong-Lf-map)

-- The action of the lifting on a family morphism in context is fibrewise the transport.
strong-Lf-map-transf : ∀ {Γ X Y : Obj} (f : Mor (Fam𝒞-P.prod Γ X) Y) {γ x} →
                       strong-Lf-map f .famf ._⇒f_.transf (γ , x) ≈ strong-Lmap (f .famf ._⇒f_.transf (γ , x))
strong-Lf-map-transf f = ≈-trans id-left (≈-trans (strong-Lmap-post _ _) (strong-Lmap-cong id-right))

private
  module CME = CMonEnriched CM

-- The payload injection, fibrewise.
injF : ∀ {X : Obj} → Mor X (Lf X)
injF .idxf = prop-setoid.idS _
injF {X} .famf ._⇒f_.transf x = inj
injF {X} .famf ._⇒f_.natural {x₁} {x₂} e =
  ≈-sym (Lmap-inj (X .fam .subst e))

injF-natural : ∀ {X Y : Obj} (f : Mor X Y) → Fam𝒞._∘_ (Lf-map f) injF ≃ Fam𝒞._∘_ injF f
injF-natural f ._≃_.idxf-eq .PS._≃m_.func-eq e = f .idxf .PS._⇒_.func-resp-≈ e
injF-natural {X} {Y} f ._≃_.famf-eq .indexed-family._≃f_.transf-eq {x} =
  ≈-trans (∘-cong (Lf Y .fam .refl*) id-left)
  (≈-trans id-left
  (≈-trans (Lmap-inj (f .famf ._⇒f_.transf x)) (≈-sym id-left)))

private
  strength-injF : ∀ {Γ X : Obj} →
    Fam𝒞._∘_ (LfS.strengthᵣ {Γ} {X}) (Fam𝒞-P.pair Fam𝒞-P.p₁ (Fam𝒞._∘_ injF Fam𝒞-P.p₂)) ≃ injF
  strength-injF ._≃_.idxf-eq .PS._≃m_.func-eq e = e
  strength-injF {Γ} {X} ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , x} =
    ≈-trans (∘-cong (Lf (Fam𝒞-P.prod Γ X) .fam .refl*) id-left)
    (≈-trans id-left
    (≈-trans (∘-cong ≈-refl (pair-cong ≈-refl id-left))
    (≈-trans (∘-cong ≈-refl (pair-cong (≈-sym id-left) ≈-refl))
    (≈-trans (strong-Lmap-inj (id _)) id-right))))

strong-Lf-map-injF : ∀ {Γ X Y : Obj} (f : Mor (Fam𝒞-P.prod Γ X) Y) →
  Fam𝒞._∘_ (strong-Lf-map f) (Fam𝒞-P.pair Fam𝒞-P.p₁ (Fam𝒞._∘_ injF Fam𝒞-P.p₂)) ≃ Fam𝒞._∘_ injF f
strong-Lf-map-injF f =
  Fam𝒞.≈-trans (Fam𝒞.assoc _ _ _)
  (Fam𝒞.≈-trans (Fam𝒞.∘-cong Fam𝒞.≈-refl strength-injF) (injF-natural f))

-- A section of a family: an element of every fibre, natural under the transports. It is what an
-- eliminator writes when it consumes a root.
record Section (X : Obj) : Set (o ⊔ m ⊔ e ⊔ os ⊔ es) where
  field
    at         : ∀ x → 𝟙c ⇒ X .fam .fm x
    at-natural : ∀ {x₁ x₂} (e : _≈s_ (X .idx) x₁ x₂) → (X .fam .subst e ∘ at x₁) ≈ at x₂

open Section public

-- Sections are structural: a simple family has a section at any chosen element, and sections
-- close under the lifting, coproducts and products, with unit weight at each root the lifting
-- adjoins.
simple-section : ∀ {A : Setoid os (os ⊔ es)} {x : obj} → (𝟙c ⇒ x) → Section simple[ A , x ]
simple-section c .at _ = c
simple-section c .at-natural _ = id-left

Lf-section : ∀ {X : Obj} → Section X → Section (Lf X)
Lf-section c .at x = L-elem (c .at x)
Lf-section {X} c .at-natural e =
  ≈-trans (L-elem-natural (X .fam .subst e) (c .at _)) (L-elem-cong (c .at-natural e))

Lf-root : ∀ {X : Obj} → Section (Lf X)
Lf-root .at x = root
Lf-root {X} .at-natural e = Lmap-root (X .fam .subst e)

coprod-section : ∀ {X Y : Obj} → Section X → Section Y →
                  Section (HasCoproducts.coprod coproducts X Y)
coprod-section c d .at (inj₁ x) = c .at x
coprod-section c d .at (inj₂ y) = d .at y
coprod-section c d .at-natural {inj₁ _} {inj₁ _} e = c .at-natural e
coprod-section c d .at-natural {inj₂ _} {inj₂ _} e = d .at-natural e

prod-section : ∀ {X Y : Obj} → Section X → Section Y → Section (Fam𝒞-P.prod X Y)
prod-section c d .at (x , y) = pair (c .at x) (d .at y)
prod-section c d .at-natural (e₁ , e₂) =
  ≈-trans (pair-compose _ _ _ _) (pair-cong (c .at-natural e₁) (d .at-natural e₂))

-- Scaling a section by an endomorphism of the unit object.
scale-section : ∀ {X : Obj} → (𝟙c ⇒ 𝟙c) → Section X → Section X
scale-section w c .at x = c .at x ∘ w
scale-section w c .at-natural e =
  ≈-trans (≈-sym (assoc _ _ _)) (∘-cong (c .at-natural e) ≈-refl)

-- Eliminating a root in context: the payload continues, and the root produces the target's
-- section.
elimF : ∀ {Γ X C : Obj} → Section C → Mor (Fam𝒞-P.prod Γ X) C → Mor (Fam𝒞-P.prod Γ (Lf X)) C
elimF cC f .idxf = f .idxf
elimF cC f .famf ._⇒f_.transf (γ , x) =
  elim-root (cC .at (f .idxf .prop-setoid._⇒_.func (γ , x))) (f .famf ._⇒f_.transf (γ , x))
elimF {Γ} {X} {C} cC f .famf ._⇒f_.natural {γ₁ , x₁} {γ₂ , x₂} (γ≈ , x≈) =
  elim-root-natural (Γ .fam .subst γ≈) (X .fam .subst x≈)
    (cC .at-natural (f .idxf .prop-setoid._⇒_.func-resp-≈ (γ≈ , x≈)))
    (f .famf ._⇒f_.transf (γ₁ , x₁)) (f .famf ._⇒f_.transf (γ₂ , x₂))
    (f .famf ._⇒f_.natural (γ≈ , x≈))

-- Not every morphism preserves a section: the payload injection sends the element to a payload with
-- zero root weight, not the lifted section's element.
record preserves-section {X Y : Obj} (f : Mor X Y) (c : Section X) (d : Section Y) : Prop (os ⊔ e) where
  field
    at : ∀ x → (f .famf ._⇒f_.transf x ∘ c .at x) ≈ d .at (f .idxf .prop-setoid._⇒_.func x)
open preserves-section public

preserves-section-id : ∀ {X : Obj} (c : Section X) → preserves-section (Fam𝒞.id X) c c
preserves-section-id c .at x = id-left

preserves-section-∘ : ∀ {X Y Z : Obj} {f : Mor Y Z} {g : Mor X Y} {cX cY cZ} →
                      preserves-section f cY cZ → preserves-section g cX cY →
                      preserves-section (f Fam𝒞.∘ g) cX cZ
preserves-section-∘ {f = f} {g} pf pg .at x =
  ≈-trans (∘-cong id-left ≈-refl)
    (≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (pg .at x)) (pf .at _)))

preserves-section-resp : ∀ {X Y : Obj} {f g : Mor X Y} {c : Section X} {d : Section Y} →
                         f Fam𝒞.≈ g → preserves-section f c d → preserves-section g c d
preserves-section-resp {X} {Y} {f} {g} {c} {d} f≃g pf .at x =
  ≈-trans (∘-cong (≈-sym (f≃g ._≃_.famf-eq .indexed-family._≃f_.transf-eq)) ≈-refl)
    (≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (pf .at x)) (d .at-natural _)))

-- Preservation inverts along an isomorphism: the target section pulls back through the inverse,
-- with the index round trip carried by the sections' naturality.
preserves-section-inv : ∀ {X Y : Obj} {f : Mor X Y} {g : Mor Y X} {c : Section X} {d : Section Y} →
                        (f Fam𝒞.∘ g) ≃ Fam𝒞.id Y → (g Fam𝒞.∘ f) ≃ Fam𝒞.id X →
                        preserves-section f c d → preserves-section g d c
preserves-section-inv {X} {Y} {f} {g} {c} {d} fg gf hf .at y =
  ≈-trans (∘-cong ≈-refl (≈-sym (≈-trans (∘-cong ≈-refl (hf .at x)) (d .at-natural fgy≈y))))
  (≈-trans (≈-sym (assoc _ _ _))
  (≈-trans (∘-cong (g .famf ._⇒f_.natural fgy≈y) ≈-refl)
  (≈-trans (assoc _ _ _)
  (≈-trans (∘-cong ≈-refl (≈-sym (assoc _ _ _)))
  (≈-trans (∘-cong ≈-refl (≈-trans (∘-cong (≈-sym id-left) ≈-refl) (hgf .at x)))
           (c .at-natural (g .idxf .prop-setoid._⇒_.func-resp-≈ fgy≈y)))))))
  where
  x = g .idxf .prop-setoid._⇒_.func y
  fgy≈y : _≈s_ (Y .idx) (f .idxf .prop-setoid._⇒_.func x) y
  fgy≈y = fg ._≃_.idxf-eq .PS._≃m_.func-eq (Y .idx .isEquivalence .refl)
  hgf : preserves-section (g Fam𝒞.∘ f) c c
  hgf = preserves-section-resp (Fam𝒞.≈-sym gf) (preserves-section-id c)

preserves-coprod-m : ∀ {X X' Y Y' : Obj} {f : Mor X X'} {g : Mor Y Y'} {cX cX' cY cY'} →
                     preserves-section f cX cX' → preserves-section g cY cY' →
                     preserves-section (HasCoproducts.coprod-m coproducts f g)
                       (coprod-section cX cY) (coprod-section cX' cY')
preserves-coprod-m pf pg .at (inj₁ x) = ≈-trans (∘-cong (≈-trans id-left id-left) ≈-refl) (pf .at x)
preserves-coprod-m pf pg .at (inj₂ y) = ≈-trans (∘-cong (≈-trans id-left id-left) ≈-refl) (pg .at y)

preserves-prod-m : ∀ {X X' Y Y' : Obj} {f : Mor X X'} {g : Mor Y Y'} {cX cX' cY cY'} →
                   preserves-section f cX cX' → preserves-section g cY cY' →
                   preserves-section (Fam𝒞-P.prod-m f g) (prod-section cX cY) (prod-section cX' cY')
preserves-prod-m pf pg .at (x , y) =
  ≈-trans (∘-cong (pair-cong id-left id-left) ≈-refl)
    (≈-trans (pair-compose _ _ _ _) (pair-cong (pf .at x) (pg .at y)))

preserves-p₂ : ∀ {X Y : Obj} {cX cY} →
               preserves-section (Fam𝒞-P.p₂ {X} {Y}) (prod-section cX cY) cY
preserves-p₂ .at (x , y) = pair-p₂ _ _

preserves-pair : ∀ {X Y Z : Obj} {f : Mor X Y} {g : Mor X Z} {cX cY cZ} →
                 preserves-section f cX cY → preserves-section g cX cZ →
                 preserves-section (Fam𝒞-P.pair f g) cX (prod-section cY cZ)
preserves-pair pf pg .at x = ≈-trans (pair-natural _ _ _) (pair-cong (pf .at x) (pg .at x))

preserves-Lf-map : ∀ {X Y : Obj} {f : Mor X Y} {c d} →
                   preserves-section f c d → preserves-section (Lf-map f) (Lf-section c) (Lf-section d)
preserves-Lf-map {f = f} {c} p .at x =
  ≈-trans (L-elem-natural (f .famf ._⇒f_.transf x) (c .at x)) (L-elem-cong (p .at x))

preserves-Lf-root : ∀ {X Y : Obj} (f : Mor X Y) → preserves-section (Lf-map f) Lf-root Lf-root
preserves-Lf-root f .at x = Lmap-root (f .famf ._⇒f_.transf x)

preserves-scale : ∀ {X Y : Obj} {f : Mor X Y} {w : 𝟙c ⇒ 𝟙c} {c d} →
                  preserves-section f c d →
                  preserves-section f (scale-section w c) (scale-section w d)
preserves-scale p .at x = ≈-trans (≈-sym (assoc _ _ _)) (∘-cong (p .at x) ≈-refl)

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
  open Srt.Tree (λ i → δ i .idx) public
  open Fibre δ public

-- Sections for a polynomial: one at every constant leaf.
PolySection : ∀ {n} → Poly n → Set (o ⊔ m ⊔ e ⊔ os ⊔ es)
PolySection (const A) = Section A
PolySection (var i)   = Lift (o ⊔ m ⊔ e ⊔ os ⊔ es) ⊤
PolySection (P' + Q') = PolySection P' ×T PolySection Q'
PolySection (P' × Q') = PolySection P' ×T PolySection Q'
PolySection (μ P')    = PolySection P'

-- The unit section of a μ-carrier, by recursion over trees: sections for the polynomial and
-- the environment determine an element at every fibre, natural in the tree, with unit weight at
-- each root.
module MuSection {n} (δ : Fin n → Obj) (δ-section : ∀ i → Section (δ i)) where
  open Tree δ

  DecoAssignSection : ∀ {r} → DecoAssign r → Set (o ⊔ m ⊔ e ⊔ os ⊔ es)
  DecoSection : ∀ {s} → Deco s → Set (o ⊔ m ⊔ e ⊔ os ⊔ es)
  DecoAssignSection {inj₁ _} _ = Lift (o ⊔ m ⊔ e ⊔ os ⊔ es) ⊤
  DecoAssignSection {inj₂ _} d = DecoSection d
  DecoSection (mkDeco Q d) = PolySection Q ×T (∀ i → DecoAssignSection (d i))

  deco-ext-section : ∀ {k} (Q : Poly (Data.Nat.suc k)) {ρ̄ : Fin k → Fin n ⊎ Srt.Sort n}
                   {d : ∀ i → DecoAssign (ρ̄ i)} →
                   PolySection Q → (∀ i → DecoAssignSection (d i)) →
                   ∀ i → DecoAssignSection (deco-ext Q d i)
  deco-ext-section Q Qc dc Fin.zero    = Qc , dc
  deco-ext-section Q Qc dc (Fin.suc i) = dc i

  mutual
    fib-unit : ∀ {k} (Q : Poly (Data.Nat.suc k)) {ρ̄ : Fin k → Fin n ⊎ Srt.Sort n}
               (d : ∀ i → DecoAssign (ρ̄ i)) → PolySection Q → (∀ i → DecoAssignSection (d i)) →
               (t : W ∣ Q ∣ ρ̄) → 𝟙c ⇒ fib Q d t
    fib-unit Q d Qc dc (sup x) = fib-shape-unit Q (deco-ext Q d) Qc (deco-ext-section Q Qc dc) x

    fib-shape-unit : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Srt.Sort n}
                     (d : ∀ i → DecoAssign (η̄ i)) → PolySection Q → (∀ i → DecoAssignSection (d i)) →
                     (x : ⟦ ∣ Q ∣ ⟧shape η̄) → 𝟙c ⇒ fib-shape Q d x
    fib-shape-unit (const A) d Ac dc x = Ac .at x
    fib-shape-unit (var i)   d _ dc x = fib-el-unit _ (d i) (dc i) x
    fib-shape-unit (P' + Q') d (Pc , Qc) dc (inj₁ x) = L-elem (fib-shape-unit P' d Pc dc x)
    fib-shape-unit (P' + Q') d (Pc , Qc) dc (inj₂ y) = L-elem (fib-shape-unit Q' d Qc dc y)
    fib-shape-unit (P' × Q') d (Pc , Qc) dc (x , y) =
      L-elem (pair (fib-shape-unit P' d Pc dc x) (fib-shape-unit Q' d Qc dc y))
    fib-shape-unit (μ Q')    d Qc dc x = fib-unit Q' d Qc dc x

    fib-el-unit : ∀ (r : Fin n ⊎ Srt.Sort n) (dr : DecoAssign r) → DecoAssignSection dr →
                  (x : El r) → 𝟙c ⇒ fib-el r dr x
    fib-el-unit (inj₁ p) _ _ x = δ-section p .at x
    fib-el-unit (inj₂ _) (mkDeco Q ρd) (Qc , ρdc) x = fib-unit Q ρd Qc ρdc x

  mutual
    fib-unit-natural : ∀ {k} (Q : Poly (Data.Nat.suc k)) {ρ̄ : Fin k → Fin n ⊎ Srt.Sort n}
                       (d : ∀ i → DecoAssign (ρ̄ i)) (Qc : PolySection Q)
                       (dc : ∀ i → DecoAssignSection (d i))
                       {t t' : W ∣ Q ∣ ρ̄} (p : W-≈ t t') →
                       (fib-subst Q d {x = t} {y = t'} p ∘ fib-unit Q d Qc dc t)
                         ≈ fib-unit Q d Qc dc t'
    fib-unit-natural Q d Qc dc {sup x} {sup y} p =
      fib-shape-unit-natural Q (deco-ext Q d) Qc (deco-ext-section Q Qc dc) p

    fib-shape-unit-natural : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Srt.Sort n}
                             (d : ∀ i → DecoAssign (η̄ i)) (Qc : PolySection Q)
                             (dc : ∀ i → DecoAssignSection (d i))
                             {x y : ⟦ ∣ Q ∣ ⟧shape η̄} (p : shape≈ ∣ Q ∣ η̄ x y) →
                             (fib-shape-subst Q d p ∘ fib-shape-unit Q d Qc dc x)
                               ≈ fib-shape-unit Q d Qc dc y
    fib-shape-unit-natural (const A) d Ac dc p = Ac .at-natural p
    fib-shape-unit-natural (var i)   d _ dc p = fib-el-unit-natural _ (d i) (dc i) p
    fib-shape-unit-natural (P' + Q') d (Pc , Qc) dc {inj₁ _} {inj₁ _} p =
      ≈-trans (L-elem-natural _ _) (L-elem-cong (fib-shape-unit-natural P' d Pc dc p))
    fib-shape-unit-natural (P' + Q') d (Pc , Qc) dc {inj₂ _} {inj₂ _} p =
      ≈-trans (L-elem-natural _ _) (L-elem-cong (fib-shape-unit-natural Q' d Qc dc p))
    fib-shape-unit-natural (P' × Q') d (Pc , Qc) dc {_ , _} {_ , _} (p₁ , p₂) =
      ≈-trans (L-elem-natural _ _)
        (L-elem-cong (≈-trans (pair-compose _ _ _ _)
          (pair-cong (fib-shape-unit-natural P' d Pc dc p₁)
                     (fib-shape-unit-natural Q' d Qc dc p₂))))
    fib-shape-unit-natural (μ Q')    d Qc dc {x} {y} p =
      fib-unit-natural Q' d Qc dc {x} {y} p

    fib-el-unit-natural : ∀ (r : Fin n ⊎ Srt.Sort n) (dr : DecoAssign r)
                          (drc : DecoAssignSection dr) {x y : El r} (p : elEq r x y) →
                          (fib-el-subst r dr p ∘ fib-el-unit r dr drc x) ≈ fib-el-unit r dr drc y
    fib-el-unit-natural (inj₁ p) _ _ e = δ-section p .at-natural e
    fib-el-unit-natural (inj₂ _) (mkDeco Q ρd) (Qc , ρdc) {x} {y} e =
      fib-unit-natural Q ρd Qc ρdc {x} {y} e

  μ-section : ∀ (P : Poly (Data.Nat.suc n)) → PolySection P → Section (μ-fam P δ)
  μ-section P Pc .at t = fib-unit P (λ i → lift tt) Pc (λ i → lift tt) t
  μ-section P Pc .at-natural {t} {t'} e =
    fib-unit-natural P (λ i → lift tt) Pc (λ i → lift tt) {t} {t'} e

poly-section : ∀ {n} {δ : Fin n → Obj} (P : Poly n) → PolySection P → (∀ i → Section (δ i)) →
               Section (fobj μ-fam P δ)
poly-section (const A) Ac δc = Ac
poly-section (var i)   _  δc = δc i
poly-section (P + Q) (Pc , Qc) δc =
  coprod-section (Lf-section (poly-section P Pc δc)) (Lf-section (poly-section Q Qc δc))
poly-section (P × Q) (Pc , Qc) δc =
  Lf-section (prod-section (poly-section P Pc δc) (poly-section Q Qc δc))
poly-section {δ = δ} (μ P) Pc δc = MuSection.μ-section δ δc P Pc

extend-section : ∀ {n} {δ : Fin n → Obj} {X : Obj} → (∀ i → Section (δ i)) → Section X →
                 ∀ i → Section (extend δ X i)
extend-section δc c Fin.zero    = c
extend-section δc c (Fin.suc i) = δc i

------------------------------------------------------------------------------
-- Reindexing of carrier trees along context morphisms: MorD carries index and
-- fibre data, IMorD the index action only (MorD's index side factors through it
-- via `erase`), and FReindex's FAct pairs an IMorD with an "external" Γ-dependent
-- fibre action. The morphisms are first-order data so the recursion stays
-- structural. The index actions work on the category-free shapes; the fibre
-- actions carry the decorations of both sides.
------------------------------------------------------------------------------

-- Reindex a tree from one parameter context to another along a context morphism.
-- The morphism is first-order data: `base` carries the leaf maps (applied only at
-- leaves), `bind` records one binder. So `reindex`'s recursive calls are syntactically
-- direct and structurally terminating — no closure, no fuel.
module Reindex {nA nB} (δA : Fin nA → Obj) (δB : Fin nB → Obj) where
  private
    module TA = Tree δA
    module TB = Tree δB

  data MorD : ∀ {k} (ρA : Fin k → Fin nA ⊎ Sort nA) (ρB : Fin k → Fin nB ⊎ Sort nB) →
              (∀ v → TA.DecoAssign (ρA v)) → (∀ v → TB.DecoAssign (ρB v)) →
              Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    base : ∀ {k} {ρA ρB dA dB} (f : ∀ v → TA.El (ρA v) → TB.El (ρB v))
           (f-resp : ∀ v {a a'} → TA.elEq (ρA v) a a' → TB.elEq (ρB v) (f v a) (f v a'))
           (ffam : ∀ v a → TA.fib-el (ρA v) (dA v) a ⇒ TB.fib-el (ρB v) (dB v) (f v a)) →
           (∀ v {a a'} (p : TA.elEq (ρA v) a a') →
              (ffam v a' ∘ TA.fib-el-subst (ρA v) (dA v) p) ≈ (TB.fib-el-subst (ρB v) (dB v) (f-resp v p) ∘ ffam v a)) →
           MorD {k} ρA ρB dA dB
    bind : ∀ {k} {ρA ρB dA dB} (Q : Poly (suc k)) → MorD ρA ρB dA dB →
           MorD (extend ρA (inj₂ (mkSort ∣ Q ∣ ρA))) (extend ρB (inj₂ (mkSort ∣ Q ∣ ρB)))
                (TA.deco-ext Q dA) (TB.deco-ext Q dB)

  -- Index-only reindex: the index action of a context morphism, with no fibre data,
  -- so entirely at the category-free shapes. Carries both `MorD`'s index side (via
  -- `erase` below) and the fusion morphisms (`combine`), whose Γ-dependent fibre
  -- action lives externally in `FReindex`.
  data IMorD : ∀ {k} → (Fin k → Fin nA ⊎ Sort nA) → (Fin k → Fin nB ⊎ Sort nB) →
               Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    ibase : ∀ {k} {ρA ρB} (f : ∀ v → TA.El (ρA v) → TB.El (ρB v))
            (f-resp : ∀ v {a a'} → TA.elEq (ρA v) a a' → TB.elEq (ρB v) (f v a) (f v a')) →
            IMorD {k} ρA ρB
    ibind : ∀ {k} {ρA ρB} (R : Srt.Poly (suc k)) → IMorD ρA ρB →
            IMorD (extend ρA (inj₂ (mkSort R ρA))) (extend ρB (inj₂ (mkSort R ρB)))

  mutual
    ireindex : ∀ {k} {R : Srt.Poly (suc k)} {ρA ρB} (md : IMorD ρA ρB) → TA.W R ρA → TB.W R ρB
    ireindex {R = R} md (TA.sup x) = TB.sup (ireindex-shape R (ibind R md) x)

    ireindex-shape : ∀ {j} (R : Srt.Poly j) {ηA ηB} (md : IMorD ηA ηB) → TA.⟦ R ⟧shape ηA → TB.⟦ R ⟧shape ηB
    ireindex-shape (const S) md a = a
    ireindex-shape (var v) md a = iapply md v a
    ireindex-shape (P + Q) md (inj₁ a) = inj₁ (ireindex-shape P md a)
    ireindex-shape (P + Q) md (inj₂ b) = inj₂ (ireindex-shape Q md b)
    ireindex-shape (P × Q) md (a , b) = ireindex-shape P md a , ireindex-shape Q md b
    ireindex-shape (μ Q') md t = ireindex md t

    iapply : ∀ {k} {ρA ρB} (md : IMorD {k} ρA ρB) (v : Fin k) → TA.El (ρA v) → TB.El (ρB v)
    iapply (ibase f _) v a = f v a
    iapply (ibind R md) Fin.zero a = ireindex md a
    iapply (ibind R md) (Fin.suc v) a = iapply md v a

  mutual
    ireindex-resp : ∀ {k} {R : Srt.Poly (suc k)} {ρA ρB} (md : IMorD ρA ρB) {t t' : TA.W R ρA} →
                    TA.W-≈ t t' → TB.W-≈ (ireindex md t) (ireindex md t')
    ireindex-resp {R = R} md {TA.sup x} {TA.sup y} p = ireindex-shape-resp R (ibind R md) {x} {y} p

    ireindex-shape-resp : ∀ {j} (R : Srt.Poly j) {ηA ηB} (md : IMorD ηA ηB) {a a' : TA.⟦ R ⟧shape ηA} →
                          TA.shape≈ R ηA a a' → TB.shape≈ R ηB (ireindex-shape R md a) (ireindex-shape R md a')
    ireindex-shape-resp (const S) md p = p
    ireindex-shape-resp (var v)   md p = iapply-resp md v p
    ireindex-shape-resp (P + Q) md {inj₁ _} {inj₁ _} p = ireindex-shape-resp P md p
    ireindex-shape-resp (P + Q) md {inj₂ _} {inj₂ _} p = ireindex-shape-resp Q md p
    ireindex-shape-resp (P × Q) md {_ , _} {_ , _} (p₁ , p₂) = ireindex-shape-resp P md p₁ , ireindex-shape-resp Q md p₂
    ireindex-shape-resp (μ Q') md {a} {a'} p = ireindex-resp md {a} {a'} p

    iapply-resp : ∀ {k} {ρA ρB} (md : IMorD {k} ρA ρB) (v : Fin k) {a a'} →
                  TA.elEq (ρA v) a a' → TB.elEq (ρB v) (iapply md v a) (iapply md v a')
    iapply-resp (ibase f f-resp) v p = f-resp v p
    iapply-resp (ibind R md) Fin.zero {a} {a'} p = ireindex-resp md {a} {a'} p
    iapply-resp (ibind R md) (Fin.suc v) p = iapply-resp md v p

  -- Erase the fibre fields; `MorD`'s index-level operations are `IMorD`'s.
  erase : ∀ {k} {ρA ρB dA dB} → MorD {k} ρA ρB dA dB → IMorD ρA ρB
  erase (base f f-resp _ _) = ibase f f-resp
  erase (bind Q md) = ibind ∣ Q ∣ (erase md)

  reindex : ∀ {k} {R : Srt.Poly (suc k)} {ρA ρB dA dB} → MorD ρA ρB dA dB → TA.W R ρA → TB.W R ρB
  reindex md = ireindex (erase md)

  reindex-shape : ∀ {j} (R : Srt.Poly j) {ηA ηB dA dB} → MorD ηA ηB dA dB → TA.⟦ R ⟧shape ηA → TB.⟦ R ⟧shape ηB
  reindex-shape R md = ireindex-shape R (erase md)

  apply : ∀ {k} {ρA ρB dA dB} (md : MorD {k} ρA ρB dA dB) (v : Fin k) → TA.El (ρA v) → TB.El (ρB v)
  apply md = iapply (erase md)

  reindex-resp : ∀ {k} {R : Srt.Poly (suc k)} {ρA ρB dA dB} (md : MorD ρA ρB dA dB) {t t' : TA.W R ρA} →
                 TA.W-≈ t t' → TB.W-≈ (reindex md t) (reindex md t')
  reindex-resp md {t} {t'} = ireindex-resp (erase md) {t} {t'}

  reindex-shape-resp : ∀ {j} (R : Srt.Poly j) {ηA ηB dA dB} (md : MorD ηA ηB dA dB) {a a' : TA.⟦ R ⟧shape ηA} →
                       TA.shape≈ R ηA a a' → TB.shape≈ R ηB (reindex-shape R md a) (reindex-shape R md a')
  reindex-shape-resp R md {a} {a'} = ireindex-shape-resp R (erase md) {a} {a'}

  apply-resp : ∀ {k} {ρA ρB dA dB} (md : MorD {k} ρA ρB dA dB) (v : Fin k) {a a'} →
               TA.elEq (ρA v) a a' → TB.elEq (ρB v) (apply md v a) (apply md v a')
  apply-resp md v {a} {a'} = iapply-resp (erase md) v {a} {a'}

  -- The fibre side of `reindex`: a 𝒞-morphism into the reindexed fibre.
  mutual
    reindex-fam : ∀ {j} (R : Poly j) {ηA ηB dA dB} (md : MorD ηA ηB dA dB) {a : TA.⟦ ∣ R ∣ ⟧shape ηA} →
                  TA.fib-shape R dA a ⇒ TB.fib-shape R dB (reindex-shape ∣ R ∣ md a)
    reindex-fam (const A) md = id _
    reindex-fam (var v) md {a} = apply-fam md v a
    reindex-fam (P + Q) md {inj₁ a} = Lmap (reindex-fam P md)
    reindex-fam (P + Q) md {inj₂ b} = Lmap (reindex-fam Q md)
    reindex-fam (P × Q) md {a , b} = Lmap (prod-m (reindex-fam P md) (reindex-fam Q md))
    reindex-fam (μ Q') md {t} = reindex-fam-W md {t}

    reindex-fam-W : ∀ {k} {Q : Poly (suc k)} {ρA ρB dA dB} (md : MorD ρA ρB dA dB) {t : TA.W ∣ Q ∣ ρA} →
                    TA.fib Q dA t ⇒ TB.fib Q dB (reindex md t)
    reindex-fam-W {Q = Q} md {TA.sup x} = reindex-fam Q (bind Q md)

    apply-fam : ∀ {k} {ρA ρB dA dB} (md : MorD {k} ρA ρB dA dB) (v : Fin k) (a : TA.El (ρA v)) →
                TA.fib-el (ρA v) (dA v) a ⇒ TB.fib-el (ρB v) (dB v) (apply md v a)
    apply-fam (base _ _ ffam _) v a = ffam v a
    apply-fam (bind Q md) Fin.zero a = reindex-fam-W md {a}
    apply-fam (bind Q md) (Fin.suc v) a = apply-fam md v a

  -- The fibre reindex commutes with subst (naturality).
  mutual
    reindex-fam-natural : ∀ {j} (R : Poly j) {ηA ηB dA dB} (md : MorD ηA ηB dA dB)
                      {a a' : TA.⟦ ∣ R ∣ ⟧shape ηA} (p : TA.shape≈ ∣ R ∣ ηA a a') →
                      (reindex-fam R md {a'} ∘ TA.fib-shape-subst R dA p)
                        ≈ (TB.fib-shape-subst R dB (reindex-shape-resp ∣ R ∣ md p) ∘ reindex-fam R md {a})
    reindex-fam-natural (const A) md p = ≈-trans id-left (≈-sym id-right)
    reindex-fam-natural (var v)   md {a} {a'} p = apply-fam-natural md v {a} {a'} p
    reindex-fam-natural (P + Q) md {inj₁ a} {inj₁ a'} p =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong (reindex-fam-natural P md p)) (Lmap-comp _ _))
    reindex-fam-natural (P + Q) md {inj₂ b} {inj₂ b'} p =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong (reindex-fam-natural Q md p)) (Lmap-comp _ _))
    reindex-fam-natural (P × Q) md {a , b} {a' , b'} (p₁ , p₂) =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong
                 (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                  (≈-trans (prod-m-cong (reindex-fam-natural P md p₁) (reindex-fam-natural Q md p₂))
                           (prod-m-comp _ _ _ _))))
               (Lmap-comp _ _))
    reindex-fam-natural (μ Q') md {t} {t'} p = reindex-fam-W-natural md {t} {t'} p

    reindex-fam-W-natural : ∀ {k} {Q : Poly (suc k)} {ρA ρB dA dB} (md : MorD ρA ρB dA dB)
                        {t t' : TA.W ∣ Q ∣ ρA} (p : TA.W-≈ t t') →
                        (reindex-fam-W md {t'} ∘ TA.fib-subst Q dA {x = t} {y = t'} p)
                          ≈ (TB.fib-subst Q dB {x = reindex md t} {y = reindex md t'}
                                          (reindex-resp md {t} {t'} p) ∘ reindex-fam-W md {t})
    reindex-fam-W-natural {Q = Q} md {TA.sup x} {TA.sup y} p = reindex-fam-natural Q (bind Q md) {x} {y} p

    apply-fam-natural : ∀ {k} {ρA ρB dA dB} (md : MorD {k} ρA ρB dA dB) (v : Fin k) {a a'}
                    (p : TA.elEq (ρA v) a a') →
                    (apply-fam md v a' ∘ TA.fib-el-subst (ρA v) (dA v) p)
                      ≈ (TB.fib-el-subst (ρB v) (dB v) (apply-resp md v p) ∘ apply-fam md v a)
    apply-fam-natural (base _ _ _ ffam-natural) v p = ffam-natural v p
    apply-fam-natural (bind Q md) Fin.zero    {a} {a'} p = reindex-fam-W-natural md {a} {a'} p
    apply-fam-natural (bind Q md) (Fin.suc v) p = apply-fam-natural md v p

module ReindexSection {nA nB} {δA : Fin nA → Obj} {δB : Fin nB → Obj}
    (δAc : ∀ i → Section (δA i)) (δBc : ∀ i → Section (δB i)) where
  private
    module TA = Tree δA
    module TB = Tree δB
    module MA = MuSection δA δAc
    module MB = MuSection δB δBc
  open Reindex δA δB

  data MorDSec : ∀ {k} {ρA : Fin k → Fin nA ⊎ Sort nA} {ρB : Fin k → Fin nB ⊎ Sort nB}
                 {dA : ∀ v → TA.DecoAssign (ρA v)} {dB : ∀ v → TB.DecoAssign (ρB v)} →
                 MorD ρA ρB dA dB → (∀ v → MA.DecoAssignSection (dA v)) →
                 (∀ v → MB.DecoAssignSection (dB v)) → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    base-s : ∀ {k} {ρA : Fin k → Fin nA ⊎ Sort nA} {ρB : Fin k → Fin nB ⊎ Sort nB}
             {dA : ∀ v → TA.DecoAssign (ρA v)} {dB : ∀ v → TB.DecoAssign (ρB v)}
             {f : ∀ v → TA.El (ρA v) → TB.El (ρB v)}
             {f-resp : ∀ v {a a'} → TA.elEq (ρA v) a a' → TB.elEq (ρB v) (f v a) (f v a')}
             {ffam : ∀ v a → TA.fib-el (ρA v) (dA v) a ⇒ TB.fib-el (ρB v) (dB v) (f v a)}
             {ffam-natural : ∀ v {a a'} (p : TA.elEq (ρA v) a a') →
                (ffam v a' ∘ TA.fib-el-subst (ρA v) (dA v) p)
                  ≈ (TB.fib-el-subst (ρB v) (dB v) (f-resp v p) ∘ ffam v a)}
             {dAc : ∀ v → MA.DecoAssignSection (dA v)} {dBc : ∀ v → MB.DecoAssignSection (dB v)} →
             (∀ v a → (ffam v a ∘ MA.fib-el-unit (ρA v) (dA v) (dAc v) a)
                      ≈ MB.fib-el-unit (ρB v) (dB v) (dBc v) (f v a)) →
             MorDSec (base {ρA = ρA} {ρB = ρB} {dA = dA} {dB = dB} f f-resp ffam ffam-natural) dAc dBc
    bind-s : ∀ {k} {ρA ρB dA dB} {md : MorD {k} ρA ρB dA dB} {dAc dBc} (Q : Poly (suc k))
             (Qc : PolySection Q) → MorDSec md dAc dBc →
             MorDSec (bind Q md) (MA.deco-ext-section Q Qc dAc) (MB.deco-ext-section Q Qc dBc)

  mutual
    reindex-fam-unit : ∀ {j} (R : Poly j) (Rc : PolySection R) {ηA ηB dA dB}
      {md : MorD ηA ηB dA dB} {dAc dBc} → MorDSec md dAc dBc →
      ∀ (a : TA.⟦ ∣ R ∣ ⟧shape ηA) →
      (reindex-fam R md {a} ∘ MA.fib-shape-unit R dA Rc dAc a)
        ≈ MB.fib-shape-unit R dB Rc dBc (reindex-shape ∣ R ∣ md a)
    reindex-fam-unit (const A) Ac ms a = id-left
    reindex-fam-unit (var v)   _  ms a = apply-fam-unit ms v a
    reindex-fam-unit (P' + Q') (P'c , Q'c) ms (inj₁ a) =
      ≈-trans (L-elem-natural _ _) (L-elem-cong (reindex-fam-unit P' P'c ms a))
    reindex-fam-unit (P' + Q') (P'c , Q'c) ms (inj₂ b) =
      ≈-trans (L-elem-natural _ _) (L-elem-cong (reindex-fam-unit Q' Q'c ms b))
    reindex-fam-unit (P' × Q') (P'c , Q'c) ms (a , b) =
      ≈-trans (L-elem-natural _ _)
        (L-elem-cong (≈-trans (pair-compose _ _ _ _)
          (pair-cong (reindex-fam-unit P' P'c ms a) (reindex-fam-unit Q' Q'c ms b))))
    reindex-fam-unit (μ Q') Q'c ms t = reindex-fam-W-unit Q'c ms t

    reindex-fam-W-unit : ∀ {k} {Q : Poly (suc k)} (Qc : PolySection Q) {ρA ρB dA dB}
      {md : MorD ρA ρB dA dB} {dAc dBc} → MorDSec md dAc dBc → ∀ (t : TA.W ∣ Q ∣ ρA) →
      (reindex-fam-W md {t} ∘ MA.fib-unit Q dA Qc dAc t)
        ≈ MB.fib-unit Q dB Qc dBc (reindex md t)
    reindex-fam-W-unit {Q = Q} Qc ms (TA.sup x) = reindex-fam-unit Q Qc (bind-s Q Qc ms) x

    apply-fam-unit : ∀ {k} {ρA ρB dA dB} {md : MorD {k} ρA ρB dA dB} {dAc dBc} →
      MorDSec md dAc dBc → ∀ (v : Fin k) (a : TA.El (ρA v)) →
      (apply-fam md v a ∘ MA.fib-el-unit (ρA v) (dA v) (dAc v) a)
        ≈ MB.fib-el-unit (ρB v) (dB v) (dBc v) (apply md v a)
    apply-fam-unit (base-s h)       v a = h v a
    apply-fam-unit (bind-s Q Qc ms) Fin.zero    a = reindex-fam-W-unit Qc ms a
    apply-fam-unit (bind-s Q Qc ms) (Fin.suc v) a = apply-fam-unit ms v a

-- Fibre reindex over an index-only reindex `cmb`, driven by an "external" per-variable action `act`: a
-- fold's fibre action is Γ-dependent, so it can't live in a reindex morphism and is carried separately.
-- The ambient Γ-fibre is `G`.
module FReindex {nA nB} {δA : Fin nA → Obj} {δB : Fin nB → Obj} (G : obj) where
  private
    module TA = Tree δA
    module TB = Tree δB
  open Reindex δA δB using (IMorD; ireindex; ireindex-shape; iapply; ibind)

  -- Defunctionalised action: `abase` supplies all var fibres directly (a Γ-dependent fold);
  -- `abind` extends across a binder. Data (not a function) so the recursion stays structural.
  data FAct : ∀ {k} {ρA : Fin k → Fin nA ⊎ Sort nA} {ρB : Fin k → Fin nB ⊎ Sort nB} →
              IMorD ρA ρB → (∀ v → TA.DecoAssign (ρA v)) → (∀ v → TB.DecoAssign (ρB v)) →
              Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    abase : ∀ {k} {ρA ρB} {cmb : IMorD {k} ρA ρB} {dA dB}
            (afib : ∀ v (a : TA.El (ρA v)) → prod G (TA.fib-el (ρA v) (dA v) a) ⇒ TB.fib-el (ρB v) (dB v) (iapply cmb v a)) →
            FAct cmb dA dB
    abind : ∀ {k} {ρA ρB} (Q : Poly (suc k)) (cmb : IMorD ρA ρB) {dA dB} → FAct cmb dA dB →
            FAct (ibind ∣ Q ∣ cmb) (TA.deco-ext Q dA) (TB.deco-ext Q dB)

  mutual
    freindex-fam : ∀ {k} {Q : Poly (suc k)} {ρA ρB} {cmb : IMorD ρA ρB} {dA dB} (act : FAct cmb dA dB)
                   {t : TA.W ∣ Q ∣ ρA} → prod G (TA.fib Q dA t) ⇒ TB.fib Q dB (ireindex cmb t)
    freindex-fam {Q = Q} {cmb = cmb} act {TA.sup x} = freindex-shape-fam Q (abind Q cmb act) {x}

    freindex-shape-fam : ∀ {j} (R : Poly j) {ηA ηB} {cmb : IMorD ηA ηB} {dA dB} (act : FAct cmb dA dB)
                         {a : TA.⟦ ∣ R ∣ ⟧shape ηA} →
                         prod G (TA.fib-shape R dA a) ⇒ TB.fib-shape R dB (ireindex-shape ∣ R ∣ cmb a)
    freindex-shape-fam (const A') act = p₂
    freindex-shape-fam (var v)    act {a} = aapply act v a
    freindex-shape-fam (P + Q) act {inj₁ a} = strong-Lmap (freindex-shape-fam P act {a})
    freindex-shape-fam (P + Q) act {inj₂ b} = strong-Lmap (freindex-shape-fam Q act {b})
    freindex-shape-fam (P × Q) act {a , b} =
      strong-Lmap (strong-prod-m (freindex-shape-fam P act {a}) (freindex-shape-fam Q act {b}))
    freindex-shape-fam (μ Q') act {t} = freindex-fam act {t}

    aapply : ∀ {k} {ρA ρB} {cmb : IMorD {k} ρA ρB} {dA dB} (act : FAct cmb dA dB) (v : Fin k) (a : TA.El (ρA v)) →
             prod G (TA.fib-el (ρA v) (dA v) a) ⇒ TB.fib-el (ρB v) (dB v) (iapply cmb v a)
    aapply (abase afib)      v           a = afib v a
    aapply (abind Q cmb act) Fin.zero    a = freindex-fam act {a}
    aapply (abind Q cmb act) (Fin.suc v) a = aapply act v a

------------------------------------------------------------------------------
-- The strong catamorphism: folding a μ-carrier in an ambient context Γ, so no
-- exponentials are required. FMor is the fold-specific reindex morphism, again
-- first-order for termination, carrying the decorations of both sides.
------------------------------------------------------------------------------

-- The fold (catamorphism) for the μ-type, lifted to a standalone module so its
-- mutual recursion is termination-checked independently of the `hasMu` copattern.
-- The fold-specific reindex morphism, shared by the fold and by the application of an algebra to a
-- candidate: `fbase` sends the outer recursion slot to the recursive map and parameters to
-- themselves; `fbind` records a binder.
module FoldBase {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj} where
    module Tδ = Tree δ
    module TA' = Tree (extend δ A)
    data FMor : ∀ {k} (ρ : Fin k → Fin n ⊎ Sort n) (ρ' : Fin k → Fin (suc n) ⊎ Sort (suc n)) →
                (∀ v → Tδ.DecoAssign (ρ v)) → (∀ v → TA'.DecoAssign (ρ' v)) →
                Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      fbase : FMor (Srt.η₀ ∣ P ∣) (λ v → inj₁ v)
                   (Tδ.deco-ext P {ρ̄ = λ i → inj₁ i} (λ i → lift tt)) (λ v → lift tt)
      fbind : ∀ {k} {ρ ρ' d d'} (Q : Poly (suc k)) → FMor ρ ρ' d d' →
              FMor (extend ρ (inj₂ (mkSort ∣ Q ∣ ρ))) (extend ρ' (inj₂ (mkSort ∣ Q ∣ ρ')))
                   (Tδ.deco-ext Q d) (TA'.deco-ext Q d')

module FoldDef {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
               (alg : Mor (Fam𝒞-P.prod Γ (fobj μ-fam P (extend δ A))) A) where
    open FoldBase {n} {Γ} {A} {P} {δ} public
    -- Fold the outer μ via `alg`; nested μ are reindexed into the `extend δ A` context,
    -- the recursion slot carrying the fold itself (inlined, so every call is structural).
    mutual
      fold-idx : Γ .idx .Carrier → Tδ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier
      fold-idx γ (Tδ.sup x) = alg .idxf .PS._⇒_.func (γ , fold-shape-idx P γ x)

      fold-shape-idx : (Q : Poly (suc n)) → Γ .idx .Carrier → Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣) →
                      fobj μ-fam Q (extend δ A) .idx .Carrier
      fold-shape-idx (const A')        γ a = a
      fold-shape-idx (var Fin.zero)    γ t = fold-idx γ t
      fold-shape-idx (var (Fin.suc i)) γ a = a
      fold-shape-idx (Q₁ + Q₂) γ (inj₁ x) = inj₁ (fold-shape-idx Q₁ γ x)
      fold-shape-idx (Q₁ + Q₂) γ (inj₂ y) = inj₂ (fold-shape-idx Q₂ γ y)
      fold-shape-idx (Q₁ × Q₂) γ (x , y) = fold-shape-idx Q₁ γ x , fold-shape-idx Q₂ γ y
      fold-shape-idx (μ Q')    γ t = fold-reindex {Q = Q'} γ fbase t

      fold-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') →
                     Tδ.W ∣ Q ∣ ρ → TA'.W ∣ Q ∣ ρ'
      fold-reindex {Q = Q} γ fm (Tδ.sup x) = TA'.sup (fold-reindex-shape γ Q (fbind Q fm) x)

      fold-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB) →
                           Tδ.⟦ ∣ R ∣ ⟧shape ηA → TA'.⟦ ∣ R ∣ ⟧shape ηB
      fold-reindex-shape γ (const A') fm a = a
      fold-reindex-shape γ (var v)    fm a = fold-apply γ fm v a
      fold-reindex-shape γ (P' + Q') fm (inj₁ a) = inj₁ (fold-reindex-shape γ P' fm a)
      fold-reindex-shape γ (P' + Q') fm (inj₂ b) = inj₂ (fold-reindex-shape γ Q' fm b)
      fold-reindex-shape γ (P' × Q') fm (a , b) = fold-reindex-shape γ P' fm a , fold-reindex-shape γ Q' fm b
      fold-reindex-shape γ (μ Q'')   fm t = fold-reindex {Q = Q''} γ fm t

      fold-apply : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k) →
                   Tδ.El (ρ v) → TA'.El (ρ' v)
      fold-apply γ fbase        Fin.zero    t = fold-idx γ t
      fold-apply γ fbase        (Fin.suc i) a = a
      fold-apply γ (fbind Q fm) Fin.zero    a = fold-reindex {Q = Q} γ fm a
      fold-apply γ (fbind Q fm) (Fin.suc v) a = fold-apply γ fm v a

    -- The index fold respects ≈ (in both Γ and the tree).
    mutual
      fold-idx-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : Tδ.W-≈ t t') →
                      _≈s_ (A .idx) (fold-idx γ t) (fold-idx γ' t')
      fold-idx-resp γ≈ {Tδ.sup x} {Tδ.sup y} p = alg .idxf .PS._⇒_.func-resp-≈ (γ≈ , fold-shape-idx-resp P γ≈ p)

      fold-shape-idx-resp : (Q : Poly (suc n)) → ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {x x'}
                           (p : Tδ.shape≈ ∣ Q ∣ (Srt.η₀ ∣ P ∣) x x') →
                           _≈s_ (fobj μ-fam Q (extend δ A) .idx) (fold-shape-idx Q γ x) (fold-shape-idx Q γ' x')
      fold-shape-idx-resp (const A')        γ≈ p = p
      fold-shape-idx-resp (var Fin.zero)    γ≈ {x} {x'} p = fold-idx-resp γ≈ {x} {x'} p
      fold-shape-idx-resp (var (Fin.suc i)) γ≈ p = p
      fold-shape-idx-resp (Q₁ + Q₂) γ≈ {inj₁ _} {inj₁ _} p = fold-shape-idx-resp Q₁ γ≈ p
      fold-shape-idx-resp (Q₁ + Q₂) γ≈ {inj₂ _} {inj₂ _} p = fold-shape-idx-resp Q₂ γ≈ p
      fold-shape-idx-resp (Q₁ × Q₂) γ≈ {_ , _} {_ , _} (p₁ , p₂) =
        fold-shape-idx-resp Q₁ γ≈ p₁ , fold-shape-idx-resp Q₂ γ≈ p₂
      fold-shape-idx-resp (μ Q')    γ≈ {x} {x'} p = fold-reindex-resp {Q = Q'} γ≈ fbase {x} {x'} p

      fold-reindex-resp : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (fm : FMor ρ ρ' d d')
                          {t t' : Tδ.W ∣ Q ∣ ρ} (p : Tδ.W-≈ t t') →
                          TA'.W-≈ (fold-reindex γ fm t) (fold-reindex γ' fm t')
      fold-reindex-resp {Q = Q} γ≈ fm {Tδ.sup x} {Tδ.sup y} p = fold-reindex-shape-resp γ≈ Q (fbind Q fm) {x} {y} p

      fold-reindex-shape-resp : ∀ {j} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB)
                                {a a' : Tδ.⟦ ∣ R ∣ ⟧shape ηA} (p : Tδ.shape≈ ∣ R ∣ ηA a a') →
                                TA'.shape≈ ∣ R ∣ ηB (fold-reindex-shape γ R fm a) (fold-reindex-shape γ' R fm a')
      fold-reindex-shape-resp γ≈ (const A') fm p = p
      fold-reindex-shape-resp γ≈ (var v)    fm p = fold-apply-resp γ≈ fm v p
      fold-reindex-shape-resp γ≈ (P' + Q') fm {inj₁ _} {inj₁ _} p = fold-reindex-shape-resp γ≈ P' fm p
      fold-reindex-shape-resp γ≈ (P' + Q') fm {inj₂ _} {inj₂ _} p = fold-reindex-shape-resp γ≈ Q' fm p
      fold-reindex-shape-resp γ≈ (P' × Q') fm {_ , _} {_ , _} (p₁ , p₂) =
        fold-reindex-shape-resp γ≈ P' fm p₁ , fold-reindex-shape-resp γ≈ Q' fm p₂
      fold-reindex-shape-resp γ≈ (μ Q'')   fm {a} {a'} p = fold-reindex-resp {Q = Q''} γ≈ fm {a} {a'} p

      fold-apply-resp : ∀ {k} {ρ ρ' d d'} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (fm : FMor ρ ρ' d d') (v : Fin k)
                        {a a'} (p : Tδ.elEq (ρ v) a a') →
                        TA'.elEq (ρ' v) (fold-apply γ fm v a) (fold-apply γ' fm v a')
      fold-apply-resp γ≈ fbase        Fin.zero    {a} {a'} p = fold-idx-resp γ≈ {a} {a'} p
      fold-apply-resp γ≈ fbase        (Fin.suc i) p = p
      fold-apply-resp γ≈ (fbind Q fm) Fin.zero    {a} {a'} p = fold-reindex-resp {Q = Q} γ≈ fm {a} {a'} p
      fold-apply-resp γ≈ (fbind Q fm) (Fin.suc v) p = fold-apply-resp γ≈ fm v p

    -- The fibre fold: collapse the tree's fibre via `alg.famf`, threading the Γ-fibre.
    mutual
      fold-fam : (γ : Γ .idx .Carrier) (t : Tδ.W ∣ P ∣ (λ i → inj₁ i)) →
                 prod (Γ .fam .fm γ) (Tδ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (fold-idx γ t)
      fold-fam γ (Tδ.sup x) =
        alg .famf ._⇒f_.transf (γ , fold-shape-idx P γ x) ∘ pair p₁ (fold-shape-fam P γ x)

      fold-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                       prod (Γ .fam .fm γ) (Tδ.fib-shape Q (Tδ.deco-ext P (λ i → lift tt)) x)
                         ⇒ fobj μ-fam Q (extend δ A) .fam .fm (fold-shape-idx Q γ x)
      fold-shape-fam (const A')        γ a = p₂
      fold-shape-fam (var Fin.zero)    γ t = fold-fam γ t
      fold-shape-fam (var (Fin.suc i)) γ a = p₂
      fold-shape-fam (Q₁ + Q₂) γ (inj₁ x) = strong-Lmap (fold-shape-fam Q₁ γ x)
      fold-shape-fam (Q₁ + Q₂) γ (inj₂ y) = strong-Lmap (fold-shape-fam Q₂ γ y)
      fold-shape-fam (Q₁ × Q₂) γ (x , y) =
        strong-Lmap (strong-prod-m (fold-shape-fam Q₁ γ x) (fold-shape-fam Q₂ γ y))
      fold-shape-fam (μ Q')    γ t = fold-reindex-fam {Q = Q'} γ fbase t

      fold-reindex-fam : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ' d d') (t : Tδ.W ∣ Q ∣ ρ) →
                         prod (Γ .fam .fm γ) (Tδ.fib Q d t) ⇒ TA'.fib Q d' (fold-reindex γ md t)
      fold-reindex-fam {Q = Q} γ md (Tδ.sup x) = fold-reindex-shape-fam γ Q (fbind Q md) x

      fold-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (md : FMor ηA ηB dA dB) (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                               prod (Γ .fam .fm γ) (Tδ.fib-shape R dA a) ⇒ TA'.fib-shape R dB (fold-reindex-shape γ R md a)
      fold-reindex-shape-fam γ (const A') md a = p₂
      fold-reindex-shape-fam γ (var v)    md a = fold-apply-fam γ md v a
      fold-reindex-shape-fam γ (P' + Q') md (inj₁ a) = strong-Lmap (fold-reindex-shape-fam γ P' md a)
      fold-reindex-shape-fam γ (P' + Q') md (inj₂ b) = strong-Lmap (fold-reindex-shape-fam γ Q' md b)
      fold-reindex-shape-fam γ (P' × Q') md (a , b) =
        strong-Lmap (strong-prod-m (fold-reindex-shape-fam γ P' md a) (fold-reindex-shape-fam γ Q' md b))
      fold-reindex-shape-fam γ (μ Q'')   md t = fold-reindex-fam {Q = Q''} γ md t

      fold-apply-fam : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ' d d') (v : Fin k) (a : Tδ.El (ρ v)) →
                       prod (Γ .fam .fm γ) (Tδ.fib-el (ρ v) (d v) a) ⇒ TA'.fib-el (ρ' v) (d' v) (fold-apply γ md v a)
      fold-apply-fam γ fbase        Fin.zero    t = fold-fam γ t
      fold-apply-fam γ fbase        (Fin.suc i) a = p₂
      fold-apply-fam γ (fbind Q md) Fin.zero    a = fold-reindex-fam {Q = Q} γ md a
      fold-apply-fam γ (fbind Q md) (Fin.suc v) a = fold-apply-fam γ md v a

    -- The fibre fold is natural: it commutes with `subst` (in both Γ and the tree).
    mutual
      fold-fam-natural : ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {t t'} (p : Tδ.W-≈ t t') →
                         fold-fam γ₂ t' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-subst P (λ i → lift tt) {x = t} {y = t'} p) ≈
                         A .fam .subst (fold-idx-resp γ≈ {t} {t'} p) ∘ fold-fam γ₁ t
      fold-fam-natural {γ₁} {γ₂} γ≈ {Tδ.sup x} {Tδ.sup y} p =
        ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (pair-natural _ _ _))
        (≈-trans (∘-cong ≈-refl (pair-cong (pair-p₁ _ _) (fold-shape-fam-natural P γ≈ {x} {y} p)))
        (≈-trans (∘-cong ≈-refl (≈-sym (pair-compose _ _ _ _)))
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong (alg .famf ._⇒f_.natural (γ≈ , fold-shape-idx-resp P γ≈ {x} {y} p)) ≈-refl)
                 (assoc _ _ _))))))

      fold-shape-fam-natural : (Q : Poly (suc n)) → ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {x x'}
                               (p : Tδ.shape≈ ∣ Q ∣ (Srt.η₀ ∣ P ∣) x x') →
                               fold-shape-fam Q γ₂ x' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-shape-subst Q (Tδ.deco-ext P (λ i → lift tt)) p) ≈
                               fobj μ-fam Q (extend δ A) .fam .subst (fold-shape-idx-resp Q γ≈ p) ∘ fold-shape-fam Q γ₁ x
      fold-shape-fam-natural (const A')        γ≈ p = pair-p₂ _ _
      fold-shape-fam-natural (var Fin.zero)    γ≈ {x} {x'} p = fold-fam-natural γ≈ {x} {x'} p
      fold-shape-fam-natural (var (Fin.suc i)) γ≈ p = pair-p₂ _ _
      fold-shape-fam-natural (Q₁ + Q₂) {γ₁} {γ₂} γ≈ {inj₁ x} {inj₁ x'} p =
        strong-Lmap-natural (Γ .fam .subst γ≈)
          (Tδ.fib-shape-subst Q₁ (Tδ.deco-ext P (λ i → lift tt)) p)
          (fobj μ-fam Q₁ (extend δ A) .fam .subst (fold-shape-idx-resp Q₁ γ≈ p))
          (fold-shape-fam Q₁ γ₁ x) (fold-shape-fam Q₁ γ₂ x')
          (fold-shape-fam-natural Q₁ γ≈ p)
      fold-shape-fam-natural (Q₁ + Q₂) {γ₁} {γ₂} γ≈ {inj₂ y} {inj₂ y'} p =
        strong-Lmap-natural (Γ .fam .subst γ≈)
          (Tδ.fib-shape-subst Q₂ (Tδ.deco-ext P (λ i → lift tt)) p)
          (fobj μ-fam Q₂ (extend δ A) .fam .subst (fold-shape-idx-resp Q₂ γ≈ p))
          (fold-shape-fam Q₂ γ₁ y) (fold-shape-fam Q₂ γ₂ y')
          (fold-shape-fam-natural Q₂ γ≈ p)
      fold-shape-fam-natural (Q₁ × Q₂) {γ₁} {γ₂} γ≈ {x₁ , x₂} {x₁' , x₂'} (p₁p , p₂p) =
        strong-Lmap-natural (Γ .fam .subst γ≈)
          (prod-m (Tδ.fib-shape-subst Q₁ (Tδ.deco-ext P (λ i → lift tt)) p₁p)
                  (Tδ.fib-shape-subst Q₂ (Tδ.deco-ext P (λ i → lift tt)) p₂p))
          (prod-m (fobj μ-fam Q₁ (extend δ A) .fam .subst (fold-shape-idx-resp Q₁ γ≈ p₁p))
                  (fobj μ-fam Q₂ (extend δ A) .fam .subst (fold-shape-idx-resp Q₂ γ≈ p₂p)))
          (strong-prod-m (fold-shape-fam Q₁ γ₁ x₁) (fold-shape-fam Q₂ γ₁ x₂))
          (strong-prod-m (fold-shape-fam Q₁ γ₂ x₁') (fold-shape-fam Q₂ γ₂ x₂'))
          (strong-prod-m-natural (fold-shape-fam-natural Q₁ γ≈ p₁p) (fold-shape-fam-natural Q₂ γ≈ p₂p))
      fold-shape-fam-natural (μ Q')    γ≈ {x} {x'} p = fold-reindex-fam-natural {Q = Q'} γ≈ fbase {x} {x'} p

      fold-reindex-fam-natural : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂)
                             (md : FMor ρ ρ' d d') {t t' : Tδ.W ∣ Q ∣ ρ} (p : Tδ.W-≈ t t') →
                             (fold-reindex-fam γ₂ md t' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-subst Q d {x = t} {y = t'} p))
                               ≈ (TA'.fib-subst Q d' {x = fold-reindex γ₁ md t} {y = fold-reindex γ₂ md t'}
                                                (fold-reindex-resp γ≈ md {t} {t'} p) ∘ fold-reindex-fam γ₁ md t)
      fold-reindex-fam-natural {Q = Q} γ≈ md {Tδ.sup x} {Tδ.sup y} p = fold-reindex-shape-fam-natural γ≈ Q (fbind Q md) {x} {y} p

      fold-reindex-shape-fam-natural : ∀ {j} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (R : Poly j) {ηA ηB dA dB} (md : FMor ηA ηB dA dB)
                                   {a a' : Tδ.⟦ ∣ R ∣ ⟧shape ηA} (p : Tδ.shape≈ ∣ R ∣ ηA a a') →
                                   (fold-reindex-shape-fam γ₂ R md a' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-shape-subst R dA p))
                                     ≈ (TA'.fib-shape-subst R dB (fold-reindex-shape-resp γ≈ R md p) ∘ fold-reindex-shape-fam γ₁ R md a)
      fold-reindex-shape-fam-natural γ≈ (const A') md p = pair-p₂ _ _
      fold-reindex-shape-fam-natural γ≈ (var v)    md p = fold-apply-fam-natural γ≈ md v p
      fold-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' + Q') {dA = dA} {dB} md {inj₁ a} {inj₁ a'} p =
        strong-Lmap-natural (Γ .fam .subst γ≈)
          (Tδ.fib-shape-subst P' dA p)
          (TA'.fib-shape-subst P' dB (fold-reindex-shape-resp γ≈ P' md p))
          (fold-reindex-shape-fam γ₁ P' md a) (fold-reindex-shape-fam γ₂ P' md a')
          (fold-reindex-shape-fam-natural γ≈ P' md p)
      fold-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' + Q') {dA = dA} {dB} md {inj₂ b} {inj₂ b'} p =
        strong-Lmap-natural (Γ .fam .subst γ≈)
          (Tδ.fib-shape-subst Q' dA p)
          (TA'.fib-shape-subst Q' dB (fold-reindex-shape-resp γ≈ Q' md p))
          (fold-reindex-shape-fam γ₁ Q' md b) (fold-reindex-shape-fam γ₂ Q' md b')
          (fold-reindex-shape-fam-natural γ≈ Q' md p)
      fold-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' × Q') {dA = dA} {dB} md {a₁ , a₂} {a₁' , a₂'} (p₁p , p₂p) =
        strong-Lmap-natural (Γ .fam .subst γ≈)
          (prod-m (Tδ.fib-shape-subst P' dA p₁p) (Tδ.fib-shape-subst Q' dA p₂p))
          (prod-m (TA'.fib-shape-subst P' dB (fold-reindex-shape-resp γ≈ P' md p₁p))
                  (TA'.fib-shape-subst Q' dB (fold-reindex-shape-resp γ≈ Q' md p₂p)))
          (strong-prod-m (fold-reindex-shape-fam γ₁ P' md a₁) (fold-reindex-shape-fam γ₁ Q' md a₂))
          (strong-prod-m (fold-reindex-shape-fam γ₂ P' md a₁') (fold-reindex-shape-fam γ₂ Q' md a₂'))
          (strong-prod-m-natural (fold-reindex-shape-fam-natural γ≈ P' md p₁p)
                                 (fold-reindex-shape-fam-natural γ≈ Q' md p₂p))
      fold-reindex-shape-fam-natural γ≈ (μ Q'')   md {a} {a'} p = fold-reindex-fam-natural {Q = Q''} γ≈ md {a} {a'} p

      fold-apply-fam-natural : ∀ {k} {ρ ρ' d d'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (md : FMor ρ ρ' d d') (v : Fin k)
                               {a a'} (p : Tδ.elEq (ρ v) a a') →
                               fold-apply-fam γ₂ md v a' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-el-subst (ρ v) (d v) p) ≈
                               TA'.fib-el-subst (ρ' v) (d' v) (fold-apply-resp γ≈ md v p) ∘ fold-apply-fam γ₁ md v a
      fold-apply-fam-natural γ≈ fbase        Fin.zero    {a} {a'} p = fold-fam-natural γ≈ {a} {a'} p
      fold-apply-fam-natural γ≈ fbase        (Fin.suc i) p = pair-p₂ _ _
      fold-apply-fam-natural γ≈ (fbind Q md) Fin.zero    {a} {a'} p = fold-reindex-fam-natural {Q = Q} γ≈ md {a} {a'} p
      fold-apply-fam-natural γ≈ (fbind Q md) (Fin.suc v) p = fold-apply-fam-natural γ≈ md v p

    foldMor : Mor (Fam𝒞-P.prod Γ (μ-fam P δ)) A
    foldMor .idxf .PS._⇒_.func (γ , t) = fold-idx γ t
    foldMor .idxf .PS._⇒_.func-resp-≈ {γ , t} {γ' , t'} (γ≈ , t≈) = fold-idx-resp γ≈ {t} {t'} t≈
    foldMor .famf ._⇒f_.transf (γ , t) = fold-fam γ t
    foldMor .famf ._⇒f_.natural {γ₁ , t₁} {γ₂ , t₂} (γ≈ , t≈) = fold-fam-natural γ≈ {t₁} {t₂} t≈

module FoldSection {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (alg : Mor (Fam𝒞-P.prod Γ (fobj μ-fam P (extend δ A))) A)
    (δc : ∀ i → Section (δ i)) (cA : Section A) (Pc : PolySection P) where

  open FoldDef {n} {Γ} {A} {P} {δ} alg
  private
    module Mδ = MuSection δ δc
    module MA' = MuSection (extend δ A) (extend-section δc cA)

  data FMorSec : ∀ {k} {ρ : Fin k → Fin n ⊎ Sort n} {ρ' : Fin k → Fin (suc n) ⊎ Sort (suc n)}
                 {d : ∀ v → Tδ.DecoAssign (ρ v)} {d' : ∀ v → TA'.DecoAssign (ρ' v)} →
                 FMor ρ ρ' d d' → (∀ v → Mδ.DecoAssignSection (d v)) →
                 (∀ v → MA'.DecoAssignSection (d' v)) → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    fbase-s : FMorSec fbase (Mδ.deco-ext-section P Pc (λ i → lift tt)) (λ v → lift tt)
    fbind-s : ∀ {k} {ρ ρ' d d'} {fm : FMor {k} ρ ρ' d d'} {dc d'c} (Q : Poly (suc k))
              (Qc : PolySection Q) → FMorSec fm dc d'c →
              FMorSec (fbind Q fm) (Mδ.deco-ext-section Q Qc dc) (MA'.deco-ext-section Q Qc d'c)

  module _ (γ : Γ .idx .Carrier) (cγ : 𝟙c ⇒ Γ .fam .fm γ)
           (halg : ∀ s → (alg .famf ._⇒f_.transf (γ , s) ∘
                           pair cγ (poly-section P Pc (extend-section δc cA) .at s))
                         ≈ cA .at (alg .idxf .PS._⇒_.func (γ , s))) where
    mutual
      fold-fam-unit : ∀ t →
        (fold-fam γ t ∘ pair cγ (Mδ.μ-section P Pc .at t)) ≈ cA .at (fold-idx γ t)
      fold-fam-unit (Tδ.sup x) =
        ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (pair-natural _ _ _))
        (≈-trans (∘-cong ≈-refl (pair-cong (pair-p₁ _ _) (fold-shape-fam-unit P Pc x)))
                 (halg (fold-shape-idx P γ x))))

      fold-shape-fam-unit : ∀ (Q : Poly (suc n)) (Qc : PolySection Q)
        (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
        (fold-shape-fam Q γ x ∘
          pair cγ (Mδ.fib-shape-unit Q (Tδ.deco-ext P (λ i → lift tt)) Qc
                     (Mδ.deco-ext-section P Pc (λ i → lift tt)) x))
        ≈ poly-section Q Qc (extend-section δc cA) .at (fold-shape-idx Q γ x)
      fold-shape-fam-unit (const A')        Ac a = pair-p₂ _ _
      fold-shape-fam-unit (var Fin.zero)    _  t = fold-fam-unit t
      fold-shape-fam-unit (var (Fin.suc i)) _  a = pair-p₂ _ _
      fold-shape-fam-unit (Q₁ + Q₂) (Q₁c , Q₂c) (inj₁ x) =
        ≈-trans (strong-Lmap-elem _ _ _) (L-elem-cong (fold-shape-fam-unit Q₁ Q₁c x))
      fold-shape-fam-unit (Q₁ + Q₂) (Q₁c , Q₂c) (inj₂ y) =
        ≈-trans (strong-Lmap-elem _ _ _) (L-elem-cong (fold-shape-fam-unit Q₂ Q₂c y))
      fold-shape-fam-unit (Q₁ × Q₂) (Q₁c , Q₂c) (x , y) =
        ≈-trans (strong-Lmap-elem _ _ _)
          (L-elem-cong (≈-trans (strong-prod-m-pair _ _ _ _ _)
            (pair-cong (fold-shape-fam-unit Q₁ Q₁c x) (fold-shape-fam-unit Q₂ Q₂c y))))
      fold-shape-fam-unit (μ Q') Q'c t = fold-reindex-fam-unit Q'c fbase-s t

      fold-reindex-fam-unit : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} {fm : FMor ρ ρ' d d'}
        {dc : ∀ v → Mδ.DecoAssignSection (d v)} {d'c : ∀ v → MA'.DecoAssignSection (d' v)}
        (Qc : PolySection Q) → FMorSec fm dc d'c → ∀ t →
        (fold-reindex-fam γ fm t ∘ pair cγ (Mδ.fib-unit Q d Qc dc t))
          ≈ MA'.fib-unit Q d' Qc d'c (fold-reindex γ fm t)
      fold-reindex-fam-unit {Q = Q} Qc fs (Tδ.sup x) =
        fold-reindex-shape-fam-unit Q Qc (fbind-s Q Qc fs) x

      fold-reindex-shape-fam-unit : ∀ {j} (R : Poly j) (Rc : PolySection R)
        {ηA : Fin j → Fin n ⊎ Sort n} {ηB : Fin j → Fin (suc n) ⊎ Sort (suc n)}
        {dA : ∀ v → Tδ.DecoAssign (ηA v)} {dB : ∀ v → TA'.DecoAssign (ηB v)}
        {fm : FMor ηA ηB dA dB}
        {dAc : ∀ v → Mδ.DecoAssignSection (dA v)} {dBc : ∀ v → MA'.DecoAssignSection (dB v)} →
        FMorSec fm dAc dBc → ∀ (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
        (fold-reindex-shape-fam γ R fm a ∘ pair cγ (Mδ.fib-shape-unit R dA Rc dAc a))
          ≈ MA'.fib-shape-unit R dB Rc dBc (fold-reindex-shape γ R fm a)
      fold-reindex-shape-fam-unit (const A') Ac fs a = pair-p₂ _ _
      fold-reindex-shape-fam-unit (var v)    _  fs a = fold-apply-fam-unit fs v a
      fold-reindex-shape-fam-unit (P' + Q') (P'c , Q'c) fs (inj₁ a) =
        ≈-trans (strong-Lmap-elem _ _ _) (L-elem-cong (fold-reindex-shape-fam-unit P' P'c fs a))
      fold-reindex-shape-fam-unit (P' + Q') (P'c , Q'c) fs (inj₂ b) =
        ≈-trans (strong-Lmap-elem _ _ _) (L-elem-cong (fold-reindex-shape-fam-unit Q' Q'c fs b))
      fold-reindex-shape-fam-unit (P' × Q') (P'c , Q'c) fs (a , b) =
        ≈-trans (strong-Lmap-elem _ _ _)
          (L-elem-cong (≈-trans (strong-prod-m-pair _ _ _ _ _)
            (pair-cong (fold-reindex-shape-fam-unit P' P'c fs a)
                       (fold-reindex-shape-fam-unit Q' Q'c fs b))))
      fold-reindex-shape-fam-unit (μ Q'') Q''c fs t = fold-reindex-fam-unit Q''c fs t

      fold-apply-fam-unit : ∀ {k} {ρ ρ' d d'} {fm : FMor {k} ρ ρ' d d'}
        {dc : ∀ w → Mδ.DecoAssignSection (d w)} {d'c : ∀ w → MA'.DecoAssignSection (d' w)} →
        FMorSec fm dc d'c → ∀ (v : Fin k) (a : Tδ.El (ρ v)) →
        (fold-apply-fam γ fm v a ∘ pair cγ (Mδ.fib-el-unit (ρ v) (d v) (dc v) a))
          ≈ MA'.fib-el-unit (ρ' v) (d' v) (d'c v) (fold-apply γ fm v a)
      fold-apply-fam-unit fbase-s           Fin.zero    t = fold-fam-unit t
      fold-apply-fam-unit fbase-s           (Fin.suc i) a = pair-p₂ _ _
      fold-apply-fam-unit (fbind-s Q Qc fs) Fin.zero    a = fold-reindex-fam-unit Qc fs a
      fold-apply-fam-unit (fbind-s Q Qc fs) (Fin.suc v) a = fold-apply-fam-unit fs v a

  preserves-foldMor : (cΓ : Section Γ) →
    preserves-section alg (prod-section cΓ (poly-section P Pc (extend-section δc cA))) cA →
    preserves-section foldMor (prod-section cΓ (Mδ.μ-section P Pc)) cA
  preserves-foldMor cΓ halg .at (γ , t) =
    fold-fam-unit γ (cΓ .at γ) (λ s → halg .at (γ , s)) t

------------------------------------------------------------------------------
-- inMap, the canonical iso between the categorical one-step unfolding
-- fobj P (δ, μ P δ) and the concrete carrier, via the embed/unembed bridges;
-- packaged with the fold as the HasMu instance.
------------------------------------------------------------------------------

-- α's reconstruction machinery.
module InMapDef {n} (P : Poly (suc n)) (δ : Fin n → Obj) where
    δ' = extend δ (μ-fam P δ)
    module Tδ = Tree δ
    module TX = Tree δ'
    module R  = Reindex δ' δ

    -- Bridge `fobj`'s native structure to our `⟦_⟧shape` (identity at leaves and μ).
    embed-idx : (Q : Poly (suc n)) → fobj μ-fam Q δ' .idx .Carrier → TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)
    embed-idx (const A) a = a
    embed-idx (var v)   a = a
    embed-idx (Q₁ + Q₂) (inj₁ x) = inj₁ (embed-idx Q₁ x)
    embed-idx (Q₁ + Q₂) (inj₂ y) = inj₂ (embed-idx Q₂ y)
    embed-idx (Q₁ × Q₂) (x , y) = embed-idx Q₁ x , embed-idx Q₂ y
    embed-idx (μ Q')    t = t
    embed-idx-resp : (Q : Poly (suc n)) {x y : fobj μ-fam Q δ' .idx .Carrier} →
                     _≈s_ (fobj μ-fam Q δ' .idx) x y → TX.shape≈ ∣ Q ∣ (λ v → inj₁ v) (embed-idx Q x) (embed-idx Q y)
    embed-idx-resp (const A) p = p
    embed-idx-resp (var v)   p = p
    embed-idx-resp (Q₁ + Q₂) {inj₁ _} {inj₁ _} p = embed-idx-resp Q₁ p
    embed-idx-resp (Q₁ + Q₂) {inj₂ _} {inj₂ _} p = embed-idx-resp Q₂ p
    embed-idx-resp (Q₁ × Q₂) {_ , _} {_ , _} (p₁ , p₂) = embed-idx-resp Q₁ p₁ , embed-idx-resp Q₂ p₂
    embed-idx-resp (μ Q')    p = p
    -- Inverse bridge: `⟦_⟧shape` over the fresh context back to `fobj`'s native
    -- structure (identity at leaves and μ, like `embed-idx`).
    unembed-idx : (Q : Poly (suc n)) → TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v) → fobj μ-fam Q δ' .idx .Carrier
    unembed-idx (const A) a = a
    unembed-idx (var v)   a = a
    unembed-idx (Q₁ + Q₂) (inj₁ x) = inj₁ (unembed-idx Q₁ x)
    unembed-idx (Q₁ + Q₂) (inj₂ y) = inj₂ (unembed-idx Q₂ y)
    unembed-idx (Q₁ × Q₂) (x , y) = unembed-idx Q₁ x , unembed-idx Q₂ y
    unembed-idx (μ Q')    t = t

    unembed-idx-resp : (Q : Poly (suc n)) {x y : TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)} →
                       TX.shape≈ ∣ Q ∣ (λ v → inj₁ v) x y →
                       _≈s_ (fobj μ-fam Q δ' .idx) (unembed-idx Q x) (unembed-idx Q y)
    unembed-idx-resp (const A) p = p
    unembed-idx-resp (var v)   p = p
    unembed-idx-resp (Q₁ + Q₂) {inj₁ _} {inj₁ _} p = unembed-idx-resp Q₁ p
    unembed-idx-resp (Q₁ + Q₂) {inj₂ _} {inj₂ _} p = unembed-idx-resp Q₂ p
    unembed-idx-resp (Q₁ × Q₂) {_ , _} {_ , _} (p₁ , p₂) = unembed-idx-resp Q₁ p₁ , unembed-idx-resp Q₂ p₂
    unembed-idx-resp (μ Q')    p = p

    -- Embedding after unembedding is the identity.
    embed-unembed : (Q : Poly (suc n)) (x : TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)) →
                    TX.shape≈ ∣ Q ∣ (λ v → inj₁ v) (embed-idx Q (unembed-idx Q x)) x
    embed-unembed (const A) a = A .idx .isEquivalence .refl
    embed-unembed (var v)   a = TX.elEq-refl (inj₁ v) a
    embed-unembed (Q₁ + Q₂) (inj₁ x) = embed-unembed Q₁ x
    embed-unembed (Q₁ + Q₂) (inj₂ y) = embed-unembed Q₂ y
    embed-unembed (Q₁ × Q₂) (x , y) = embed-unembed Q₁ x , embed-unembed Q₂ y
    embed-unembed (μ Q')    t = TX.W-≈-refl t

    m₀ : ∀ v → TX.El (inj₁ v) → Tδ.El (Srt.η₀ ∣ P ∣ v)
    m₀ Fin.zero    a = a
    m₀ (Fin.suc i) a = a
    m₀-resp : ∀ v {a a'} → TX.elEq (inj₁ v) a a' → Tδ.elEq (Srt.η₀ ∣ P ∣ v) (m₀ v a) (m₀ v a')
    m₀-resp Fin.zero    p = p
    m₀-resp (Fin.suc i) p = p
    m₀-fam : ∀ v (a : TX.El (inj₁ v)) →
             TX.fib-el (inj₁ v) (lift tt) a ⇒ Tδ.fib-el (Srt.η₀ ∣ P ∣ v) (Tδ.deco-ext P (λ i → lift tt) v) (m₀ v a)
    m₀-fam Fin.zero    a = id _
    m₀-fam (Fin.suc i) a = id _
    m₀-fam-natural : ∀ v {a a'} (p : TX.elEq (inj₁ v) a a') →
                 (m₀-fam v a' ∘ TX.fib-el-subst (inj₁ v) (lift tt) p)
                   ≈ (Tδ.fib-el-subst (Srt.η₀ ∣ P ∣ v) (Tδ.deco-ext P (λ i → lift tt) v) (m₀-resp v p) ∘ m₀-fam v a)
    m₀-fam-natural Fin.zero    p = ≈-trans id-left (≈-sym id-right)
    m₀-fam-natural (Fin.suc i) p = ≈-trans id-left (≈-sym id-right)
    mor₀ : R.MorD (λ v → inj₁ v) (Srt.η₀ ∣ P ∣) (λ v → lift tt) (Tδ.deco-ext P (λ i → lift tt))
    mor₀ = R.base m₀ m₀-resp m₀-fam m₀-fam-natural
    -- Fibre bridge: `fobj`'s fibre to our `fib-shape` (identity at leaves, products at ×).
    embed-fam : (Q : Poly (suc n)) (x : fobj μ-fam Q δ' .idx .Carrier) →
                fobj μ-fam Q δ' .fam .fm x ⇒ TX.fib-shape Q (λ v → lift tt) (embed-idx Q x)
    embed-fam (const A) a = id _
    embed-fam (var v)   a = id _
    embed-fam (Q₁ + Q₂) (inj₁ x) = Lmap (embed-fam Q₁ x)
    embed-fam (Q₁ + Q₂) (inj₂ y) = Lmap (embed-fam Q₂ y)
    embed-fam (Q₁ × Q₂) (x , y) = Lmap (prod-m (embed-fam Q₁ x) (embed-fam Q₂ y))
    embed-fam (μ Q')    t = id _
    embed-fam-natural : (Q : Poly (suc n)) {x y : fobj μ-fam Q δ' .idx .Carrier} (e : _≈s_ (fobj μ-fam Q δ' .idx) x y) →
                        (embed-fam Q y ∘ fobj μ-fam Q δ' .fam .subst e)
                          ≈ (TX.fib-shape-subst Q (λ v → lift tt) (embed-idx-resp Q e) ∘ embed-fam Q x)
    embed-fam-natural (const A) e = ≈-trans id-left (≈-sym id-right)
    embed-fam-natural (var v)   e = ≈-trans id-left (≈-sym id-right)
    embed-fam-natural (Q₁ + Q₂) {inj₁ _} {inj₁ _} e =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong (embed-fam-natural Q₁ e)) (Lmap-comp _ _))
    embed-fam-natural (Q₁ + Q₂) {inj₂ _} {inj₂ _} e =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong (embed-fam-natural Q₂ e)) (Lmap-comp _ _))
    embed-fam-natural (Q₁ × Q₂) {_ , _} {_ , _} (e₁ , e₂) =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong
                 (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                  (≈-trans (prod-m-cong (embed-fam-natural Q₁ e₁) (embed-fam-natural Q₂ e₂))
                           (prod-m-comp _ _ _ _))))
               (Lmap-comp _ _))
    embed-fam-natural (μ Q')    e = ≈-trans id-left (≈-sym id-right)

    -- Fibre half of the inverse bridge.
    unembed-fam : (Q : Poly (suc n)) (y : TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)) →
                  TX.fib-shape Q (λ v → lift tt) y ⇒ fobj μ-fam Q δ' .fam .fm (unembed-idx Q y)
    unembed-fam (const A) a = id _
    unembed-fam (var v)   a = id _
    unembed-fam (Q₁ + Q₂) (inj₁ x) = Lmap (unembed-fam Q₁ x)
    unembed-fam (Q₁ + Q₂) (inj₂ y) = Lmap (unembed-fam Q₂ y)
    unembed-fam (Q₁ × Q₂) (x , y) = Lmap (prod-m (unembed-fam Q₁ x) (unembed-fam Q₂ y))
    unembed-fam (μ Q')    t = id _

    unembed-fam-natural : (Q : Poly (suc n)) {x y : TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)}
                          (e : TX.shape≈ ∣ Q ∣ (λ v → inj₁ v) x y) →
                          (unembed-fam Q y ∘ TX.fib-shape-subst Q (λ v → lift tt) e)
                            ≈ (fobj μ-fam Q δ' .fam .subst (unembed-idx-resp Q e) ∘ unembed-fam Q x)
    unembed-fam-natural (const A) e = ≈-trans id-left (≈-sym id-right)
    unembed-fam-natural (var v)   e = ≈-trans id-left (≈-sym id-right)
    unembed-fam-natural (Q₁ + Q₂) {inj₁ _} {inj₁ _} e =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong (unembed-fam-natural Q₁ e)) (Lmap-comp _ _))
    unembed-fam-natural (Q₁ + Q₂) {inj₂ _} {inj₂ _} e =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong (unembed-fam-natural Q₂ e)) (Lmap-comp _ _))
    unembed-fam-natural (Q₁ × Q₂) {_ , _} {_ , _} (e₁ , e₂) =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong
                 (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                  (≈-trans (prod-m-cong (unembed-fam-natural Q₁ e₁) (unembed-fam-natural Q₂ e₂))
                           (prod-m-comp _ _ _ _))))
               (Lmap-comp _ _))
    unembed-fam-natural (μ Q')    e = ≈-trans id-left (≈-sym id-right)

    -- Embedding after unembedding is the identity on fibres too.
    embed-unembed-fam : (Q : Poly (suc n)) (y : TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)) →
                        (TX.fib-shape-subst Q (λ v → lift tt) (embed-unembed Q y)
                         ∘ (embed-fam Q (unembed-idx Q y) ∘ unembed-fam Q y))
                        ≈ id _
    embed-unembed-fam (const A) a =
      ≈-trans (∘-cong (A .fam .refl*) ≈-refl) (≈-trans id-left id-left)
    embed-unembed-fam (var v) a =
      ≈-trans (∘-cong (TX.fib-el-refl* (inj₁ v) (lift tt) a) ≈-refl) (≈-trans id-left id-left)
    embed-unembed-fam (Q₁ + Q₂) (inj₁ x) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (embed-unembed-fam Q₁ x)) Lmap-id))
    embed-unembed-fam (Q₁ + Q₂) (inj₂ y) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (embed-unembed-fam Q₂ y)) Lmap-id))
    embed-unembed-fam (Q₁ × Q₂) (x , y) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong
                   (≈-trans (∘-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _)))
                     (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                       (≈-trans (prod-m-cong (embed-unembed-fam Q₁ x) (embed-unembed-fam Q₂ y))
                                prod-m-id))))
                 Lmap-id))
    embed-unembed-fam (μ Q') t =
      ≈-trans (∘-cong (TX.fib-refl* Q' (λ v → lift tt) t) ≈-refl) (≈-trans id-left id-left)

    -- Unembedding after embedding is the identity, on indexes and on fibres.
    unembed-embed : (Q : Poly (suc n)) (x : fobj μ-fam Q δ' .idx .Carrier) →
                    _≈s_ (fobj μ-fam Q δ' .idx) (unembed-idx Q (embed-idx Q x)) x
    unembed-embed (const A) a = A .idx .isEquivalence .refl
    unembed-embed (var v)   a = TX.elEq-refl (inj₁ v) a
    unembed-embed (Q₁ + Q₂) (inj₁ x) = unembed-embed Q₁ x
    unembed-embed (Q₁ + Q₂) (inj₂ y) = unembed-embed Q₂ y
    unembed-embed (Q₁ × Q₂) (x , y) = unembed-embed Q₁ x , unembed-embed Q₂ y
    unembed-embed (μ Q')    t = TX.W-≈-refl t

    unembed-embed-fam : (Q : Poly (suc n)) (x : fobj μ-fam Q δ' .idx .Carrier) →
                        (fobj μ-fam Q δ' .fam .subst (unembed-embed Q x)
                         ∘ (unembed-fam Q (embed-idx Q x) ∘ embed-fam Q x))
                        ≈ id _
    unembed-embed-fam (const A) a =
      ≈-trans (∘-cong (A .fam .refl*) ≈-refl) (≈-trans id-left id-left)
    unembed-embed-fam (var v) a =
      ≈-trans (∘-cong (TX.fib-el-refl* (inj₁ v) (lift tt) a) ≈-refl) (≈-trans id-left id-left)
    unembed-embed-fam (Q₁ + Q₂) (inj₁ x) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (unembed-embed-fam Q₁ x)) Lmap-id))
    unembed-embed-fam (Q₁ + Q₂) (inj₂ y) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (unembed-embed-fam Q₂ y)) Lmap-id))
    unembed-embed-fam (Q₁ × Q₂) (x , y) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong
                   (≈-trans (∘-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _)))
                     (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                       (≈-trans (prod-m-cong (unembed-embed-fam Q₁ x) (unembed-embed-fam Q₂ y))
                                prod-m-id))))
                 Lmap-id))
    unembed-embed-fam (μ Q') t =
      ≈-trans (∘-cong (TX.fib-refl* Q' (λ v → lift tt) t) ≈-refl) (≈-trans id-left id-left)

    inMor : Mor (fobj μ-fam P δ') (μ-fam P δ)
    inMor .idxf .PS._⇒_.func i = Tδ.sup (R.reindex-shape ∣ P ∣ mor₀ (embed-idx P i))
    inMor .idxf .PS._⇒_.func-resp-≈ x≈y = R.reindex-shape-resp ∣ P ∣ mor₀ (embed-idx-resp P x≈y)
    inMor .famf ._⇒f_.transf x = R.reindex-fam P mor₀ ∘ embed-fam P x
    inMor .famf ._⇒f_.natural e =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong₂ (embed-fam-natural P e))
      (≈-trans (≈-sym (assoc _ _ _))
      (≈-trans (∘-cong₁ (R.reindex-fam-natural P mor₀ (embed-idx-resp P e)))
               (assoc _ _ _))))

    module InMapSection (δc : ∀ i → Section (δ i)) (Pc : PolySection P) where
      private
        μc : Section (μ-fam P δ)
        μc = MuSection.μ-section δ δc P Pc
        module MX = MuSection δ' (extend-section δc μc)
        module Mδ = MuSection δ δc
        module RS = ReindexSection (extend-section δc μc) δc

      mor₀-sec : RS.MorDSec mor₀ (λ v → lift tt) (Mδ.deco-ext-section P Pc (λ i → lift tt))
      mor₀-sec = RS.base-s h
        where
        h : ∀ v a → (m₀-fam v a ∘ MX.fib-el-unit (inj₁ v) (lift tt) (lift tt) a)
                    ≈ Mδ.fib-el-unit (Srt.η₀ ∣ P ∣ v) (Tδ.deco-ext P (λ i → lift tt) v)
                                     (Mδ.deco-ext-section P Pc (λ i → lift tt) v) (m₀ v a)
        h Fin.zero    a = id-left
        h (Fin.suc i) a = id-left

      embed-unit : (Q : Poly (suc n)) (Qc : PolySection Q) (x : fobj μ-fam Q δ' .idx .Carrier) →
        (embed-fam Q x ∘ poly-section Q Qc (extend-section δc μc) .at x)
          ≈ MX.fib-shape-unit Q (λ v → lift tt) Qc (λ v → lift tt) (embed-idx Q x)
      embed-unit (const A) Ac a = id-left
      embed-unit (var v)   _  a = id-left
      embed-unit (Q₁ + Q₂) (Q₁c , Q₂c) (inj₁ x) =
        ≈-trans (L-elem-natural _ _) (L-elem-cong (embed-unit Q₁ Q₁c x))
      embed-unit (Q₁ + Q₂) (Q₁c , Q₂c) (inj₂ y) =
        ≈-trans (L-elem-natural _ _) (L-elem-cong (embed-unit Q₂ Q₂c y))
      embed-unit (Q₁ × Q₂) (Q₁c , Q₂c) (x , y) =
        ≈-trans (L-elem-natural _ _)
          (L-elem-cong (≈-trans (pair-compose _ _ _ _)
            (pair-cong (embed-unit Q₁ Q₁c x) (embed-unit Q₂ Q₂c y))))
      embed-unit (μ Q') Q'c t = id-left

      unembed-unit : (Q : Poly (suc n)) (Qc : PolySection Q) (y : TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)) →
        (unembed-fam Q y ∘ MX.fib-shape-unit Q (λ v → lift tt) Qc (λ v → lift tt) y)
          ≈ poly-section Q Qc (extend-section δc μc) .at (unembed-idx Q y)
      unembed-unit (const A) Ac y = id-left
      unembed-unit (var v)   _  y = id-left
      unembed-unit (Q₁ + Q₂) (Q₁c , Q₂c) (inj₁ x) =
        ≈-trans (L-elem-natural _ _) (L-elem-cong (unembed-unit Q₁ Q₁c x))
      unembed-unit (Q₁ + Q₂) (Q₁c , Q₂c) (inj₂ y) =
        ≈-trans (L-elem-natural _ _) (L-elem-cong (unembed-unit Q₂ Q₂c y))
      unembed-unit (Q₁ × Q₂) (Q₁c , Q₂c) (x , y) =
        ≈-trans (L-elem-natural _ _)
          (L-elem-cong (≈-trans (pair-compose _ _ _ _)
            (pair-cong (unembed-unit Q₁ Q₁c x) (unembed-unit Q₂ Q₂c y))))
      unembed-unit (μ Q') Q'c t = id-left

      preserves-inMor : preserves-section inMor (poly-section P Pc (extend-section δc μc)) μc
      preserves-inMor .at x =
        ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (embed-unit P Pc x))
                 (RS.reindex-fam-unit P Pc mor₀-sec (embed-idx P x)))

hasMu : HasMu
hasMu .HasMu.μ-obj = μ-fam
hasMu .HasMu.inMap P δ = InMapDef.inMor P δ
hasMu .HasMu.⦅_⦆ alg = FoldDef.foldMor alg

preserves-inMap : ∀ {n} (P : Poly (suc n)) (δ : Fin n → Obj)
                  (δc : ∀ i → Section (δ i)) (Pc : PolySection P) →
                  preserves-section (InMapDef.inMor P δ)
                    (poly-section P Pc (extend-section δc (MuSection.μ-section δ δc P Pc)))
                    (MuSection.μ-section δ δc P Pc)
preserves-inMap P δ δc Pc = InMapDef.InMapSection.preserves-inMor P δ δc Pc

-- The strong functorial action of a μ-polynomial on indices is reindexing along the pointwise
-- family of its argument maps.

fuse-idx : ∀ {n} {Γ : Obj} {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
               let module Rs = Reindex sₛ sₜ in
               (cmb : Γ .idx .Carrier → Rs.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
               (fsk : ∀ i → Mor (Fam𝒞-P.prod Γ (sₛ i)) (sₜ i))
               (corr : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                       _≈s_ (sₜ i .idx) (Rs.iapply (cmb γ₁) i a₁) (fsk i .idxf .PS._⇒_.func (γ₂ , a₂))) →
               ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {m₁ m₂}
               (m≈ : _≈s_ (μ-fam Q sₛ .idx) m₁ m₂) →
               _≈s_ (μ-fam Q sₜ .idx) (Rs.ireindex (cmb γ₁) m₁) (HasMu.strong-fmor hasMu (μ Q) fsk .idxf .PS._⇒_.func (γ₂ , m₂))
fuse-shape : ∀ {n} {Γ : Obj} {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
                 let module Rs = Reindex sₛ sₜ
                     module Ts = Tree sₛ
                     module Tt = Tree sₜ
                     module At = InMapDef Q sₜ in
                 (cmb : Γ .idx .Carrier → Rs.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
                 (fsk : ∀ i → Mor (Fam𝒞-P.prod Γ (sₛ i)) (sₜ i))
                 (corr : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                         _≈s_ (sₜ i .idx) (Rs.iapply (cmb γ₁) i a₁) (fsk i .idxf .PS._⇒_.func (γ₂ , a₂))) →
                 let module Ft = FoldDef {Γ = Γ} {A = μ-fam Q sₜ} {P = Q} {δ = sₛ}
                                   (Fam𝒞._∘_ At.inMor (HasMu.strong-fmor hasMu Q (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂))) in
                 (R : Poly (suc n)) →
                 ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {x₁ x₂}
                 (x≈ : Ts.shape≈ ∣ R ∣ (Srt.η₀ ∣ Q ∣) x₁ x₂) →
                 Tt.shape≈ ∣ R ∣ (Srt.η₀ ∣ Q ∣)
                   (Rs.ireindex-shape ∣ R ∣ (Rs.ibind ∣ Q ∣ (cmb γ₁)) x₁)
                   (At.R.reindex-shape ∣ R ∣ At.mor₀
                    (At.embed-idx R (HasMu.strong-fmor hasMu R (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂) .idxf .PS._⇒_.func
                      (γ₂ , Ft.fold-shape-idx R γ₂ x₂))))

fuse-idx Q cmb fsk corr γ≈ {Tree.sup x₁} {Tree.sup x₂} m≈ = fuse-shape Q cmb fsk corr Q γ≈ {x₁} {x₂} m≈

fuse-shape Q cmb fsk corr (const A')                  γ≈ x≈ = x≈
fuse-shape Q cmb fsk corr (var Fin.zero)              γ≈ {x₁} {x₂} x≈ = fuse-idx Q cmb fsk corr γ≈ {x₁} {x₂} x≈
fuse-shape Q cmb fsk corr (var (Fin.suc i))           γ≈ x≈ = corr i γ≈ x≈
fuse-shape Q cmb fsk corr (R₁ + R₂) γ≈ {inj₁ _} {inj₁ _} x≈ = fuse-shape Q cmb fsk corr R₁ γ≈ x≈
fuse-shape Q cmb fsk corr (R₁ + R₂) γ≈ {inj₂ _} {inj₂ _} x≈ = fuse-shape Q cmb fsk corr R₂ γ≈ x≈
fuse-shape Q cmb fsk corr (R₁ × R₂) γ≈ {_ , _} {_ , _} (x≈₁ , x≈₂) =
  fuse-shape Q cmb fsk corr R₁ γ≈ x≈₁ , fuse-shape Q cmb fsk corr R₂ γ≈ x≈₂
fuse-shape {Γ = Γ} {sₛ = sₛ} {sₜ = sₜ} Q cmb fsk corr (μ R'') {γ₁} {γ₂} γ≈ {x₁} {x₂} x≈ =
  Tt.W-≈-trans {x = Rs.ireindex-shape ∣ μ R'' ∣ (Rs.ibind ∣ Q ∣ (cmb γ₁)) x₁}
               {z = At.R.reindex-shape ∣ μ R'' ∣ At.mor₀ (At.embed-idx (μ R'')
                      (HasMu.strong-fmor hasMu (μ R'') (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)
                        .idxf .PS._⇒_.func (γ₂ , w)))}
               telescope
               (At.R.reindex-resp At.mor₀
                 {t = Rs'.ireindex (cmb' γ₁) wm₁}
                 {t' = HasMu.strong-fmor hasMu (μ R'') (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂) .idxf .PS._⇒_.func (γ₂ , w)}
                 rec)
  where
    module Tt = Tree sₜ
    module Ts = Tree sₛ
    module At = InMapDef Q sₜ
    module Rs = Reindex sₛ sₜ
    module Rs' = Reindex (extend sₛ (μ-fam Q sₜ)) (extend sₜ (μ-fam Q sₜ))
    module Ft = FoldDef {Γ = Γ} {A = μ-fam Q sₜ} {P = Q} {δ = sₛ}
                  (Fam𝒞._∘_ At.inMor (HasMu.strong-fmor hasMu Q (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)))
    wm₁ = Ft.fold-reindex {Q = R''} γ₁ Ft.fbase x₁
    w   = Ft.fold-reindex {Q = R''} γ₂ Ft.fbase x₂
    cmb' : Γ .idx .Carrier → Rs'.IMorD (λ v → inj₁ v) (λ v → inj₁ v)
    cmb' γ = Rs'.ibase (λ { Fin.zero a → a ; (Fin.suc i) a → Rs.iapply (cmb γ) i a })
                       (λ { Fin.zero p → p ; (Fin.suc i) p → Rs.iapply-resp (cmb γ) i p })
    rec : _≈s_ (μ-fam R'' (extend sₜ (μ-fam Q sₜ)) .idx)
               (Rs'.ireindex (cmb' γ₁) wm₁)
               (HasMu.strong-fmor hasMu (μ R'') (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂) .idxf .PS._⇒_.func (γ₂ , w))
    rec = fuse-idx R'' cmb' (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)
            (λ { Fin.zero γ≈ a≈ → a≈ ; (Fin.suc j) γ≈ a≈ → corr j γ≈ a≈ })
            γ≈ {m₁ = wm₁} {m₂ = w}  (Ft.fold-reindex-resp {Q = R''} γ≈ Ft.fbase {x₁} {x₂} x≈)
    mutual
      data TeleRel : ∀ {j} {ηA ηB ηC ηD}
                     {dA : ∀ v → Ts.DecoAssign (ηA v)} {dB : ∀ v → Tt.DecoAssign (ηB v)}
                     {dC : ∀ v → At.TX.DecoAssign (ηC v)} {dD : ∀ v → Ft.TA'.DecoAssign (ηD v)} →
                     Rs.IMorD {j} ηA ηB → At.R.MorD {j} ηC ηB dC dB → Rs'.IMorD {j} ηD ηC → Ft.FMor {j} ηA ηD dA dD →
                     Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
        tbase : TeleRel (Rs.ibind ∣ Q ∣ (cmb γ₁)) At.mor₀ (cmb' γ₁) Ft.fbase
        tbind : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD} {md mdA md' fm} (S' : Poly (suc j)) →
                TeleRel {j} {ηA} {ηB} {ηC} {ηD} {dA} {dB} {dC} {dD} md mdA md' fm →
                TeleRel (Rs.ibind ∣ S' ∣ md) (At.R.bind S' mdA) (Rs'.ibind ∣ S' ∣ md') (Ft.fbind S' fm)

      tele-shape : ∀ {j} (S : Poly j) {ηA ηB ηC ηD} {dA dB dC dD}
                   {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                   (rel : TeleRel md mdA md' fm) (z : Ft.Tδ.⟦ ∣ S ∣ ⟧shape ηA) →
                   Tt.shape≈ ∣ S ∣ ηB
                     (Rs.ireindex-shape ∣ S ∣ md z)
                     (At.R.reindex-shape ∣ S ∣ mdA (Rs'.ireindex-shape ∣ S ∣ md' (Ft.fold-reindex-shape γ₁ S fm z)))
      tele-shape (const A') rel z = A' .idx .isEquivalence .refl
      tele-shape (var v) rel z = tele-apply rel v
      tele-shape (S₁ + S₂) rel (inj₁ z) = tele-shape S₁ rel z
      tele-shape (S₁ + S₂) rel (inj₂ z) = tele-shape S₂ rel z
      tele-shape (S₁ × S₂) rel (z₁ , z₂) = tele-shape S₁ rel z₁ , tele-shape S₂ rel z₂
      tele-shape (μ S') rel (Ts.sup z') = tele-shape S' (tbind S' rel) z'

      tele-apply : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD}
                   {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                   (rel : TeleRel md mdA md' fm) (v : Fin j) {z} →
                   Tt.elEq (ηB v) (Rs.iapply md v z) (At.R.apply mdA v (Rs'.iapply md' v (Ft.fold-apply γ₁ fm v z)))
      tele-apply (tbind S' r) Fin.zero    {z} = tele-shape (μ S') r z
      tele-apply (tbind S' r) (Fin.suc v)     = tele-apply r v
      tele-apply tbase Fin.zero    {z} =
        fuse-idx Q cmb fsk corr (Γ .idx .isEquivalence .refl {γ₁}) {m₁ = z} {m₂ = z}
          (μ-fam Q sₛ .idx .isEquivalence .refl {z})
      tele-apply tbase (Fin.suc i) {z} = Tt.elEq-refl (inj₁ i) (Rs.iapply (cmb γ₁) i z)

    telescope : Tt.W-≈ (Rs.ireindex-shape ∣ μ R'' ∣ (Rs.ibind ∣ Q ∣ (cmb γ₁)) x₁)
                       (At.R.reindex At.mor₀ (Rs'.ireindex (cmb' γ₁) wm₁))
    telescope = tele-shape (μ R'') tbase x₁

-- The fibre map of the strong product action is the strong product action of the fibre maps.
strong-prod-m-transf : ∀ {Γ X₁ X₂ Y₁ Y₂ : Obj} (f : Mor (Fam𝒞-P.prod Γ X₁) Y₁) (g : Mor (Fam𝒞-P.prod Γ X₂) Y₂)
                       {γ x₁ x₂} →
                       Fam𝒞-P.strong-prod-m f g .famf ._⇒f_.transf (γ , (x₁ , x₂))
                         ≈ strong-prod-m (f .famf ._⇒f_.transf (γ , x₁)) (g .famf ._⇒f_.transf (γ , x₂))
strong-prod-m-transf f g =
  pair-cong (≈-trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left)))
            (≈-trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left)))

-- The fibre half: the fibre reindexing along an external action agreeing with the argument maps is
-- the strong action's fibre map, transported along the index half.
fuse-fam : ∀ {n} {Γ : Obj} (γ : Γ .idx .Carrier) {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
               let module Rs = Reindex sₛ sₜ
                   module FR = FReindex {δA = sₛ} {δB = sₜ} (Γ .fam .fm γ) in
               (cmb : Γ .idx .Carrier → Rs.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
               (act : FR.FAct (cmb γ) (λ v → lift tt) (λ v → lift tt))
               (fsk : ∀ i → Mor (Fam𝒞-P.prod Γ (sₛ i)) (sₜ i))
               (corr : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                       _≈s_ (sₜ i .idx) (Rs.iapply (cmb γ₁) i a₁) (fsk i .idxf .PS._⇒_.func (γ₂ , a₂)))
               (corr-fam : ∀ i {a} →
                  Category._≈_ 𝒞
                    (sₜ i .fam .subst (corr i (Γ .idx .isEquivalence .refl) (sₛ i .idx .isEquivalence .refl {a}))
                     ∘ FR.aapply act i a)
                    (fsk i .famf ._⇒f_.transf (γ , a))) →
               ∀ {m} →
               Category._≈_ 𝒞
                 (μ-fam Q sₜ .fam .subst {x = Rs.ireindex (cmb γ) m}
                    (fuse-idx Q cmb fsk corr (Γ .idx .isEquivalence .refl)
                      {m} {m} (μ-fam Q sₛ .idx .isEquivalence .refl {m}))
                  ∘ FR.freindex-fam act {m})
                 (HasMu.strong-fmor hasMu (μ Q) fsk .famf ._⇒f_.transf (γ , m))

fuse-shape-fam : ∀ {n} {Γ : Obj} (γ : Γ .idx .Carrier) {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
                     let module Rs = Reindex sₛ sₜ
                         module Ts = Tree sₛ
                         module Tt = Tree sₜ
                         module At = InMapDef Q sₜ
                         module FR = FReindex {δA = sₛ} {δB = sₜ} (Γ .fam .fm γ) in
                     (cmb : Γ .idx .Carrier → Rs.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
                     (act : FR.FAct (cmb γ) (λ v → lift tt) (λ v → lift tt))
                     (fsk : ∀ i → Mor (Fam𝒞-P.prod Γ (sₛ i)) (sₜ i))
                     (corr : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                             _≈s_ (sₜ i .idx) (Rs.iapply (cmb γ₁) i a₁) (fsk i .idxf .PS._⇒_.func (γ₂ , a₂)))
                     (corr-fam : ∀ i {a} →
                        Category._≈_ 𝒞
                          (sₜ i .fam .subst (corr i (Γ .idx .isEquivalence .refl) (sₛ i .idx .isEquivalence .refl {a}))
                           ∘ FR.aapply act i a)
                          (fsk i .famf ._⇒f_.transf (γ , a))) →
                     let module Ft = FoldDef {Γ = Γ} {A = μ-fam Q sₜ} {P = Q} {δ = sₛ}
                                       (Fam𝒞._∘_ At.inMor (HasMu.strong-fmor hasMu Q (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)))
                         fsk' = HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂ in
                     (R : Poly (suc n))
                     {x : Ts.⟦ ∣ R ∣ ⟧shape (Srt.η₀ ∣ Q ∣)} →
                     Category._≈_ 𝒞
                       (Tt.fib-shape-subst R (Tt.deco-ext Q (λ i → lift tt))
                          (fuse-shape Q cmb fsk corr R (Γ .idx .isEquivalence .refl) (Ts.shape≈-refl ∣ R ∣ (Srt.η₀ ∣ Q ∣) x))
                        ∘ FR.freindex-shape-fam R (FR.abind Q (cmb γ) act) {x})
                       (At.R.reindex-fam R At.mor₀
                        ∘ (At.embed-fam R (HasMu.strong-fmor hasMu R fsk' .idxf .PS._⇒_.func (γ , Ft.fold-shape-idx R γ x))
                           ∘ (HasMu.strong-fmor hasMu R fsk' .famf ._⇒f_.transf (γ , Ft.fold-shape-idx R γ x)
                              ∘ pair p₁ (Ft.fold-shape-fam R γ x))))

fuse-fam γ Q cmb act fsk corr corr-fam {Tree.sup x} =
  ≈-trans (fuse-shape-fam γ Q cmb act fsk corr corr-fam Q {x})
    (≈-sym (≈-trans (∘-cong id-left ≈-refl) (≈-trans (assoc _ _ _) (assoc _ _ _))))
fuse-shape-fam γ Q cmb act fsk corr corr-fam (const A') =
  ≈-trans (∘-cong (A' .fam .refl*) ≈-refl)
    (≈-trans id-left (≈-sym (≈-trans id-left (≈-trans id-left (pair-p₂ _ _)))))
fuse-shape-fam γ Q cmb act fsk corr corr-fam (var Fin.zero) {x} =
  ≈-trans (fuse-fam γ Q cmb act fsk corr corr-fam {x})
    (≈-sym (≈-trans id-left (≈-trans id-left (pair-p₂ _ _))))
fuse-shape-fam γ Q cmb act fsk corr corr-fam (var (Fin.suc i)) {x} =
  ≈-trans (corr-fam i)
    (≈-sym (≈-trans id-left (≈-trans id-left (≈-trans (∘-cong ≈-refl pair-ext0) id-right))))
fuse-shape-fam γ Q cmb act fsk corr corr-fam (R₁ + R₂) {inj₁ a} =
  ≈-trans (strong-Lmap-post _ _)
  (≈-trans (strong-Lmap-cong (fuse-shape-fam γ Q cmb act fsk corr corr-fam R₁ {a}))
  (≈-sym (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (≈-trans (∘-cong (≈-trans id-left (≈-trans id-left (strong-Lf-map-transf (HasMu.strong-fmor hasMu R₁ (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂))))) ≈-refl) (strong-Lmap-co _ _))))
                  (≈-trans (∘-cong ≈-refl (strong-Lmap-post _ _)) (strong-Lmap-post _ _)))))
fuse-shape-fam γ Q cmb act fsk corr corr-fam (R₁ + R₂) {inj₂ b} =
  ≈-trans (strong-Lmap-post _ _)
  (≈-trans (strong-Lmap-cong (fuse-shape-fam γ Q cmb act fsk corr corr-fam R₂ {b}))
  (≈-sym (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (≈-trans (∘-cong (≈-trans id-left (≈-trans id-left (strong-Lf-map-transf (HasMu.strong-fmor hasMu R₂ (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂))))) ≈-refl) (strong-Lmap-co _ _))))
                  (≈-trans (∘-cong ≈-refl (strong-Lmap-post _ _)) (strong-Lmap-post _ _)))))
fuse-shape-fam {Γ = Γ} γ {sₛ = sₛ} {sₜ = sₜ} Q cmb act fsk corr corr-fam (R₁ × R₂) {a , b} =
  ≈-trans (strong-Lmap-post _ _)
  (≈-trans (strong-Lmap-cong
             (≈-trans (strong-prod-m-post _ _ _ _)
             (≈-trans (strong-prod-m-cong (fuse-shape-fam γ Q cmb act fsk corr corr-fam R₁ {a})
                                          (fuse-shape-fam γ Q cmb act fsk corr corr-fam R₂ {b}))
             (≈-sym (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (strong-prod-m-comp _ _ _ _)))
                    (≈-trans (∘-cong ≈-refl (strong-prod-m-post _ _ _ _)) (strong-prod-m-post _ _ _ _)))))))
  (≈-sym (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (≈-trans (∘-cong (≈-trans (strong-Lf-map-transf (Fam𝒞-P.strong-prod-m (HasMu.strong-fmor hasMu R₁ fsk') (HasMu.strong-fmor hasMu R₂ fsk')))
                                                                          (strong-Lmap-cong
                                                                            (strong-prod-m-transf (HasMu.strong-fmor hasMu R₁ fsk') (HasMu.strong-fmor hasMu R₂ fsk')
                                                                               {γ} {Ft.fold-shape-idx R₁ γ a} {Ft.fold-shape-idx R₂ γ b})))
                                                                 ≈-refl)
                                                         (strong-Lmap-co _ _))))
                  (≈-trans (∘-cong ≈-refl (strong-Lmap-post _ _)) (strong-Lmap-post _ _)))))
  where
    module At = InMapDef Q sₜ
    fsk' = HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂
    module Ft = FoldDef {Γ = Γ} {A = μ-fam Q sₜ} {P = Q} {δ = sₛ}
                  (Fam𝒞._∘_ At.inMor (HasMu.strong-fmor hasMu Q fsk'))
fuse-shape-fam {Γ = Γ} γ {sₛ = sₛ} {sₜ = sₜ} Q cmb act fsk corr corr-fam (μ R'') {x} =
  ≈-trans (∘-cong (Tt.fib-trans* R'' (Tt.deco-ext Q (λ i → lift tt))
                     {x = Rs.ireindex-shape ∣ μ R'' ∣ (Rs.ibind ∣ Q ∣ (cmb γ)) x}
                     {y = At.R.reindex At.mor₀ (Rs'.ireindex (cmb' γ) wm₁)}
                     {z = At.R.reindex At.mor₀ (HasMu.strong-fmor hasMu (μ R'') fsk' .idxf .PS._⇒_.func (γ , wm₁))}
                     (At.R.reindex-resp At.mor₀
                        {t = Rs'.ireindex (cmb' γ) wm₁}
                        {t' = HasMu.strong-fmor hasMu (μ R'') fsk' .idxf .PS._⇒_.func (γ , wm₁)}
                        rec-idx)
                     (tele-shape (μ R'') tbase x)) ≈-refl)
    (≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (tele-shape-fam (μ R'') tbase x))
        (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong (≈-sym (At.R.reindex-fam-W-natural {Q = R''} At.mor₀
                                     {t = Rs'.ireindex (cmb' γ) wm₁}
                                     {t' = HasMu.strong-fmor hasMu (μ R'') fsk' .idxf .PS._⇒_.func (γ , wm₁)}
                                     rec-idx)) ≈-refl)
            (≈-trans (assoc _ _ _)
              (∘-cong ≈-refl
                (≈-trans (≈-sym (assoc _ _ _))
                  (≈-trans (∘-cong rec-fam ≈-refl) (≈-sym id-left)))))))))
  where
    module Tt = Tree sₜ
    module Ts = Tree sₛ
    module At = InMapDef Q sₜ
    module Rs = Reindex sₛ sₜ
    module Rs' = Reindex (extend sₛ (μ-fam Q sₜ)) (extend sₜ (μ-fam Q sₜ))
    module FR = FReindex {δA = sₛ} {δB = sₜ} (Γ .fam .fm γ)
    module FR' = FReindex {δA = extend sₛ (μ-fam Q sₜ)} {δB = extend sₜ (μ-fam Q sₜ)} (Γ .fam .fm γ)
    module Ft = FoldDef {Γ = Γ} {A = μ-fam Q sₜ} {P = Q} {δ = sₛ}
                  (Fam𝒞._∘_ At.inMor (HasMu.strong-fmor hasMu Q (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)))
    fsk' = HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂
    wm₁ = Ft.fold-reindex {Q = R''} γ Ft.fbase x
    cmb' : Γ .idx .Carrier → Rs'.IMorD (λ v → inj₁ v) (λ v → inj₁ v)
    cmb' γ' = Rs'.ibase (λ { Fin.zero a → a ; (Fin.suc i) a → Rs.iapply (cmb γ') i a })
                        (λ { Fin.zero p → p ; (Fin.suc i) p → Rs.iapply-resp (cmb γ') i p })
    act' : FR'.FAct (cmb' γ) (λ v → lift tt) (λ v → lift tt)
    act' = FR'.abase (λ { Fin.zero a → p₂ ; (Fin.suc i) a → FR.aapply act i a })
    corr' : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (extend sₛ (μ-fam Q sₜ) i .idx) a₁ a₂) →
            _≈s_ (extend sₜ (μ-fam Q sₜ) i .idx) (Rs'.iapply (cmb' γ₁) i a₁) (fsk' i .idxf .PS._⇒_.func (γ₂ , a₂))
    corr' Fin.zero    γ≈ a≈ = a≈
    corr' (Fin.suc j) γ≈ a≈ = corr j γ≈ a≈
    corr-fam' : ∀ i {a} → Category._≈_ 𝒞
                  (extend sₜ (μ-fam Q sₜ) i .fam .subst
                     (corr' i (Γ .idx .isEquivalence .refl) (extend sₛ (μ-fam Q sₜ) i .idx .isEquivalence .refl {a}))
                   ∘ FR'.aapply act' i a)
                  (fsk' i .famf ._⇒f_.transf (γ , a))
    corr-fam' Fin.zero {a} = ≈-trans (∘-cong (μ-fam Q sₜ .fam .refl* {a}) ≈-refl) id-left
    corr-fam' (Fin.suc j) = corr-fam j
    rec-fam : Category._≈_ 𝒞
                (μ-fam R'' (extend sₜ (μ-fam Q sₜ)) .fam .subst {x = Rs'.ireindex (cmb' γ) wm₁}
                   (fuse-idx R'' cmb' fsk' corr' (Γ .idx .isEquivalence .refl)
                     {wm₁} {wm₁} (μ-fam R'' (extend sₛ (μ-fam Q sₜ)) .idx .isEquivalence .refl {wm₁}))
                 ∘ FR'.freindex-fam act' {wm₁})
                (HasMu.strong-fmor hasMu (μ R'') fsk' .famf ._⇒f_.transf (γ , wm₁))
    rec-fam = fuse-fam γ R'' cmb' act' fsk' corr' corr-fam' {wm₁}
    rec-idx = fuse-idx R'' cmb' fsk' corr' (Γ .idx .isEquivalence .refl)
                {wm₁} {wm₁} (μ-fam R'' (extend sₛ (μ-fam Q sₜ)) .idx .isEquivalence .refl {wm₁})
    mutual
      data TeleRel : ∀ {j} {ηA ηB ηC ηD}
                     {dA : ∀ v → Ts.DecoAssign (ηA v)} {dB : ∀ v → Tt.DecoAssign (ηB v)}
                     {dC : ∀ v → At.TX.DecoAssign (ηC v)} {dD : ∀ v → Ft.TA'.DecoAssign (ηD v)}
                     (md : Rs.IMorD {j} ηA ηB) (mdA : At.R.MorD {j} ηC ηB dC dB) (md' : Rs'.IMorD {j} ηD ηC) (fm : Ft.FMor {j} ηA ηD dA dD) →
                     FR.FAct md dA dB → FR'.FAct md' dD dC → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
        tbase : TeleRel (Rs.ibind ∣ Q ∣ (cmb γ)) At.mor₀ (cmb' γ) Ft.fbase (FR.abind Q (cmb γ) act) act'
        tbind : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD} {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                {am : FR.FAct md dA dB} {am' : FR'.FAct md' dD dC} (S' : Poly (suc j)) →
                TeleRel md mdA md' fm am am' →
                TeleRel (Rs.ibind ∣ S' ∣ md) (At.R.bind S' mdA) (Rs'.ibind ∣ S' ∣ md') (Ft.fbind S' fm)
                        (FR.abind S' md am) (FR'.abind S' md' am')

      tele-shape : ∀ {j} (S : Poly j) {ηA ηB ηC ηD} {dA dB dC dD}
                   {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                   {am : FR.FAct md dA dB} {am' : FR'.FAct md' dD dC}
                   (rel : TeleRel md mdA md' fm am am') (z : Ft.Tδ.⟦ ∣ S ∣ ⟧shape ηA) →
                   Tt.shape≈ ∣ S ∣ ηB
                     (Rs.ireindex-shape ∣ S ∣ md z)
                     (At.R.reindex-shape ∣ S ∣ mdA (Rs'.ireindex-shape ∣ S ∣ md' (Ft.fold-reindex-shape γ S fm z)))
      tele-shape (const A') rel z = A' .idx .isEquivalence .refl
      tele-shape (var v) rel z = tele-apply rel v
      tele-shape (S₁ + S₂) rel (inj₁ z) = tele-shape S₁ rel z
      tele-shape (S₁ + S₂) rel (inj₂ z) = tele-shape S₂ rel z
      tele-shape (S₁ × S₂) rel (z₁ , z₂) = tele-shape S₁ rel z₁ , tele-shape S₂ rel z₂
      tele-shape (μ S') rel (Ts.sup z') = tele-shape S' (tbind S' rel) z'

      tele-apply : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD}
                   {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                   {am : FR.FAct md dA dB} {am' : FR'.FAct md' dD dC}
                   (rel : TeleRel md mdA md' fm am am') (v : Fin j) {z} →
                   Tt.elEq (ηB v) (Rs.iapply md v z) (At.R.apply mdA v (Rs'.iapply md' v (Ft.fold-apply γ fm v z)))
      tele-apply (tbind S' r) Fin.zero    {z} = tele-shape (μ S') r z
      tele-apply (tbind S' r) (Fin.suc v)     = tele-apply r v
      tele-apply tbase Fin.zero    {z} =
        fuse-idx Q cmb fsk corr (Γ .idx .isEquivalence .refl {γ}) {m₁ = z} {m₂ = z}
          (μ-fam Q sₛ .idx .isEquivalence .refl {z})
      tele-apply tbase (Fin.suc i) {z} = Tt.elEq-refl (inj₁ i) (Rs.iapply (cmb γ) i z)

      tele-shape-fam : ∀ {j} (S : Poly j) {ηA ηB ηC ηD} {dA dB dC dD}
                       {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                       {am : FR.FAct md dA dB} {am' : FR'.FAct md' dD dC}
                       (rel : TeleRel md mdA md' fm am am') (z : Ft.Tδ.⟦ ∣ S ∣ ⟧shape ηA) →
                       (Tt.fib-shape-subst S dB (tele-shape S rel z) ∘ FR.freindex-shape-fam S am {z})
                       ≈ (At.R.reindex-fam S mdA
                          ∘ (FR'.freindex-shape-fam S am' {Ft.fold-reindex-shape γ S fm z}
                             ∘ pair p₁ (Ft.fold-reindex-shape-fam γ S fm z)))
      tele-shape-fam (const A') rel z =
        ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) (≈-trans id-left (≈-sym (≈-trans id-left (pair-p₂ _ _))))
      tele-shape-fam (var v) rel z = tele-apply-fam rel v
      tele-shape-fam (S₁ + S₂) rel (inj₁ z) =
        ≈-trans (strong-Lmap-post _ _)
        (≈-trans (strong-Lmap-cong (tele-shape-fam S₁ rel z))
                 (≈-sym (≈-trans (∘-cong ≈-refl (strong-Lmap-co _ _)) (strong-Lmap-post _ _))))
      tele-shape-fam (S₁ + S₂) rel (inj₂ z) =
        ≈-trans (strong-Lmap-post _ _)
        (≈-trans (strong-Lmap-cong (tele-shape-fam S₂ rel z))
                 (≈-sym (≈-trans (∘-cong ≈-refl (strong-Lmap-co _ _)) (strong-Lmap-post _ _))))
      tele-shape-fam (S₁ × S₂) rel (z₁ , z₂) =
        ≈-trans (strong-Lmap-post _ _)
        (≈-trans (strong-Lmap-cong
                   (≈-trans (strong-prod-m-post _ _ _ _)
                     (≈-trans (strong-prod-m-cong (tele-shape-fam S₁ rel z₁) (tele-shape-fam S₂ rel z₂))
                       (≈-sym (≈-trans (∘-cong ≈-refl (strong-prod-m-comp _ _ _ _)) (strong-prod-m-post _ _ _ _))))))
                 (≈-sym (≈-trans (∘-cong ≈-refl (strong-Lmap-co _ _)) (strong-Lmap-post _ _))))
      tele-shape-fam (μ S') rel (Ts.sup z') = tele-shape-fam S' (tbind S' rel) z'

      tele-apply-fam : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD}
                       {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                       {am : FR.FAct md dA dB} {am' : FR'.FAct md' dD dC}
                       (rel : TeleRel md mdA md' fm am am') (v : Fin j) {z} →
                       (Tt.fib-el-subst (ηB v) (dB v) (tele-apply rel v {z}) ∘ FR.aapply am v z)
                       ≈ (At.R.apply-fam mdA v (Rs'.iapply md' v (Ft.fold-apply γ fm v z))
                          ∘ (FR'.aapply am' v (Ft.fold-apply γ fm v z)
                             ∘ pair p₁ (Ft.fold-apply-fam γ fm v z)))
      tele-apply-fam (tbind S' r) Fin.zero    {z} = tele-shape-fam (μ S') r z
      tele-apply-fam (tbind S' r) (Fin.suc v)     = tele-apply-fam r v
      tele-apply-fam tbase Fin.zero    {z} =
        ≈-trans (fuse-fam γ Q cmb act fsk corr corr-fam {z}) (≈-sym (≈-trans id-left (pair-p₂ _ _)))
      tele-apply-fam tbase (Fin.suc i) {z} =
        ≈-trans (∘-cong (sₜ i .fam .refl*) ≈-refl)
          (≈-trans id-left (≈-sym (≈-trans id-left (≈-trans (∘-cong ≈-refl pair-ext0) id-right))))

-- The algebra map is an isomorphism. The bridge reindexing has an inverse with identity fibre maps,
-- and the two composites are the identity on trees and on fibres, the relation pairing each
-- extension of the inverse with the extension it undoes.

module LambekDef {n} (P : Poly (suc n)) (δ : Fin n → Obj) where
  private module At = InMapDef P δ
  open At using (module TX; module R; mor₀; m₀; embed-idx; unembed-idx)
  private
    module Tδ = Tree δ
    module R' = Reindex δ (extend δ (μ-fam P δ))

  -- The inverse bridge: the recursion slot and the parameters map to themselves.
  m₀⁻ : ∀ v → Tδ.El (Srt.η₀ ∣ P ∣ v) → TX.El (inj₁ v)
  m₀⁻ Fin.zero    a = a
  m₀⁻ (Fin.suc i) a = a

  m₀⁻-resp : ∀ v {a a'} → Tδ.elEq (Srt.η₀ ∣ P ∣ v) a a' → TX.elEq (inj₁ v) (m₀⁻ v a) (m₀⁻ v a')
  m₀⁻-resp Fin.zero    p = p
  m₀⁻-resp (Fin.suc i) p = p

  m₀⁻-fam : ∀ v (a : Tδ.El (Srt.η₀ ∣ P ∣ v)) →
            Tδ.fib-el (Srt.η₀ ∣ P ∣ v) (Tδ.deco-ext P (λ i → lift tt) v) a
              ⇒ TX.fib-el (inj₁ v) (lift tt) (m₀⁻ v a)
  m₀⁻-fam Fin.zero    a = id _
  m₀⁻-fam (Fin.suc i) a = id _

  m₀⁻-fam-natural : ∀ v {a a'} (p : Tδ.elEq (Srt.η₀ ∣ P ∣ v) a a') →
                    (m₀⁻-fam v a' ∘ Tδ.fib-el-subst (Srt.η₀ ∣ P ∣ v) (Tδ.deco-ext P (λ i → lift tt) v) p)
                      ≈ (TX.fib-el-subst (inj₁ v) (lift tt) (m₀⁻-resp v p) ∘ m₀⁻-fam v a)
  m₀⁻-fam-natural Fin.zero    p = ≈-trans id-left (≈-sym id-right)
  m₀⁻-fam-natural (Fin.suc i) p = ≈-trans id-left (≈-sym id-right)

  mor₀⁻ : R'.MorD (Srt.η₀ ∣ P ∣) (λ v → inj₁ v) (Tδ.deco-ext P (λ i → lift tt)) (λ v → lift tt)
  mor₀⁻ = R'.base m₀⁻ m₀⁻-resp m₀⁻-fam m₀⁻-fam-natural

  -- Pair each extension of the inverse bridge with the extension of the bridge it undoes.
  data DRel : ∀ {j} {ρ : Fin j → Fin n ⊎ Sort n} {ρ' : Fin j → Fin (suc n) ⊎ Sort (suc n)}
              {d : ∀ v → Tδ.DecoAssign (ρ v)} {d' : ∀ v → TX.DecoAssign (ρ' v)} →
              R'.MorD ρ ρ' d d' → R.MorD ρ' ρ d' d →
              Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    dbase : DRel mor₀⁻ mor₀
    dbind : ∀ {j} {ρ ρ' d d'} {md' : R'.MorD {j} ρ ρ' d d'} {md} (Q' : Poly (suc j)) →
            DRel md' md → DRel (R'.bind Q' md') (R.bind Q' md)

  -- Round trip on the parameter side: back and forth is the identity.
  mutual
    drt-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md} → DRel md' md →
            (t : Tδ.W ∣ Q̂ ∣ ρ) → Tδ.W-≈ (R.reindex md (R'.reindex md' t)) t
    drt-W {Q̂ = Q̂} rel (Tδ.sup x) = drt-shape Q̂ (dbind Q̂ rel) x

    drt-shape : ∀ {j} (S : Poly j) {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md} → DRel md' md →
                (a : Tδ.⟦ ∣ S ∣ ⟧shape ρ) →
                Tδ.shape≈ ∣ S ∣ ρ (R.reindex-shape ∣ S ∣ md (R'.reindex-shape ∣ S ∣ md' a)) a
    drt-shape (const A') rel a = A' .idx .isEquivalence .refl
    drt-shape (var v)    rel a = drt-el rel v a
    drt-shape (P' + Q') rel (inj₁ a) = drt-shape P' rel a
    drt-shape (P' + Q') rel (inj₂ b) = drt-shape Q' rel b
    drt-shape (P' × Q') rel (a , b) = drt-shape P' rel a , drt-shape Q' rel b
    drt-shape (μ Q'')   rel t = drt-W {Q̂ = Q''} rel t

    drt-el : ∀ {j} {ρ ρ' d d'} {md' : R'.MorD {j} ρ ρ' d d'} {md} → DRel md' md →
             (v : Fin j) (a : Tδ.El (ρ v)) →
             Tδ.elEq (ρ v) (R.apply md v (R'.apply md' v a)) a
    drt-el dbase          Fin.zero    t = Tδ.elEq-refl (Srt.η₀ ∣ P ∣ Fin.zero) t
    drt-el dbase          (Fin.suc i) a = Tδ.elEq-refl (Srt.η₀ ∣ P ∣ (Fin.suc i)) a
    drt-el (dbind Q' rel) Fin.zero    a = drt-W {Q̂ = Q'} rel a
    drt-el (dbind Q' rel) (Fin.suc v) a = drt-el rel v a

  -- Round trip on the recursion side.
  mutual
    drt'-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md} → DRel md' md →
             (u : TX.W ∣ Q̂ ∣ ρ') → TX.W-≈ (R'.reindex md' (R.reindex md u)) u
    drt'-W {Q̂ = Q̂} rel (TX.sup x) = drt'-shape Q̂ (dbind Q̂ rel) x

    drt'-shape : ∀ {j} (S : Poly j) {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md} → DRel md' md →
                 (a : TX.⟦ ∣ S ∣ ⟧shape ρ') →
                 TX.shape≈ ∣ S ∣ ρ' (R'.reindex-shape ∣ S ∣ md' (R.reindex-shape ∣ S ∣ md a)) a
    drt'-shape (const A') rel a = A' .idx .isEquivalence .refl
    drt'-shape (var v)    rel a = drt'-el rel v a
    drt'-shape (P' + Q') rel (inj₁ a) = drt'-shape P' rel a
    drt'-shape (P' + Q') rel (inj₂ b) = drt'-shape Q' rel b
    drt'-shape (P' × Q') rel (a , b) = drt'-shape P' rel a , drt'-shape Q' rel b
    drt'-shape (μ Q'')   rel t = drt'-W {Q̂ = Q''} rel t

    drt'-el : ∀ {j} {ρ ρ' d d'} {md' : R'.MorD {j} ρ ρ' d d'} {md} → DRel md' md →
              (v : Fin j) (a : TX.El (ρ' v)) →
              TX.elEq (ρ' v) (R'.apply md' v (R.apply md v a)) a
    drt'-el dbase          Fin.zero    t = TX.elEq-refl (inj₁ Fin.zero) t
    drt'-el dbase          (Fin.suc i) a = TX.elEq-refl (inj₁ (Fin.suc i)) a
    drt'-el (dbind Q' rel) Fin.zero    a = drt'-W {Q̂ = Q'} rel a
    drt'-el (dbind Q' rel) (Fin.suc v) a = drt'-el rel v a

  -- Fibre halves of the round trips: the fibre composites, transported along the index round
  -- trips, are the identity. Pure Lmap and prod-m algebra; no isomorphisms are needed.
  mutual
    drt-fam-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
                (rel : DRel md' md) (t : Tδ.W ∣ Q̂ ∣ ρ) →
                (Tδ.fib-subst Q̂ d {x = R.reindex md (R'.reindex md' t)} {y = t} (drt-W rel t)
                  ∘ (R.reindex-fam-W md {t = R'.reindex md' t} ∘ R'.reindex-fam-W md' {t = t}))
                  ≈ id (Tδ.fib Q̂ d t)
    drt-fam-W {Q̂ = Q̂} rel (Tδ.sup x) = drt-shape-fam Q̂ (dbind Q̂ rel) x

    drt-shape-fam : ∀ {j} (S : Poly j) {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
                    (rel : DRel md' md) (a : Tδ.⟦ ∣ S ∣ ⟧shape ρ) →
                    (Tδ.fib-shape-subst S d (drt-shape S rel a)
                      ∘ (R.reindex-fam S md {a = R'.reindex-shape ∣ S ∣ md' a} ∘ R'.reindex-fam S md' {a = a}))
                      ≈ id (Tδ.fib-shape S d a)
    drt-shape-fam (const A') rel a =
      ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) (≈-trans id-left id-left)
    drt-shape-fam (var v) rel a = drt-el-fam rel v a
    drt-shape-fam (P' + Q') rel (inj₁ a) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (drt-shape-fam P' rel a)) Lmap-id))
    drt-shape-fam (P' + Q') rel (inj₂ b) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (drt-shape-fam Q' rel b)) Lmap-id))
    drt-shape-fam (P' × Q') rel (a , b) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong
                   (≈-trans (∘-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _)))
                     (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                       (≈-trans (prod-m-cong (drt-shape-fam P' rel a) (drt-shape-fam Q' rel b))
                                prod-m-id))))
                 Lmap-id))
    drt-shape-fam (μ Q'') rel t = drt-fam-W {Q̂ = Q''} rel t

    drt-el-fam : ∀ {j} {ρ ρ' d d'} {md' : R'.MorD {j} ρ ρ' d d'} {md}
                 (rel : DRel md' md) (v : Fin j) (a : Tδ.El (ρ v)) →
                 (Tδ.fib-el-subst (ρ v) (d v) (drt-el rel v a)
                   ∘ (R.apply-fam md v (R'.apply md' v a) ∘ R'.apply-fam md' v a))
                   ≈ id (Tδ.fib-el (ρ v) (d v) a)
    drt-el-fam dbase Fin.zero t =
      ≈-trans (∘-cong (Tδ.fib-el-refl* (Srt.η₀ ∣ P ∣ Fin.zero) (Tδ.deco-ext P (λ i → lift tt) Fin.zero) t)
                      ≈-refl)
              (≈-trans id-left id-left)
    drt-el-fam dbase (Fin.suc i) a =
      ≈-trans (∘-cong (Tδ.fib-el-refl* (Srt.η₀ ∣ P ∣ (Fin.suc i))
                                       (Tδ.deco-ext P {ρ̄ = λ v → inj₁ v} (λ _ → lift tt) (Fin.suc i)) a)
                      ≈-refl)
              (≈-trans id-left id-left)
    drt-el-fam (dbind Q' rel) Fin.zero    a = drt-fam-W {Q̂ = Q'} rel a
    drt-el-fam (dbind Q' rel) (Fin.suc v) a = drt-el-fam rel v a

  mutual
    drt'-fam-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
                 (rel : DRel md' md) (u : TX.W ∣ Q̂ ∣ ρ') →
                 (TX.fib-subst Q̂ d' {x = R'.reindex md' (R.reindex md u)} {y = u} (drt'-W rel u)
                   ∘ (R'.reindex-fam-W md' {t = R.reindex md u} ∘ R.reindex-fam-W md {t = u}))
                   ≈ id (TX.fib Q̂ d' u)
    drt'-fam-W {Q̂ = Q̂} rel (TX.sup x) = drt'-shape-fam Q̂ (dbind Q̂ rel) x

    drt'-shape-fam : ∀ {j} (S : Poly j) {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
                     (rel : DRel md' md) (a : TX.⟦ ∣ S ∣ ⟧shape ρ') →
                     (TX.fib-shape-subst S d' (drt'-shape S rel a)
                       ∘ (R'.reindex-fam S md' {a = R.reindex-shape ∣ S ∣ md a} ∘ R.reindex-fam S md {a = a}))
                       ≈ id (TX.fib-shape S d' a)
    drt'-shape-fam (const A') rel a =
      ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) (≈-trans id-left id-left)
    drt'-shape-fam (var v) rel a = drt'-el-fam rel v a
    drt'-shape-fam (P' + Q') rel (inj₁ a) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (drt'-shape-fam P' rel a)) Lmap-id))
    drt'-shape-fam (P' + Q') rel (inj₂ b) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (drt'-shape-fam Q' rel b)) Lmap-id))
    drt'-shape-fam (P' × Q') rel (a , b) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong
                   (≈-trans (∘-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _)))
                     (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                       (≈-trans (prod-m-cong (drt'-shape-fam P' rel a) (drt'-shape-fam Q' rel b))
                                prod-m-id))))
                 Lmap-id))
    drt'-shape-fam (μ Q'') rel t = drt'-fam-W {Q̂ = Q''} rel t

    drt'-el-fam : ∀ {j} {ρ ρ' d d'} {md' : R'.MorD {j} ρ ρ' d d'} {md}
                  (rel : DRel md' md) (v : Fin j) (a : TX.El (ρ' v)) →
                  (TX.fib-el-subst (ρ' v) (d' v) (drt'-el rel v a)
                    ∘ (R'.apply-fam md' v (R.apply md v a) ∘ R.apply-fam md v a))
                    ≈ id (TX.fib-el (ρ' v) (d' v) a)
    drt'-el-fam dbase Fin.zero t =
      ≈-trans (∘-cong (TX.fib-el-refl* (inj₁ Fin.zero) (lift tt) t) ≈-refl) (≈-trans id-left id-left)
    drt'-el-fam dbase (Fin.suc i) a =
      ≈-trans (∘-cong (TX.fib-el-refl* (inj₁ (Fin.suc i)) (lift tt) a) ≈-refl) (≈-trans id-left id-left)
    drt'-el-fam (dbind Q' rel) Fin.zero    a = drt'-fam-W {Q̂ = Q'} rel a
    drt'-el-fam (dbind Q' rel) (Fin.suc v) a = drt'-el-fam rel v a

  -- The inverse of inMor: strip the root, reindex back to the fresh context, unembed.
  u-idx : Tδ.W ∣ P ∣ (λ i → inj₁ i) → fobj μ-fam P At.δ' .idx .Carrier
  u-idx (Tδ.sup x) = unembed-idx P (R'.reindex-shape ∣ P ∣ mor₀⁻ x)

  u-resp : {t t' : Tδ.W ∣ P ∣ (λ i → inj₁ i)} → Tδ.W-≈ t t' →
           _≈s_ (fobj μ-fam P At.δ' .idx) (u-idx t) (u-idx t')
  u-resp {Tδ.sup x} {Tδ.sup y} p =
    At.unembed-idx-resp P (R'.reindex-shape-resp ∣ P ∣ mor₀⁻ p)

  u-fam : (t : Tδ.W ∣ P ∣ (λ i → inj₁ i)) →
          μ-fam P δ .fam .fm t ⇒ fobj μ-fam P At.δ' .fam .fm (u-idx t)
  u-fam (Tδ.sup x) =
    At.unembed-fam P (R'.reindex-shape ∣ P ∣ mor₀⁻ x) ∘ R'.reindex-fam P mor₀⁻ {a = x}

  outMor : Mor (μ-fam P δ) (fobj μ-fam P At.δ')
  outMor .idxf .PS._⇒_.func = u-idx
  outMor .idxf .PS._⇒_.func-resp-≈ {t} {t'} = u-resp {t} {t'}
  outMor .famf ._⇒f_.transf = u-fam
  outMor .famf ._⇒f_.natural {Tδ.sup x} {Tδ.sup y} e =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (R'.reindex-fam-natural P mor₀⁻ e))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (At.unembed-fam-natural P (R'.reindex-shape-resp ∣ P ∣ mor₀⁻ e)))
             (assoc _ _ _))))

  -- The triangle identities: inMor is an isomorphism (Lambek), with outMor the inverse. The index
  -- halves compose the bridges' round trips with the reindex round trips; the fibre halves push
  -- the transports through the fibre actions by naturality and close with the fibre round trips.
  inMor-outMor : Fam𝒞._∘_ At.inMor outMor ≃ Fam𝒞.id (μ-fam P δ)
  inMor-outMor ._≃_.idxf-eq .PS._≃m_.func-eq {Tδ.sup x} {Tδ.sup y} e =
    Tδ.shape≈-trans ∣ P ∣ (Srt.η₀ ∣ P ∣)
      (Tδ.shape≈-trans ∣ P ∣ (Srt.η₀ ∣ P ∣)
        (R.reindex-shape-resp ∣ P ∣ mor₀ (At.embed-unembed P (R'.reindex-shape ∣ P ∣ mor₀⁻ x)))
        (drt-shape P dbase x))
      e
  inMor-outMor ._≃_.famf-eq .indexed-family._≃f_.transf-eq {Tδ.sup x} =
    ≈-trans (∘-cong (Tδ.fib-shape-trans* P (Tδ.deco-ext P {ρ̄ = λ v → inj₁ v} (λ _ → lift tt))
                       (drt-shape P dbase x)
                       (R.reindex-shape-resp ∣ P ∣ mor₀ (At.embed-unembed P z)))
                    id-left)
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ step₂) (drt-shape-fam P dbase x)))
    where
      z = R'.reindex-shape ∣ P ∣ mor₀⁻ x

      step₃ = ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (≈-sym (R.reindex-fam-natural P mor₀ (At.embed-unembed P z))))
                       (assoc _ _ _))
      step₄ = ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (≈-trans (assoc _ _ _) (At.embed-unembed-fam P z)))
                       id-left)
      step₂ = ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ step₃)
              (≈-trans (assoc _ _ _)
                       (∘-cong₂ step₄)))

  outMor-inMor : Fam𝒞._∘_ outMor At.inMor ≃ Fam𝒞.id (fobj μ-fam P At.δ')
  outMor-inMor ._≃_.idxf-eq .PS._≃m_.func-eq {i} {i'} e =
    fobj μ-fam P At.δ' .idx .isEquivalence .trans
      (fobj μ-fam P At.δ' .idx .isEquivalence .trans
        (At.unembed-idx-resp P (drt'-shape P dbase (At.embed-idx P i)))
        (At.unembed-embed P i))
      e
  outMor-inMor ._≃_.famf-eq .indexed-family._≃f_.transf-eq {i} =
    ≈-trans (∘-cong (fobj μ-fam P At.δ' .fam .trans*
                       (At.unembed-embed P i)
                       (At.unembed-idx-resp P (drt'-shape P dbase (At.embed-idx P i))))
                    id-left)
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ step₂) (At.unembed-embed-fam P i)))
    where
      step₃ = ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (≈-sym (At.unembed-fam-natural P (drt'-shape P dbase (At.embed-idx P i)))))
                       (assoc _ _ _))
      step₄ = ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (≈-trans (assoc _ _ _) (drt'-shape-fam P dbase (At.embed-idx P i))))
                       id-left)
      step₂ = ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ step₃)
              (≈-trans (assoc _ _ _)
                       (∘-cong₂ step₄)))

  module OutMorSection (δc : ∀ i → Section (δ i)) (Pc : PolySection P) where
    private
      μc : Section (μ-fam P δ)
      μc = MuSection.μ-section δ δc P Pc
      module Mδ = MuSection δ δc
      module MXs = MuSection (extend δ (μ-fam P δ)) (extend-section δc μc)
      module RS' = ReindexSection δc (extend-section δc μc)
      module AtS = At.InMapSection δc Pc

    mor₀⁻-sec : RS'.MorDSec mor₀⁻ (Mδ.deco-ext-section P Pc (λ i → lift tt)) (λ v → lift tt)
    mor₀⁻-sec = RS'.base-s h
      where
      h : ∀ v a → (m₀⁻-fam v a ∘ Mδ.fib-el-unit (Srt.η₀ ∣ P ∣ v) (Tδ.deco-ext P (λ i → lift tt) v)
                     (Mδ.deco-ext-section P Pc (λ i → lift tt) v) a)
                  ≈ MXs.fib-el-unit (inj₁ v) (lift tt) (lift tt) (m₀⁻ v a)
      h Fin.zero    a = id-left
      h (Fin.suc i) a = id-left

    preserves-outMor : preserves-section outMor μc (poly-section P Pc (extend-section δc μc))
    preserves-outMor .at (Tδ.sup x) =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (RS'.reindex-fam-unit P Pc mor₀⁻-sec x))
               (AtS.unembed-unit P Pc (R'.reindex-shape ∣ P ∣ mor₀⁻ x)))

preserves-outMor : ∀ {n} (P : Poly (suc n)) (δ : Fin n → Obj)
                   (δc : ∀ i → Section (δ i)) (Pc : PolySection P) →
                   preserves-section (LambekDef.outMor P δ)
                     (MuSection.μ-section δ δc P Pc)
                     (poly-section P Pc (extend-section δc (MuSection.μ-section δ δc P Pc)))
preserves-outMor P δ δc Pc = LambekDef.OutMorSection.preserves-outMor P δ δc Pc

-- The initial-algebra laws for the tree model. A fused form first: a candidate is a fold when it is
-- the algebra applied to itself at every node, by the same recursion as the fold. The bridge then
-- identifies that application, at the shape under the algebra map, with the strong action of the
-- candidate, which gives β and η in their categorical form and the HasMuLaws instance.

-- One application of the algebra against a candidate at the recursive positions: the same
-- recursion as the fold, with the candidate at the slot.
module ApplyDef {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (let module Tδ = Tree δ)
    (h-idx : Γ .idx .Carrier → Tδ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier)
    (h-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : Tδ.W-≈ t t') →
              _≈s_ (A .idx) (h-idx γ t) (h-idx γ' t'))
    (h-fam : ∀ γ t →
             prod (Γ .fam .fm γ) (Tδ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (h-idx γ t))
    where
    open FoldBase {n} {Γ} {A} {P} {δ} hiding (module Tδ)
    mutual
      apply-shape-idx : (Q : Poly (suc n)) → Γ .idx .Carrier → Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣) →
                      fobj μ-fam Q (extend δ A) .idx .Carrier
      apply-shape-idx (const A')        γ a = a
      apply-shape-idx (var Fin.zero)    γ t = h-idx γ t
      apply-shape-idx (var (Fin.suc i)) γ a = a
      apply-shape-idx (Q₁ + Q₂) γ (inj₁ x) = inj₁ (apply-shape-idx Q₁ γ x)
      apply-shape-idx (Q₁ + Q₂) γ (inj₂ y) = inj₂ (apply-shape-idx Q₂ γ y)
      apply-shape-idx (Q₁ × Q₂) γ (x , y) = apply-shape-idx Q₁ γ x , apply-shape-idx Q₂ γ y
      apply-shape-idx (μ Q')    γ t = apply-reindex {Q = Q'} γ fbase t

      apply-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') →
                     Tδ.W ∣ Q ∣ ρ → TA'.W ∣ Q ∣ ρ'
      apply-reindex {Q = Q} γ fm (Tδ.sup x) = TA'.sup (apply-reindex-shape γ Q (fbind Q fm) x)

      apply-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB) →
                           Tδ.⟦ ∣ R ∣ ⟧shape ηA → TA'.⟦ ∣ R ∣ ⟧shape ηB
      apply-reindex-shape γ (const A') fm a = a
      apply-reindex-shape γ (var v)    fm a = apply-apply γ fm v a
      apply-reindex-shape γ (P' + Q') fm (inj₁ a) = inj₁ (apply-reindex-shape γ P' fm a)
      apply-reindex-shape γ (P' + Q') fm (inj₂ b) = inj₂ (apply-reindex-shape γ Q' fm b)
      apply-reindex-shape γ (P' × Q') fm (a , b) = apply-reindex-shape γ P' fm a , apply-reindex-shape γ Q' fm b
      apply-reindex-shape γ (μ Q'')   fm t = apply-reindex {Q = Q''} γ fm t

      apply-apply : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k) →
                   Tδ.El (ρ v) → TA'.El (ρ' v)
      apply-apply γ fbase        Fin.zero    t = h-idx γ t
      apply-apply γ fbase        (Fin.suc i) a = a
      apply-apply γ (fbind Q fm) Fin.zero    a = apply-reindex {Q = Q} γ fm a
      apply-apply γ (fbind Q fm) (Fin.suc v) a = apply-apply γ fm v a

    mutual
      apply-shape-idx-resp : (Q : Poly (suc n)) → ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {x x'}
                           (p : Tδ.shape≈ ∣ Q ∣ (Srt.η₀ ∣ P ∣) x x') →
                           _≈s_ (fobj μ-fam Q (extend δ A) .idx) (apply-shape-idx Q γ x) (apply-shape-idx Q γ' x')
      apply-shape-idx-resp (const A')        γ≈ p = p
      apply-shape-idx-resp (var Fin.zero)    γ≈ {x} {x'} p = h-resp γ≈ {x} {x'} p
      apply-shape-idx-resp (var (Fin.suc i)) γ≈ p = p
      apply-shape-idx-resp (Q₁ + Q₂) γ≈ {inj₁ _} {inj₁ _} p = apply-shape-idx-resp Q₁ γ≈ p
      apply-shape-idx-resp (Q₁ + Q₂) γ≈ {inj₂ _} {inj₂ _} p = apply-shape-idx-resp Q₂ γ≈ p
      apply-shape-idx-resp (Q₁ × Q₂) γ≈ {_ , _} {_ , _} (p₁ , p₂) =
        apply-shape-idx-resp Q₁ γ≈ p₁ , apply-shape-idx-resp Q₂ γ≈ p₂
      apply-shape-idx-resp (μ Q')    γ≈ {x} {x'} p = apply-reindex-resp {Q = Q'} γ≈ fbase {x} {x'} p

      apply-reindex-resp : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (fm : FMor ρ ρ' d d')
                          {t t' : Tδ.W ∣ Q ∣ ρ} (p : Tδ.W-≈ t t') →
                          TA'.W-≈ (apply-reindex γ fm t) (apply-reindex γ' fm t')
      apply-reindex-resp {Q = Q} γ≈ fm {Tδ.sup x} {Tδ.sup y} p = apply-reindex-shape-resp γ≈ Q (fbind Q fm) {x} {y} p

      apply-reindex-shape-resp : ∀ {j} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB)
                                {a a' : Tδ.⟦ ∣ R ∣ ⟧shape ηA} (p : Tδ.shape≈ ∣ R ∣ ηA a a') →
                                TA'.shape≈ ∣ R ∣ ηB (apply-reindex-shape γ R fm a) (apply-reindex-shape γ' R fm a')
      apply-reindex-shape-resp γ≈ (const A') fm p = p
      apply-reindex-shape-resp γ≈ (var v)    fm p = apply-apply-resp γ≈ fm v p
      apply-reindex-shape-resp γ≈ (P' + Q') fm {inj₁ _} {inj₁ _} p = apply-reindex-shape-resp γ≈ P' fm p
      apply-reindex-shape-resp γ≈ (P' + Q') fm {inj₂ _} {inj₂ _} p = apply-reindex-shape-resp γ≈ Q' fm p
      apply-reindex-shape-resp γ≈ (P' × Q') fm {_ , _} {_ , _} (p₁ , p₂) =
        apply-reindex-shape-resp γ≈ P' fm p₁ , apply-reindex-shape-resp γ≈ Q' fm p₂
      apply-reindex-shape-resp γ≈ (μ Q'')   fm {a} {a'} p = apply-reindex-resp {Q = Q''} γ≈ fm {a} {a'} p

      apply-apply-resp : ∀ {k} {ρ ρ' d d'} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (fm : FMor ρ ρ' d d') (v : Fin k)
                        {a a'} (p : Tδ.elEq (ρ v) a a') →
                        TA'.elEq (ρ' v) (apply-apply γ fm v a) (apply-apply γ' fm v a')
      apply-apply-resp γ≈ fbase        Fin.zero    {a} {a'} p = h-resp γ≈ {a} {a'} p
      apply-apply-resp γ≈ fbase        (Fin.suc i) p = p
      apply-apply-resp γ≈ (fbind Q fm) Fin.zero    {a} {a'} p = apply-reindex-resp {Q = Q} γ≈ fm {a} {a'} p
      apply-apply-resp γ≈ (fbind Q fm) (Fin.suc v) p = apply-apply-resp γ≈ fm v p

    mutual
      apply-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                       prod (Γ .fam .fm γ) (Tδ.fib-shape Q (Tδ.deco-ext P (λ i → lift tt)) x)
                         ⇒ fobj μ-fam Q (extend δ A) .fam .fm (apply-shape-idx Q γ x)
      apply-shape-fam (const A')        γ a = p₂
      apply-shape-fam (var Fin.zero)    γ t = h-fam γ t
      apply-shape-fam (var (Fin.suc i)) γ a = p₂
      apply-shape-fam (Q₁ + Q₂) γ (inj₁ x) = strong-Lmap (apply-shape-fam Q₁ γ x)
      apply-shape-fam (Q₁ + Q₂) γ (inj₂ y) = strong-Lmap (apply-shape-fam Q₂ γ y)
      apply-shape-fam (Q₁ × Q₂) γ (x , y) =
        strong-Lmap (strong-prod-m (apply-shape-fam Q₁ γ x) (apply-shape-fam Q₂ γ y))
      apply-shape-fam (μ Q')    γ t = apply-reindex-fam {Q = Q'} γ fbase t

      apply-reindex-fam : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ' d d') (t : Tδ.W ∣ Q ∣ ρ) →
                         prod (Γ .fam .fm γ) (Tδ.fib Q d t) ⇒ TA'.fib Q d' (apply-reindex γ md t)
      apply-reindex-fam {Q = Q} γ md (Tδ.sup x) = apply-reindex-shape-fam γ Q (fbind Q md) x

      apply-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (md : FMor ηA ηB dA dB) (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                               prod (Γ .fam .fm γ) (Tδ.fib-shape R dA a) ⇒ TA'.fib-shape R dB (apply-reindex-shape γ R md a)
      apply-reindex-shape-fam γ (const A') md a = p₂
      apply-reindex-shape-fam γ (var v)    md a = apply-apply-fam γ md v a
      apply-reindex-shape-fam γ (P' + Q') md (inj₁ a) = strong-Lmap (apply-reindex-shape-fam γ P' md a)
      apply-reindex-shape-fam γ (P' + Q') md (inj₂ b) = strong-Lmap (apply-reindex-shape-fam γ Q' md b)
      apply-reindex-shape-fam γ (P' × Q') md (a , b) =
        strong-Lmap (strong-prod-m (apply-reindex-shape-fam γ P' md a) (apply-reindex-shape-fam γ Q' md b))
      apply-reindex-shape-fam γ (μ Q'')   md t = apply-reindex-fam {Q = Q''} γ md t

      apply-apply-fam : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ' d d') (v : Fin k) (a : Tδ.El (ρ v)) →
                       prod (Γ .fam .fm γ) (Tδ.fib-el (ρ v) (d v) a) ⇒ TA'.fib-el (ρ' v) (d' v) (apply-apply γ md v a)
      apply-apply-fam γ fbase        Fin.zero    t = h-fam γ t
      apply-apply-fam γ fbase        (Fin.suc i) a = p₂
      apply-apply-fam γ (fbind Q md) Fin.zero    a = apply-reindex-fam {Q = Q} γ md a
      apply-apply-fam γ (fbind Q md) (Fin.suc v) a = apply-apply-fam γ md v a


-- The fused law: a candidate is a fold when it is the algebra applied to itself at every node. The
-- fold's recursion agrees with the application at the fold, and the fused law determines the fold.
module Laws {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (alg : Mor (Fam𝒞-P.prod Γ (fobj μ-fam P (extend δ A))) A) where
  open FoldBase {n} {Γ} {A} {P} {δ}
  module Ft = FoldDef {n} {Γ} {A} {P} {δ} alg
  module Ap (h-idx : Γ .idx .Carrier → Tδ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier)
            (h-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : Tδ.W-≈ t t') →
                      _≈s_ (A .idx) (h-idx γ t) (h-idx γ' t'))
            (h-fam : ∀ γ t →
                     prod (Γ .fam .fm γ) (Tδ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (h-idx γ t)) =
    ApplyDef {n} {Γ} {A} {P} {δ} h-idx h-resp h-fam
  module Af = Ap Ft.fold-idx Ft.fold-idx-resp Ft.fold-fam

  record IsFold
      (h-idx : Γ .idx .Carrier → Tδ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier)
      (h-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : Tδ.W-≈ t t') →
                _≈s_ (A .idx) (h-idx γ t) (h-idx γ' t'))
      (h-fam : ∀ γ t →
               prod (Γ .fam .fm γ) (Tδ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (h-idx γ t)) :
      Prop (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    field
      is-idx : ∀ γ x → _≈s_ (A .idx)
               (h-idx γ (Tδ.sup x))
               (alg .idxf .PS._⇒_.func (γ , Ap.apply-shape-idx h-idx h-resp h-fam P γ x))
      is-fam : ∀ γ x →
               h-fam γ (Tδ.sup x)
               ≈ (A .fam .subst (A .idx .isEquivalence .sym (is-idx γ x))
                  ∘ (alg .famf ._⇒f_.transf (γ , Ap.apply-shape-idx h-idx h-resp h-fam P γ x)
                     ∘ pair p₁ (Ap.apply-shape-fam h-idx h-resp h-fam P γ x)))

  -- Index agreement between the fold's recursion and the application at the fold.
  mutual
    agree-shape : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                  _≈s_ (fobj μ-fam Q (extend δ A) .idx) (Ft.fold-shape-idx Q γ x) (Af.apply-shape-idx Q γ x)
    agree-shape (const A')        γ a = A' .idx .isEquivalence .refl
    agree-shape (var Fin.zero)    γ t = A .idx .isEquivalence .refl
    agree-shape (var (Fin.suc i)) γ a = δ i .idx .isEquivalence .refl
    agree-shape (Q₁ + Q₂) γ (inj₁ x) = agree-shape Q₁ γ x
    agree-shape (Q₁ + Q₂) γ (inj₂ y) = agree-shape Q₂ γ y
    agree-shape (Q₁ × Q₂) γ (x , y) = agree-shape Q₁ γ x , agree-shape Q₂ γ y
    agree-shape (μ Q')    γ t = agree-reindex {Q = Q'} γ fbase t

    agree-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d')
                    (t : Tδ.W ∣ Q ∣ ρ) →
                    TA'.W-≈ (Ft.fold-reindex γ fm t) (Af.apply-reindex γ fm t)
    agree-reindex {Q = Q} γ fm (Tδ.sup x) = agree-reindex-shape γ Q (fbind Q fm) x

    agree-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB)
                          (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                          TA'.shape≈ ∣ R ∣ ηB (Ft.fold-reindex-shape γ R fm a) (Af.apply-reindex-shape γ R fm a)
    agree-reindex-shape γ (const A') fm a = A' .idx .isEquivalence .refl
    agree-reindex-shape γ (var v)    fm a = agree-apply γ fm v a
    agree-reindex-shape γ (P' + Q') fm (inj₁ a) = agree-reindex-shape γ P' fm a
    agree-reindex-shape γ (P' + Q') fm (inj₂ b) = agree-reindex-shape γ Q' fm b
    agree-reindex-shape γ (P' × Q') fm (a , b) = agree-reindex-shape γ P' fm a , agree-reindex-shape γ Q' fm b
    agree-reindex-shape γ (μ Q'')   fm t = agree-reindex {Q = Q''} γ fm t

    agree-apply : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k)
                  (a : Tδ.El (ρ v)) →
                  TA'.elEq (ρ' v) (Ft.fold-apply γ fm v a) (Af.apply-apply γ fm v a)
    agree-apply γ fbase        Fin.zero    t = A .idx .isEquivalence .refl
    agree-apply γ fbase        (Fin.suc i) a = TA'.elEq-refl (inj₁ (Fin.suc i)) a
    agree-apply γ (fbind Q fm) Fin.zero    a = agree-reindex {Q = Q} γ fm a
    agree-apply γ (fbind Q fm) (Fin.suc v) a = agree-apply γ fm v a

  -- Fibre agreement: the fold's fibre transported along the index agreement is the application's
  -- fibre. At the value formers the transport passes across the lifting and the congruence closes
  -- on the branch, exactly as in the fold's naturality.
  mutual
    agree-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                      (fobj μ-fam Q (extend δ A) .fam .subst (agree-shape Q γ x) ∘ Ft.fold-shape-fam Q γ x)
                        ≈ Af.apply-shape-fam Q γ x
    agree-shape-fam (const A')        γ a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
    agree-shape-fam (var Fin.zero)    γ t = ≈-trans (∘-cong (A .fam .refl*) ≈-refl) id-left
    agree-shape-fam (var (Fin.suc i)) γ a = ≈-trans (∘-cong (δ i .fam .refl*) ≈-refl) id-left
    agree-shape-fam (Q₁ + Q₂) γ (inj₁ x) =
      ≈-trans (strong-Lmap-post _
                (Ft.fold-shape-fam Q₁ γ x))
              (strong-Lmap-cong (agree-shape-fam Q₁ γ x))
    agree-shape-fam (Q₁ + Q₂) γ (inj₂ y) =
      ≈-trans (strong-Lmap-post _
                (Ft.fold-shape-fam Q₂ γ y))
              (strong-Lmap-cong (agree-shape-fam Q₂ γ y))
    agree-shape-fam (Q₁ × Q₂) γ (x , y) =
      ≈-trans (strong-Lmap-post _
                (strong-prod-m (Ft.fold-shape-fam Q₁ γ x) (Ft.fold-shape-fam Q₂ γ y)))
              (strong-Lmap-cong
                (≈-trans (strong-prod-m-post _ _ _ _)
                         (strong-prod-m-cong (agree-shape-fam Q₁ γ x) (agree-shape-fam Q₂ γ y))))
    agree-shape-fam (μ Q') γ t = agree-reindex-fam {Q = Q'} γ fbase t

    agree-reindex-fam : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier)
                        (fm : FMor ρ ρ' d d') (t : Tδ.W ∣ Q ∣ ρ) →
                        (TA'.fib-subst Q d' {x = Ft.fold-reindex γ fm t} {y = Af.apply-reindex γ fm t}
                           (agree-reindex {Q = Q} γ fm t)
                         ∘ Ft.fold-reindex-fam γ fm t)
                          ≈ Af.apply-reindex-fam γ fm t
    agree-reindex-fam {Q = Q} γ fm (Tδ.sup x) = agree-reindex-shape-fam γ Q (fbind Q fm) x

    agree-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB}
                              (fm : FMor ηA ηB dA dB) (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                              (TA'.fib-shape-subst R dB (agree-reindex-shape γ R fm a)
                               ∘ Ft.fold-reindex-shape-fam γ R fm a)
                                ≈ Af.apply-reindex-shape-fam γ R fm a
    agree-reindex-shape-fam γ (const A') fm a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
    agree-reindex-shape-fam γ (var v)    fm a = agree-apply-fam γ fm v a
    agree-reindex-shape-fam γ (P' + Q') {dA = dA} {dB} fm (inj₁ a) =
      ≈-trans (strong-Lmap-post _
                (Ft.fold-reindex-shape-fam γ P' fm a))
              (strong-Lmap-cong (agree-reindex-shape-fam γ P' fm a))
    agree-reindex-shape-fam γ (P' + Q') {dA = dA} {dB} fm (inj₂ b) =
      ≈-trans (strong-Lmap-post _
                (Ft.fold-reindex-shape-fam γ Q' fm b))
              (strong-Lmap-cong (agree-reindex-shape-fam γ Q' fm b))
    agree-reindex-shape-fam γ (P' × Q') {dA = dA} {dB} fm (a , b) =
      ≈-trans (strong-Lmap-post _
                (strong-prod-m (Ft.fold-reindex-shape-fam γ P' fm a) (Ft.fold-reindex-shape-fam γ Q' fm b)))
              (strong-Lmap-cong
                (≈-trans (strong-prod-m-post _ _ _ _)
                         (strong-prod-m-cong (agree-reindex-shape-fam γ P' fm a)
                                             (agree-reindex-shape-fam γ Q' fm b))))
    agree-reindex-shape-fam γ (μ Q'')   fm t = agree-reindex-fam {Q = Q''} γ fm t

    agree-apply-fam : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k)
                      (a : Tδ.El (ρ v)) →
                      (TA'.fib-el-subst (ρ' v) (d' v) (agree-apply γ fm v a)
                       ∘ Ft.fold-apply-fam γ fm v a)
                        ≈ Af.apply-apply-fam γ fm v a
    agree-apply-fam γ fbase        Fin.zero    t = ≈-trans (∘-cong (A .fam .refl*) ≈-refl) id-left
    agree-apply-fam γ fbase        (Fin.suc i) a =
      ≈-trans (∘-cong (TA'.fib-el-refl* (inj₁ (Fin.suc i)) (lift tt) a) ≈-refl) id-left
    agree-apply-fam γ (fbind Q fm) Fin.zero    a = agree-reindex-fam {Q = Q} γ fm a
    agree-apply-fam γ (fbind Q fm) (Fin.suc v) a = agree-apply-fam γ fm v a

  -- The fused law determines the fold: the comparison of the application at the candidate with the
  -- fold's recursion carries the tree induction at the recursive slots.
  module Unique (h-idx : Γ .idx .Carrier → Tδ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier)
                (h-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : Tδ.W-≈ t t') →
                          _≈s_ (A .idx) (h-idx γ t) (h-idx γ' t'))
                (h-fam : ∀ γ t →
                         prod (Γ .fam .fm γ) (Tδ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (h-idx γ t))
                (H : IsFold h-idx h-resp h-fam) where
    module Ah = Ap h-idx h-resp h-fam

    mutual
      uniq-idx : ∀ γ t → _≈s_ (A .idx) (h-idx γ t) (Ft.fold-idx γ t)
      uniq-idx γ (Tδ.sup x) =
        A .idx .isEquivalence .trans (H .IsFold.is-idx γ x)
          (alg .idxf .PS._⇒_.func-resp-≈ (Γ .idx .isEquivalence .refl , compare-shape P γ x))

      compare-shape : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                    _≈s_ (fobj μ-fam Q (extend δ A) .idx) (Ah.apply-shape-idx Q γ x) (Ft.fold-shape-idx Q γ x)
      compare-shape (const A')        γ a = A' .idx .isEquivalence .refl
      compare-shape (var Fin.zero)    γ t = uniq-idx γ t
      compare-shape (var (Fin.suc i)) γ a = δ i .idx .isEquivalence .refl
      compare-shape (Q₁ + Q₂) γ (inj₁ x) = compare-shape Q₁ γ x
      compare-shape (Q₁ + Q₂) γ (inj₂ y) = compare-shape Q₂ γ y
      compare-shape (Q₁ × Q₂) γ (x , y) = compare-shape Q₁ γ x , compare-shape Q₂ γ y
      compare-shape (μ Q')    γ t = compare-reindex {Q = Q'} γ fbase t

      compare-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d')
                      (t : Tδ.W ∣ Q ∣ ρ) →
                      TA'.W-≈ (Ah.apply-reindex γ fm t) (Ft.fold-reindex γ fm t)
      compare-reindex {Q = Q} γ fm (Tδ.sup x) = compare-reindex-shape γ Q (fbind Q fm) x

      compare-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB)
                            (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                            TA'.shape≈ ∣ R ∣ ηB (Ah.apply-reindex-shape γ R fm a) (Ft.fold-reindex-shape γ R fm a)
      compare-reindex-shape γ (const A') fm a = A' .idx .isEquivalence .refl
      compare-reindex-shape γ (var v)    fm a = compare-apply γ fm v a
      compare-reindex-shape γ (P' + Q') fm (inj₁ a) = compare-reindex-shape γ P' fm a
      compare-reindex-shape γ (P' + Q') fm (inj₂ b) = compare-reindex-shape γ Q' fm b
      compare-reindex-shape γ (P' × Q') fm (a , b) = compare-reindex-shape γ P' fm a , compare-reindex-shape γ Q' fm b
      compare-reindex-shape γ (μ Q'')   fm t = compare-reindex {Q = Q''} γ fm t

      compare-apply : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k)
                    (a : Tδ.El (ρ v)) →
                    TA'.elEq (ρ' v) (Ah.apply-apply γ fm v a) (Ft.fold-apply γ fm v a)
      compare-apply γ fbase        Fin.zero    t = uniq-idx γ t
      compare-apply γ fbase        (Fin.suc i) a = TA'.elEq-refl (inj₁ (Fin.suc i)) a
      compare-apply γ (fbind Q fm) Fin.zero    a = compare-reindex {Q = Q} γ fm a
      compare-apply γ (fbind Q fm) (Fin.suc v) a = compare-apply γ fm v a

    mutual
      uniq-fam : ∀ γ t → (A .fam .subst (uniq-idx γ t) ∘ h-fam γ t) ≈ Ft.fold-fam γ t
      uniq-fam γ (Tδ.sup x) =
        ≈-trans (∘-cong ≈-refl (H .IsFold.is-fam γ x))
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong (≈-sym (A .fam .trans*
                   (uniq-idx γ (Tδ.sup x))
                   (A .idx .isEquivalence .sym (H .IsFold.is-idx γ x)))) ≈-refl)
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong (≈-sym (alg .famf ._⇒f_.natural
                   (Γ .idx .isEquivalence .refl , compare-shape P γ x))) ≈-refl)
        (≈-trans (assoc _ _ _)
        (∘-cong ≈-refl
          (≈-trans (pair-compose _ _ _ _)
                   (pair-cong (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left)
                              (compare-shape-fam P γ x)))))))))

      compare-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                        (fobj μ-fam Q (extend δ A) .fam .subst (compare-shape Q γ x) ∘ Ah.apply-shape-fam Q γ x)
                          ≈ Ft.fold-shape-fam Q γ x
      compare-shape-fam (const A')        γ a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
      compare-shape-fam (var Fin.zero)    γ t = uniq-fam γ t
      compare-shape-fam (var (Fin.suc i)) γ a = ≈-trans (∘-cong (δ i .fam .refl*) ≈-refl) id-left
      compare-shape-fam (Q₁ + Q₂) γ (inj₁ x) =
        ≈-trans (strong-Lmap-post _
                  (Ah.apply-shape-fam Q₁ γ x))
                (strong-Lmap-cong (compare-shape-fam Q₁ γ x))
      compare-shape-fam (Q₁ + Q₂) γ (inj₂ y) =
        ≈-trans (strong-Lmap-post _
                  (Ah.apply-shape-fam Q₂ γ y))
                (strong-Lmap-cong (compare-shape-fam Q₂ γ y))
      compare-shape-fam (Q₁ × Q₂) γ (x , y) =
        ≈-trans (strong-Lmap-post _
                  (strong-prod-m (Ah.apply-shape-fam Q₁ γ x) (Ah.apply-shape-fam Q₂ γ y)))
                (strong-Lmap-cong
                  (≈-trans (strong-prod-m-post _ _ _ _)
                           (strong-prod-m-cong (compare-shape-fam Q₁ γ x) (compare-shape-fam Q₂ γ y))))
      compare-shape-fam (μ Q') γ t = compare-reindex-fam {Q = Q'} γ fbase t

      compare-reindex-fam : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier)
                          (fm : FMor ρ ρ' d d') (t : Tδ.W ∣ Q ∣ ρ) →
                          (TA'.fib-subst Q d' {x = Ah.apply-reindex γ fm t} {y = Ft.fold-reindex γ fm t}
                             (compare-reindex {Q = Q} γ fm t)
                           ∘ Ah.apply-reindex-fam γ fm t)
                            ≈ Ft.fold-reindex-fam γ fm t
      compare-reindex-fam {Q = Q} γ fm (Tδ.sup x) = compare-reindex-shape-fam γ Q (fbind Q fm) x

      compare-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB}
                                (fm : FMor ηA ηB dA dB) (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                                (TA'.fib-shape-subst R dB (compare-reindex-shape γ R fm a)
                                 ∘ Ah.apply-reindex-shape-fam γ R fm a)
                                  ≈ Ft.fold-reindex-shape-fam γ R fm a
      compare-reindex-shape-fam γ (const A') fm a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
      compare-reindex-shape-fam γ (var v)    fm a = compare-apply-fam γ fm v a
      compare-reindex-shape-fam γ (P' + Q') {dA = dA} {dB} fm (inj₁ a) =
        ≈-trans (strong-Lmap-post _
                  (Ah.apply-reindex-shape-fam γ P' fm a))
                (strong-Lmap-cong (compare-reindex-shape-fam γ P' fm a))
      compare-reindex-shape-fam γ (P' + Q') {dA = dA} {dB} fm (inj₂ b) =
        ≈-trans (strong-Lmap-post _
                  (Ah.apply-reindex-shape-fam γ Q' fm b))
                (strong-Lmap-cong (compare-reindex-shape-fam γ Q' fm b))
      compare-reindex-shape-fam γ (P' × Q') {dA = dA} {dB} fm (a , b) =
        ≈-trans (strong-Lmap-post _
                  (strong-prod-m (Ah.apply-reindex-shape-fam γ P' fm a) (Ah.apply-reindex-shape-fam γ Q' fm b)))
                (strong-Lmap-cong
                  (≈-trans (strong-prod-m-post _ _ _ _)
                           (strong-prod-m-cong (compare-reindex-shape-fam γ P' fm a)
                                               (compare-reindex-shape-fam γ Q' fm b))))
      compare-reindex-shape-fam γ (μ Q'')   fm t = compare-reindex-fam {Q = Q''} γ fm t

      compare-apply-fam : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k)
                        (a : Tδ.El (ρ v)) →
                        (TA'.fib-el-subst (ρ' v) (d' v) (compare-apply γ fm v a)
                         ∘ Ah.apply-apply-fam γ fm v a)
                          ≈ Ft.fold-apply-fam γ fm v a
      compare-apply-fam γ fbase        Fin.zero    t = uniq-fam γ t
      compare-apply-fam γ fbase        (Fin.suc i) a =
        ≈-trans (∘-cong (TA'.fib-el-refl* (inj₁ (Fin.suc i)) (lift tt) a) ≈-refl) id-left
      compare-apply-fam γ (fbind Q fm) Fin.zero    a = compare-reindex-fam {Q = Q} γ fm a
      compare-apply-fam γ (fbind Q fm) (Fin.suc v) a = compare-apply-fam γ fm v a


  -- The fused law for a candidate given as a family morphism, and uniqueness at that level.
  IsFoldMor : (h : Mor (Fam𝒞-P.prod Γ (μ-fam P δ)) A) → Prop (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es)
  IsFoldMor h =
    IsFold (λ γ t → h .idxf .PS._⇒_.func (γ , t))
           (λ γ≈ p → h .idxf .PS._⇒_.func-resp-≈ (γ≈ , p))
           (λ γ t → h .famf ._⇒f_.transf (γ , t))

  unique : (h : Mor (Fam𝒞-P.prod Γ (μ-fam P δ)) A) → IsFoldMor h →
           h ≃ FoldDef.foldMor {n} {Γ} {A} {P} {δ} alg
  unique h H = go
    where
    module E = Unique (λ γ t → h .idxf .PS._⇒_.func (γ , t))
                      (λ γ≈ p → h .idxf .PS._⇒_.func-resp-≈ (γ≈ , p))
                      (λ γ t → h .famf ._⇒f_.transf (γ , t)) H

    go : h ≃ FoldDef.foldMor {n} {Γ} {A} {P} {δ} alg
    go ._≃_.idxf-eq .PS._≃m_.func-eq {γ₁ , t₁} {γ₂ , t₂} (γ≈ , t≈) =
      A .idx .isEquivalence .trans (E.uniq-idx γ₁ t₁) (Ft.fold-idx-resp γ≈ {t₁} {t₂} t≈)
    go ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , t} = E.uniq-fam γ t

private module FMuC = HasMu hasMu

-- The candidate's application at the shape under the algebra map, against its strong action.
module Bridge {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (h : Mor (Fam𝒞-P.prod Γ (μ-fam P δ)) A) where
  open FoldBase {n} {Γ} {A} {P} {δ}
  private
    module At = InMapDef P δ
    module TX = Tree At.δ'
    module RX = Reindex At.δ' (extend δ A)

  h-idx : Γ .idx .Carrier → Tδ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier
  h-idx γ t = h .idxf .PS._⇒_.func (γ , t)

  h-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : Tδ.W-≈ t t') → _≈s_ (A .idx) (h-idx γ t) (h-idx γ' t')
  h-resp γ≈ p = h .idxf .PS._⇒_.func-resp-≈ (γ≈ , p)

  h-fam : ∀ γ t → prod (Γ .fam .fm γ) (Tδ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (h-idx γ t)
  h-fam γ t = h .famf ._⇒f_.transf (γ , t)

  open ApplyDef {n} {Γ} {A} {P} {δ} h-idx h-resp h-fam public

  -- The fibre maps of the application are natural in the shape.
  mutual
    apply-shape-fam-natural : (Q : Poly (suc n)) → ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {x x'}
                              (p : Tδ.shape≈ ∣ Q ∣ (Srt.η₀ ∣ P ∣) x x') →
                              (apply-shape-fam Q γ₂ x'
                               ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-shape-subst Q (Tδ.deco-ext P (λ i → lift tt)) p))
                              ≈ (fobj μ-fam Q (extend δ A) .fam .subst (apply-shape-idx-resp Q γ≈ p) ∘ apply-shape-fam Q γ₁ x)
    apply-shape-fam-natural (const A')        γ≈ p = pair-p₂ _ _
    apply-shape-fam-natural (var Fin.zero)    γ≈ {x} {x'} p = h .famf ._⇒f_.natural (γ≈ , p)
    apply-shape-fam-natural (var (Fin.suc i)) γ≈ p = pair-p₂ _ _
    apply-shape-fam-natural (Q₁ + Q₂) {γ₁} {γ₂} γ≈ {inj₁ x} {inj₁ x'} p =
      strong-Lmap-natural (Γ .fam .subst γ≈)
        (Tδ.fib-shape-subst Q₁ (Tδ.deco-ext P (λ i → lift tt)) p)
        (fobj μ-fam Q₁ (extend δ A) .fam .subst (apply-shape-idx-resp Q₁ γ≈ p))
        (apply-shape-fam Q₁ γ₁ x) (apply-shape-fam Q₁ γ₂ x')
        (apply-shape-fam-natural Q₁ γ≈ p)
    apply-shape-fam-natural (Q₁ + Q₂) {γ₁} {γ₂} γ≈ {inj₂ y} {inj₂ y'} p =
      strong-Lmap-natural (Γ .fam .subst γ≈)
        (Tδ.fib-shape-subst Q₂ (Tδ.deco-ext P (λ i → lift tt)) p)
        (fobj μ-fam Q₂ (extend δ A) .fam .subst (apply-shape-idx-resp Q₂ γ≈ p))
        (apply-shape-fam Q₂ γ₁ y) (apply-shape-fam Q₂ γ₂ y')
        (apply-shape-fam-natural Q₂ γ≈ p)
    apply-shape-fam-natural (Q₁ × Q₂) {γ₁} {γ₂} γ≈ {x₁ , x₂} {x₁' , x₂'} (p₁p , p₂p) =
      strong-Lmap-natural (Γ .fam .subst γ≈)
        (prod-m (Tδ.fib-shape-subst Q₁ (Tδ.deco-ext P (λ i → lift tt)) p₁p)
                (Tδ.fib-shape-subst Q₂ (Tδ.deco-ext P (λ i → lift tt)) p₂p))
        (prod-m (fobj μ-fam Q₁ (extend δ A) .fam .subst (apply-shape-idx-resp Q₁ γ≈ p₁p))
                (fobj μ-fam Q₂ (extend δ A) .fam .subst (apply-shape-idx-resp Q₂ γ≈ p₂p)))
        (strong-prod-m (apply-shape-fam Q₁ γ₁ x₁) (apply-shape-fam Q₂ γ₁ x₂))
        (strong-prod-m (apply-shape-fam Q₁ γ₂ x₁') (apply-shape-fam Q₂ γ₂ x₂'))
        (strong-prod-m-natural (apply-shape-fam-natural Q₁ γ≈ p₁p) (apply-shape-fam-natural Q₂ γ≈ p₂p))
    apply-shape-fam-natural (μ Q')    γ≈ {x} {x'} p = apply-reindex-fam-natural {Q = Q'} γ≈ fbase {x} {x'} p

    apply-reindex-fam-natural : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂)
                                (md : FMor ρ ρ' d d') {t t' : Tδ.W ∣ Q ∣ ρ} (p : Tδ.W-≈ t t') →
                                (apply-reindex-fam γ₂ md t' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-subst Q d {x = t} {y = t'} p))
                                ≈ (TA'.fib-subst Q d' {x = apply-reindex γ₁ md t} {y = apply-reindex γ₂ md t'}
                                                 (apply-reindex-resp γ≈ md {t} {t'} p) ∘ apply-reindex-fam γ₁ md t)
    apply-reindex-fam-natural {Q = Q} γ≈ md {Tδ.sup x} {Tδ.sup y} p =
      apply-reindex-shape-fam-natural γ≈ Q (fbind Q md) {x} {y} p

    apply-reindex-shape-fam-natural : ∀ {j} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (R : Poly j) {ηA ηB dA dB}
                                      (md : FMor ηA ηB dA dB) {a a' : Tδ.⟦ ∣ R ∣ ⟧shape ηA} (p : Tδ.shape≈ ∣ R ∣ ηA a a') →
                                      (apply-reindex-shape-fam γ₂ R md a' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-shape-subst R dA p))
                                      ≈ (TA'.fib-shape-subst R dB (apply-reindex-shape-resp γ≈ R md p) ∘ apply-reindex-shape-fam γ₁ R md a)
    apply-reindex-shape-fam-natural γ≈ (const A') md p = pair-p₂ _ _
    apply-reindex-shape-fam-natural γ≈ (var v)    md p = apply-apply-fam-natural γ≈ md v p
    apply-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' + Q') {dA = dA} {dB} md {inj₁ a} {inj₁ a'} p =
      strong-Lmap-natural (Γ .fam .subst γ≈)
        (Tδ.fib-shape-subst P' dA p)
        (TA'.fib-shape-subst P' dB (apply-reindex-shape-resp γ≈ P' md p))
        (apply-reindex-shape-fam γ₁ P' md a) (apply-reindex-shape-fam γ₂ P' md a')
        (apply-reindex-shape-fam-natural γ≈ P' md p)
    apply-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' + Q') {dA = dA} {dB} md {inj₂ b} {inj₂ b'} p =
      strong-Lmap-natural (Γ .fam .subst γ≈)
        (Tδ.fib-shape-subst Q' dA p)
        (TA'.fib-shape-subst Q' dB (apply-reindex-shape-resp γ≈ Q' md p))
        (apply-reindex-shape-fam γ₁ Q' md b) (apply-reindex-shape-fam γ₂ Q' md b')
        (apply-reindex-shape-fam-natural γ≈ Q' md p)
    apply-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' × Q') {dA = dA} {dB} md {a₁ , a₂} {a₁' , a₂'} (p₁p , p₂p) =
      strong-Lmap-natural (Γ .fam .subst γ≈)
        (prod-m (Tδ.fib-shape-subst P' dA p₁p) (Tδ.fib-shape-subst Q' dA p₂p))
        (prod-m (TA'.fib-shape-subst P' dB (apply-reindex-shape-resp γ≈ P' md p₁p))
                (TA'.fib-shape-subst Q' dB (apply-reindex-shape-resp γ≈ Q' md p₂p)))
        (strong-prod-m (apply-reindex-shape-fam γ₁ P' md a₁) (apply-reindex-shape-fam γ₁ Q' md a₂))
        (strong-prod-m (apply-reindex-shape-fam γ₂ P' md a₁') (apply-reindex-shape-fam γ₂ Q' md a₂'))
        (strong-prod-m-natural (apply-reindex-shape-fam-natural γ≈ P' md p₁p)
                               (apply-reindex-shape-fam-natural γ≈ Q' md p₂p))
    apply-reindex-shape-fam-natural γ≈ (μ Q'')   md {a} {a'} p = apply-reindex-fam-natural {Q = Q''} γ≈ md {a} {a'} p

    apply-apply-fam-natural : ∀ {k} {ρ ρ' d d'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (md : FMor ρ ρ' d d') (v : Fin k)
                              {a a'} (p : Tδ.elEq (ρ v) a a') →
                              (apply-apply-fam γ₂ md v a' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-el-subst (ρ v) (d v) p))
                              ≈ (TA'.fib-el-subst (ρ' v) (d' v) (apply-apply-resp γ≈ md v p) ∘ apply-apply-fam γ₁ md v a)
    apply-apply-fam-natural γ≈ fbase        Fin.zero    {a} {a'} p = h .famf ._⇒f_.natural (γ≈ , p)
    apply-apply-fam-natural γ≈ fbase        (Fin.suc i) p = pair-p₂ _ _
    apply-apply-fam-natural γ≈ (fbind Q md) Fin.zero    {a} {a'} p = apply-reindex-fam-natural {Q = Q} γ≈ md {a} {a'} p
    apply-apply-fam-natural γ≈ (fbind Q md) (Fin.suc v) p = apply-apply-fam-natural γ≈ md v p

  fs : ∀ i → Mor (Fam𝒞-P.prod Γ (At.δ' i)) (extend δ A i)
  fs = FMuC.strong-extend-mor (λ i → Fam𝒞-P.p₂) h

  -- Reindexing along the candidate at the recursion slot and the identity at the parameters.
  cmb : Γ .idx .Carrier → RX.IMorD (λ v → inj₁ v) (λ v → inj₁ v)
  cmb γ = RX.ibase (λ { Fin.zero t → h-idx γ t ; (Fin.suc i) a → a })
                   (λ { Fin.zero p → h-resp (Γ .idx .isEquivalence .refl) p ; (Fin.suc i) p → p })

  corr : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (At.δ' i .idx) a₁ a₂) →
         _≈s_ (extend δ A i .idx) (RX.iapply (cmb γ₁) i a₁) (fs i .idxf .PS._⇒_.func (γ₂ , a₂))
  corr Fin.zero    γ≈ {a₁} {a₂} a≈ = h-resp γ≈ {a₁} {a₂} a≈
  corr (Fin.suc i) γ≈ a≈ = a≈

  module Comp (γ : Γ .idx .Carrier) where
    private module FRX = FReindex {δA = At.δ'} {δB = extend δ A} (Γ .fam .fm γ)

    act : FRX.FAct (cmb γ) (λ v → lift tt) (λ v → lift tt)
    act = FRX.abase (λ { Fin.zero t → h-fam γ t ; (Fin.suc i) a → p₂ })

    corr-fam : ∀ i {a} →
               (extend δ A i .fam .subst (corr i (Γ .idx .isEquivalence .refl) (At.δ' i .idx .isEquivalence .refl {a}))
                ∘ FRX.aapply act i a)
               ≈ fs i .famf ._⇒f_.transf (γ , a)
    corr-fam Fin.zero    = ≈-trans (∘-cong (A .fam .refl*) ≈-refl) id-left
    corr-fam (Fin.suc i) = ≈-trans (∘-cong (δ i .fam .refl*) ≈-refl) id-left

    -- The application after the bridge reindexing, paired with the one reindexing they compose to.
    data CRel : ∀ {j} {ρX : Fin j → Fin (suc n) ⊎ Sort (suc n)} {ρ : Fin j → Fin n ⊎ Sort n}
                {ρ' : Fin j → Fin (suc n) ⊎ Sort (suc n)}
                {dX : ∀ v → TX.DecoAssign (ρX v)} {d : ∀ v → Tδ.DecoAssign (ρ v)} {d' : ∀ v → TA'.DecoAssign (ρ' v)} →
                FMor ρ ρ' d d' → At.R.MorD ρX ρ dX d → (im : RX.IMorD ρX ρ') → FRX.FAct im dX d' →
                Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      cbase : CRel fbase At.mor₀ (cmb γ) act
      cbind : ∀ {j} {ρX ρ ρ' dX d d'} {fm : FMor {j} ρ ρ' d d'} {md : At.R.MorD ρX ρ dX d} {im} {am : FRX.FAct im dX d'}
              (Q : Poly (suc j)) → CRel fm md im am →
              CRel (fbind Q fm) (At.R.bind Q md) (RX.ibind ∣ Q ∣ im) (FRX.abind Q im am)

    mutual
      comp-W : ∀ {j} {Q̂ : Poly (suc j)} {ρX ρ ρ' dX d d'} {fm : FMor ρ ρ' d d'} {md : At.R.MorD ρX ρ dX d} {im}
               {am : FRX.FAct im dX d'} → CRel fm md im am → (t : TX.W ∣ Q̂ ∣ ρX) →
               TA'.W-≈ (apply-reindex {Q = Q̂} γ fm (At.R.reindex md t)) (RX.ireindex im t)
      comp-W {Q̂ = Q̂} rel (TX.sup x) = comp-shape Q̂ (cbind Q̂ rel) x

      comp-shape : ∀ {j} (S : Poly j) {ρX ρ ρ' dX d d'} {fm : FMor ρ ρ' d d'} {md : At.R.MorD ρX ρ dX d} {im}
                   {am : FRX.FAct im dX d'} → CRel fm md im am → (a : TX.⟦ ∣ S ∣ ⟧shape ρX) →
                   TA'.shape≈ ∣ S ∣ ρ' (apply-reindex-shape γ S fm (At.R.reindex-shape ∣ S ∣ md a)) (RX.ireindex-shape ∣ S ∣ im a)
      comp-shape (const A') rel a = A' .idx .isEquivalence .refl
      comp-shape (var v)    rel a = comp-el rel v a
      comp-shape (P' + Q') rel (inj₁ a) = comp-shape P' rel a
      comp-shape (P' + Q') rel (inj₂ b) = comp-shape Q' rel b
      comp-shape (P' × Q') rel (a , b) = comp-shape P' rel a , comp-shape Q' rel b
      comp-shape (μ Q'')   rel t = comp-W {Q̂ = Q''} rel t

      comp-el : ∀ {j} {ρX ρ ρ' dX d d'} {fm : FMor {j} ρ ρ' d d'} {md : At.R.MorD ρX ρ dX d} {im}
                {am : FRX.FAct im dX d'} → CRel fm md im am → (v : Fin j) (a : TX.El (ρX v)) →
                TA'.elEq (ρ' v) (apply-apply γ fm v (At.R.apply md v a)) (RX.iapply im v a)
      comp-el cbase          Fin.zero    t = A .idx .isEquivalence .refl
      comp-el cbase          (Fin.suc i) a = TA'.elEq-refl (inj₁ (Fin.suc i)) a
      comp-el (cbind Q rel)  Fin.zero    a = comp-W {Q̂ = Q} rel a
      comp-el (cbind Q rel)  (Fin.suc v) a = comp-el rel v a

    mutual
      comp-W-fam : ∀ {j} {Q̂ : Poly (suc j)} {ρX ρ ρ' dX d d'} {fm : FMor ρ ρ' d d'} {md : At.R.MorD ρX ρ dX d} {im}
                   {am : FRX.FAct im dX d'} (rel : CRel fm md im am) (t : TX.W ∣ Q̂ ∣ ρX) →
                   (TA'.fib-subst Q̂ d' {x = apply-reindex {Q = Q̂} γ fm (At.R.reindex md t)} {y = RX.ireindex im t}
                      (comp-W rel t)
                    ∘ (apply-reindex-fam {Q = Q̂} γ fm (At.R.reindex md t)
                       ∘ prod-m (id _) (At.R.reindex-fam-W {Q = Q̂} md {t})))
                   ≈ FRX.freindex-fam {Q = Q̂} am {t}
      comp-W-fam {Q̂ = Q̂} rel (TX.sup x) = comp-shape-fam Q̂ (cbind Q̂ rel) x

      comp-shape-fam : ∀ {j} (S : Poly j) {ρX ρ ρ' dX d d'} {fm : FMor ρ ρ' d d'} {md : At.R.MorD ρX ρ dX d} {im}
                       {am : FRX.FAct im dX d'} (rel : CRel fm md im am) (a : TX.⟦ ∣ S ∣ ⟧shape ρX) →
                       (TA'.fib-shape-subst S d' (comp-shape S rel a)
                        ∘ (apply-reindex-shape-fam γ S fm (At.R.reindex-shape ∣ S ∣ md a)
                           ∘ prod-m (id _) (At.R.reindex-fam S md {a})))
                       ≈ FRX.freindex-shape-fam S am {a}
      comp-shape-fam (const A') rel a =
        ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) (≈-trans id-left (≈-trans (pair-p₂ _ _) id-left))
      comp-shape-fam (var v)    rel a = comp-el-fam rel v a
      comp-shape-fam (P' + Q') rel (inj₁ a) =
        ≈-trans (∘-cong ≈-refl (strong-Lmap-pre (id _) _ _))
        (≈-trans (strong-Lmap-post _ _) (strong-Lmap-cong (comp-shape-fam P' rel a)))
      comp-shape-fam (P' + Q') rel (inj₂ b) =
        ≈-trans (∘-cong ≈-refl (strong-Lmap-pre (id _) _ _))
        (≈-trans (strong-Lmap-post _ _) (strong-Lmap-cong (comp-shape-fam Q' rel b)))
      comp-shape-fam (P' × Q') rel (a , b) =
        ≈-trans (∘-cong ≈-refl (strong-Lmap-pre (id _) _ _))
        (≈-trans (strong-Lmap-post _ _)
                 (strong-Lmap-cong
                   (≈-trans (∘-cong ≈-refl (strong-prod-m-pre _ _ _ _ _))
                   (≈-trans (strong-prod-m-post _ _ _ _)
                            (strong-prod-m-cong (comp-shape-fam P' rel a) (comp-shape-fam Q' rel b))))))
      comp-shape-fam (μ Q'')   rel t = comp-W-fam {Q̂ = Q''} rel t

      comp-el-fam : ∀ {j} {ρX ρ ρ' dX d d'} {fm : FMor {j} ρ ρ' d d'} {md : At.R.MorD ρX ρ dX d} {im}
                    {am : FRX.FAct im dX d'} (rel : CRel fm md im am) (v : Fin j) (a : TX.El (ρX v)) →
                    (TA'.fib-el-subst (ρ' v) (d' v) (comp-el rel v a)
                     ∘ (apply-apply-fam γ fm v (At.R.apply md v a) ∘ prod-m (id _) (At.R.apply-fam md v a)))
                    ≈ FRX.aapply am v a
      comp-el-fam cbase          Fin.zero    t =
        ≈-trans (∘-cong (A .fam .refl*) ≈-refl)
                (≈-trans id-left (≈-trans (∘-cong ≈-refl prod-m-id) id-right))
      comp-el-fam cbase          (Fin.suc i) a =
        ≈-trans (∘-cong (TA'.fib-el-refl* (inj₁ (Fin.suc i)) (lift tt) a) ≈-refl)
                (≈-trans id-left (≈-trans (pair-p₂ _ _) id-left))
      comp-el-fam (cbind Q rel)  Fin.zero    a = comp-W-fam {Q̂ = Q} rel a
      comp-el-fam (cbind Q rel)  (Fin.suc v) a = comp-el-fam rel v a

  -- The candidate applied at the shape under the algebra map is the strong action, on indices.
  bridge-idx : ∀ (Q : Poly (suc n)) γ (y : fobj μ-fam Q At.δ' .idx .Carrier) →
               _≈s_ (fobj μ-fam Q (extend δ A) .idx)
                 (apply-shape-idx Q γ (At.R.reindex-shape ∣ Q ∣ At.mor₀ (At.embed-idx Q y)))
                 (FMuC.strong-fmor Q fs .idxf .PS._⇒_.func (γ , y))
  bridge-idx (const A')        γ a = A' .idx .isEquivalence .refl
  bridge-idx (var Fin.zero)    γ t = A .idx .isEquivalence .refl
  bridge-idx (var (Fin.suc i)) γ a = δ i .idx .isEquivalence .refl
  bridge-idx (Q₁ + Q₂) γ (inj₁ y) = bridge-idx Q₁ γ y
  bridge-idx (Q₁ + Q₂) γ (inj₂ y) = bridge-idx Q₂ γ y
  bridge-idx (Q₁ × Q₂) γ (y₁ , y₂) = bridge-idx Q₁ γ y₁ , bridge-idx Q₂ γ y₂
  bridge-idx (μ Q') γ t =
    TA'.W-≈-trans {x = apply-reindex {Q = Q'} γ fbase (At.R.reindex At.mor₀ t)} {y = RX.ireindex (cmb γ) t}
      (comp-W cbase t)
      (fuse-idx {Γ = Γ} {sₛ = At.δ'} {sₜ = extend δ A} Q' cmb fs corr
         (Γ .idx .isEquivalence .refl) {m₁ = t} {m₂ = t} (TX.W-≈-refl t))
    where open Comp γ

  -- The same on fibres.
  bridge-fam : ∀ (Q : Poly (suc n)) γ (y : fobj μ-fam Q At.δ' .idx .Carrier) →
               (fobj μ-fam Q (extend δ A) .fam .subst (bridge-idx Q γ y)
                ∘ (apply-shape-fam Q γ (At.R.reindex-shape ∣ Q ∣ At.mor₀ (At.embed-idx Q y))
                   ∘ prod-m (id _) (At.R.reindex-fam Q At.mor₀ ∘ At.embed-fam Q y)))
               ≈ FMuC.strong-fmor Q fs .famf ._⇒f_.transf (γ , y)
  bridge-fam (const A')        γ a =
    ≈-trans (∘-cong (A' .fam .refl*) ≈-refl)
            (≈-trans id-left (≈-trans (pair-p₂ _ _) (≈-trans (∘-cong id-left ≈-refl) id-left)))
  bridge-fam (var Fin.zero)    γ t =
    ≈-trans (∘-cong (A .fam .refl*) ≈-refl)
            (≈-trans id-left (≈-trans (∘-cong ≈-refl (≈-trans (prod-m-cong ≈-refl id-left) prod-m-id)) id-right))
  bridge-fam (var (Fin.suc i)) γ a =
    ≈-trans (∘-cong (δ i .fam .refl*) ≈-refl)
            (≈-trans id-left (≈-trans (pair-p₂ _ _) (≈-trans (∘-cong id-left ≈-refl) id-left)))
  bridge-fam (Q₁ + Q₂) γ (inj₁ y) =
    ≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (prod-m-cong ≈-refl (≈-sym (Lmap-comp _ _)))))
    (≈-trans (∘-cong ≈-refl (strong-Lmap-pre (id _) _ _))
    (≈-trans (strong-Lmap-post _ _)
    (≈-trans (strong-Lmap-cong (bridge-fam Q₁ γ y))
             (≈-sym (≈-trans id-left (≈-trans id-left (strong-Lf-map-transf (FMuC.strong-fmor Q₁ fs))))))))
  bridge-fam (Q₁ + Q₂) γ (inj₂ y) =
    ≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (prod-m-cong ≈-refl (≈-sym (Lmap-comp _ _)))))
    (≈-trans (∘-cong ≈-refl (strong-Lmap-pre (id _) _ _))
    (≈-trans (strong-Lmap-post _ _)
    (≈-trans (strong-Lmap-cong (bridge-fam Q₂ γ y))
             (≈-sym (≈-trans id-left (≈-trans id-left (strong-Lf-map-transf (FMuC.strong-fmor Q₂ fs))))))))
  bridge-fam (Q₁ × Q₂) γ (y₁ , y₂) =
    ≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (prod-m-cong ≈-refl
               (≈-trans (≈-sym (Lmap-comp _ _)) (Lmap-cong (≈-sym (prod-m-comp _ _ _ _)))))))
    (≈-trans (∘-cong ≈-refl (strong-Lmap-pre (id _) _ _))
    (≈-trans (strong-Lmap-post _ _)
    (≈-trans (strong-Lmap-cong
               (≈-trans (∘-cong ≈-refl (strong-prod-m-pre _ _ _ _ _))
               (≈-trans (strong-prod-m-post _ _ _ _)
                        (strong-prod-m-cong (bridge-fam Q₁ γ y₁) (bridge-fam Q₂ γ y₂)))))
             (≈-sym (≈-trans (strong-Lf-map-transf (Fam𝒞-P.strong-prod-m (FMuC.strong-fmor Q₁ fs) (FMuC.strong-fmor Q₂ fs)))
                             (strong-Lmap-cong
                               (strong-prod-m-transf (FMuC.strong-fmor Q₁ fs) (FMuC.strong-fmor Q₂ fs) {γ} {y₁} {y₂})))))))
  bridge-fam (μ Q') γ t =
    ≈-trans (∘-cong (TA'.fib-trans* Q' (λ v → lift tt)
                       {x = apply-reindex {Q = Q'} γ fbase (At.R.reindex At.mor₀ t)}
                       {y = RX.ireindex (cmb γ) t}
                       {z = FMuC.strong-fmor (μ Q') fs .idxf .PS._⇒_.func (γ , t)}
                       (fuse-idx {Γ = Γ} {sₛ = At.δ'} {sₜ = extend δ A} Q' cmb fs corr
                          (Γ .idx .isEquivalence .refl) {m₁ = t} {m₂ = t} (TX.W-≈-refl t))
                       (comp-W cbase t))
                    ≈-refl)
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl
               (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (prod-m-cong ≈-refl id-right)))
                        (comp-W-fam cbase t)))
             (fuse-fam γ Q' cmb act fs corr corr-fam {t})))
    where open Comp γ

-- β: the fold after the algebra map is the algebra after the strong action of the fold.
module Beta {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (alg : Mor (Fam𝒞-P.prod Γ (fobj μ-fam P (extend δ A))) A) where
  private
    module At = InMapDef P δ
    module Ft = FoldDef {n} {Γ} {A} {P} {δ} alg
    module L = Laws {n} {Γ} {A} {P} {δ} alg
  open Bridge {n} {Γ} {A} {P} {δ} Ft.foldMor

  private
    sf = FMuC.strong-fmor P fs
    F = fobj μ-fam P (extend δ A)

  β-idx : ∀ γ y → _≈s_ (A .idx)
            (Ft.fold-idx γ (At.inMor .idxf .PS._⇒_.func y))
            (alg .idxf .PS._⇒_.func (γ , sf .idxf .PS._⇒_.func (γ , y)))
  β-idx γ y =
    alg .idxf .PS._⇒_.func-resp-≈
      (Γ .idx .isEquivalence .refl ,
       F .idx .isEquivalence .trans
         (L.agree-shape P γ (At.R.reindex-shape ∣ P ∣ At.mor₀ (At.embed-idx P y)))
         (bridge-idx P γ y))

  β-fam : ∀ γ y →
          (A .fam .subst (β-idx γ y)
           ∘ (Ft.fold-fam γ (At.inMor .idxf .PS._⇒_.func y) ∘ pair p₁ (At.inMor .famf ._⇒f_.transf y ∘ p₂)))
          ≈ (alg .famf ._⇒f_.transf (γ , sf .idxf .PS._⇒_.func (γ , y)) ∘ pair p₁ (sf .famf ._⇒f_.transf (γ , y)))
  β-fam γ y =
    ≈-trans (∘-cong ≈-refl (assoc _ _ _))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong (≈-sym (alg .famf ._⇒f_.natural (Γ .idx .isEquivalence .refl , e′))) ≈-refl)
    (≈-trans (assoc _ _ _)
    (∘-cong ≈-refl
      (≈-trans (∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) ≈-refl)))
      (≈-trans (pair-compose _ _ _ _)
      (pair-cong (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left)
        (≈-trans (∘-cong (F .fam .trans* (bridge-idx P γ y) (L.agree-shape P γ x))
                         (∘-cong ≈-refl (pair-cong (≈-sym id-left) ≈-refl)))
        (≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (≈-trans (≈-sym (assoc _ _ _)) (∘-cong (L.agree-shape-fam P γ x) ≈-refl)))
                 (bridge-fam P γ y)))))))))))
    where
      x = At.R.reindex-shape ∣ P ∣ At.mor₀ (At.embed-idx P y)
      e′ = F .idx .isEquivalence .trans (L.agree-shape P γ x) (bridge-idx P γ y)

  ⦅⦆-β : (FMuC.⦅ alg ⦆ ∘co (FMuC.inMap P δ Fam𝒞.∘ Fam𝒞-P.p₂))
         ≃ (alg ∘co FMuC.strong-fmor P (FMuC.strong-extend-mor (λ i → Fam𝒞-P.p₂) FMuC.⦅ alg ⦆))
  ⦅⦆-β ._≃_.idxf-eq .PS._≃m_.func-eq {γ₁ , y₁} {γ₂ , y₂} (γ≈ , y≈) =
    A .idx .isEquivalence .trans (β-idx γ₁ y₁)
      (alg .idxf .PS._⇒_.func-resp-≈ (γ≈ , sf .idxf .PS._⇒_.func-resp-≈ (γ≈ , y≈)))
  ⦅⦆-β ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , y} =
    ≈-trans (∘-cong ≈-refl (≈-trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left))))
            (≈-trans (β-fam γ y) (≈-sym id-left))

-- η: a morphism satisfying the fold equation is the fold. The equation at a tree, taken at the
-- tree's unfolding, gives the fused law at its shape by the bridge and the algebra map's inverse.
module Eta {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (alg : Mor (Fam𝒞-P.prod Γ (fobj μ-fam P (extend δ A))) A)
    (h : Mor (Fam𝒞-P.prod Γ (μ-fam P δ)) A)
    (H : (h ∘co (FMuC.inMap P δ Fam𝒞.∘ Fam𝒞-P.p₂))
         ≃ (alg ∘co FMuC.strong-fmor P (FMuC.strong-extend-mor (λ i → Fam𝒞-P.p₂) h))) where
  private
    module At = InMapDef P δ
    module Lk = LambekDef P δ
    module L = Laws {n} {Γ} {A} {P} {δ} alg
  open FoldBase {n} {Γ} {A} {P} {δ}
  open Bridge {n} {Γ} {A} {P} {δ} h

  private
    sf = FMuC.strong-fmor P fs
    F = fobj μ-fam P (extend δ A)
    μF = μ-fam P δ .fam

  module _ (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ P ∣ ⟧shape (Srt.η₀ ∣ P ∣)) where
    private
      y  = Lk.u-idx (Tδ.sup x)
      x' = At.R.reindex-shape ∣ P ∣ At.mor₀ (At.embed-idx P y)
      rt : Tδ.W-≈ {Q = ∣ P ∣} {ρ = λ i → inj₁ i} (Tδ.sup x') (Tδ.sup x)
      rt = Lk.inMor-outMor ._≃_.idxf-eq .PS._≃m_.func-eq {Tδ.sup x} {Tδ.sup x} (Tδ.W-≈-refl {Q = ∣ P ∣} {ρ = λ i → inj₁ i} (Tδ.sup x))
      tr : Tδ.W-≈ {Q = ∣ P ∣} {ρ = λ i → inj₁ i} (Tδ.sup x) (Tδ.sup x')
      tr = Tδ.W-≈-sym {Q = ∣ P ∣} {ρ = λ i → inj₁ i} {x = Tδ.sup x'} {y = Tδ.sup x} rt
      Hi : _≈s_ (A .idx) (h-idx γ (Tδ.sup x')) (alg .idxf .PS._⇒_.func (γ , sf .idxf .PS._⇒_.func (γ , y)))
      Hi = H ._≃_.idxf-eq .PS._≃m_.func-eq {γ , y} {γ , y}
             (Γ .idx .isEquivalence .refl , fobj μ-fam P At.δ' .idx .isEquivalence .refl)
      ex : _≈s_ (F .idx) (apply-shape-idx P γ x) (sf .idxf .PS._⇒_.func (γ , y))
      ex = F .idx .isEquivalence .trans (apply-shape-idx-resp P (Γ .idx .isEquivalence .refl) {x} {x'} tr) (bridge-idx P γ y)

    is-idx : _≈s_ (A .idx) (h-idx γ (Tδ.sup x)) (alg .idxf .PS._⇒_.func (γ , apply-shape-idx P γ x))
    is-idx =
      A .idx .isEquivalence .trans (h-resp (Γ .idx .isEquivalence .refl) tr)
      (A .idx .isEquivalence .trans Hi
        (alg .idxf .PS._⇒_.func-resp-≈ (Γ .idx .isEquivalence .refl , F .idx .isEquivalence .sym ex)))

    private
      ι = At.inMor .famf ._⇒f_.transf y
      υ = Lk.u-fam (Tδ.sup x)
      s  = μF .subst {Tδ.sup x'} {Tδ.sup x} rt
      s⁻ = μF .subst {Tδ.sup x} {Tδ.sup x'} tr
      hx' = h-fam γ (Tδ.sup x')
      asf = apply-shape-fam P γ x
      sft = sf .famf ._⇒f_.transf (γ , y)
      algT = alg .famf ._⇒f_.transf (γ , sf .idxf .PS._⇒_.func (γ , y))

      inv : (s ∘ (ι ∘ υ)) ≈ id _
      inv = ≈-trans (∘-cong ≈-refl (≈-sym id-left)) (Lk.inMor-outMor ._≃_.famf-eq .indexed-family._≃f_.transf-eq {Tδ.sup x})

      ιυ : (ι ∘ υ) ≈ s⁻
      ιυ = ≈-trans (≈-sym id-left)
           (≈-trans (∘-cong (≈-sym (fam-subst-iso₂ μF rt)) ≈-refl)
           (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl inv) id-right)))

      ιυs : (ι ∘ (υ ∘ s)) ≈ id _
      ιυs = ≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong ιυ ≈-refl) (fam-subst-iso₂ μF rt))

      Hf : (A .fam .subst Hi ∘ (hx' ∘ pair p₁ (ι ∘ p₂))) ≈ (algT ∘ pair p₁ sft)
      Hf = ≈-trans (∘-cong ≈-refl (≈-sym (≈-trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left)))))
           (≈-trans (H ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , y}) id-left)

      -- The candidate at the shape's unfolding, through the strong action and the bridge.
      step : (hx' ∘ prod-m (id _) s⁻)
             ≈ (A .fam .subst (A .idx .isEquivalence .sym Hi)
                ∘ (A .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (Γ .idx .isEquivalence .refl , ex))
                   ∘ (alg .famf ._⇒f_.transf (γ , apply-shape-idx P γ x) ∘ pair p₁ asf)))
      step =
        ≈-trans (∘-cong (≈-sym (≈-trans (∘-cong ≈-refl (≈-trans (pair-cong ≈-refl (≈-trans (∘-cong ιυs ≈-refl) id-left)) pair-ext0)) id-right)) ≈-refl)
        (≈-trans (∘-cong (≈-trans (∘-cong ≈-refl (≈-sym PP)) (≈-sym (assoc _ _ _))) ≈-refl)
        (≈-trans (∘-cong (∘-cong (≈-trans (≈-sym id-left)
                                   (≈-trans (∘-cong (≈-sym (fam-subst-iso₂ (A .fam) Hi)) ≈-refl)
                                   (≈-trans (assoc _ _ _) (∘-cong ≈-refl Hf)))) ≈-refl) ≈-refl)
        (≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl QQ)
        (≈-trans (assoc _ _ _)
        (∘-cong ≈-refl
          (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) sfυ)))
          (≈-trans (∘-cong ≈-refl (≈-trans (pair-cong (≈-sym (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left)) ≈-refl)
                                            (≈-sym (pair-compose _ _ _ _))))
          (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong (alg .famf ._⇒f_.natural (Γ .idx .isEquivalence .refl , ex)) ≈-refl)
                   (assoc _ _ _))))))))))))
        where
          PP : (pair p₁ (ι ∘ p₂) ∘ pair p₁ ((υ ∘ s) ∘ p₂)) ≈ pair p₁ ((ι ∘ (υ ∘ s)) ∘ p₂)
          PP = ≈-trans (pair-natural _ _ _)
               (pair-cong (pair-p₁ _ _) (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (≈-sym (assoc _ _ _)))))
          QQ : (pair p₁ ((υ ∘ s) ∘ p₂) ∘ prod-m (id _) s⁻) ≈ pair p₁ (υ ∘ p₂)
          QQ = ≈-trans (pair-natural _ _ _)
               (pair-cong (≈-trans (pair-p₁ _ _) id-left)
                          (≈-trans (assoc _ _ _)
                          (≈-trans (∘-cong ≈-refl (pair-p₂ _ _))
                          (≈-trans (assoc _ _ _)
                                   (∘-cong ≈-refl (≈-trans (≈-sym (assoc _ _ _))
                                                  (≈-trans (∘-cong (fam-subst-iso₁ μF rt) ≈-refl) id-left)))))))
          sfυ : (sft ∘ pair p₁ (υ ∘ p₂)) ≈ (F .fam .subst ex ∘ asf)
          sfυ = ≈-trans (∘-cong (≈-sym (bridge-fam P γ y)) ≈-refl)
                (≈-trans (assoc _ _ _)
                (≈-trans (∘-cong ≈-refl
                           (≈-trans (assoc _ _ _)
                           (∘-cong ≈-refl
                             (≈-trans (pair-compose _ _ _ _)
                                      (pair-cong (∘-cong (≈-sym (Γ .fam .refl*)) ≈-refl)
                                                 (≈-trans (≈-sym (assoc _ _ _)) (∘-cong ιυ ≈-refl)))))))
                (≈-trans (∘-cong ≈-refl (apply-shape-fam-natural P (Γ .idx .isEquivalence .refl) {x} {x'} tr))
                (≈-trans (≈-sym (assoc _ _ _))
                         (∘-cong (≈-sym (F .fam .trans* (bridge-idx P γ y)
                                          (apply-shape-idx-resp P (Γ .idx .isEquivalence .refl) {x} {x'} tr))) ≈-refl)))))

    is-fam : h-fam γ (Tδ.sup x)
             ≈ (A .fam .subst (A .idx .isEquivalence .sym is-idx)
                ∘ (alg .famf ._⇒f_.transf (γ , apply-shape-idx P γ x) ∘ pair p₁ asf))
    is-fam =
      ≈-trans (≈-sym (≈-trans (∘-cong ≈-refl (prod-m-iso (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left)
                                                          (fam-subst-iso₁ μF rt)))
                              id-right))
      (≈-trans (≈-sym (assoc _ _ _))
      (≈-trans (∘-cong (h .famf ._⇒f_.natural {γ , Tδ.sup x'} {γ , Tδ.sup x} (Γ .idx .isEquivalence .refl , rt)) ≈-refl)
      (≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl step)
      (≈-trans (≈-sym (assoc _ _ _))
      (≈-trans (∘-cong (≈-sym (A .fam .trans* (h-resp (Γ .idx .isEquivalence .refl) rt) (A .idx .isEquivalence .sym Hi))) ≈-refl)
      (≈-trans (≈-sym (assoc _ _ _))
               (∘-cong (≈-sym (A .fam .trans*
                                (A .idx .isEquivalence .trans (A .idx .isEquivalence .sym Hi) (h-resp (Γ .idx .isEquivalence .refl) rt))
                                (alg .idxf .PS._⇒_.func-resp-≈ (Γ .idx .isEquivalence .refl , ex)))) ≈-refl))))))))

  is-fold : L.IsFoldMor h
  is-fold .L.IsFold.is-idx = is-idx
  is-fold .L.IsFold.is-fam = is-fam

  ⦅⦆-η : h ≃ FMuC.⦅ alg ⦆
  ⦅⦆-η = L.unique h is-fold

-- The tree model satisfies the initial-algebra laws.
hasMuLaws : HasMuLaws hasMu
hasMuLaws .HasMuLaws.⦅⦆-β alg = Beta.⦅⦆-β alg
hasMuLaws .HasMuLaws.⦅⦆-η alg h H = Eta.⦅⦆-η alg h H

-- The functorial action and the map between μ-carriers need a terminal object, to enter a fold
-- from the empty context.
module WithTerminal (T : HasTerminal 𝒞) where
  open HasMu.WithTerminal hasMu (terminal T) public using (fmor; μ-map)
  open HasMuLaws.WithTerminal hasMuLaws (terminal T) public
    using (fmor-cong; fmor-id; fmor-comp; fmor-const; fmor-var; fmor-+; fmor-×; fmor-μ;
           μ-map-cong; μ-map-id; μ-map-in; μ-map-comp)

  terminal-section : Section (HasTerminal.witness (terminal T))
  terminal-section .at _ = HasTerminal.to-terminal T
  terminal-section .at-natural _ = HasTerminal.to-terminal-unique T _ _

  preserves-to-terminal : ∀ {X : Obj} (cX : Section X) →
    preserves-section (HasTerminal.to-terminal (terminal T)) cX terminal-section
  preserves-to-terminal cX .at x = HasTerminal.to-terminal-unique T _ _

  preserves-μ-map : ∀ {j k} (P : Poly (suc j)) (δ : Fin j → Obj) (Q : Poly (suc k)) (δ' : Fin k → Obj)
    (δc : ∀ i → Section (δ i)) (δ'c : ∀ i → Section (δ' i))
    (Pc : PolySection P) (Qc : PolySection Q)
    (u : Mor (fobj μ-fam P (extend δ (μ-fam Q δ'))) (fobj μ-fam Q (extend δ' (μ-fam Q δ')))) →
    preserves-section u
      (poly-section P Pc (extend-section δc (MuSection.μ-section δ' δ'c Q Qc)))
      (poly-section Q Qc (extend-section δ'c (MuSection.μ-section δ' δ'c Q Qc))) →
    preserves-section (μ-map P δ Q δ' u)
      (MuSection.μ-section δ δc P Pc) (MuSection.μ-section δ' δ'c Q Qc)
  preserves-μ-map P δ Q δ' δc δ'c Pc Qc u hu =
    preserves-section-∘
      (FoldSection.preserves-foldMor {P = P} {δ = δ} alg δc μQc Pc terminal-section
        (preserves-section-∘ (preserves-section-∘ (preserves-inMap Q δ' δ'c Qc) hu)
          (preserves-p₂ {cX = terminal-section} {cY = poly-section P Pc (extend-section δc μQc)})))
      (preserves-pair (preserves-to-terminal μPc) (preserves-section-id μPc))
    where
    μQc = MuSection.μ-section δ' δ'c Q Qc
    μPc = MuSection.μ-section δ δc P Pc
    alg : Mor (Fam𝒞-P.prod (HasTerminal.witness (terminal T))
                (fobj μ-fam P (extend δ (μ-fam Q δ'))))
              (μ-fam Q δ')
    alg = (hasMu .HasMu.inMap Q δ' Fam𝒞.∘ u) Fam𝒞.∘ Fam𝒞-P.p₂
