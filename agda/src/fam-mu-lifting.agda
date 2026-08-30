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
open import indexed-family using (Fam; _⇒f_; fam-subst-iso₁; fam-subst-iso₂)
import fam
import fam-functor
open import functor using (StrongFunctor; functor-preserve-iso)
import polynomial-functor
import fam-mu-lifting.sort
import fam-mu-lifting.fibre

module fam-mu-lifting {o m e} (os es : Level) {𝒞 : Category o m e}
    (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    (𝟙𝒞 : Category.obj 𝒞) where

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
  module Lc = lifting CM BP 𝟙𝒞
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
module Fam-cat = Category cat
open products 𝒞-products public  -- Fam-level products
module Fam-P = HasProducts products
open _⇒f_ public

open _≃_
open PS._⇒_
open PS._≃m_
open indexed-family._≃f_
open polynomial-functor using (extend) public
open polynomial-functor.Poly public
Poly = polynomial-functor.Poly cat
open Setoid using (Carrier; isEquivalence) renaming (_≈_ to _≈s_) public

open import Data.Sum using (_⊎_) public
open import Data.Product using () renaming (_×_ to _×T_) public
open import prop using (_∧_; ⊥) public

module sort = fam-mu-lifting.sort os es
open sort using (η₀)
open sort public using (Sort; mkSort)
open fam-mu-lifting.fibre os es CM BP 𝟙𝒞 public using (Idx; ∣_∣; module Fibre; μ-fam)

private
  LfS : StrongFunctor products
  LfS = fam-functor.FamF-strong os (os ⊔ es) 𝒞-products Lc.L-strong
  module LfS = StrongFunctor LfS

Lf : Obj → Obj
Lf = LfS.fobj

Lf-map : ∀ {X Y : Obj} → Mor X Y → Mor (Lf X) (Lf Y)
Lf-map = LfS.fmor

open LfS public using () renaming (fmor-cong to Lf-map-cong; fmor-id to Lf-map-id; fmor-comp to Lf-map-comp)

prod-m-iso : ∀ {a₁ a₂ b₁ b₂} {f : a₁ ⇒ a₂} {f' : a₂ ⇒ a₁} {h : b₁ ⇒ b₂} {h' : b₂ ⇒ b₁} →
             (f ∘ f') ≈ id a₂ → (h ∘ h') ≈ id b₂ → (prod-m f h ∘ prod-m f' h') ≈ id (prod a₂ b₂)
prod-m-iso e₁ e₂ = ≈-trans (≈-sym (prod-m-comp _ _ _ _)) (≈-trans (prod-m-cong e₁ e₂) prod-m-id)

open polynomial-functor.Interp products strongCoproducts LfS public
  using (fobj; extend-mor; HasMu; HasMuLaws; _∘co_)
  renaming (strong-Lmap to strong-Lf-map; strong-Lmap-cong to strong-Lf-map-cong;
            strong-Lmap-comp to strong-Lf-map-comp; strong-Lmap-p₂ to strong-Lf-map-p₂;
            strong-Lmap-pre to strong-Lf-map-pre; strong-Lmap-post to strong-Lf-map-post)

strong-Lf-map-transf : ∀ {Γ X Y : Obj} (f : Mor (Fam-P.prod Γ X) Y) {γ x} →
                       strong-Lf-map f .famf .transf (γ , x) ≈ strong-Lmap (f .famf .transf (γ , x))
strong-Lf-map-transf f = ≈-trans id-left (≈-trans (strong-Lmap-post _ _) (strong-Lmap-cong id-right))

injF : ∀ {X : Obj} → Mor X (Lf X)
injF .idxf = prop-setoid.idS _
injF {X} .famf .transf x = inj
injF {X} .famf .natural {x₁} {x₂} e = ≈-sym (Lmap-inj (X .fam .subst e))

injF-natural : ∀ {X Y : Obj} (f : Mor X Y) → Fam-cat._∘_ (Lf-map f) injF ≃ Fam-cat._∘_ injF f
injF-natural f .idxf-eq .func-eq e = f .idxf .func-resp-≈ e
injF-natural {X} {Y} f .famf-eq .transf-eq {x} =
  ≈-trans (∘-cong (Lf Y .fam .refl*) id-left)
  (≈-trans id-left
  (≈-trans (Lmap-inj (f .famf .transf x)) (≈-sym id-left)))

private
  strength-injF : ∀ {Γ X : Obj} →
    Fam-cat._∘_ (LfS.strengthᵣ {Γ} {X}) (Fam-P.pair Fam-P.p₁ (Fam-cat._∘_ injF Fam-P.p₂)) ≃ injF
  strength-injF .idxf-eq .func-eq e = e
  strength-injF {Γ} {X} .famf-eq .transf-eq {γ , x} =
    ≈-trans (∘-cong (Lf (Fam-P.prod Γ X) .fam .refl*) id-left)
    (≈-trans id-left
    (≈-trans (∘-cong ≈-refl (pair-cong ≈-refl id-left))
    (≈-trans (∘-cong ≈-refl (pair-cong (≈-sym id-left) ≈-refl))
    (≈-trans (strong-Lmap-inj (id _)) id-right))))

strong-Lf-map-injF : ∀ {Γ X Y : Obj} (f : Mor (Fam-P.prod Γ X) Y) →
  Fam-cat._∘_ (strong-Lf-map f) (Fam-P.pair Fam-P.p₁ (Fam-cat._∘_ injF Fam-P.p₂)) ≃ Fam-cat._∘_ injF f
strong-Lf-map-injF f =
  Fam-cat.≈-trans (Fam-cat.assoc _ _ _)
  (Fam-cat.≈-trans (Fam-cat.∘-cong Fam-cat.≈-refl strength-injF) (injF-natural f))

record Section (X : Obj) : Set (o ⊔ m ⊔ e ⊔ os ⊔ es) where
  field
    at         : ∀ x → 𝟙𝒞 ⇒ X .fam .fm x
    at-natural : ∀ {x₁ x₂} (e : _≈s_ (X .idx) x₁ x₂) → (X .fam .subst e ∘ at x₁) ≈ at x₂

open Section public

simple-section : ∀ {A : Setoid os (os ⊔ es)} {x : obj} → (𝟙𝒞 ⇒ x) → Section simple[ A , x ]
simple-section c .at _ = c
simple-section c .at-natural _ = id-left

Lf-section : ∀ {X : Obj} → Section X → Section (Lf X)
Lf-section c .at x = L-elem (c .at x)
Lf-section {X} c .at-natural e =
  ≈-trans (L-elem-natural (X .fam .subst e) (c .at _)) (L-elem-cong (c .at-natural e))

Lf-root : ∀ {X : Obj} → Section (Lf X)
Lf-root .at x = root
Lf-root {X} .at-natural e = Lmap-root (X .fam .subst e)

coprod-section : ∀ {X Y : Obj} → Section X → Section Y → Section (HasCoproducts.coprod coproducts X Y)
coprod-section c d .at (inj₁ x) = c .at x
coprod-section c d .at (inj₂ y) = d .at y
coprod-section c d .at-natural {inj₁ _} {inj₁ _} e = c .at-natural e
coprod-section c d .at-natural {inj₂ _} {inj₂ _} e = d .at-natural e

prod-section : ∀ {X Y : Obj} → Section X → Section Y → Section (Fam-P.prod X Y)
prod-section c d .at (x , y) = pair (c .at x) (d .at y)
prod-section c d .at-natural (e₁ , e₂) =
  ≈-trans (pair-compose _ _ _ _) (pair-cong (c .at-natural e₁) (d .at-natural e₂))

scale-section : ∀ {X : Obj} → (𝟙𝒞 ⇒ 𝟙𝒞) → Section X → Section X
scale-section w c .at x = c .at x ∘ w
scale-section w c .at-natural e = head-cong (c .at-natural e)

elimF : ∀ {Γ X C : Obj} → Section C → Mor (Fam-P.prod Γ X) C → Mor (Fam-P.prod Γ (Lf X)) C
elimF cC f .idxf = f .idxf
elimF cC f .famf .transf (γ , x) =
  elim-root (cC .at (f .idxf .prop-setoid._⇒_.func (γ , x))) (f .famf .transf (γ , x))
elimF {Γ} {X} {C} cC f .famf .natural {γ₁ , x₁} {γ₂ , x₂} (γ≈ , x≈) =
  elim-root-natural (Γ .fam .subst γ≈) (X .fam .subst x≈)
    (cC .at-natural (f .idxf .prop-setoid._⇒_.func-resp-≈ (γ≈ , x≈)))
    (f .famf .transf (γ₁ , x₁)) (f .famf .transf (γ₂ , x₂))
    (f .famf .natural (γ≈ , x≈))

-- Not every morphism preserves a section: the payload injection sends the element to a payload with
-- zero root weight, not the lifted section's element.
record preserves-section {X Y : Obj} (f : Mor X Y) (c : Section X) (d : Section Y) : Prop (os ⊔ e) where
  field
    at : ∀ x → (f .famf .transf x ∘ c .at x) ≈ d .at (f .idxf .prop-setoid._⇒_.func x)
open preserves-section public

preserves-section-id : ∀ {X : Obj} (c : Section X) → preserves-section (Fam-cat.id X) c c
preserves-section-id c .at x = id-left

preserves-section-∘ : ∀ {X Y Z : Obj} {f : Mor Y Z} {g : Mor X Y} {cX cY cZ} →
                      preserves-section f cY cZ → preserves-section g cX cY →
                      preserves-section (f Fam-cat.∘ g) cX cZ
preserves-section-∘ {f = f} {g} pf pg .at x =
  ≈-trans (∘-cong id-left ≈-refl)
    (≈-trans (tail-cong (pg .at x)) (pf .at _))

preserves-section-resp : ∀ {X Y : Obj} {f g : Mor X Y} {c : Section X} {d : Section Y} →
                         f Fam-cat.≈ g → preserves-section f c d → preserves-section g c d
preserves-section-resp {X} {Y} {f} {g} {c} {d} f≃g pf .at x =
  ≈-trans (∘-cong (≈-sym (f≃g .famf-eq .transf-eq)) ≈-refl)
    (≈-trans (tail-cong (pf .at x)) (d .at-natural _))

preserves-section-inv : ∀ {X Y : Obj} {f : Mor X Y} {g : Mor Y X} {c : Section X} {d : Section Y} →
                        (f Fam-cat.∘ g) ≃ Fam-cat.id Y → (g Fam-cat.∘ f) ≃ Fam-cat.id X →
                        preserves-section f c d → preserves-section g d c
preserves-section-inv {X} {Y} {f} {g} {c} {d} fg gf hf .at y =
  ≈-trans (∘-cong ≈-refl (≈-sym (≈-trans (∘-cong ≈-refl (hf .at x)) (d .at-natural fgy≈y))))
  (≈-trans (head-cong (g .famf .natural fgy≈y))
   (≈-trans (tail-cong (≈-trans (head-cong (≈-sym id-left)) (hgf .at x)))
             (c .at-natural (g .idxf .prop-setoid._⇒_.func-resp-≈ fgy≈y))))
  where
  x = g .idxf .prop-setoid._⇒_.func y
  fgy≈y : _≈s_ (Y .idx) (f .idxf .prop-setoid._⇒_.func x) y
  fgy≈y = fg .idxf-eq .func-eq (Y .idx .isEquivalence .refl)
  hgf : preserves-section (g Fam-cat.∘ f) c c
  hgf = preserves-section-resp (Fam-cat.≈-sym gf) (preserves-section-id c)

preserves-coprod-m : ∀ {X X' Y Y' : Obj} {f : Mor X X'} {g : Mor Y Y'} {cX cX' cY cY'} →
                     preserves-section f cX cX' → preserves-section g cY cY' →
                     preserves-section (HasCoproducts.coprod-m coproducts f g)
                       (coprod-section cX cY) (coprod-section cX' cY')
preserves-coprod-m pf pg .at (inj₁ x) = ≈-trans (∘-cong (≈-trans id-left id-left) ≈-refl) (pf .at x)
preserves-coprod-m pf pg .at (inj₂ y) = ≈-trans (∘-cong (≈-trans id-left id-left) ≈-refl) (pg .at y)

preserves-prod-m : ∀ {X X' Y Y' : Obj} {f : Mor X X'} {g : Mor Y Y'} {cX cX' cY cY'} →
                   preserves-section f cX cX' → preserves-section g cY cY' →
                   preserves-section (Fam-P.prod-m f g) (prod-section cX cY) (prod-section cX' cY')
preserves-prod-m pf pg .at (x , y) =
  ≈-trans (∘-cong (pair-cong id-left id-left) ≈-refl)
    (≈-trans (pair-compose _ _ _ _) (pair-cong (pf .at x) (pg .at y)))

preserves-p₂ : ∀ {X Y : Obj} {cX cY} → preserves-section (Fam-P.p₂ {X} {Y}) (prod-section cX cY) cY
preserves-p₂ .at (x , y) = pair-p₂ _ _

preserves-pair : ∀ {X Y Z : Obj} {f : Mor X Y} {g : Mor X Z} {cX cY cZ} →
                 preserves-section f cX cY → preserves-section g cX cZ →
                 preserves-section (Fam-P.pair f g) cX (prod-section cY cZ)
preserves-pair pf pg .at x = ≈-trans (pair-natural _ _ _) (pair-cong (pf .at x) (pg .at x))

preserves-Lf-map : ∀ {X Y : Obj} {f : Mor X Y} {c d} →
                   preserves-section f c d → preserves-section (Lf-map f) (Lf-section c) (Lf-section d)
preserves-Lf-map {f = f} {c} p .at x =
  ≈-trans (L-elem-natural (f .famf .transf x) (c .at x)) (L-elem-cong (p .at x))

preserves-scale : ∀ {X Y : Obj} {f : Mor X Y} {w : 𝟙𝒞 ⇒ 𝟙𝒞} {c d} →
                  preserves-section f c d →
                  preserves-section f (scale-section w c) (scale-section w d)
preserves-scale p .at x = head-cong (p .at x)

Lf-iso : ∀ {X Y : Obj} → Fam-cat.Iso X Y → Fam-cat.Iso (Lf X) (Lf Y)
Lf-iso = functor-preserve-iso LfS.F

module Tree {n} (δ : Fin n → Obj) where
  open sort.Tree (λ i → δ i .idx) public
  open Fibre δ public

PolySection : ∀ {n} → Poly n → Set (o ⊔ m ⊔ e ⊔ os ⊔ es)
PolySection (const A) = Section A
PolySection (var i)   = Lift (o ⊔ m ⊔ e ⊔ os ⊔ es) ⊤
PolySection (P' + Q') = PolySection P' ×T PolySection Q'
PolySection (P' × Q') = PolySection P' ×T PolySection Q'
PolySection (μ P')    = PolySection P'

module MuSection {n} (δ : Fin n → Obj) (δ-section : ∀ i → Section (δ i)) where
  open Tree δ

  DecoAssignSection : ∀ {r} → DecoAssign r → Set (o ⊔ m ⊔ e ⊔ os ⊔ es)
  DecoSection : ∀ {s} → Deco s → Set (o ⊔ m ⊔ e ⊔ os ⊔ es)
  DecoAssignSection {inj₁ _} _ = Lift (o ⊔ m ⊔ e ⊔ os ⊔ es) ⊤
  DecoAssignSection {inj₂ _} d = DecoSection d
  DecoSection (mkDeco Q d) = PolySection Q ×T (∀ i → DecoAssignSection (d i))

  deco-ext-section : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ sort.Sort n}
                   {d : ∀ i → DecoAssign (ρ̄ i)} →
                   PolySection Q → (∀ i → DecoAssignSection (d i)) →
                   ∀ i → DecoAssignSection (deco-ext Q d i)
  deco-ext-section Q Qc dc Fin.zero    = Qc , dc
  deco-ext-section Q Qc dc (Fin.suc i) = dc i

  mutual
    fib-unit : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ sort.Sort n}
               (d : ∀ i → DecoAssign (ρ̄ i)) → PolySection Q → (∀ i → DecoAssignSection (d i)) →
               (t : W ∣ Q ∣ ρ̄) → 𝟙𝒞 ⇒ fib Q d t
    fib-unit Q d Qc dc (sup x) = fib-shape-unit Q (deco-ext Q d) Qc (deco-ext-section Q Qc dc) x

    fib-shape-unit : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ sort.Sort n}
                     (d : ∀ i → DecoAssign (η̄ i)) → PolySection Q → (∀ i → DecoAssignSection (d i)) →
                     (x : ⟦ ∣ Q ∣ ⟧shape η̄) → 𝟙𝒞 ⇒ fib-shape Q d x
    fib-shape-unit (const A) d Ac dc x = Ac .at x
    fib-shape-unit (var i)   d _ dc x = fib-el-unit _ (d i) (dc i) x
    fib-shape-unit (P' + Q') d (Pc , Qc) dc (inj₁ x) = L-elem (fib-shape-unit P' d Pc dc x)
    fib-shape-unit (P' + Q') d (Pc , Qc) dc (inj₂ y) = L-elem (fib-shape-unit Q' d Qc dc y)
    fib-shape-unit (P' × Q') d (Pc , Qc) dc (x , y) =
      L-elem (pair (fib-shape-unit P' d Pc dc x) (fib-shape-unit Q' d Qc dc y))
    fib-shape-unit (μ Q')    d Qc dc x = fib-unit Q' d Qc dc x

    fib-el-unit : ∀ (r : Fin n ⊎ sort.Sort n) (dr : DecoAssign r) → DecoAssignSection dr →
                  (x : El r) → 𝟙𝒞 ⇒ fib-el r dr x
    fib-el-unit (inj₁ p) _ _ x = δ-section p .at x
    fib-el-unit (inj₂ _) (mkDeco Q ρd) (Qc , ρdc) x = fib-unit Q ρd Qc ρdc x

  mutual
    fib-unit-natural : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ sort.Sort n}
                       (d : ∀ i → DecoAssign (ρ̄ i)) (Qc : PolySection Q)
                       (dc : ∀ i → DecoAssignSection (d i))
                       {t t' : W ∣ Q ∣ ρ̄} (p : W-≈ t t') →
                       (fib-subst Q d {x = t} {y = t'} p ∘ fib-unit Q d Qc dc t)
                         ≈ fib-unit Q d Qc dc t'
    fib-unit-natural Q d Qc dc {sup x} {sup y} p =
      fib-shape-unit-natural Q (deco-ext Q d) Qc (deco-ext-section Q Qc dc) p

    fib-shape-unit-natural : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ sort.Sort n}
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
    fib-shape-unit-natural (μ Q')    d Qc dc {x} {y} p = fib-unit-natural Q' d Qc dc {x} {y} p

    fib-el-unit-natural : ∀ (r : Fin n ⊎ sort.Sort n) (dr : DecoAssign r)
                          (drc : DecoAssignSection dr) {x y : El r} (p : elEq r x y) →
                          (fib-el-subst r dr p ∘ fib-el-unit r dr drc x) ≈ fib-el-unit r dr drc y
    fib-el-unit-natural (inj₁ p) _ _ e = δ-section p .at-natural e
    fib-el-unit-natural (inj₂ _) (mkDeco Q ρd) (Qc , ρdc) {x} {y} e = fib-unit-natural Q ρd Qc ρdc {x} {y} e

  μ-section : ∀ (P : Poly (suc n)) → PolySection P → Section (μ-fam P δ)
  μ-section P Pc .at t = fib-unit P (λ i → lift tt) Pc (λ i → lift tt) t
  μ-section P Pc .at-natural {t} {t'} e = fib-unit-natural P (λ i → lift tt) Pc (λ i → lift tt) {t} {t'} e

poly-section : ∀ {n} {δ : Fin n → Obj} (P : Poly n) → PolySection P → (∀ i → Section (δ i)) →
               Section (fobj μ-fam P δ)
poly-section (const A) Ac δc = Ac
poly-section (var i)   _  δc = δc i
poly-section (P + Q) (Pc , Qc) δc =
  coprod-section (Lf-section (poly-section P Pc δc)) (Lf-section (poly-section Q Qc δc))
poly-section (P × Q) (Pc , Qc) δc = Lf-section (prod-section (poly-section P Pc δc) (poly-section Q Qc δc))
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

module Reindex {nA nB} (δA : Fin nA → Obj) (δB : Fin nB → Obj) where
  private
    module T-δA = Tree δA
    module T-δB = Tree δB

  data MorD : ∀ {k} (ρA : Fin k → Fin nA ⊎ Sort nA) (ρB : Fin k → Fin nB ⊎ Sort nB) →
              (∀ v → T-δA.DecoAssign (ρA v)) → (∀ v → T-δB.DecoAssign (ρB v)) →
              Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    base : ∀ {k} {ρA ρB dA dB} (f : ∀ v → T-δA.El (ρA v) → T-δB.El (ρB v))
           (f-resp : ∀ v {a a'} → T-δA.elEq (ρA v) a a' → T-δB.elEq (ρB v) (f v a) (f v a'))
           (ffam : ∀ v a → T-δA.fib-el (ρA v) (dA v) a ⇒ T-δB.fib-el (ρB v) (dB v) (f v a)) →
           (∀ v {a a'} (p : T-δA.elEq (ρA v) a a') →
              (ffam v a' ∘ T-δA.fib-el-subst (ρA v) (dA v) p) ≈ (T-δB.fib-el-subst (ρB v) (dB v) (f-resp v p) ∘ ffam v a)) →
           MorD {k} ρA ρB dA dB
    bind : ∀ {k} {ρA ρB dA dB} (Q : Poly (suc k)) → MorD ρA ρB dA dB →
           MorD (extend ρA (inj₂ (mkSort ∣ Q ∣ ρA))) (extend ρB (inj₂ (mkSort ∣ Q ∣ ρB)))
                (T-δA.deco-ext Q dA) (T-δB.deco-ext Q dB)

  data IMorD : ∀ {k} → (Fin k → Fin nA ⊎ Sort nA) → (Fin k → Fin nB ⊎ Sort nB) →
               Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    ibase : ∀ {k} {ρA ρB} (f : ∀ v → T-δA.El (ρA v) → T-δB.El (ρB v))
            (f-resp : ∀ v {a a'} → T-δA.elEq (ρA v) a a' → T-δB.elEq (ρB v) (f v a) (f v a')) →
            IMorD {k} ρA ρB
    ibind : ∀ {k} {ρA ρB} (R : sort.Poly (suc k)) → IMorD ρA ρB →
            IMorD (extend ρA (inj₂ (mkSort R ρA))) (extend ρB (inj₂ (mkSort R ρB)))

  mutual
    ireindex : ∀ {k} {R : sort.Poly (suc k)} {ρA ρB} (md : IMorD ρA ρB) → T-δA.W R ρA → T-δB.W R ρB
    ireindex {R = R} md (T-δA.sup x) = T-δB.sup (ireindex-shape R (ibind R md) x)

    ireindex-shape : ∀ {j} (R : sort.Poly j) {ηA ηB} (md : IMorD ηA ηB) → T-δA.⟦ R ⟧shape ηA → T-δB.⟦ R ⟧shape ηB
    ireindex-shape (const S) md a = a
    ireindex-shape (var v) md a = iapply md v a
    ireindex-shape (P + Q) md (inj₁ a) = inj₁ (ireindex-shape P md a)
    ireindex-shape (P + Q) md (inj₂ b) = inj₂ (ireindex-shape Q md b)
    ireindex-shape (P × Q) md (a , b) = ireindex-shape P md a , ireindex-shape Q md b
    ireindex-shape (μ Q') md t = ireindex md t

    iapply : ∀ {k} {ρA ρB} (md : IMorD {k} ρA ρB) (v : Fin k) → T-δA.El (ρA v) → T-δB.El (ρB v)
    iapply (ibase f _) v a = f v a
    iapply (ibind R md) Fin.zero a = ireindex md a
    iapply (ibind R md) (Fin.suc v) a = iapply md v a

  mutual
    ireindex-resp : ∀ {k} {R : sort.Poly (suc k)} {ρA ρB} (md : IMorD ρA ρB) {t t' : T-δA.W R ρA} →
                    T-δA.W-≈ t t' → T-δB.W-≈ (ireindex md t) (ireindex md t')
    ireindex-resp {R = R} md {T-δA.sup x} {T-δA.sup y} p = ireindex-shape-resp R (ibind R md) {x} {y} p

    ireindex-shape-resp : ∀ {j} (R : sort.Poly j) {ηA ηB} (md : IMorD ηA ηB) {a a' : T-δA.⟦ R ⟧shape ηA} →
                          T-δA.shape≈ R ηA a a' → T-δB.shape≈ R ηB (ireindex-shape R md a) (ireindex-shape R md a')
    ireindex-shape-resp (const S) md p = p
    ireindex-shape-resp (var v)   md p = iapply-resp md v p
    ireindex-shape-resp (P + Q) md {inj₁ _} {inj₁ _} p = ireindex-shape-resp P md p
    ireindex-shape-resp (P + Q) md {inj₂ _} {inj₂ _} p = ireindex-shape-resp Q md p
    ireindex-shape-resp (P × Q) md {_ , _} {_ , _} (p₁ , p₂) = ireindex-shape-resp P md p₁ , ireindex-shape-resp Q md p₂
    ireindex-shape-resp (μ Q') md {a} {a'} p = ireindex-resp md {a} {a'} p

    iapply-resp : ∀ {k} {ρA ρB} (md : IMorD {k} ρA ρB) (v : Fin k) {a a'} →
                  T-δA.elEq (ρA v) a a' → T-δB.elEq (ρB v) (iapply md v a) (iapply md v a')
    iapply-resp (ibase f f-resp) v p = f-resp v p
    iapply-resp (ibind R md) Fin.zero {a} {a'} p = ireindex-resp md {a} {a'} p
    iapply-resp (ibind R md) (Fin.suc v) p = iapply-resp md v p

  erase : ∀ {k} {ρA ρB dA dB} → MorD {k} ρA ρB dA dB → IMorD ρA ρB
  erase (base f f-resp _ _) = ibase f f-resp
  erase (bind Q md) = ibind ∣ Q ∣ (erase md)

  reindex : ∀ {k} {R : sort.Poly (suc k)} {ρA ρB dA dB} → MorD ρA ρB dA dB → T-δA.W R ρA → T-δB.W R ρB
  reindex md = ireindex (erase md)

  reindex-shape : ∀ {j} (R : sort.Poly j) {ηA ηB dA dB} → MorD ηA ηB dA dB → T-δA.⟦ R ⟧shape ηA → T-δB.⟦ R ⟧shape ηB
  reindex-shape R md = ireindex-shape R (erase md)

  apply : ∀ {k} {ρA ρB dA dB} (md : MorD {k} ρA ρB dA dB) (v : Fin k) → T-δA.El (ρA v) → T-δB.El (ρB v)
  apply md = iapply (erase md)

  reindex-resp : ∀ {k} {R : sort.Poly (suc k)} {ρA ρB dA dB} (md : MorD ρA ρB dA dB) {t t' : T-δA.W R ρA} →
                 T-δA.W-≈ t t' → T-δB.W-≈ (reindex md t) (reindex md t')
  reindex-resp md {t} {t'} = ireindex-resp (erase md) {t} {t'}

  reindex-shape-resp : ∀ {j} (R : sort.Poly j) {ηA ηB dA dB} (md : MorD ηA ηB dA dB) {a a' : T-δA.⟦ R ⟧shape ηA} →
                       T-δA.shape≈ R ηA a a' → T-δB.shape≈ R ηB (reindex-shape R md a) (reindex-shape R md a')
  reindex-shape-resp R md {a} {a'} = ireindex-shape-resp R (erase md) {a} {a'}

  apply-resp : ∀ {k} {ρA ρB dA dB} (md : MorD {k} ρA ρB dA dB) (v : Fin k) {a a'} →
               T-δA.elEq (ρA v) a a' → T-δB.elEq (ρB v) (apply md v a) (apply md v a')
  apply-resp md v {a} {a'} = iapply-resp (erase md) v {a} {a'}

  mutual
    reindex-fam : ∀ {j} (R : Poly j) {ηA ηB dA dB} (md : MorD ηA ηB dA dB) {a : T-δA.⟦ ∣ R ∣ ⟧shape ηA} →
                  T-δA.fib-shape R dA a ⇒ T-δB.fib-shape R dB (reindex-shape ∣ R ∣ md a)
    reindex-fam (const A) md = id _
    reindex-fam (var v) md {a} = apply-fam md v a
    reindex-fam (P + Q) md {inj₁ a} = Lmap (reindex-fam P md)
    reindex-fam (P + Q) md {inj₂ b} = Lmap (reindex-fam Q md)
    reindex-fam (P × Q) md {a , b} = Lmap (prod-m (reindex-fam P md) (reindex-fam Q md))
    reindex-fam (μ Q') md {t} = reindex-fam-W md {t}

    reindex-fam-W : ∀ {k} {Q : Poly (suc k)} {ρA ρB dA dB} (md : MorD ρA ρB dA dB) {t : T-δA.W ∣ Q ∣ ρA} →
                    T-δA.fib Q dA t ⇒ T-δB.fib Q dB (reindex md t)
    reindex-fam-W {Q = Q} md {T-δA.sup x} = reindex-fam Q (bind Q md)

    apply-fam : ∀ {k} {ρA ρB dA dB} (md : MorD {k} ρA ρB dA dB) (v : Fin k) (a : T-δA.El (ρA v)) →
                T-δA.fib-el (ρA v) (dA v) a ⇒ T-δB.fib-el (ρB v) (dB v) (apply md v a)
    apply-fam (base _ _ ffam _) v a = ffam v a
    apply-fam (bind Q md) Fin.zero a = reindex-fam-W md {a}
    apply-fam (bind Q md) (Fin.suc v) a = apply-fam md v a

  mutual
    reindex-fam-natural : ∀ {j} (R : Poly j) {ηA ηB dA dB} (md : MorD ηA ηB dA dB)
                      {a a' : T-δA.⟦ ∣ R ∣ ⟧shape ηA} (p : T-δA.shape≈ ∣ R ∣ ηA a a') →
                      (reindex-fam R md {a'} ∘ T-δA.fib-shape-subst R dA p)
                        ≈ (T-δB.fib-shape-subst R dB (reindex-shape-resp ∣ R ∣ md p) ∘ reindex-fam R md {a})
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
                        {t t' : T-δA.W ∣ Q ∣ ρA} (p : T-δA.W-≈ t t') →
                        (reindex-fam-W md {t'} ∘ T-δA.fib-subst Q dA {x = t} {y = t'} p)
                          ≈ (T-δB.fib-subst Q dB {x = reindex md t} {y = reindex md t'}
                                          (reindex-resp md {t} {t'} p) ∘ reindex-fam-W md {t})
    reindex-fam-W-natural {Q = Q} md {T-δA.sup x} {T-δA.sup y} p = reindex-fam-natural Q (bind Q md) {x} {y} p

    apply-fam-natural : ∀ {k} {ρA ρB dA dB} (md : MorD {k} ρA ρB dA dB) (v : Fin k) {a a'}
                    (p : T-δA.elEq (ρA v) a a') →
                    (apply-fam md v a' ∘ T-δA.fib-el-subst (ρA v) (dA v) p)
                      ≈ (T-δB.fib-el-subst (ρB v) (dB v) (apply-resp md v p) ∘ apply-fam md v a)
    apply-fam-natural (base _ _ _ ffam-natural) v p = ffam-natural v p
    apply-fam-natural (bind Q md) Fin.zero    {a} {a'} p = reindex-fam-W-natural md {a} {a'} p
    apply-fam-natural (bind Q md) (Fin.suc v) p = apply-fam-natural md v p

module ReindexSection {nA nB} {δA : Fin nA → Obj} {δB : Fin nB → Obj}
    (δAc : ∀ i → Section (δA i)) (δBc : ∀ i → Section (δB i)) where
  private
    module T-δA = Tree δA
    module T-δB = Tree δB
    module MA = MuSection δA δAc
    module MB = MuSection δB δBc
  open Reindex δA δB

  data MorDSec : ∀ {k} {ρA : Fin k → Fin nA ⊎ Sort nA} {ρB : Fin k → Fin nB ⊎ Sort nB}
                 {dA : ∀ v → T-δA.DecoAssign (ρA v)} {dB : ∀ v → T-δB.DecoAssign (ρB v)} →
                 MorD ρA ρB dA dB → (∀ v → MA.DecoAssignSection (dA v)) →
                 (∀ v → MB.DecoAssignSection (dB v)) → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    base-s : ∀ {k} {ρA : Fin k → Fin nA ⊎ Sort nA} {ρB : Fin k → Fin nB ⊎ Sort nB}
             {dA : ∀ v → T-δA.DecoAssign (ρA v)} {dB : ∀ v → T-δB.DecoAssign (ρB v)}
             {f : ∀ v → T-δA.El (ρA v) → T-δB.El (ρB v)}
             {f-resp : ∀ v {a a'} → T-δA.elEq (ρA v) a a' → T-δB.elEq (ρB v) (f v a) (f v a')}
             {ffam : ∀ v a → T-δA.fib-el (ρA v) (dA v) a ⇒ T-δB.fib-el (ρB v) (dB v) (f v a)}
             {ffam-natural : ∀ v {a a'} (p : T-δA.elEq (ρA v) a a') →
                (ffam v a' ∘ T-δA.fib-el-subst (ρA v) (dA v) p)
                  ≈ (T-δB.fib-el-subst (ρB v) (dB v) (f-resp v p) ∘ ffam v a)}
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
      ∀ (a : T-δA.⟦ ∣ R ∣ ⟧shape ηA) →
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
      {md : MorD ρA ρB dA dB} {dAc dBc} → MorDSec md dAc dBc → ∀ (t : T-δA.W ∣ Q ∣ ρA) →
      (reindex-fam-W md {t} ∘ MA.fib-unit Q dA Qc dAc t)
        ≈ MB.fib-unit Q dB Qc dBc (reindex md t)
    reindex-fam-W-unit {Q = Q} Qc ms (T-δA.sup x) = reindex-fam-unit Q Qc (bind-s Q Qc ms) x

    apply-fam-unit : ∀ {k} {ρA ρB dA dB} {md : MorD {k} ρA ρB dA dB} {dAc dBc} →
      MorDSec md dAc dBc → ∀ (v : Fin k) (a : T-δA.El (ρA v)) →
      (apply-fam md v a ∘ MA.fib-el-unit (ρA v) (dA v) (dAc v) a)
        ≈ MB.fib-el-unit (ρB v) (dB v) (dBc v) (apply md v a)
    apply-fam-unit (base-s h)       v a = h v a
    apply-fam-unit (bind-s Q Qc ms) Fin.zero    a = reindex-fam-W-unit Qc ms a
    apply-fam-unit (bind-s Q Qc ms) (Fin.suc v) a = apply-fam-unit ms v a

-- Fibre reindex over an index-only reindex, with the Γ-dependent per-variable action carried separately.
module FReindex {nA nB} {δA : Fin nA → Obj} {δB : Fin nB → Obj} (G : obj) where
  private
    module T-δA = Tree δA
    module T-δB = Tree δB
  open Reindex δA δB using (IMorD; ireindex; ireindex-shape; iapply; ibind)

  -- Defunctionalised action: `abase` supplies all var fibres directly (a Γ-dependent fold);
  -- `abind` extends across a binder. Data (not a function) so the recursion stays structural.
  data FAct : ∀ {k} {ρA : Fin k → Fin nA ⊎ Sort nA} {ρB : Fin k → Fin nB ⊎ Sort nB} →
              IMorD ρA ρB → (∀ v → T-δA.DecoAssign (ρA v)) → (∀ v → T-δB.DecoAssign (ρB v)) →
              Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    abase : ∀ {k} {ρA ρB} {imor : IMorD {k} ρA ρB} {dA dB}
            (afib : ∀ v (a : T-δA.El (ρA v)) → prod G (T-δA.fib-el (ρA v) (dA v) a) ⇒ T-δB.fib-el (ρB v) (dB v) (iapply imor v a)) →
            FAct imor dA dB
    abind : ∀ {k} {ρA ρB} (Q : Poly (suc k)) (imor : IMorD ρA ρB) {dA dB} → FAct imor dA dB →
            FAct (ibind ∣ Q ∣ imor) (T-δA.deco-ext Q dA) (T-δB.deco-ext Q dB)

  mutual
    freindex-fam : ∀ {k} {Q : Poly (suc k)} {ρA ρB} {imor : IMorD ρA ρB} {dA dB} (act : FAct imor dA dB)
                   {t : T-δA.W ∣ Q ∣ ρA} → prod G (T-δA.fib Q dA t) ⇒ T-δB.fib Q dB (ireindex imor t)
    freindex-fam {Q = Q} {imor = imor} act {T-δA.sup x} = freindex-shape-fam Q (abind Q imor act) {x}

    freindex-shape-fam : ∀ {j} (R : Poly j) {ηA ηB} {imor : IMorD ηA ηB} {dA dB} (act : FAct imor dA dB)
                         {a : T-δA.⟦ ∣ R ∣ ⟧shape ηA} →
                         prod G (T-δA.fib-shape R dA a) ⇒ T-δB.fib-shape R dB (ireindex-shape ∣ R ∣ imor a)
    freindex-shape-fam (const A') act = p₂
    freindex-shape-fam (var v)    act {a} = aapply act v a
    freindex-shape-fam (P + Q) act {inj₁ a} = strong-Lmap (freindex-shape-fam P act {a})
    freindex-shape-fam (P + Q) act {inj₂ b} = strong-Lmap (freindex-shape-fam Q act {b})
    freindex-shape-fam (P × Q) act {a , b} =
      strong-Lmap (strong-prod-m (freindex-shape-fam P act {a}) (freindex-shape-fam Q act {b}))
    freindex-shape-fam (μ Q') act {t} = freindex-fam act {t}

    aapply : ∀ {k} {ρA ρB} {imor : IMorD {k} ρA ρB} {dA dB} (act : FAct imor dA dB) (v : Fin k) (a : T-δA.El (ρA v)) →
             prod G (T-δA.fib-el (ρA v) (dA v) a) ⇒ T-δB.fib-el (ρB v) (dB v) (iapply imor v a)
    aapply (abase afib)      v           a = afib v a
    aapply (abind Q imor act) Fin.zero    a = freindex-fam act {a}
    aapply (abind Q imor act) (Fin.suc v) a = aapply act v a

------------------------------------------------------------------------------
-- The strong catamorphism: folding a μ-carrier in an ambient context Γ, so no
-- exponentials are required. FMor is the fold-specific reindex morphism, again
-- first-order for termination, carrying the decorations of both sides.
------------------------------------------------------------------------------

-- The fold (catamorphism) for the μ-type, lifted to a standalone module so its
-- mutual recursion is termination-checked independently of the `hasMu` copattern.
module FoldBase {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj} where
    module T-δ = Tree δ
    module T-δA-ext = Tree (extend δ A)
    data FMor : ∀ {k} (ρ : Fin k → Fin n ⊎ Sort n) (ρ' : Fin k → Fin (suc n) ⊎ Sort (suc n)) →
                (∀ v → T-δ.DecoAssign (ρ v)) → (∀ v → T-δA-ext.DecoAssign (ρ' v)) →
                Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      fbase : FMor (η₀ ∣ P ∣) (λ v → inj₁ v)
                   (T-δ.deco-ext P {ρ̄ = λ i → inj₁ i} (λ i → lift tt)) (λ v → lift tt)
      fbind : ∀ {k} {ρ ρ' d d'} (Q : Poly (suc k)) → FMor ρ ρ' d d' →
              FMor (extend ρ (inj₂ (mkSort ∣ Q ∣ ρ))) (extend ρ' (inj₂ (mkSort ∣ Q ∣ ρ')))
                   (T-δ.deco-ext Q d) (T-δA-ext.deco-ext Q d')

module FoldDef {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
               (alg : Mor (Fam-P.prod Γ (fobj μ-fam P (extend δ A))) A) where
    open FoldBase {n} {Γ} {A} {P} {δ} public
    -- Fold the outer μ via `alg`; nested μ are reindexed into the `extend δ A` context,
    -- the recursion slot carrying the fold itself (inlined, so every call is structural).
    mutual
      fold-idx : Γ .idx .Carrier → T-δ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier
      fold-idx γ (T-δ.sup x) = alg .idxf .func (γ , fold-shape-idx P γ x)

      fold-shape-idx : (Q : Poly (suc n)) → Γ .idx .Carrier → T-δ.⟦ ∣ Q ∣ ⟧shape (η₀ ∣ P ∣) →
                      fobj μ-fam Q (extend δ A) .idx .Carrier
      fold-shape-idx (const A')        γ a = a
      fold-shape-idx (var Fin.zero)    γ t = fold-idx γ t
      fold-shape-idx (var (Fin.suc i)) γ a = a
      fold-shape-idx (Q₁ + Q₂) γ (inj₁ x) = inj₁ (fold-shape-idx Q₁ γ x)
      fold-shape-idx (Q₁ + Q₂) γ (inj₂ y) = inj₂ (fold-shape-idx Q₂ γ y)
      fold-shape-idx (Q₁ × Q₂) γ (x , y) = fold-shape-idx Q₁ γ x , fold-shape-idx Q₂ γ y
      fold-shape-idx (μ Q')    γ t = fold-reindex {Q = Q'} γ fbase t

      fold-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') →
                     T-δ.W ∣ Q ∣ ρ → T-δA-ext.W ∣ Q ∣ ρ'
      fold-reindex {Q = Q} γ fm (T-δ.sup x) = T-δA-ext.sup (fold-reindex-shape γ Q (fbind Q fm) x)

      fold-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB) →
                           T-δ.⟦ ∣ R ∣ ⟧shape ηA → T-δA-ext.⟦ ∣ R ∣ ⟧shape ηB
      fold-reindex-shape γ (const A') fm a = a
      fold-reindex-shape γ (var v)    fm a = fold-apply γ fm v a
      fold-reindex-shape γ (P' + Q') fm (inj₁ a) = inj₁ (fold-reindex-shape γ P' fm a)
      fold-reindex-shape γ (P' + Q') fm (inj₂ b) = inj₂ (fold-reindex-shape γ Q' fm b)
      fold-reindex-shape γ (P' × Q') fm (a , b) = fold-reindex-shape γ P' fm a , fold-reindex-shape γ Q' fm b
      fold-reindex-shape γ (μ Q'')   fm t = fold-reindex {Q = Q''} γ fm t

      fold-apply : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k) →
                   T-δ.El (ρ v) → T-δA-ext.El (ρ' v)
      fold-apply γ fbase        Fin.zero    t = fold-idx γ t
      fold-apply γ fbase        (Fin.suc i) a = a
      fold-apply γ (fbind Q fm) Fin.zero    a = fold-reindex {Q = Q} γ fm a
      fold-apply γ (fbind Q fm) (Fin.suc v) a = fold-apply γ fm v a

    mutual
      fold-idx-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : T-δ.W-≈ t t') →
                      _≈s_ (A .idx) (fold-idx γ t) (fold-idx γ' t')
      fold-idx-resp γ≈ {T-δ.sup x} {T-δ.sup y} p = alg .idxf .func-resp-≈ (γ≈ , fold-shape-idx-resp P γ≈ p)

      fold-shape-idx-resp : (Q : Poly (suc n)) → ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {x x'}
                           (p : T-δ.shape≈ ∣ Q ∣ (η₀ ∣ P ∣) x x') →
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
                          {t t' : T-δ.W ∣ Q ∣ ρ} (p : T-δ.W-≈ t t') →
                          T-δA-ext.W-≈ (fold-reindex γ fm t) (fold-reindex γ' fm t')
      fold-reindex-resp {Q = Q} γ≈ fm {T-δ.sup x} {T-δ.sup y} p = fold-reindex-shape-resp γ≈ Q (fbind Q fm) {x} {y} p

      fold-reindex-shape-resp : ∀ {j} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB)
                                {a a' : T-δ.⟦ ∣ R ∣ ⟧shape ηA} (p : T-δ.shape≈ ∣ R ∣ ηA a a') →
                                T-δA-ext.shape≈ ∣ R ∣ ηB (fold-reindex-shape γ R fm a) (fold-reindex-shape γ' R fm a')
      fold-reindex-shape-resp γ≈ (const A') fm p = p
      fold-reindex-shape-resp γ≈ (var v)    fm p = fold-apply-resp γ≈ fm v p
      fold-reindex-shape-resp γ≈ (P' + Q') fm {inj₁ _} {inj₁ _} p = fold-reindex-shape-resp γ≈ P' fm p
      fold-reindex-shape-resp γ≈ (P' + Q') fm {inj₂ _} {inj₂ _} p = fold-reindex-shape-resp γ≈ Q' fm p
      fold-reindex-shape-resp γ≈ (P' × Q') fm {_ , _} {_ , _} (p₁ , p₂) =
        fold-reindex-shape-resp γ≈ P' fm p₁ , fold-reindex-shape-resp γ≈ Q' fm p₂
      fold-reindex-shape-resp γ≈ (μ Q'')   fm {a} {a'} p = fold-reindex-resp {Q = Q''} γ≈ fm {a} {a'} p

      fold-apply-resp : ∀ {k} {ρ ρ' d d'} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (fm : FMor ρ ρ' d d') (v : Fin k)
                        {a a'} (p : T-δ.elEq (ρ v) a a') →
                        T-δA-ext.elEq (ρ' v) (fold-apply γ fm v a) (fold-apply γ' fm v a')
      fold-apply-resp γ≈ fbase        Fin.zero    {a} {a'} p = fold-idx-resp γ≈ {a} {a'} p
      fold-apply-resp γ≈ fbase        (Fin.suc i) p = p
      fold-apply-resp γ≈ (fbind Q fm) Fin.zero    {a} {a'} p = fold-reindex-resp {Q = Q} γ≈ fm {a} {a'} p
      fold-apply-resp γ≈ (fbind Q fm) (Fin.suc v) p = fold-apply-resp γ≈ fm v p

    mutual
      fold-fam : (γ : Γ .idx .Carrier) (t : T-δ.W ∣ P ∣ (λ i → inj₁ i)) →
                 prod (Γ .fam .fm γ) (T-δ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (fold-idx γ t)
      fold-fam γ (T-δ.sup x) =
        alg .famf .transf (γ , fold-shape-idx P γ x) ∘ pair p₁ (fold-shape-fam P γ x)

      fold-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : T-δ.⟦ ∣ Q ∣ ⟧shape (η₀ ∣ P ∣)) →
                       prod (Γ .fam .fm γ) (T-δ.fib-shape Q (T-δ.deco-ext P (λ i → lift tt)) x)
                         ⇒ fobj μ-fam Q (extend δ A) .fam .fm (fold-shape-idx Q γ x)
      fold-shape-fam (const A')        γ a = p₂
      fold-shape-fam (var Fin.zero)    γ t = fold-fam γ t
      fold-shape-fam (var (Fin.suc i)) γ a = p₂
      fold-shape-fam (Q₁ + Q₂) γ (inj₁ x) = strong-Lmap (fold-shape-fam Q₁ γ x)
      fold-shape-fam (Q₁ + Q₂) γ (inj₂ y) = strong-Lmap (fold-shape-fam Q₂ γ y)
      fold-shape-fam (Q₁ × Q₂) γ (x , y) =
        strong-Lmap (strong-prod-m (fold-shape-fam Q₁ γ x) (fold-shape-fam Q₂ γ y))
      fold-shape-fam (μ Q')    γ t = fold-reindex-fam {Q = Q'} γ fbase t

      fold-reindex-fam : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ' d d') (t : T-δ.W ∣ Q ∣ ρ) →
                         prod (Γ .fam .fm γ) (T-δ.fib Q d t) ⇒ T-δA-ext.fib Q d' (fold-reindex γ md t)
      fold-reindex-fam {Q = Q} γ md (T-δ.sup x) = fold-reindex-shape-fam γ Q (fbind Q md) x

      fold-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (md : FMor ηA ηB dA dB) (a : T-δ.⟦ ∣ R ∣ ⟧shape ηA) →
                               prod (Γ .fam .fm γ) (T-δ.fib-shape R dA a) ⇒ T-δA-ext.fib-shape R dB (fold-reindex-shape γ R md a)
      fold-reindex-shape-fam γ (const A') md a = p₂
      fold-reindex-shape-fam γ (var v)    md a = fold-apply-fam γ md v a
      fold-reindex-shape-fam γ (P' + Q') md (inj₁ a) = strong-Lmap (fold-reindex-shape-fam γ P' md a)
      fold-reindex-shape-fam γ (P' + Q') md (inj₂ b) = strong-Lmap (fold-reindex-shape-fam γ Q' md b)
      fold-reindex-shape-fam γ (P' × Q') md (a , b) =
        strong-Lmap (strong-prod-m (fold-reindex-shape-fam γ P' md a) (fold-reindex-shape-fam γ Q' md b))
      fold-reindex-shape-fam γ (μ Q'')   md t = fold-reindex-fam {Q = Q''} γ md t

      fold-apply-fam : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ' d d') (v : Fin k) (a : T-δ.El (ρ v)) →
                       prod (Γ .fam .fm γ) (T-δ.fib-el (ρ v) (d v) a) ⇒ T-δA-ext.fib-el (ρ' v) (d' v) (fold-apply γ md v a)
      fold-apply-fam γ fbase        Fin.zero    t = fold-fam γ t
      fold-apply-fam γ fbase        (Fin.suc i) a = p₂
      fold-apply-fam γ (fbind Q md) Fin.zero    a = fold-reindex-fam {Q = Q} γ md a
      fold-apply-fam γ (fbind Q md) (Fin.suc v) a = fold-apply-fam γ md v a

    mutual
      fold-fam-natural : ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {t t'} (p : T-δ.W-≈ t t') →
                         fold-fam γ₂ t' ∘ prod-m (Γ .fam .subst γ≈) (T-δ.fib-subst P (λ i → lift tt) {x = t} {y = t'} p) ≈
                         A .fam .subst (fold-idx-resp γ≈ {t} {t'} p) ∘ fold-fam γ₁ t
      fold-fam-natural {γ₁} {γ₂} γ≈ {T-δ.sup x} {T-δ.sup y} p =
        ≈-trans (tail-cong (≈-trans (pair-natural _ _ _)
                                    (≈-trans (pair-cong (pair-p₁ _ _) (fold-shape-fam-natural P γ≈ {x} {y} p))
                                             (≈-sym (pair-compose _ _ _ _)))))
        (head-cong-assoc (alg .famf .natural (γ≈ , fold-shape-idx-resp P γ≈ {x} {y} p)))

      fold-shape-fam-natural : (Q : Poly (suc n)) → ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {x x'}
                               (p : T-δ.shape≈ ∣ Q ∣ (η₀ ∣ P ∣) x x') →
                               fold-shape-fam Q γ₂ x' ∘ prod-m (Γ .fam .subst γ≈) (T-δ.fib-shape-subst Q (T-δ.deco-ext P (λ i → lift tt)) p) ≈
                               fobj μ-fam Q (extend δ A) .fam .subst (fold-shape-idx-resp Q γ≈ p) ∘ fold-shape-fam Q γ₁ x
      fold-shape-fam-natural (const A')        γ≈ p = pair-p₂ _ _
      fold-shape-fam-natural (var Fin.zero)    γ≈ {x} {x'} p = fold-fam-natural γ≈ {x} {x'} p
      fold-shape-fam-natural (var (Fin.suc i)) γ≈ p = pair-p₂ _ _
      fold-shape-fam-natural (Q₁ + Q₂) {γ₁} {γ₂} γ≈ {inj₁ x} {inj₁ x'} p =
        strong-Lmap-natural (Γ .fam .subst γ≈)
          (T-δ.fib-shape-subst Q₁ (T-δ.deco-ext P (λ i → lift tt)) p)
          (fobj μ-fam Q₁ (extend δ A) .fam .subst (fold-shape-idx-resp Q₁ γ≈ p))
          (fold-shape-fam Q₁ γ₁ x) (fold-shape-fam Q₁ γ₂ x')
          (fold-shape-fam-natural Q₁ γ≈ p)
      fold-shape-fam-natural (Q₁ + Q₂) {γ₁} {γ₂} γ≈ {inj₂ y} {inj₂ y'} p =
        strong-Lmap-natural (Γ .fam .subst γ≈)
          (T-δ.fib-shape-subst Q₂ (T-δ.deco-ext P (λ i → lift tt)) p)
          (fobj μ-fam Q₂ (extend δ A) .fam .subst (fold-shape-idx-resp Q₂ γ≈ p))
          (fold-shape-fam Q₂ γ₁ y) (fold-shape-fam Q₂ γ₂ y')
          (fold-shape-fam-natural Q₂ γ≈ p)
      fold-shape-fam-natural (Q₁ × Q₂) {γ₁} {γ₂} γ≈ {x₁ , x₂} {x₁' , x₂'} (p₁p , p₂p) =
        strong-Lmap-natural (Γ .fam .subst γ≈)
          (prod-m (T-δ.fib-shape-subst Q₁ (T-δ.deco-ext P (λ i → lift tt)) p₁p)
                  (T-δ.fib-shape-subst Q₂ (T-δ.deco-ext P (λ i → lift tt)) p₂p))
          (prod-m (fobj μ-fam Q₁ (extend δ A) .fam .subst (fold-shape-idx-resp Q₁ γ≈ p₁p))
                  (fobj μ-fam Q₂ (extend δ A) .fam .subst (fold-shape-idx-resp Q₂ γ≈ p₂p)))
          (strong-prod-m (fold-shape-fam Q₁ γ₁ x₁) (fold-shape-fam Q₂ γ₁ x₂))
          (strong-prod-m (fold-shape-fam Q₁ γ₂ x₁') (fold-shape-fam Q₂ γ₂ x₂'))
          (strong-prod-m-natural (fold-shape-fam-natural Q₁ γ≈ p₁p) (fold-shape-fam-natural Q₂ γ≈ p₂p))
      fold-shape-fam-natural (μ Q')    γ≈ {x} {x'} p = fold-reindex-fam-natural {Q = Q'} γ≈ fbase {x} {x'} p

      fold-reindex-fam-natural : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂)
                             (md : FMor ρ ρ' d d') {t t' : T-δ.W ∣ Q ∣ ρ} (p : T-δ.W-≈ t t') →
                             (fold-reindex-fam γ₂ md t' ∘ prod-m (Γ .fam .subst γ≈) (T-δ.fib-subst Q d {x = t} {y = t'} p))
                               ≈ (T-δA-ext.fib-subst Q d' {x = fold-reindex γ₁ md t} {y = fold-reindex γ₂ md t'}
                                                (fold-reindex-resp γ≈ md {t} {t'} p) ∘ fold-reindex-fam γ₁ md t)
      fold-reindex-fam-natural {Q = Q} γ≈ md {T-δ.sup x} {T-δ.sup y} p = fold-reindex-shape-fam-natural γ≈ Q (fbind Q md) {x} {y} p

      fold-reindex-shape-fam-natural : ∀ {j} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (R : Poly j) {ηA ηB dA dB} (md : FMor ηA ηB dA dB)
                                   {a a' : T-δ.⟦ ∣ R ∣ ⟧shape ηA} (p : T-δ.shape≈ ∣ R ∣ ηA a a') →
                                   (fold-reindex-shape-fam γ₂ R md a' ∘ prod-m (Γ .fam .subst γ≈) (T-δ.fib-shape-subst R dA p))
                                     ≈ (T-δA-ext.fib-shape-subst R dB (fold-reindex-shape-resp γ≈ R md p) ∘ fold-reindex-shape-fam γ₁ R md a)
      fold-reindex-shape-fam-natural γ≈ (const A') md p = pair-p₂ _ _
      fold-reindex-shape-fam-natural γ≈ (var v)    md p = fold-apply-fam-natural γ≈ md v p
      fold-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' + Q') {dA = dA} {dB} md {inj₁ a} {inj₁ a'} p =
        strong-Lmap-natural (Γ .fam .subst γ≈)
          (T-δ.fib-shape-subst P' dA p)
          (T-δA-ext.fib-shape-subst P' dB (fold-reindex-shape-resp γ≈ P' md p))
          (fold-reindex-shape-fam γ₁ P' md a) (fold-reindex-shape-fam γ₂ P' md a')
          (fold-reindex-shape-fam-natural γ≈ P' md p)
      fold-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' + Q') {dA = dA} {dB} md {inj₂ b} {inj₂ b'} p =
        strong-Lmap-natural (Γ .fam .subst γ≈)
          (T-δ.fib-shape-subst Q' dA p)
          (T-δA-ext.fib-shape-subst Q' dB (fold-reindex-shape-resp γ≈ Q' md p))
          (fold-reindex-shape-fam γ₁ Q' md b) (fold-reindex-shape-fam γ₂ Q' md b')
          (fold-reindex-shape-fam-natural γ≈ Q' md p)
      fold-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' × Q') {dA = dA} {dB} md {a₁ , a₂} {a₁' , a₂'} (p₁p , p₂p) =
        strong-Lmap-natural (Γ .fam .subst γ≈)
          (prod-m (T-δ.fib-shape-subst P' dA p₁p) (T-δ.fib-shape-subst Q' dA p₂p))
          (prod-m (T-δA-ext.fib-shape-subst P' dB (fold-reindex-shape-resp γ≈ P' md p₁p))
                  (T-δA-ext.fib-shape-subst Q' dB (fold-reindex-shape-resp γ≈ Q' md p₂p)))
          (strong-prod-m (fold-reindex-shape-fam γ₁ P' md a₁) (fold-reindex-shape-fam γ₁ Q' md a₂))
          (strong-prod-m (fold-reindex-shape-fam γ₂ P' md a₁') (fold-reindex-shape-fam γ₂ Q' md a₂'))
          (strong-prod-m-natural (fold-reindex-shape-fam-natural γ≈ P' md p₁p)
                                 (fold-reindex-shape-fam-natural γ≈ Q' md p₂p))
      fold-reindex-shape-fam-natural γ≈ (μ Q'')   md {a} {a'} p = fold-reindex-fam-natural {Q = Q''} γ≈ md {a} {a'} p

      fold-apply-fam-natural : ∀ {k} {ρ ρ' d d'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (md : FMor ρ ρ' d d') (v : Fin k)
                               {a a'} (p : T-δ.elEq (ρ v) a a') →
                               fold-apply-fam γ₂ md v a' ∘ prod-m (Γ .fam .subst γ≈) (T-δ.fib-el-subst (ρ v) (d v) p) ≈
                               T-δA-ext.fib-el-subst (ρ' v) (d' v) (fold-apply-resp γ≈ md v p) ∘ fold-apply-fam γ₁ md v a
      fold-apply-fam-natural γ≈ fbase        Fin.zero    {a} {a'} p = fold-fam-natural γ≈ {a} {a'} p
      fold-apply-fam-natural γ≈ fbase        (Fin.suc i) p = pair-p₂ _ _
      fold-apply-fam-natural γ≈ (fbind Q md) Fin.zero    {a} {a'} p = fold-reindex-fam-natural {Q = Q} γ≈ md {a} {a'} p
      fold-apply-fam-natural γ≈ (fbind Q md) (Fin.suc v) p = fold-apply-fam-natural γ≈ md v p

    foldMor : Mor (Fam-P.prod Γ (μ-fam P δ)) A
    foldMor .idxf .func (γ , t) = fold-idx γ t
    foldMor .idxf .func-resp-≈ {γ , t} {γ' , t'} (γ≈ , t≈) = fold-idx-resp γ≈ {t} {t'} t≈
    foldMor .famf .transf (γ , t) = fold-fam γ t
    foldMor .famf .natural {γ₁ , t₁} {γ₂ , t₂} (γ≈ , t≈) = fold-fam-natural γ≈ {t₁} {t₂} t≈

module FoldSection {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (alg : Mor (Fam-P.prod Γ (fobj μ-fam P (extend δ A))) A)
    (δc : ∀ i → Section (δ i)) (cA : Section A) (Pc : PolySection P) where

  open FoldDef {n} {Γ} {A} {P} {δ} alg
  private
    module MuSection-δ = MuSection δ δc
    module MuSection-A = MuSection (extend δ A) (extend-section δc cA)

  data FMorSec : ∀ {k} {ρ : Fin k → Fin n ⊎ Sort n} {ρ' : Fin k → Fin (suc n) ⊎ Sort (suc n)}
                 {d : ∀ v → T-δ.DecoAssign (ρ v)} {d' : ∀ v → T-δA-ext.DecoAssign (ρ' v)} →
                 FMor ρ ρ' d d' → (∀ v → MuSection-δ.DecoAssignSection (d v)) →
                 (∀ v → MuSection-A.DecoAssignSection (d' v)) → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    fbase-s : FMorSec fbase (MuSection-δ.deco-ext-section P Pc (λ i → lift tt)) (λ v → lift tt)
    fbind-s : ∀ {k} {ρ ρ' d d'} {fm : FMor {k} ρ ρ' d d'} {dc d'c} (Q : Poly (suc k))
              (Qc : PolySection Q) → FMorSec fm dc d'c →
              FMorSec (fbind Q fm) (MuSection-δ.deco-ext-section Q Qc dc) (MuSection-A.deco-ext-section Q Qc d'c)

  module _ (γ : Γ .idx .Carrier) (cγ : 𝟙𝒞 ⇒ Γ .fam .fm γ)
           (halg : ∀ s → (alg .famf .transf (γ , s) ∘
                           pair cγ (poly-section P Pc (extend-section δc cA) .at s))
                         ≈ cA .at (alg .idxf .func (γ , s))) where
    mutual
      fold-fam-unit : ∀ t →
        (fold-fam γ t ∘ pair cγ (MuSection-δ.μ-section P Pc .at t)) ≈ cA .at (fold-idx γ t)
      fold-fam-unit (T-δ.sup x) =
        ≈-trans (tail-cong (≈-trans (pair-natural _ _ _)
                                    (pair-cong (pair-p₁ _ _) (fold-shape-fam-unit P Pc x))))
                 (halg (fold-shape-idx P γ x))

      fold-shape-fam-unit : ∀ (Q : Poly (suc n)) (Qc : PolySection Q)
        (x : T-δ.⟦ ∣ Q ∣ ⟧shape (η₀ ∣ P ∣)) →
        (fold-shape-fam Q γ x ∘
          pair cγ (MuSection-δ.fib-shape-unit Q (T-δ.deco-ext P (λ i → lift tt)) Qc
                     (MuSection-δ.deco-ext-section P Pc (λ i → lift tt)) x))
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
        {dc : ∀ v → MuSection-δ.DecoAssignSection (d v)} {d'c : ∀ v → MuSection-A.DecoAssignSection (d' v)}
        (Qc : PolySection Q) → FMorSec fm dc d'c → ∀ t →
        (fold-reindex-fam γ fm t ∘ pair cγ (MuSection-δ.fib-unit Q d Qc dc t))
          ≈ MuSection-A.fib-unit Q d' Qc d'c (fold-reindex γ fm t)
      fold-reindex-fam-unit {Q = Q} Qc fs (T-δ.sup x) = fold-reindex-shape-fam-unit Q Qc (fbind-s Q Qc fs) x

      fold-reindex-shape-fam-unit : ∀ {j} (R : Poly j) (Rc : PolySection R)
        {ηA : Fin j → Fin n ⊎ Sort n} {ηB : Fin j → Fin (suc n) ⊎ Sort (suc n)}
        {dA : ∀ v → T-δ.DecoAssign (ηA v)} {dB : ∀ v → T-δA-ext.DecoAssign (ηB v)}
        {fm : FMor ηA ηB dA dB}
        {dAc : ∀ v → MuSection-δ.DecoAssignSection (dA v)} {dBc : ∀ v → MuSection-A.DecoAssignSection (dB v)} →
        FMorSec fm dAc dBc → ∀ (a : T-δ.⟦ ∣ R ∣ ⟧shape ηA) →
        (fold-reindex-shape-fam γ R fm a ∘ pair cγ (MuSection-δ.fib-shape-unit R dA Rc dAc a))
          ≈ MuSection-A.fib-shape-unit R dB Rc dBc (fold-reindex-shape γ R fm a)
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
        {dc : ∀ w → MuSection-δ.DecoAssignSection (d w)} {d'c : ∀ w → MuSection-A.DecoAssignSection (d' w)} →
        FMorSec fm dc d'c → ∀ (v : Fin k) (a : T-δ.El (ρ v)) →
        (fold-apply-fam γ fm v a ∘ pair cγ (MuSection-δ.fib-el-unit (ρ v) (d v) (dc v) a))
          ≈ MuSection-A.fib-el-unit (ρ' v) (d' v) (d'c v) (fold-apply γ fm v a)
      fold-apply-fam-unit fbase-s           Fin.zero    t = fold-fam-unit t
      fold-apply-fam-unit fbase-s           (Fin.suc i) a = pair-p₂ _ _
      fold-apply-fam-unit (fbind-s Q Qc fs) Fin.zero    a = fold-reindex-fam-unit Qc fs a
      fold-apply-fam-unit (fbind-s Q Qc fs) (Fin.suc v) a = fold-apply-fam-unit fs v a

  preserves-foldMor : (cΓ : Section Γ) →
    preserves-section alg (prod-section cΓ (poly-section P Pc (extend-section δc cA))) cA →
    preserves-section foldMor (prod-section cΓ (MuSection-δ.μ-section P Pc)) cA
  preserves-foldMor cΓ halg .at (γ , t) = fold-fam-unit γ (cΓ .at γ) (λ s → halg .at (γ , s)) t

------------------------------------------------------------------------------
-- inMap, the canonical iso between the categorical one-step unfolding
-- fobj P (δ, μ P δ) and the concrete carrier, via the embed/unembed bridges;
-- packaged with the fold as the HasMu instance.
------------------------------------------------------------------------------

module InMapDef {n} (P : Poly (suc n)) (δ : Fin n → Obj) where
    δ' = extend δ (μ-fam P δ)
    module T-δ = Tree δ
    module T-δ' = Tree δ'
    module Reindex-δ' = Reindex δ' δ
    open Reindex-δ' public using (MorD; base; bind; apply; apply-fam; reindex; reindex-resp; reindex-shape; reindex-shape-resp; reindex-fam; reindex-fam-natural; reindex-fam-W; reindex-fam-W-natural)

    embed-idx : (Q : Poly (suc n)) → fobj μ-fam Q δ' .idx .Carrier → T-δ'.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)
    embed-idx (const A) a = a
    embed-idx (var v)   a = a
    embed-idx (Q₁ + Q₂) (inj₁ x) = inj₁ (embed-idx Q₁ x)
    embed-idx (Q₁ + Q₂) (inj₂ y) = inj₂ (embed-idx Q₂ y)
    embed-idx (Q₁ × Q₂) (x , y) = embed-idx Q₁ x , embed-idx Q₂ y
    embed-idx (μ Q')    t = t
    embed-idx-resp : (Q : Poly (suc n)) {x y : fobj μ-fam Q δ' .idx .Carrier} →
                     _≈s_ (fobj μ-fam Q δ' .idx) x y → T-δ'.shape≈ ∣ Q ∣ (λ v → inj₁ v) (embed-idx Q x) (embed-idx Q y)
    embed-idx-resp (const A) p = p
    embed-idx-resp (var v)   p = p
    embed-idx-resp (Q₁ + Q₂) {inj₁ _} {inj₁ _} p = embed-idx-resp Q₁ p
    embed-idx-resp (Q₁ + Q₂) {inj₂ _} {inj₂ _} p = embed-idx-resp Q₂ p
    embed-idx-resp (Q₁ × Q₂) {_ , _} {_ , _} (p₁ , p₂) = embed-idx-resp Q₁ p₁ , embed-idx-resp Q₂ p₂
    embed-idx-resp (μ Q')    p = p
    unembed-idx : (Q : Poly (suc n)) → T-δ'.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v) → fobj μ-fam Q δ' .idx .Carrier
    unembed-idx (const A) a = a
    unembed-idx (var v)   a = a
    unembed-idx (Q₁ + Q₂) (inj₁ x) = inj₁ (unembed-idx Q₁ x)
    unembed-idx (Q₁ + Q₂) (inj₂ y) = inj₂ (unembed-idx Q₂ y)
    unembed-idx (Q₁ × Q₂) (x , y) = unembed-idx Q₁ x , unembed-idx Q₂ y
    unembed-idx (μ Q')    t = t

    unembed-idx-resp : (Q : Poly (suc n)) {x y : T-δ'.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)} →
                       T-δ'.shape≈ ∣ Q ∣ (λ v → inj₁ v) x y →
                       _≈s_ (fobj μ-fam Q δ' .idx) (unembed-idx Q x) (unembed-idx Q y)
    unembed-idx-resp (const A) p = p
    unembed-idx-resp (var v)   p = p
    unembed-idx-resp (Q₁ + Q₂) {inj₁ _} {inj₁ _} p = unembed-idx-resp Q₁ p
    unembed-idx-resp (Q₁ + Q₂) {inj₂ _} {inj₂ _} p = unembed-idx-resp Q₂ p
    unembed-idx-resp (Q₁ × Q₂) {_ , _} {_ , _} (p₁ , p₂) = unembed-idx-resp Q₁ p₁ , unembed-idx-resp Q₂ p₂
    unembed-idx-resp (μ Q')    p = p

    embed-unembed : (Q : Poly (suc n)) (x : T-δ'.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)) →
                    T-δ'.shape≈ ∣ Q ∣ (λ v → inj₁ v) (embed-idx Q (unembed-idx Q x)) x
    embed-unembed (const A) a = A .idx .isEquivalence .refl
    embed-unembed (var v)   a = T-δ'.elEq-refl (inj₁ v) a
    embed-unembed (Q₁ + Q₂) (inj₁ x) = embed-unembed Q₁ x
    embed-unembed (Q₁ + Q₂) (inj₂ y) = embed-unembed Q₂ y
    embed-unembed (Q₁ × Q₂) (x , y) = embed-unembed Q₁ x , embed-unembed Q₂ y
    embed-unembed (μ Q')    t = T-δ'.W-≈-refl t

    m₀ : ∀ v → T-δ'.El (inj₁ v) → T-δ.El (η₀ ∣ P ∣ v)
    m₀ Fin.zero    a = a
    m₀ (Fin.suc i) a = a
    m₀-resp : ∀ v {a a'} → T-δ'.elEq (inj₁ v) a a' → T-δ.elEq (η₀ ∣ P ∣ v) (m₀ v a) (m₀ v a')
    m₀-resp Fin.zero    p = p
    m₀-resp (Fin.suc i) p = p
    m₀-fam : ∀ v (a : T-δ'.El (inj₁ v)) →
             T-δ'.fib-el (inj₁ v) (lift tt) a ⇒ T-δ.fib-el (η₀ ∣ P ∣ v) (T-δ.deco-ext P (λ i → lift tt) v) (m₀ v a)
    m₀-fam Fin.zero    a = id _
    m₀-fam (Fin.suc i) a = id _
    m₀-fam-natural : ∀ v {a a'} (p : T-δ'.elEq (inj₁ v) a a') →
                 (m₀-fam v a' ∘ T-δ'.fib-el-subst (inj₁ v) (lift tt) p)
                   ≈ (T-δ.fib-el-subst (η₀ ∣ P ∣ v) (T-δ.deco-ext P (λ i → lift tt) v) (m₀-resp v p) ∘ m₀-fam v a)
    m₀-fam-natural Fin.zero    p = ≈-trans id-left (≈-sym id-right)
    m₀-fam-natural (Fin.suc i) p = ≈-trans id-left (≈-sym id-right)
    mor₀ : MorD (λ v → inj₁ v) (η₀ ∣ P ∣) (λ v → lift tt) (T-δ.deco-ext P (λ i → lift tt))
    mor₀ = base m₀ m₀-resp m₀-fam m₀-fam-natural
    embed-fam : (Q : Poly (suc n)) (x : fobj μ-fam Q δ' .idx .Carrier) →
                fobj μ-fam Q δ' .fam .fm x ⇒ T-δ'.fib-shape Q (λ v → lift tt) (embed-idx Q x)
    embed-fam (const A) a = id _
    embed-fam (var v)   a = id _
    embed-fam (Q₁ + Q₂) (inj₁ x) = Lmap (embed-fam Q₁ x)
    embed-fam (Q₁ + Q₂) (inj₂ y) = Lmap (embed-fam Q₂ y)
    embed-fam (Q₁ × Q₂) (x , y) = Lmap (prod-m (embed-fam Q₁ x) (embed-fam Q₂ y))
    embed-fam (μ Q')    t = id _
    embed-fam-natural : (Q : Poly (suc n)) {x y : fobj μ-fam Q δ' .idx .Carrier} (e : _≈s_ (fobj μ-fam Q δ' .idx) x y) →
                        (embed-fam Q y ∘ fobj μ-fam Q δ' .fam .subst e)
                          ≈ (T-δ'.fib-shape-subst Q (λ v → lift tt) (embed-idx-resp Q e) ∘ embed-fam Q x)
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

    unembed-fam : (Q : Poly (suc n)) (y : T-δ'.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)) →
                  T-δ'.fib-shape Q (λ v → lift tt) y ⇒ fobj μ-fam Q δ' .fam .fm (unembed-idx Q y)
    unembed-fam (const A) a = id _
    unembed-fam (var v)   a = id _
    unembed-fam (Q₁ + Q₂) (inj₁ x) = Lmap (unembed-fam Q₁ x)
    unembed-fam (Q₁ + Q₂) (inj₂ y) = Lmap (unembed-fam Q₂ y)
    unembed-fam (Q₁ × Q₂) (x , y) = Lmap (prod-m (unembed-fam Q₁ x) (unembed-fam Q₂ y))
    unembed-fam (μ Q')    t = id _

    unembed-fam-natural : (Q : Poly (suc n)) {x y : T-δ'.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)}
                          (e : T-δ'.shape≈ ∣ Q ∣ (λ v → inj₁ v) x y) →
                          (unembed-fam Q y ∘ T-δ'.fib-shape-subst Q (λ v → lift tt) e)
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

    embed-unembed-fam : (Q : Poly (suc n)) (y : T-δ'.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)) →
                        (T-δ'.fib-shape-subst Q (λ v → lift tt) (embed-unembed Q y)
                         ∘ (embed-fam Q (unembed-idx Q y) ∘ unembed-fam Q y))
                        ≈ id _
    embed-unembed-fam (const A) a = ≈-trans (∘-cong (A .fam .refl*) ≈-refl) (≈-trans id-left id-left)
    embed-unembed-fam (var v) a =
      ≈-trans (∘-cong (T-δ'.fib-el-refl* (inj₁ v) (lift tt) a) ≈-refl) (≈-trans id-left id-left)
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
      ≈-trans (∘-cong (T-δ'.fib-refl* Q' (λ v → lift tt) t) ≈-refl) (≈-trans id-left id-left)

    unembed-embed : (Q : Poly (suc n)) (x : fobj μ-fam Q δ' .idx .Carrier) →
                    _≈s_ (fobj μ-fam Q δ' .idx) (unembed-idx Q (embed-idx Q x)) x
    unembed-embed (const A) a = A .idx .isEquivalence .refl
    unembed-embed (var v)   a = T-δ'.elEq-refl (inj₁ v) a
    unembed-embed (Q₁ + Q₂) (inj₁ x) = unembed-embed Q₁ x
    unembed-embed (Q₁ + Q₂) (inj₂ y) = unembed-embed Q₂ y
    unembed-embed (Q₁ × Q₂) (x , y) = unembed-embed Q₁ x , unembed-embed Q₂ y
    unembed-embed (μ Q')    t = T-δ'.W-≈-refl t

    unembed-embed-fam : (Q : Poly (suc n)) (x : fobj μ-fam Q δ' .idx .Carrier) →
                        (fobj μ-fam Q δ' .fam .subst (unembed-embed Q x)
                         ∘ (unembed-fam Q (embed-idx Q x) ∘ embed-fam Q x))
                        ≈ id _
    unembed-embed-fam (const A) a = ≈-trans (∘-cong (A .fam .refl*) ≈-refl) (≈-trans id-left id-left)
    unembed-embed-fam (var v) a =
      ≈-trans (∘-cong (T-δ'.fib-el-refl* (inj₁ v) (lift tt) a) ≈-refl) (≈-trans id-left id-left)
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
      ≈-trans (∘-cong (T-δ'.fib-refl* Q' (λ v → lift tt) t) ≈-refl) (≈-trans id-left id-left)

    inMor : Mor (fobj μ-fam P δ') (μ-fam P δ)
    inMor .idxf .func i = T-δ.sup (reindex-shape ∣ P ∣ mor₀ (embed-idx P i))
    inMor .idxf .func-resp-≈ x≈y = reindex-shape-resp ∣ P ∣ mor₀ (embed-idx-resp P x≈y)
    inMor .famf .transf x = reindex-fam P mor₀ ∘ embed-fam P x
    inMor .famf .natural e =
      ≈-trans (tail-cong (embed-fam-natural P e))
      (head-cong-assoc (reindex-fam-natural P mor₀ (embed-idx-resp P e)))

    module InMapSection (δc : ∀ i → Section (δ i)) (Pc : PolySection P) where
      private
        μc : Section (μ-fam P δ)
        μc = MuSection.μ-section δ δc P Pc
        module MuSection-δ' = MuSection δ' (extend-section δc μc)
        module MuSection-δ = MuSection δ δc
        module ReindexSection-δc = ReindexSection (extend-section δc μc) δc

      mor₀-sec : ReindexSection-δc.MorDSec mor₀ (λ v → lift tt) (MuSection-δ.deco-ext-section P Pc (λ i → lift tt))
      mor₀-sec = ReindexSection-δc.base-s h
        where
        h : ∀ v a → (m₀-fam v a ∘ MuSection-δ'.fib-el-unit (inj₁ v) (lift tt) (lift tt) a)
                    ≈ MuSection-δ.fib-el-unit (η₀ ∣ P ∣ v) (T-δ.deco-ext P (λ i → lift tt) v)
                                     (MuSection-δ.deco-ext-section P Pc (λ i → lift tt) v) (m₀ v a)
        h Fin.zero    a = id-left
        h (Fin.suc i) a = id-left

      embed-unit : (Q : Poly (suc n)) (Qc : PolySection Q) (x : fobj μ-fam Q δ' .idx .Carrier) →
        (embed-fam Q x ∘ poly-section Q Qc (extend-section δc μc) .at x)
          ≈ MuSection-δ'.fib-shape-unit Q (λ v → lift tt) Qc (λ v → lift tt) (embed-idx Q x)
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

      unembed-unit : (Q : Poly (suc n)) (Qc : PolySection Q) (y : T-δ'.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)) →
        (unembed-fam Q y ∘ MuSection-δ'.fib-shape-unit Q (λ v → lift tt) Qc (λ v → lift tt) y)
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
        ≈-trans (tail-cong (embed-unit P Pc x))
                 (ReindexSection-δc.reindex-fam-unit P Pc mor₀-sec (embed-idx P x))

hasMu : HasMu
hasMu .HasMu.μ-obj = μ-fam
hasMu .HasMu.inMap P δ = InMapDef.inMor P δ
hasMu .HasMu.⦅_⦆ alg = FoldDef.foldMor alg

private module hasMu = HasMu hasMu
open hasMu using (strong-fmor; strong-extend-mor)

preserves-inMap : ∀ {n} (P : Poly (suc n)) (δ : Fin n → Obj)
                  (δc : ∀ i → Section (δ i)) (Pc : PolySection P) →
                  preserves-section (InMapDef.inMor P δ)
                    (poly-section P Pc (extend-section δc (MuSection.μ-section δ δc P Pc)))
                    (MuSection.μ-section δ δc P Pc)
preserves-inMap P δ δc Pc = InMapDef.InMapSection.preserves-inMor P δ δc Pc

fuse-idx : ∀ {n} {Γ : Obj} {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
               let module Reindex-sₛ = Reindex sₛ sₜ in
               (imor : Γ .idx .Carrier → Reindex-sₛ.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
               (mors : ∀ i → Mor (Fam-P.prod Γ (sₛ i)) (sₜ i))
               (agree : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                       _≈s_ (sₜ i .idx) (Reindex-sₛ.iapply (imor γ₁) i a₁) (mors i .idxf .func (γ₂ , a₂))) →
               ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {m₁ m₂}
               (m≈ : _≈s_ (μ-fam Q sₛ .idx) m₁ m₂) →
               _≈s_ (μ-fam Q sₜ .idx) (Reindex-sₛ.ireindex (imor γ₁) m₁) (strong-fmor (μ Q) mors .idxf .func (γ₂ , m₂))
fuse-shape : ∀ {n} {Γ : Obj} {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
                 let module Reindex-sₛ = Reindex sₛ sₜ
                     module T-sₛ = Tree sₛ
                     module T-sₜ = Tree sₜ
                     module InMapDef-P = InMapDef Q sₜ in
                 (imor : Γ .idx .Carrier → Reindex-sₛ.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
                 (mors : ∀ i → Mor (Fam-P.prod Γ (sₛ i)) (sₜ i))
                 (agree : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                         _≈s_ (sₜ i .idx) (Reindex-sₛ.iapply (imor γ₁) i a₁) (mors i .idxf .func (γ₂ , a₂))) →
                 let module FoldDef-alg = FoldDef {Γ = Γ} {A = μ-fam Q sₜ} {P = Q} {δ = sₛ}
                                   (Fam-cat._∘_ InMapDef-P.inMor (strong-fmor Q (strong-extend-mor mors Fam-P.p₂))) in
                 (R : Poly (suc n)) →
                 ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {x₁ x₂}
                 (x≈ : T-sₛ.shape≈ ∣ R ∣ (η₀ ∣ Q ∣) x₁ x₂) →
                 T-sₜ.shape≈ ∣ R ∣ (η₀ ∣ Q ∣)
                   (Reindex-sₛ.ireindex-shape ∣ R ∣ (Reindex-sₛ.ibind ∣ Q ∣ (imor γ₁)) x₁)
                   (InMapDef-P.reindex-shape ∣ R ∣ InMapDef-P.mor₀
                    (InMapDef-P.embed-idx R (strong-fmor R (strong-extend-mor mors Fam-P.p₂) .idxf .func
                      (γ₂ , FoldDef-alg.fold-shape-idx R γ₂ x₂))))

fuse-idx Q imor mors agree γ≈ {Tree.sup x₁} {Tree.sup x₂} m≈ = fuse-shape Q imor mors agree Q γ≈ {x₁} {x₂} m≈

fuse-shape Q imor mors agree (const A')                  γ≈ x≈ = x≈
fuse-shape Q imor mors agree (var Fin.zero)              γ≈ {x₁} {x₂} x≈ = fuse-idx Q imor mors agree γ≈ {x₁} {x₂} x≈
fuse-shape Q imor mors agree (var (Fin.suc i))           γ≈ x≈ = agree i γ≈ x≈
fuse-shape Q imor mors agree (R₁ + R₂) γ≈ {inj₁ _} {inj₁ _} x≈ = fuse-shape Q imor mors agree R₁ γ≈ x≈
fuse-shape Q imor mors agree (R₁ + R₂) γ≈ {inj₂ _} {inj₂ _} x≈ = fuse-shape Q imor mors agree R₂ γ≈ x≈
fuse-shape Q imor mors agree (R₁ × R₂) γ≈ {_ , _} {_ , _} (x≈₁ , x≈₂) =
  fuse-shape Q imor mors agree R₁ γ≈ x≈₁ , fuse-shape Q imor mors agree R₂ γ≈ x≈₂
fuse-shape {Γ = Γ} {sₛ = sₛ} {sₜ = sₜ} Q imor mors agree (μ R'') {γ₁} {γ₂} γ≈ {x₁} {x₂} x≈ =
  T-sₜ.W-≈-trans {x = Reindex-sₛ.ireindex-shape ∣ μ R'' ∣ (Reindex-sₛ.ibind ∣ Q ∣ (imor γ₁)) x₁}
               {z = InMapDef-P.reindex-shape ∣ μ R'' ∣ InMapDef-P.mor₀ (InMapDef-P.embed-idx (μ R'')
                      (strong-fmor (μ R'') (strong-extend-mor mors Fam-P.p₂)
                        .idxf .func (γ₂ , w)))}
               telescope
               (InMapDef-P.reindex-resp InMapDef-P.mor₀
                 {t = Reindex-ext.ireindex (cmb' γ₁) wm₁}
                 {t' = strong-fmor (μ R'') (strong-extend-mor mors Fam-P.p₂) .idxf .func (γ₂ , w)}
                 rec)
  where
    module T-sₜ = Tree sₜ
    module T-sₛ = Tree sₛ
    module InMapDef-P = InMapDef Q sₜ
    module Reindex-sₛ = Reindex sₛ sₜ
    module Reindex-ext = Reindex (extend sₛ (μ-fam Q sₜ)) (extend sₜ (μ-fam Q sₜ))
    module FoldDef-alg = FoldDef {Γ = Γ} {A = μ-fam Q sₜ} {P = Q} {δ = sₛ}
                  (Fam-cat._∘_ InMapDef-P.inMor (strong-fmor Q (strong-extend-mor mors Fam-P.p₂)))
    wm₁ = FoldDef-alg.fold-reindex {Q = R''} γ₁ FoldDef-alg.fbase x₁
    w   = FoldDef-alg.fold-reindex {Q = R''} γ₂ FoldDef-alg.fbase x₂
    cmb' : Γ .idx .Carrier → Reindex-ext.IMorD (λ v → inj₁ v) (λ v → inj₁ v)
    cmb' γ = Reindex-ext.ibase (λ { Fin.zero a → a ; (Fin.suc i) a → Reindex-sₛ.iapply (imor γ) i a })
                       (λ { Fin.zero p → p ; (Fin.suc i) p → Reindex-sₛ.iapply-resp (imor γ) i p })
    rec : _≈s_ (μ-fam R'' (extend sₜ (μ-fam Q sₜ)) .idx)
               (Reindex-ext.ireindex (cmb' γ₁) wm₁)
               (strong-fmor (μ R'') (strong-extend-mor mors Fam-P.p₂) .idxf .func (γ₂ , w))
    rec = fuse-idx R'' cmb' (strong-extend-mor mors Fam-P.p₂)
            (λ { Fin.zero γ≈ a≈ → a≈ ; (Fin.suc j) γ≈ a≈ → agree j γ≈ a≈ })
            γ≈ {m₁ = wm₁} {m₂ = w}  (FoldDef-alg.fold-reindex-resp {Q = R''} γ≈ FoldDef-alg.fbase {x₁} {x₂} x≈)
    mutual
      data TeleRel : ∀ {j} {ηA ηB ηC ηD}
                     {dA : ∀ v → T-sₛ.DecoAssign (ηA v)} {dB : ∀ v → T-sₜ.DecoAssign (ηB v)}
                     {dC : ∀ v → InMapDef-P.T-δ'.DecoAssign (ηC v)} {dD : ∀ v → FoldDef-alg.T-δA-ext.DecoAssign (ηD v)} →
                     Reindex-sₛ.IMorD {j} ηA ηB → InMapDef-P.MorD {j} ηC ηB dC dB → Reindex-ext.IMorD {j} ηD ηC → FoldDef-alg.FMor {j} ηA ηD dA dD →
                     Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
        tbase : TeleRel (Reindex-sₛ.ibind ∣ Q ∣ (imor γ₁)) InMapDef-P.mor₀ (cmb' γ₁) FoldDef-alg.fbase
        tbind : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD} {md mdA md' fm} (S' : Poly (suc j)) →
                TeleRel {j} {ηA} {ηB} {ηC} {ηD} {dA} {dB} {dC} {dD} md mdA md' fm →
                TeleRel (Reindex-sₛ.ibind ∣ S' ∣ md) (InMapDef-P.bind S' mdA) (Reindex-ext.ibind ∣ S' ∣ md') (FoldDef-alg.fbind S' fm)

      tele-shape : ∀ {j} (S : Poly j) {ηA ηB ηC ηD} {dA dB dC dD}
                   {md : Reindex-sₛ.IMorD ηA ηB} {mdA : InMapDef-P.MorD ηC ηB dC dB} {md' : Reindex-ext.IMorD ηD ηC} {fm : FoldDef-alg.FMor ηA ηD dA dD}
                   (rel : TeleRel md mdA md' fm) (z : FoldDef-alg.T-δ.⟦ ∣ S ∣ ⟧shape ηA) →
                   T-sₜ.shape≈ ∣ S ∣ ηB
                     (Reindex-sₛ.ireindex-shape ∣ S ∣ md z)
                     (InMapDef-P.reindex-shape ∣ S ∣ mdA (Reindex-ext.ireindex-shape ∣ S ∣ md' (FoldDef-alg.fold-reindex-shape γ₁ S fm z)))
      tele-shape (const A') rel z = A' .idx .isEquivalence .refl
      tele-shape (var v) rel z = tele-apply rel v
      tele-shape (S₁ + S₂) rel (inj₁ z) = tele-shape S₁ rel z
      tele-shape (S₁ + S₂) rel (inj₂ z) = tele-shape S₂ rel z
      tele-shape (S₁ × S₂) rel (z₁ , z₂) = tele-shape S₁ rel z₁ , tele-shape S₂ rel z₂
      tele-shape (μ S') rel (T-sₛ.sup z') = tele-shape S' (tbind S' rel) z'

      tele-apply : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD}
                   {md : Reindex-sₛ.IMorD ηA ηB} {mdA : InMapDef-P.MorD ηC ηB dC dB} {md' : Reindex-ext.IMorD ηD ηC} {fm : FoldDef-alg.FMor ηA ηD dA dD}
                   (rel : TeleRel md mdA md' fm) (v : Fin j) {z} →
                   T-sₜ.elEq (ηB v) (Reindex-sₛ.iapply md v z) (InMapDef-P.apply mdA v (Reindex-ext.iapply md' v (FoldDef-alg.fold-apply γ₁ fm v z)))
      tele-apply (tbind S' r) Fin.zero    {z} = tele-shape (μ S') r z
      tele-apply (tbind S' r) (Fin.suc v)     = tele-apply r v
      tele-apply tbase Fin.zero    {z} =
        fuse-idx Q imor mors agree (Γ .idx .isEquivalence .refl {γ₁}) {m₁ = z} {m₂ = z}
          (μ-fam Q sₛ .idx .isEquivalence .refl {z})
      tele-apply tbase (Fin.suc i) {z} = T-sₜ.elEq-refl (inj₁ i) (Reindex-sₛ.iapply (imor γ₁) i z)

    telescope : T-sₜ.W-≈ (Reindex-sₛ.ireindex-shape ∣ μ R'' ∣ (Reindex-sₛ.ibind ∣ Q ∣ (imor γ₁)) x₁)
                       (InMapDef-P.reindex InMapDef-P.mor₀ (Reindex-ext.ireindex (cmb' γ₁) wm₁))
    telescope = tele-shape (μ R'') tbase x₁

strong-prod-m-transf : ∀ {Γ X₁ X₂ Y₁ Y₂ : Obj} (f : Mor (Fam-P.prod Γ X₁) Y₁) (g : Mor (Fam-P.prod Γ X₂) Y₂)
                       {γ x₁ x₂} →
                       Fam-P.strong-prod-m f g .famf .transf (γ , (x₁ , x₂))
                         ≈ strong-prod-m (f .famf .transf (γ , x₁)) (g .famf .transf (γ , x₂))
strong-prod-m-transf f g =
  pair-cong (≈-trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left)))
            (≈-trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left)))

fuse-fam : ∀ {n} {Γ : Obj} (γ : Γ .idx .Carrier) {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
               let module Reindex-sₛ = Reindex sₛ sₜ
                   module FReindex-γ = FReindex {δA = sₛ} {δB = sₜ} (Γ .fam .fm γ) in
               (imor : Γ .idx .Carrier → Reindex-sₛ.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
               (act : FReindex-γ.FAct (imor γ) (λ v → lift tt) (λ v → lift tt))
               (mors : ∀ i → Mor (Fam-P.prod Γ (sₛ i)) (sₜ i))
               (agree : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                       _≈s_ (sₜ i .idx) (Reindex-sₛ.iapply (imor γ₁) i a₁) (mors i .idxf .func (γ₂ , a₂)))
               (corr-fam : ∀ i {a} →
                  _≈_
                    (sₜ i .fam .subst (agree i (Γ .idx .isEquivalence .refl) (sₛ i .idx .isEquivalence .refl {a}))
                     ∘ FReindex-γ.aapply act i a)
                    (mors i .famf .transf (γ , a))) →
               ∀ {m} →
               _≈_
                 (μ-fam Q sₜ .fam .subst {x = Reindex-sₛ.ireindex (imor γ) m}
                    (fuse-idx Q imor mors agree (Γ .idx .isEquivalence .refl)
                      {m} {m} (μ-fam Q sₛ .idx .isEquivalence .refl {m}))
                  ∘ FReindex-γ.freindex-fam act {m})
                 (strong-fmor (μ Q) mors .famf .transf (γ , m))

fuse-shape-fam : ∀ {n} {Γ : Obj} (γ : Γ .idx .Carrier) {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
                     let module Reindex-sₛ = Reindex sₛ sₜ
                         module T-sₛ = Tree sₛ
                         module T-sₜ = Tree sₜ
                         module InMapDef-P = InMapDef Q sₜ
                         module FReindex-γ = FReindex {δA = sₛ} {δB = sₜ} (Γ .fam .fm γ) in
                     (imor : Γ .idx .Carrier → Reindex-sₛ.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
                     (act : FReindex-γ.FAct (imor γ) (λ v → lift tt) (λ v → lift tt))
                     (mors : ∀ i → Mor (Fam-P.prod Γ (sₛ i)) (sₜ i))
                     (agree : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                             _≈s_ (sₜ i .idx) (Reindex-sₛ.iapply (imor γ₁) i a₁) (mors i .idxf .func (γ₂ , a₂)))
                     (corr-fam : ∀ i {a} →
                        _≈_
                          (sₜ i .fam .subst (agree i (Γ .idx .isEquivalence .refl) (sₛ i .idx .isEquivalence .refl {a}))
                           ∘ FReindex-γ.aapply act i a)
                          (mors i .famf .transf (γ , a))) →
                     let module FoldDef-alg = FoldDef {Γ = Γ} {A = μ-fam Q sₜ} {P = Q} {δ = sₛ}
                                       (Fam-cat._∘_ InMapDef-P.inMor (strong-fmor Q (strong-extend-mor mors Fam-P.p₂)))
                         fsk' = strong-extend-mor mors Fam-P.p₂ in
                     (R : Poly (suc n))
                     {x : T-sₛ.⟦ ∣ R ∣ ⟧shape (η₀ ∣ Q ∣)} →
                     _≈_
                       (T-sₜ.fib-shape-subst R (T-sₜ.deco-ext Q (λ i → lift tt))
                          (fuse-shape Q imor mors agree R (Γ .idx .isEquivalence .refl) (T-sₛ.shape≈-refl ∣ R ∣ (η₀ ∣ Q ∣) x))
                        ∘ FReindex-γ.freindex-shape-fam R (FReindex-γ.abind Q (imor γ) act) {x})
                       (InMapDef-P.reindex-fam R InMapDef-P.mor₀
                        ∘ (InMapDef-P.embed-fam R (strong-fmor R fsk' .idxf .func (γ , FoldDef-alg.fold-shape-idx R γ x))
                           ∘ (strong-fmor R fsk' .famf .transf (γ , FoldDef-alg.fold-shape-idx R γ x)
                              ∘ pair p₁ (FoldDef-alg.fold-shape-fam R γ x))))

fuse-fam γ Q imor act mors agree corr-fam {Tree.sup x} =
  ≈-trans (fuse-shape-fam γ Q imor act mors agree corr-fam Q {x})
    (≈-sym (≈-trans (∘-cong id-left ≈-refl) (≈-trans (assoc _ _ _) (assoc _ _ _))))
fuse-shape-fam γ Q imor act mors agree corr-fam (const A') =
  ≈-trans (∘-cong (A' .fam .refl*) ≈-refl)
    (≈-trans id-left (≈-sym (≈-trans id-left (≈-trans id-left (pair-p₂ _ _)))))
fuse-shape-fam γ Q imor act mors agree corr-fam (var Fin.zero) {x} =
  ≈-trans (fuse-fam γ Q imor act mors agree corr-fam {x})
    (≈-sym (≈-trans id-left (≈-trans id-left (pair-p₂ _ _))))
fuse-shape-fam γ Q imor act mors agree corr-fam (var (Fin.suc i)) {x} =
  ≈-trans (corr-fam i)
    (≈-sym (≈-trans id-left (≈-trans id-left (≈-trans (∘-cong ≈-refl pair-ext0) id-right))))
fuse-shape-fam γ Q imor act mors agree corr-fam (R₁ + R₂) {inj₁ a} =
  ≈-trans (strong-Lmap-post _ _)
  (≈-trans (strong-Lmap-cong (fuse-shape-fam γ Q imor act mors agree corr-fam R₁ {a}))
  (≈-sym (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (≈-trans (∘-cong (≈-trans id-left (≈-trans id-left (strong-Lf-map-transf (strong-fmor R₁ (strong-extend-mor mors Fam-P.p₂))))) ≈-refl) (strong-Lmap-co _ _))))
                  (≈-trans (∘-cong ≈-refl (strong-Lmap-post _ _)) (strong-Lmap-post _ _)))))
fuse-shape-fam γ Q imor act mors agree corr-fam (R₁ + R₂) {inj₂ b} =
  ≈-trans (strong-Lmap-post _ _)
  (≈-trans (strong-Lmap-cong (fuse-shape-fam γ Q imor act mors agree corr-fam R₂ {b}))
  (≈-sym (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (≈-trans (∘-cong (≈-trans id-left (≈-trans id-left (strong-Lf-map-transf (strong-fmor R₂ (strong-extend-mor mors Fam-P.p₂))))) ≈-refl) (strong-Lmap-co _ _))))
                  (≈-trans (∘-cong ≈-refl (strong-Lmap-post _ _)) (strong-Lmap-post _ _)))))
fuse-shape-fam {Γ = Γ} γ {sₛ = sₛ} {sₜ = sₜ} Q imor act mors agree corr-fam (R₁ × R₂) {a , b} =
  ≈-trans (strong-Lmap-post _ _)
  (≈-trans (strong-Lmap-cong
             (≈-trans (strong-prod-m-post _ _ _ _)
             (≈-trans (strong-prod-m-cong (fuse-shape-fam γ Q imor act mors agree corr-fam R₁ {a})
                                          (fuse-shape-fam γ Q imor act mors agree corr-fam R₂ {b}))
             (≈-sym (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (strong-prod-m-comp _ _ _ _)))
                    (≈-trans (∘-cong ≈-refl (strong-prod-m-post _ _ _ _)) (strong-prod-m-post _ _ _ _)))))))
  (≈-sym (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (≈-trans (∘-cong (≈-trans (strong-Lf-map-transf (Fam-P.strong-prod-m (strong-fmor R₁ fsk') (strong-fmor R₂ fsk')))
                                                                          (strong-Lmap-cong
                                                                            (strong-prod-m-transf (strong-fmor R₁ fsk') (strong-fmor R₂ fsk')
                                                                               {γ} {FoldDef-alg.fold-shape-idx R₁ γ a} {FoldDef-alg.fold-shape-idx R₂ γ b})))
                                                                 ≈-refl)
                                                         (strong-Lmap-co _ _))))
                  (≈-trans (∘-cong ≈-refl (strong-Lmap-post _ _)) (strong-Lmap-post _ _)))))
  where
    module InMapDef-P = InMapDef Q sₜ
    fsk' = strong-extend-mor mors Fam-P.p₂
    module FoldDef-alg = FoldDef {Γ = Γ} {A = μ-fam Q sₜ} {P = Q} {δ = sₛ}
                  (Fam-cat._∘_ InMapDef-P.inMor (strong-fmor Q fsk'))
fuse-shape-fam {Γ = Γ} γ {sₛ = sₛ} {sₜ = sₜ} Q imor act mors agree corr-fam (μ R'') {x} =
  ≈-trans (∘-cong (T-sₜ.fib-trans* R'' (T-sₜ.deco-ext Q (λ i → lift tt))
                     {x = Reindex-sₛ.ireindex-shape ∣ μ R'' ∣ (Reindex-sₛ.ibind ∣ Q ∣ (imor γ)) x}
                     {y = InMapDef-P.reindex InMapDef-P.mor₀ (Reindex-ext.ireindex (cmb' γ) wm₁)}
                     {z = InMapDef-P.reindex InMapDef-P.mor₀ (strong-fmor (μ R'') fsk' .idxf .func (γ , wm₁))}
                     (InMapDef-P.reindex-resp InMapDef-P.mor₀
                        {t = Reindex-ext.ireindex (cmb' γ) wm₁}
                        {t' = strong-fmor (μ R'') fsk' .idxf .func (γ , wm₁)}
                        rec-idx)
                     (tele-shape (μ R'') tbase x)) ≈-refl)
    (≈-trans (tail-cong (tele-shape-fam (μ R'') tbase x))
     (≈-trans (head-cong (≈-sym (InMapDef-P.reindex-fam-W-natural {Q = R''} InMapDef-P.mor₀
                                   {t = Reindex-ext.ireindex (cmb' γ) wm₁}
                                   {t' = strong-fmor (μ R'') fsk' .idxf .func (γ , wm₁)}
                                   rec-idx)))
              (tail-cong (≈-trans (head-cong rec-fam) (≈-sym id-left)))))
  where
    module T-sₜ = Tree sₜ
    module T-sₛ = Tree sₛ
    module InMapDef-P = InMapDef Q sₜ
    module Reindex-sₛ = Reindex sₛ sₜ
    module Reindex-ext = Reindex (extend sₛ (μ-fam Q sₜ)) (extend sₜ (μ-fam Q sₜ))
    module FReindex-γ = FReindex {δA = sₛ} {δB = sₜ} (Γ .fam .fm γ)
    module FR' = FReindex {δA = extend sₛ (μ-fam Q sₜ)} {δB = extend sₜ (μ-fam Q sₜ)} (Γ .fam .fm γ)
    module FoldDef-alg = FoldDef {Γ = Γ} {A = μ-fam Q sₜ} {P = Q} {δ = sₛ}
                  (Fam-cat._∘_ InMapDef-P.inMor (strong-fmor Q (strong-extend-mor mors Fam-P.p₂)))
    fsk' = strong-extend-mor mors Fam-P.p₂
    wm₁ = FoldDef-alg.fold-reindex {Q = R''} γ FoldDef-alg.fbase x
    cmb' : Γ .idx .Carrier → Reindex-ext.IMorD (λ v → inj₁ v) (λ v → inj₁ v)
    cmb' γ' = Reindex-ext.ibase (λ { Fin.zero a → a ; (Fin.suc i) a → Reindex-sₛ.iapply (imor γ') i a })
                        (λ { Fin.zero p → p ; (Fin.suc i) p → Reindex-sₛ.iapply-resp (imor γ') i p })
    act' : FR'.FAct (cmb' γ) (λ v → lift tt) (λ v → lift tt)
    act' = FR'.abase (λ { Fin.zero a → p₂ ; (Fin.suc i) a → FReindex-γ.aapply act i a })
    corr' : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (extend sₛ (μ-fam Q sₜ) i .idx) a₁ a₂) →
            _≈s_ (extend sₜ (μ-fam Q sₜ) i .idx) (Reindex-ext.iapply (cmb' γ₁) i a₁) (fsk' i .idxf .func (γ₂ , a₂))
    corr' Fin.zero    γ≈ a≈ = a≈
    corr' (Fin.suc j) γ≈ a≈ = agree j γ≈ a≈
    corr-fam' : ∀ i {a} → _≈_
                  (extend sₜ (μ-fam Q sₜ) i .fam .subst
                     (corr' i (Γ .idx .isEquivalence .refl) (extend sₛ (μ-fam Q sₜ) i .idx .isEquivalence .refl {a}))
                   ∘ FR'.aapply act' i a)
                  (fsk' i .famf .transf (γ , a))
    corr-fam' Fin.zero {a} = ≈-trans (∘-cong (μ-fam Q sₜ .fam .refl* {a}) ≈-refl) id-left
    corr-fam' (Fin.suc j) = corr-fam j
    rec-fam : _≈_
                (μ-fam R'' (extend sₜ (μ-fam Q sₜ)) .fam .subst {x = Reindex-ext.ireindex (cmb' γ) wm₁}
                   (fuse-idx R'' cmb' fsk' corr' (Γ .idx .isEquivalence .refl)
                     {wm₁} {wm₁} (μ-fam R'' (extend sₛ (μ-fam Q sₜ)) .idx .isEquivalence .refl {wm₁}))
                 ∘ FR'.freindex-fam act' {wm₁})
                (strong-fmor (μ R'') fsk' .famf .transf (γ , wm₁))
    rec-fam = fuse-fam γ R'' cmb' act' fsk' corr' corr-fam' {wm₁}
    rec-idx = fuse-idx R'' cmb' fsk' corr' (Γ .idx .isEquivalence .refl)
                {wm₁} {wm₁} (μ-fam R'' (extend sₛ (μ-fam Q sₜ)) .idx .isEquivalence .refl {wm₁})
    mutual
      data TeleRel : ∀ {j} {ηA ηB ηC ηD}
                     {dA : ∀ v → T-sₛ.DecoAssign (ηA v)} {dB : ∀ v → T-sₜ.DecoAssign (ηB v)}
                     {dC : ∀ v → InMapDef-P.T-δ'.DecoAssign (ηC v)} {dD : ∀ v → FoldDef-alg.T-δA-ext.DecoAssign (ηD v)}
                     (md : Reindex-sₛ.IMorD {j} ηA ηB) (mdA : InMapDef-P.MorD {j} ηC ηB dC dB) (md' : Reindex-ext.IMorD {j} ηD ηC) (fm : FoldDef-alg.FMor {j} ηA ηD dA dD) →
                     FReindex-γ.FAct md dA dB → FR'.FAct md' dD dC → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
        tbase : TeleRel (Reindex-sₛ.ibind ∣ Q ∣ (imor γ)) InMapDef-P.mor₀ (cmb' γ) FoldDef-alg.fbase (FReindex-γ.abind Q (imor γ) act) act'
        tbind : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD} {md : Reindex-sₛ.IMorD ηA ηB} {mdA : InMapDef-P.MorD ηC ηB dC dB} {md' : Reindex-ext.IMorD ηD ηC} {fm : FoldDef-alg.FMor ηA ηD dA dD}
                {am : FReindex-γ.FAct md dA dB} {am' : FR'.FAct md' dD dC} (S' : Poly (suc j)) →
                TeleRel md mdA md' fm am am' →
                TeleRel (Reindex-sₛ.ibind ∣ S' ∣ md) (InMapDef-P.bind S' mdA) (Reindex-ext.ibind ∣ S' ∣ md') (FoldDef-alg.fbind S' fm)
                        (FReindex-γ.abind S' md am) (FR'.abind S' md' am')

      tele-shape : ∀ {j} (S : Poly j) {ηA ηB ηC ηD} {dA dB dC dD}
                   {md : Reindex-sₛ.IMorD ηA ηB} {mdA : InMapDef-P.MorD ηC ηB dC dB} {md' : Reindex-ext.IMorD ηD ηC} {fm : FoldDef-alg.FMor ηA ηD dA dD}
                   {am : FReindex-γ.FAct md dA dB} {am' : FR'.FAct md' dD dC}
                   (rel : TeleRel md mdA md' fm am am') (z : FoldDef-alg.T-δ.⟦ ∣ S ∣ ⟧shape ηA) →
                   T-sₜ.shape≈ ∣ S ∣ ηB
                     (Reindex-sₛ.ireindex-shape ∣ S ∣ md z)
                     (InMapDef-P.reindex-shape ∣ S ∣ mdA (Reindex-ext.ireindex-shape ∣ S ∣ md' (FoldDef-alg.fold-reindex-shape γ S fm z)))
      tele-shape (const A') rel z = A' .idx .isEquivalence .refl
      tele-shape (var v) rel z = tele-apply rel v
      tele-shape (S₁ + S₂) rel (inj₁ z) = tele-shape S₁ rel z
      tele-shape (S₁ + S₂) rel (inj₂ z) = tele-shape S₂ rel z
      tele-shape (S₁ × S₂) rel (z₁ , z₂) = tele-shape S₁ rel z₁ , tele-shape S₂ rel z₂
      tele-shape (μ S') rel (T-sₛ.sup z') = tele-shape S' (tbind S' rel) z'

      tele-apply : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD}
                   {md : Reindex-sₛ.IMorD ηA ηB} {mdA : InMapDef-P.MorD ηC ηB dC dB} {md' : Reindex-ext.IMorD ηD ηC} {fm : FoldDef-alg.FMor ηA ηD dA dD}
                   {am : FReindex-γ.FAct md dA dB} {am' : FR'.FAct md' dD dC}
                   (rel : TeleRel md mdA md' fm am am') (v : Fin j) {z} →
                   T-sₜ.elEq (ηB v) (Reindex-sₛ.iapply md v z) (InMapDef-P.apply mdA v (Reindex-ext.iapply md' v (FoldDef-alg.fold-apply γ fm v z)))
      tele-apply (tbind S' r) Fin.zero    {z} = tele-shape (μ S') r z
      tele-apply (tbind S' r) (Fin.suc v)     = tele-apply r v
      tele-apply tbase Fin.zero    {z} =
        fuse-idx Q imor mors agree (Γ .idx .isEquivalence .refl {γ}) {m₁ = z} {m₂ = z}
          (μ-fam Q sₛ .idx .isEquivalence .refl {z})
      tele-apply tbase (Fin.suc i) {z} = T-sₜ.elEq-refl (inj₁ i) (Reindex-sₛ.iapply (imor γ) i z)

      tele-shape-fam : ∀ {j} (S : Poly j) {ηA ηB ηC ηD} {dA dB dC dD}
                       {md : Reindex-sₛ.IMorD ηA ηB} {mdA : InMapDef-P.MorD ηC ηB dC dB} {md' : Reindex-ext.IMorD ηD ηC} {fm : FoldDef-alg.FMor ηA ηD dA dD}
                       {am : FReindex-γ.FAct md dA dB} {am' : FR'.FAct md' dD dC}
                       (rel : TeleRel md mdA md' fm am am') (z : FoldDef-alg.T-δ.⟦ ∣ S ∣ ⟧shape ηA) →
                       (T-sₜ.fib-shape-subst S dB (tele-shape S rel z) ∘ FReindex-γ.freindex-shape-fam S am {z})
                       ≈ (InMapDef-P.reindex-fam S mdA
                          ∘ (FR'.freindex-shape-fam S am' {FoldDef-alg.fold-reindex-shape γ S fm z}
                             ∘ pair p₁ (FoldDef-alg.fold-reindex-shape-fam γ S fm z)))
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
      tele-shape-fam (μ S') rel (T-sₛ.sup z') = tele-shape-fam S' (tbind S' rel) z'

      tele-apply-fam : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD}
                       {md : Reindex-sₛ.IMorD ηA ηB} {mdA : InMapDef-P.MorD ηC ηB dC dB} {md' : Reindex-ext.IMorD ηD ηC} {fm : FoldDef-alg.FMor ηA ηD dA dD}
                       {am : FReindex-γ.FAct md dA dB} {am' : FR'.FAct md' dD dC}
                       (rel : TeleRel md mdA md' fm am am') (v : Fin j) {z} →
                       (T-sₜ.fib-el-subst (ηB v) (dB v) (tele-apply rel v {z}) ∘ FReindex-γ.aapply am v z)
                       ≈ (InMapDef-P.apply-fam mdA v (Reindex-ext.iapply md' v (FoldDef-alg.fold-apply γ fm v z))
                          ∘ (FR'.aapply am' v (FoldDef-alg.fold-apply γ fm v z)
                             ∘ pair p₁ (FoldDef-alg.fold-apply-fam γ fm v z)))
      tele-apply-fam (tbind S' r) Fin.zero    {z} = tele-shape-fam (μ S') r z
      tele-apply-fam (tbind S' r) (Fin.suc v)     = tele-apply-fam r v
      tele-apply-fam tbase Fin.zero    {z} =
        ≈-trans (fuse-fam γ Q imor act mors agree corr-fam {z}) (≈-sym (≈-trans id-left (pair-p₂ _ _)))
      tele-apply-fam tbase (Fin.suc i) {z} =
        ≈-trans (∘-cong (sₜ i .fam .refl*) ≈-refl)
          (≈-trans id-left (≈-sym (≈-trans id-left (≈-trans (∘-cong ≈-refl pair-ext0) id-right))))

-- The algebra map is an isomorphism. The bridge reindexing has an inverse with identity fibre maps,
-- and the two composites are the identity on trees and on fibres, the relation pairing each
-- extension of the inverse with the extension it undoes.

module LambekDef {n} (P : Poly (suc n)) (δ : Fin n → Obj) where
  private module InMapDef-P = InMapDef P δ
  open InMapDef-P using (module T-δ'; module Reindex-δ'; mor₀; m₀; embed-idx; unembed-idx)
  private
    module T-δ = Tree δ
    module Reindex-μ = Reindex δ (extend δ (μ-fam P δ))
    open Reindex-μ using (MorD; base; bind; apply; apply-fam; reindex; reindex-shape; reindex-shape-resp; reindex-fam; reindex-fam-natural; reindex-fam-W)

  m₀⁻ : ∀ v → T-δ.El (η₀ ∣ P ∣ v) → T-δ'.El (inj₁ v)
  m₀⁻ Fin.zero    a = a
  m₀⁻ (Fin.suc i) a = a

  m₀⁻-resp : ∀ v {a a'} → T-δ.elEq (η₀ ∣ P ∣ v) a a' → T-δ'.elEq (inj₁ v) (m₀⁻ v a) (m₀⁻ v a')
  m₀⁻-resp Fin.zero    p = p
  m₀⁻-resp (Fin.suc i) p = p

  m₀⁻-fam : ∀ v (a : T-δ.El (η₀ ∣ P ∣ v)) →
            T-δ.fib-el (η₀ ∣ P ∣ v) (T-δ.deco-ext P (λ i → lift tt) v) a
              ⇒ T-δ'.fib-el (inj₁ v) (lift tt) (m₀⁻ v a)
  m₀⁻-fam Fin.zero    a = id _
  m₀⁻-fam (Fin.suc i) a = id _

  m₀⁻-fam-natural : ∀ v {a a'} (p : T-δ.elEq (η₀ ∣ P ∣ v) a a') →
                    (m₀⁻-fam v a' ∘ T-δ.fib-el-subst (η₀ ∣ P ∣ v) (T-δ.deco-ext P (λ i → lift tt) v) p)
                      ≈ (T-δ'.fib-el-subst (inj₁ v) (lift tt) (m₀⁻-resp v p) ∘ m₀⁻-fam v a)
  m₀⁻-fam-natural Fin.zero    p = ≈-trans id-left (≈-sym id-right)
  m₀⁻-fam-natural (Fin.suc i) p = ≈-trans id-left (≈-sym id-right)

  mor₀⁻ : MorD (η₀ ∣ P ∣) (λ v → inj₁ v) (T-δ.deco-ext P (λ i → lift tt)) (λ v → lift tt)
  mor₀⁻ = base m₀⁻ m₀⁻-resp m₀⁻-fam m₀⁻-fam-natural

  data DRel : ∀ {j} {ρ : Fin j → Fin n ⊎ Sort n} {ρ' : Fin j → Fin (suc n) ⊎ Sort (suc n)}
              {d : ∀ v → T-δ.DecoAssign (ρ v)} {d' : ∀ v → T-δ'.DecoAssign (ρ' v)} →
              MorD ρ ρ' d d' → Reindex-δ'.MorD ρ' ρ d' d →
              Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    dbase : DRel mor₀⁻ mor₀
    dbind : ∀ {j} {ρ ρ' d d'} {md' : MorD {j} ρ ρ' d d'} {md} (Q' : Poly (suc j)) →
            DRel md' md → DRel (bind Q' md') (Reindex-δ'.bind Q' md)

  mutual
    drt-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {md' : MorD ρ ρ' d d'} {md} → DRel md' md →
            (t : T-δ.W ∣ Q̂ ∣ ρ) → T-δ.W-≈ (Reindex-δ'.reindex md (reindex md' t)) t
    drt-W {Q̂ = Q̂} rel (T-δ.sup x) = drt-shape Q̂ (dbind Q̂ rel) x

    drt-shape : ∀ {j} (S : Poly j) {ρ ρ' d d'} {md' : MorD ρ ρ' d d'} {md} → DRel md' md →
                (a : T-δ.⟦ ∣ S ∣ ⟧shape ρ) →
                T-δ.shape≈ ∣ S ∣ ρ (Reindex-δ'.reindex-shape ∣ S ∣ md (reindex-shape ∣ S ∣ md' a)) a
    drt-shape (const A') rel a = A' .idx .isEquivalence .refl
    drt-shape (var v)    rel a = drt-el rel v a
    drt-shape (P' + Q') rel (inj₁ a) = drt-shape P' rel a
    drt-shape (P' + Q') rel (inj₂ b) = drt-shape Q' rel b
    drt-shape (P' × Q') rel (a , b) = drt-shape P' rel a , drt-shape Q' rel b
    drt-shape (μ Q'')   rel t = drt-W {Q̂ = Q''} rel t

    drt-el : ∀ {j} {ρ ρ' d d'} {md' : MorD {j} ρ ρ' d d'} {md} → DRel md' md →
             (v : Fin j) (a : T-δ.El (ρ v)) →
             T-δ.elEq (ρ v) (Reindex-δ'.apply md v (apply md' v a)) a
    drt-el dbase          Fin.zero    t = T-δ.elEq-refl (η₀ ∣ P ∣ Fin.zero) t
    drt-el dbase          (Fin.suc i) a = T-δ.elEq-refl (η₀ ∣ P ∣ (Fin.suc i)) a
    drt-el (dbind Q' rel) Fin.zero    a = drt-W {Q̂ = Q'} rel a
    drt-el (dbind Q' rel) (Fin.suc v) a = drt-el rel v a

  mutual
    drt'-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {md' : MorD ρ ρ' d d'} {md} → DRel md' md →
             (u : T-δ'.W ∣ Q̂ ∣ ρ') → T-δ'.W-≈ (reindex md' (Reindex-δ'.reindex md u)) u
    drt'-W {Q̂ = Q̂} rel (T-δ'.sup x) = drt'-shape Q̂ (dbind Q̂ rel) x

    drt'-shape : ∀ {j} (S : Poly j) {ρ ρ' d d'} {md' : MorD ρ ρ' d d'} {md} → DRel md' md →
                 (a : T-δ'.⟦ ∣ S ∣ ⟧shape ρ') →
                 T-δ'.shape≈ ∣ S ∣ ρ' (reindex-shape ∣ S ∣ md' (Reindex-δ'.reindex-shape ∣ S ∣ md a)) a
    drt'-shape (const A') rel a = A' .idx .isEquivalence .refl
    drt'-shape (var v)    rel a = drt'-el rel v a
    drt'-shape (P' + Q') rel (inj₁ a) = drt'-shape P' rel a
    drt'-shape (P' + Q') rel (inj₂ b) = drt'-shape Q' rel b
    drt'-shape (P' × Q') rel (a , b) = drt'-shape P' rel a , drt'-shape Q' rel b
    drt'-shape (μ Q'')   rel t = drt'-W {Q̂ = Q''} rel t

    drt'-el : ∀ {j} {ρ ρ' d d'} {md' : MorD {j} ρ ρ' d d'} {md} → DRel md' md →
              (v : Fin j) (a : T-δ'.El (ρ' v)) →
              T-δ'.elEq (ρ' v) (apply md' v (Reindex-δ'.apply md v a)) a
    drt'-el dbase          Fin.zero    t = T-δ'.elEq-refl (inj₁ Fin.zero) t
    drt'-el dbase          (Fin.suc i) a = T-δ'.elEq-refl (inj₁ (Fin.suc i)) a
    drt'-el (dbind Q' rel) Fin.zero    a = drt'-W {Q̂ = Q'} rel a
    drt'-el (dbind Q' rel) (Fin.suc v) a = drt'-el rel v a

  mutual
    drt-fam-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {md' : MorD ρ ρ' d d'} {md}
                (rel : DRel md' md) (t : T-δ.W ∣ Q̂ ∣ ρ) →
                (T-δ.fib-subst Q̂ d {x = Reindex-δ'.reindex md (reindex md' t)} {y = t} (drt-W rel t)
                  ∘ (Reindex-δ'.reindex-fam-W md {t = reindex md' t} ∘ reindex-fam-W md' {t = t}))
                  ≈ id (T-δ.fib Q̂ d t)
    drt-fam-W {Q̂ = Q̂} rel (T-δ.sup x) = drt-shape-fam Q̂ (dbind Q̂ rel) x

    drt-shape-fam : ∀ {j} (S : Poly j) {ρ ρ' d d'} {md' : MorD ρ ρ' d d'} {md}
                    (rel : DRel md' md) (a : T-δ.⟦ ∣ S ∣ ⟧shape ρ) →
                    (T-δ.fib-shape-subst S d (drt-shape S rel a)
                      ∘ (Reindex-δ'.reindex-fam S md {a = reindex-shape ∣ S ∣ md' a} ∘ reindex-fam S md' {a = a}))
                      ≈ id (T-δ.fib-shape S d a)
    drt-shape-fam (const A') rel a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) (≈-trans id-left id-left)
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

    drt-el-fam : ∀ {j} {ρ ρ' d d'} {md' : MorD {j} ρ ρ' d d'} {md}
                 (rel : DRel md' md) (v : Fin j) (a : T-δ.El (ρ v)) →
                 (T-δ.fib-el-subst (ρ v) (d v) (drt-el rel v a)
                   ∘ (Reindex-δ'.apply-fam md v (apply md' v a) ∘ apply-fam md' v a))
                   ≈ id (T-δ.fib-el (ρ v) (d v) a)
    drt-el-fam dbase Fin.zero t =
      ≈-trans (∘-cong (T-δ.fib-el-refl* (η₀ ∣ P ∣ Fin.zero) (T-δ.deco-ext P (λ i → lift tt) Fin.zero) t)
                      ≈-refl)
              (≈-trans id-left id-left)
    drt-el-fam dbase (Fin.suc i) a =
      ≈-trans (∘-cong (T-δ.fib-el-refl* (η₀ ∣ P ∣ (Fin.suc i))
                                       (T-δ.deco-ext P {ρ̄ = λ v → inj₁ v} (λ _ → lift tt) (Fin.suc i)) a)
                      ≈-refl)
              (≈-trans id-left id-left)
    drt-el-fam (dbind Q' rel) Fin.zero    a = drt-fam-W {Q̂ = Q'} rel a
    drt-el-fam (dbind Q' rel) (Fin.suc v) a = drt-el-fam rel v a

  mutual
    drt'-fam-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {md' : MorD ρ ρ' d d'} {md}
                 (rel : DRel md' md) (u : T-δ'.W ∣ Q̂ ∣ ρ') →
                 (T-δ'.fib-subst Q̂ d' {x = reindex md' (Reindex-δ'.reindex md u)} {y = u} (drt'-W rel u)
                   ∘ (reindex-fam-W md' {t = Reindex-δ'.reindex md u} ∘ Reindex-δ'.reindex-fam-W md {t = u}))
                   ≈ id (T-δ'.fib Q̂ d' u)
    drt'-fam-W {Q̂ = Q̂} rel (T-δ'.sup x) = drt'-shape-fam Q̂ (dbind Q̂ rel) x

    drt'-shape-fam : ∀ {j} (S : Poly j) {ρ ρ' d d'} {md' : MorD ρ ρ' d d'} {md}
                     (rel : DRel md' md) (a : T-δ'.⟦ ∣ S ∣ ⟧shape ρ') →
                     (T-δ'.fib-shape-subst S d' (drt'-shape S rel a)
                       ∘ (reindex-fam S md' {a = Reindex-δ'.reindex-shape ∣ S ∣ md a} ∘ Reindex-δ'.reindex-fam S md {a = a}))
                       ≈ id (T-δ'.fib-shape S d' a)
    drt'-shape-fam (const A') rel a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) (≈-trans id-left id-left)
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

    drt'-el-fam : ∀ {j} {ρ ρ' d d'} {md' : MorD {j} ρ ρ' d d'} {md}
                  (rel : DRel md' md) (v : Fin j) (a : T-δ'.El (ρ' v)) →
                  (T-δ'.fib-el-subst (ρ' v) (d' v) (drt'-el rel v a)
                    ∘ (apply-fam md' v (Reindex-δ'.apply md v a) ∘ Reindex-δ'.apply-fam md v a))
                    ≈ id (T-δ'.fib-el (ρ' v) (d' v) a)
    drt'-el-fam dbase Fin.zero t =
      ≈-trans (∘-cong (T-δ'.fib-el-refl* (inj₁ Fin.zero) (lift tt) t) ≈-refl) (≈-trans id-left id-left)
    drt'-el-fam dbase (Fin.suc i) a =
      ≈-trans (∘-cong (T-δ'.fib-el-refl* (inj₁ (Fin.suc i)) (lift tt) a) ≈-refl) (≈-trans id-left id-left)
    drt'-el-fam (dbind Q' rel) Fin.zero    a = drt'-fam-W {Q̂ = Q'} rel a
    drt'-el-fam (dbind Q' rel) (Fin.suc v) a = drt'-el-fam rel v a

  u-idx : T-δ.W ∣ P ∣ (λ i → inj₁ i) → fobj μ-fam P InMapDef-P.δ' .idx .Carrier
  u-idx (T-δ.sup x) = unembed-idx P (reindex-shape ∣ P ∣ mor₀⁻ x)

  u-resp : {t t' : T-δ.W ∣ P ∣ (λ i → inj₁ i)} → T-δ.W-≈ t t' →
           _≈s_ (fobj μ-fam P InMapDef-P.δ' .idx) (u-idx t) (u-idx t')
  u-resp {T-δ.sup x} {T-δ.sup y} p = InMapDef-P.unembed-idx-resp P (reindex-shape-resp ∣ P ∣ mor₀⁻ p)

  u-fam : (t : T-δ.W ∣ P ∣ (λ i → inj₁ i)) → μ-fam P δ .fam .fm t ⇒ fobj μ-fam P InMapDef-P.δ' .fam .fm (u-idx t)
  u-fam (T-δ.sup x) = InMapDef-P.unembed-fam P (reindex-shape ∣ P ∣ mor₀⁻ x) ∘ reindex-fam P mor₀⁻ {a = x}

  outMor : Mor (μ-fam P δ) (fobj μ-fam P InMapDef-P.δ')
  outMor .idxf .func = u-idx
  outMor .idxf .func-resp-≈ {t} {t'} = u-resp {t} {t'}
  outMor .famf .transf = u-fam
  outMor .famf .natural {T-δ.sup x} {T-δ.sup y} e =
    ≈-trans (tail-cong (reindex-fam-natural P mor₀⁻ e))
    (head-cong-assoc (InMapDef-P.unembed-fam-natural P (reindex-shape-resp ∣ P ∣ mor₀⁻ e)))

  inMor-outMor : Fam-cat._∘_ InMapDef-P.inMor outMor ≃ Fam-cat.id (μ-fam P δ)
  inMor-outMor .idxf-eq .func-eq {T-δ.sup x} {T-δ.sup y} e =
    T-δ.shape≈-trans ∣ P ∣ (η₀ ∣ P ∣)
      (T-δ.shape≈-trans ∣ P ∣ (η₀ ∣ P ∣)
        (Reindex-δ'.reindex-shape-resp ∣ P ∣ mor₀ (InMapDef-P.embed-unembed P (reindex-shape ∣ P ∣ mor₀⁻ x)))
        (drt-shape P dbase x))
      e
  inMor-outMor .famf-eq .transf-eq {T-δ.sup x} =
    ≈-trans (∘-cong (T-δ.fib-shape-trans* P (T-δ.deco-ext P {ρ̄ = λ v → inj₁ v} (λ _ → lift tt))
                       (drt-shape P dbase x)
                       (Reindex-δ'.reindex-shape-resp ∣ P ∣ mor₀ (InMapDef-P.embed-unembed P z)))
                    id-left)
    (≈-trans (tail-cong step₂) (drt-shape-fam P dbase x))
    where
      z = reindex-shape ∣ P ∣ mor₀⁻ x

      step₃ = head-cong-assoc (≈-sym (Reindex-δ'.reindex-fam-natural P mor₀ (InMapDef-P.embed-unembed P z)))
      step₄ = head-cancel (≈-trans (assoc _ _ _) (InMapDef-P.embed-unembed-fam P z))
      step₂ = ≈-trans (head-cong step₃) (tail-cong step₄)

  outMor-inMor : Fam-cat._∘_ outMor InMapDef-P.inMor ≃ Fam-cat.id (fobj μ-fam P InMapDef-P.δ')
  outMor-inMor .idxf-eq .func-eq {i} {i'} e =
    fobj μ-fam P InMapDef-P.δ' .idx .isEquivalence .trans
      (fobj μ-fam P InMapDef-P.δ' .idx .isEquivalence .trans
        (InMapDef-P.unembed-idx-resp P (drt'-shape P dbase (InMapDef-P.embed-idx P i)))
        (InMapDef-P.unembed-embed P i))
      e
  outMor-inMor .famf-eq .transf-eq {i} =
    ≈-trans (∘-cong (fobj μ-fam P InMapDef-P.δ' .fam .trans*
                       (InMapDef-P.unembed-embed P i)
                       (InMapDef-P.unembed-idx-resp P (drt'-shape P dbase (InMapDef-P.embed-idx P i))))
                    id-left)
    (≈-trans (tail-cong step₂) (InMapDef-P.unembed-embed-fam P i))
    where
      step₃ = head-cong-assoc (≈-sym (InMapDef-P.unembed-fam-natural P (drt'-shape P dbase (InMapDef-P.embed-idx P i))))
      step₄ = head-cancel (≈-trans (assoc _ _ _) (drt'-shape-fam P dbase (InMapDef-P.embed-idx P i)))
      step₂ = ≈-trans (head-cong step₃)
                      (tail-cong step₄)

  module OutMorSection (δc : ∀ i → Section (δ i)) (Pc : PolySection P) where
    private
      μc : Section (μ-fam P δ)
      μc = MuSection.μ-section δ δc P Pc
      module MuSection-δ = MuSection δ δc
      module MuSection-ext = MuSection (extend δ (μ-fam P δ)) (extend-section δc μc)
      module ReindexSection-μ = ReindexSection δc (extend-section δc μc)
      module InMapSection-δc = InMapDef-P.InMapSection δc Pc

    mor₀⁻-sec : ReindexSection-μ.MorDSec mor₀⁻ (MuSection-δ.deco-ext-section P Pc (λ i → lift tt)) (λ v → lift tt)
    mor₀⁻-sec = ReindexSection-μ.base-s h
      where
      h : ∀ v a → (m₀⁻-fam v a ∘ MuSection-δ.fib-el-unit (η₀ ∣ P ∣ v) (T-δ.deco-ext P (λ i → lift tt) v)
                     (MuSection-δ.deco-ext-section P Pc (λ i → lift tt) v) a)
                  ≈ MuSection-ext.fib-el-unit (inj₁ v) (lift tt) (lift tt) (m₀⁻ v a)
      h Fin.zero    a = id-left
      h (Fin.suc i) a = id-left

    preserves-outMor : preserves-section outMor μc (poly-section P Pc (extend-section δc μc))
    preserves-outMor .at (T-δ.sup x) =
      ≈-trans (tail-cong (ReindexSection-μ.reindex-fam-unit P Pc mor₀⁻-sec x))
               (InMapSection-δc.unembed-unit P Pc (reindex-shape ∣ P ∣ mor₀⁻ x))

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

module ApplyDef {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (h : Mor (Fam-P.prod Γ (μ-fam P δ)) A) where
    open FoldBase {n} {Γ} {A} {P} {δ}

    h-idx : Γ .idx .Carrier → T-δ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier
    h-idx γ t = h .idxf .func (γ , t)

    h-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : T-δ.W-≈ t t') →
             _≈s_ (A .idx) (h-idx γ t) (h-idx γ' t')
    h-resp γ≈ p = h .idxf .func-resp-≈ (γ≈ , p)

    h-fam : ∀ γ t → prod (Γ .fam .fm γ) (T-δ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (h-idx γ t)
    h-fam γ t = h .famf .transf (γ , t)

    mutual
      apply-shape-idx : (Q : Poly (suc n)) → Γ .idx .Carrier → T-δ.⟦ ∣ Q ∣ ⟧shape (η₀ ∣ P ∣) →
                      fobj μ-fam Q (extend δ A) .idx .Carrier
      apply-shape-idx (const A')        γ a = a
      apply-shape-idx (var Fin.zero)    γ t = h-idx γ t
      apply-shape-idx (var (Fin.suc i)) γ a = a
      apply-shape-idx (Q₁ + Q₂) γ (inj₁ x) = inj₁ (apply-shape-idx Q₁ γ x)
      apply-shape-idx (Q₁ + Q₂) γ (inj₂ y) = inj₂ (apply-shape-idx Q₂ γ y)
      apply-shape-idx (Q₁ × Q₂) γ (x , y) = apply-shape-idx Q₁ γ x , apply-shape-idx Q₂ γ y
      apply-shape-idx (μ Q')    γ t = apply-reindex {Q = Q'} γ fbase t

      apply-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') →
                     T-δ.W ∣ Q ∣ ρ → T-δA-ext.W ∣ Q ∣ ρ'
      apply-reindex {Q = Q} γ fm (T-δ.sup x) = T-δA-ext.sup (apply-reindex-shape γ Q (fbind Q fm) x)

      apply-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB) →
                           T-δ.⟦ ∣ R ∣ ⟧shape ηA → T-δA-ext.⟦ ∣ R ∣ ⟧shape ηB
      apply-reindex-shape γ (const A') fm a = a
      apply-reindex-shape γ (var v)    fm a = apply-apply γ fm v a
      apply-reindex-shape γ (P' + Q') fm (inj₁ a) = inj₁ (apply-reindex-shape γ P' fm a)
      apply-reindex-shape γ (P' + Q') fm (inj₂ b) = inj₂ (apply-reindex-shape γ Q' fm b)
      apply-reindex-shape γ (P' × Q') fm (a , b) = apply-reindex-shape γ P' fm a , apply-reindex-shape γ Q' fm b
      apply-reindex-shape γ (μ Q'')   fm t = apply-reindex {Q = Q''} γ fm t

      apply-apply : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k) →
                   T-δ.El (ρ v) → T-δA-ext.El (ρ' v)
      apply-apply γ fbase        Fin.zero    t = h-idx γ t
      apply-apply γ fbase        (Fin.suc i) a = a
      apply-apply γ (fbind Q fm) Fin.zero    a = apply-reindex {Q = Q} γ fm a
      apply-apply γ (fbind Q fm) (Fin.suc v) a = apply-apply γ fm v a

    mutual
      apply-shape-idx-resp : (Q : Poly (suc n)) → ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {x x'}
                           (p : T-δ.shape≈ ∣ Q ∣ (η₀ ∣ P ∣) x x') →
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
                          {t t' : T-δ.W ∣ Q ∣ ρ} (p : T-δ.W-≈ t t') →
                          T-δA-ext.W-≈ (apply-reindex γ fm t) (apply-reindex γ' fm t')
      apply-reindex-resp {Q = Q} γ≈ fm {T-δ.sup x} {T-δ.sup y} p = apply-reindex-shape-resp γ≈ Q (fbind Q fm) {x} {y} p

      apply-reindex-shape-resp : ∀ {j} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB)
                                {a a' : T-δ.⟦ ∣ R ∣ ⟧shape ηA} (p : T-δ.shape≈ ∣ R ∣ ηA a a') →
                                T-δA-ext.shape≈ ∣ R ∣ ηB (apply-reindex-shape γ R fm a) (apply-reindex-shape γ' R fm a')
      apply-reindex-shape-resp γ≈ (const A') fm p = p
      apply-reindex-shape-resp γ≈ (var v)    fm p = apply-apply-resp γ≈ fm v p
      apply-reindex-shape-resp γ≈ (P' + Q') fm {inj₁ _} {inj₁ _} p = apply-reindex-shape-resp γ≈ P' fm p
      apply-reindex-shape-resp γ≈ (P' + Q') fm {inj₂ _} {inj₂ _} p = apply-reindex-shape-resp γ≈ Q' fm p
      apply-reindex-shape-resp γ≈ (P' × Q') fm {_ , _} {_ , _} (p₁ , p₂) =
        apply-reindex-shape-resp γ≈ P' fm p₁ , apply-reindex-shape-resp γ≈ Q' fm p₂
      apply-reindex-shape-resp γ≈ (μ Q'')   fm {a} {a'} p = apply-reindex-resp {Q = Q''} γ≈ fm {a} {a'} p

      apply-apply-resp : ∀ {k} {ρ ρ' d d'} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (fm : FMor ρ ρ' d d') (v : Fin k)
                        {a a'} (p : T-δ.elEq (ρ v) a a') →
                        T-δA-ext.elEq (ρ' v) (apply-apply γ fm v a) (apply-apply γ' fm v a')
      apply-apply-resp γ≈ fbase        Fin.zero    {a} {a'} p = h-resp γ≈ {a} {a'} p
      apply-apply-resp γ≈ fbase        (Fin.suc i) p = p
      apply-apply-resp γ≈ (fbind Q fm) Fin.zero    {a} {a'} p = apply-reindex-resp {Q = Q} γ≈ fm {a} {a'} p
      apply-apply-resp γ≈ (fbind Q fm) (Fin.suc v) p = apply-apply-resp γ≈ fm v p

    mutual
      apply-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : T-δ.⟦ ∣ Q ∣ ⟧shape (η₀ ∣ P ∣)) →
                       prod (Γ .fam .fm γ) (T-δ.fib-shape Q (T-δ.deco-ext P (λ i → lift tt)) x)
                         ⇒ fobj μ-fam Q (extend δ A) .fam .fm (apply-shape-idx Q γ x)
      apply-shape-fam (const A')        γ a = p₂
      apply-shape-fam (var Fin.zero)    γ t = h-fam γ t
      apply-shape-fam (var (Fin.suc i)) γ a = p₂
      apply-shape-fam (Q₁ + Q₂) γ (inj₁ x) = strong-Lmap (apply-shape-fam Q₁ γ x)
      apply-shape-fam (Q₁ + Q₂) γ (inj₂ y) = strong-Lmap (apply-shape-fam Q₂ γ y)
      apply-shape-fam (Q₁ × Q₂) γ (x , y) =
        strong-Lmap (strong-prod-m (apply-shape-fam Q₁ γ x) (apply-shape-fam Q₂ γ y))
      apply-shape-fam (μ Q')    γ t = apply-reindex-fam {Q = Q'} γ fbase t

      apply-reindex-fam : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ' d d') (t : T-δ.W ∣ Q ∣ ρ) →
                         prod (Γ .fam .fm γ) (T-δ.fib Q d t) ⇒ T-δA-ext.fib Q d' (apply-reindex γ md t)
      apply-reindex-fam {Q = Q} γ md (T-δ.sup x) = apply-reindex-shape-fam γ Q (fbind Q md) x

      apply-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (md : FMor ηA ηB dA dB) (a : T-δ.⟦ ∣ R ∣ ⟧shape ηA) →
                               prod (Γ .fam .fm γ) (T-δ.fib-shape R dA a) ⇒ T-δA-ext.fib-shape R dB (apply-reindex-shape γ R md a)
      apply-reindex-shape-fam γ (const A') md a = p₂
      apply-reindex-shape-fam γ (var v)    md a = apply-apply-fam γ md v a
      apply-reindex-shape-fam γ (P' + Q') md (inj₁ a) = strong-Lmap (apply-reindex-shape-fam γ P' md a)
      apply-reindex-shape-fam γ (P' + Q') md (inj₂ b) = strong-Lmap (apply-reindex-shape-fam γ Q' md b)
      apply-reindex-shape-fam γ (P' × Q') md (a , b) =
        strong-Lmap (strong-prod-m (apply-reindex-shape-fam γ P' md a) (apply-reindex-shape-fam γ Q' md b))
      apply-reindex-shape-fam γ (μ Q'')   md t = apply-reindex-fam {Q = Q''} γ md t

      apply-apply-fam : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ' d d') (v : Fin k) (a : T-δ.El (ρ v)) →
                       prod (Γ .fam .fm γ) (T-δ.fib-el (ρ v) (d v) a) ⇒ T-δA-ext.fib-el (ρ' v) (d' v) (apply-apply γ md v a)
      apply-apply-fam γ fbase        Fin.zero    t = h-fam γ t
      apply-apply-fam γ fbase        (Fin.suc i) a = p₂
      apply-apply-fam γ (fbind Q md) Fin.zero    a = apply-reindex-fam {Q = Q} γ md a
      apply-apply-fam γ (fbind Q md) (Fin.suc v) a = apply-apply-fam γ md v a

module Laws {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (alg : Mor (Fam-P.prod Γ (fobj μ-fam P (extend δ A))) A) where
  open FoldBase {n} {Γ} {A} {P} {δ}
  module FoldDef-alg = FoldDef {n} {Γ} {A} {P} {δ} alg
  module Ap (h : Mor (Fam-P.prod Γ (μ-fam P δ)) A) = ApplyDef {n} {Γ} {A} {P} {δ} h
  module Af = Ap FoldDef-alg.foldMor

  record IsFold (h : Mor (Fam-P.prod Γ (μ-fam P δ)) A) : Prop (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    field
      is-idx : ∀ γ x → _≈s_ (A .idx)
               (Ap.h-idx h γ (T-δ.sup x))
               (alg .idxf .func (γ , Ap.apply-shape-idx h P γ x))
      is-fam : ∀ γ x →
               Ap.h-fam h γ (T-δ.sup x)
               ≈ (A .fam .subst (A .idx .isEquivalence .sym (is-idx γ x))
                  ∘ (alg .famf .transf (γ , Ap.apply-shape-idx h P γ x)
                     ∘ pair p₁ (Ap.apply-shape-fam h P γ x)))

  mutual
    agree-shape : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : T-δ.⟦ ∣ Q ∣ ⟧shape (η₀ ∣ P ∣)) →
                  _≈s_ (fobj μ-fam Q (extend δ A) .idx) (FoldDef-alg.fold-shape-idx Q γ x) (Af.apply-shape-idx Q γ x)
    agree-shape (const A')        γ a = A' .idx .isEquivalence .refl
    agree-shape (var Fin.zero)    γ t = A .idx .isEquivalence .refl
    agree-shape (var (Fin.suc i)) γ a = δ i .idx .isEquivalence .refl
    agree-shape (Q₁ + Q₂) γ (inj₁ x) = agree-shape Q₁ γ x
    agree-shape (Q₁ + Q₂) γ (inj₂ y) = agree-shape Q₂ γ y
    agree-shape (Q₁ × Q₂) γ (x , y) = agree-shape Q₁ γ x , agree-shape Q₂ γ y
    agree-shape (μ Q')    γ t = agree-reindex {Q = Q'} γ fbase t

    agree-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d')
                    (t : T-δ.W ∣ Q ∣ ρ) →
                    T-δA-ext.W-≈ (FoldDef-alg.fold-reindex γ fm t) (Af.apply-reindex γ fm t)
    agree-reindex {Q = Q} γ fm (T-δ.sup x) = agree-reindex-shape γ Q (fbind Q fm) x

    agree-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB)
                          (a : T-δ.⟦ ∣ R ∣ ⟧shape ηA) →
                          T-δA-ext.shape≈ ∣ R ∣ ηB (FoldDef-alg.fold-reindex-shape γ R fm a) (Af.apply-reindex-shape γ R fm a)
    agree-reindex-shape γ (const A') fm a = A' .idx .isEquivalence .refl
    agree-reindex-shape γ (var v)    fm a = agree-apply γ fm v a
    agree-reindex-shape γ (P' + Q') fm (inj₁ a) = agree-reindex-shape γ P' fm a
    agree-reindex-shape γ (P' + Q') fm (inj₂ b) = agree-reindex-shape γ Q' fm b
    agree-reindex-shape γ (P' × Q') fm (a , b) = agree-reindex-shape γ P' fm a , agree-reindex-shape γ Q' fm b
    agree-reindex-shape γ (μ Q'')   fm t = agree-reindex {Q = Q''} γ fm t

    agree-apply : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k)
                  (a : T-δ.El (ρ v)) →
                  T-δA-ext.elEq (ρ' v) (FoldDef-alg.fold-apply γ fm v a) (Af.apply-apply γ fm v a)
    agree-apply γ fbase        Fin.zero    t = A .idx .isEquivalence .refl
    agree-apply γ fbase        (Fin.suc i) a = T-δA-ext.elEq-refl (inj₁ (Fin.suc i)) a
    agree-apply γ (fbind Q fm) Fin.zero    a = agree-reindex {Q = Q} γ fm a
    agree-apply γ (fbind Q fm) (Fin.suc v) a = agree-apply γ fm v a

  mutual
    agree-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : T-δ.⟦ ∣ Q ∣ ⟧shape (η₀ ∣ P ∣)) →
                      (fobj μ-fam Q (extend δ A) .fam .subst (agree-shape Q γ x) ∘ FoldDef-alg.fold-shape-fam Q γ x)
                        ≈ Af.apply-shape-fam Q γ x
    agree-shape-fam (const A')        γ a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
    agree-shape-fam (var Fin.zero)    γ t = ≈-trans (∘-cong (A .fam .refl*) ≈-refl) id-left
    agree-shape-fam (var (Fin.suc i)) γ a = ≈-trans (∘-cong (δ i .fam .refl*) ≈-refl) id-left
    agree-shape-fam (Q₁ + Q₂) γ (inj₁ x) =
      ≈-trans (strong-Lmap-post _
                (FoldDef-alg.fold-shape-fam Q₁ γ x))
              (strong-Lmap-cong (agree-shape-fam Q₁ γ x))
    agree-shape-fam (Q₁ + Q₂) γ (inj₂ y) =
      ≈-trans (strong-Lmap-post _
                (FoldDef-alg.fold-shape-fam Q₂ γ y))
              (strong-Lmap-cong (agree-shape-fam Q₂ γ y))
    agree-shape-fam (Q₁ × Q₂) γ (x , y) =
      ≈-trans (strong-Lmap-post _
                (strong-prod-m (FoldDef-alg.fold-shape-fam Q₁ γ x) (FoldDef-alg.fold-shape-fam Q₂ γ y)))
              (strong-Lmap-cong
                (≈-trans (strong-prod-m-post _ _ _ _)
                         (strong-prod-m-cong (agree-shape-fam Q₁ γ x) (agree-shape-fam Q₂ γ y))))
    agree-shape-fam (μ Q') γ t = agree-reindex-fam {Q = Q'} γ fbase t

    agree-reindex-fam : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier)
                        (fm : FMor ρ ρ' d d') (t : T-δ.W ∣ Q ∣ ρ) →
                        (T-δA-ext.fib-subst Q d' {x = FoldDef-alg.fold-reindex γ fm t} {y = Af.apply-reindex γ fm t}
                           (agree-reindex {Q = Q} γ fm t)
                         ∘ FoldDef-alg.fold-reindex-fam γ fm t)
                          ≈ Af.apply-reindex-fam γ fm t
    agree-reindex-fam {Q = Q} γ fm (T-δ.sup x) = agree-reindex-shape-fam γ Q (fbind Q fm) x

    agree-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB}
                              (fm : FMor ηA ηB dA dB) (a : T-δ.⟦ ∣ R ∣ ⟧shape ηA) →
                              (T-δA-ext.fib-shape-subst R dB (agree-reindex-shape γ R fm a)
                               ∘ FoldDef-alg.fold-reindex-shape-fam γ R fm a)
                                ≈ Af.apply-reindex-shape-fam γ R fm a
    agree-reindex-shape-fam γ (const A') fm a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
    agree-reindex-shape-fam γ (var v)    fm a = agree-apply-fam γ fm v a
    agree-reindex-shape-fam γ (P' + Q') {dA = dA} {dB} fm (inj₁ a) =
      ≈-trans (strong-Lmap-post _
                (FoldDef-alg.fold-reindex-shape-fam γ P' fm a))
              (strong-Lmap-cong (agree-reindex-shape-fam γ P' fm a))
    agree-reindex-shape-fam γ (P' + Q') {dA = dA} {dB} fm (inj₂ b) =
      ≈-trans (strong-Lmap-post _
                (FoldDef-alg.fold-reindex-shape-fam γ Q' fm b))
              (strong-Lmap-cong (agree-reindex-shape-fam γ Q' fm b))
    agree-reindex-shape-fam γ (P' × Q') {dA = dA} {dB} fm (a , b) =
      ≈-trans (strong-Lmap-post _
                (strong-prod-m (FoldDef-alg.fold-reindex-shape-fam γ P' fm a) (FoldDef-alg.fold-reindex-shape-fam γ Q' fm b)))
              (strong-Lmap-cong
                (≈-trans (strong-prod-m-post _ _ _ _)
                         (strong-prod-m-cong (agree-reindex-shape-fam γ P' fm a)
                                             (agree-reindex-shape-fam γ Q' fm b))))
    agree-reindex-shape-fam γ (μ Q'')   fm t = agree-reindex-fam {Q = Q''} γ fm t

    agree-apply-fam : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k)
                      (a : T-δ.El (ρ v)) →
                      (T-δA-ext.fib-el-subst (ρ' v) (d' v) (agree-apply γ fm v a)
                       ∘ FoldDef-alg.fold-apply-fam γ fm v a)
                        ≈ Af.apply-apply-fam γ fm v a
    agree-apply-fam γ fbase        Fin.zero    t = ≈-trans (∘-cong (A .fam .refl*) ≈-refl) id-left
    agree-apply-fam γ fbase        (Fin.suc i) a =
      ≈-trans (∘-cong (T-δA-ext.fib-el-refl* (inj₁ (Fin.suc i)) (lift tt) a) ≈-refl) id-left
    agree-apply-fam γ (fbind Q fm) Fin.zero    a = agree-reindex-fam {Q = Q} γ fm a
    agree-apply-fam γ (fbind Q fm) (Fin.suc v) a = agree-apply-fam γ fm v a

  module Unique (h : Mor (Fam-P.prod Γ (μ-fam P δ)) A) (H : IsFold h) where
    module Ah = Ap h
    open Ah using (h-idx; h-resp; h-fam)

    mutual
      uniq-idx : ∀ γ t → _≈s_ (A .idx) (h-idx γ t) (FoldDef-alg.fold-idx γ t)
      uniq-idx γ (T-δ.sup x) =
        A .idx .isEquivalence .trans (H .IsFold.is-idx γ x)
          (alg .idxf .func-resp-≈ (Γ .idx .isEquivalence .refl , compare-shape P γ x))

      compare-shape : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : T-δ.⟦ ∣ Q ∣ ⟧shape (η₀ ∣ P ∣)) →
                    _≈s_ (fobj μ-fam Q (extend δ A) .idx) (Ah.apply-shape-idx Q γ x) (FoldDef-alg.fold-shape-idx Q γ x)
      compare-shape (const A')        γ a = A' .idx .isEquivalence .refl
      compare-shape (var Fin.zero)    γ t = uniq-idx γ t
      compare-shape (var (Fin.suc i)) γ a = δ i .idx .isEquivalence .refl
      compare-shape (Q₁ + Q₂) γ (inj₁ x) = compare-shape Q₁ γ x
      compare-shape (Q₁ + Q₂) γ (inj₂ y) = compare-shape Q₂ γ y
      compare-shape (Q₁ × Q₂) γ (x , y) = compare-shape Q₁ γ x , compare-shape Q₂ γ y
      compare-shape (μ Q')    γ t = compare-reindex {Q = Q'} γ fbase t

      compare-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d')
                      (t : T-δ.W ∣ Q ∣ ρ) →
                      T-δA-ext.W-≈ (Ah.apply-reindex γ fm t) (FoldDef-alg.fold-reindex γ fm t)
      compare-reindex {Q = Q} γ fm (T-δ.sup x) = compare-reindex-shape γ Q (fbind Q fm) x

      compare-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB)
                            (a : T-δ.⟦ ∣ R ∣ ⟧shape ηA) →
                            T-δA-ext.shape≈ ∣ R ∣ ηB (Ah.apply-reindex-shape γ R fm a) (FoldDef-alg.fold-reindex-shape γ R fm a)
      compare-reindex-shape γ (const A') fm a = A' .idx .isEquivalence .refl
      compare-reindex-shape γ (var v)    fm a = compare-apply γ fm v a
      compare-reindex-shape γ (P' + Q') fm (inj₁ a) = compare-reindex-shape γ P' fm a
      compare-reindex-shape γ (P' + Q') fm (inj₂ b) = compare-reindex-shape γ Q' fm b
      compare-reindex-shape γ (P' × Q') fm (a , b) = compare-reindex-shape γ P' fm a , compare-reindex-shape γ Q' fm b
      compare-reindex-shape γ (μ Q'')   fm t = compare-reindex {Q = Q''} γ fm t

      compare-apply : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k)
                    (a : T-δ.El (ρ v)) →
                    T-δA-ext.elEq (ρ' v) (Ah.apply-apply γ fm v a) (FoldDef-alg.fold-apply γ fm v a)
      compare-apply γ fbase        Fin.zero    t = uniq-idx γ t
      compare-apply γ fbase        (Fin.suc i) a = T-δA-ext.elEq-refl (inj₁ (Fin.suc i)) a
      compare-apply γ (fbind Q fm) Fin.zero    a = compare-reindex {Q = Q} γ fm a
      compare-apply γ (fbind Q fm) (Fin.suc v) a = compare-apply γ fm v a

    mutual
      uniq-fam : ∀ γ t → (A .fam .subst (uniq-idx γ t) ∘ h-fam γ t) ≈ FoldDef-alg.fold-fam γ t
      uniq-fam γ (T-δ.sup x) =
        ≈-trans (∘-cong ≈-refl (H .IsFold.is-fam γ x))
        (≈-trans (head-cong (≈-sym (A .fam .trans*
                      (uniq-idx γ (T-δ.sup x))
                      (A .idx .isEquivalence .sym (H .IsFold.is-idx γ x)))))
         (≈-trans (head-cong (≈-sym (alg .famf .natural
                       (Γ .idx .isEquivalence .refl , compare-shape P γ x))))
                  (tail-cong (≈-trans (pair-compose _ _ _ _)
                                      (pair-cong (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left)
                                                 (compare-shape-fam P γ x))))))

      compare-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : T-δ.⟦ ∣ Q ∣ ⟧shape (η₀ ∣ P ∣)) →
                        (fobj μ-fam Q (extend δ A) .fam .subst (compare-shape Q γ x) ∘ Ah.apply-shape-fam Q γ x)
                          ≈ FoldDef-alg.fold-shape-fam Q γ x
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
                          (fm : FMor ρ ρ' d d') (t : T-δ.W ∣ Q ∣ ρ) →
                          (T-δA-ext.fib-subst Q d' {x = Ah.apply-reindex γ fm t} {y = FoldDef-alg.fold-reindex γ fm t}
                             (compare-reindex {Q = Q} γ fm t)
                           ∘ Ah.apply-reindex-fam γ fm t)
                            ≈ FoldDef-alg.fold-reindex-fam γ fm t
      compare-reindex-fam {Q = Q} γ fm (T-δ.sup x) = compare-reindex-shape-fam γ Q (fbind Q fm) x

      compare-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB}
                                (fm : FMor ηA ηB dA dB) (a : T-δ.⟦ ∣ R ∣ ⟧shape ηA) →
                                (T-δA-ext.fib-shape-subst R dB (compare-reindex-shape γ R fm a)
                                 ∘ Ah.apply-reindex-shape-fam γ R fm a)
                                  ≈ FoldDef-alg.fold-reindex-shape-fam γ R fm a
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
                        (a : T-δ.El (ρ v)) →
                        (T-δA-ext.fib-el-subst (ρ' v) (d' v) (compare-apply γ fm v a)
                         ∘ Ah.apply-apply-fam γ fm v a)
                          ≈ FoldDef-alg.fold-apply-fam γ fm v a
      compare-apply-fam γ fbase        Fin.zero    t = uniq-fam γ t
      compare-apply-fam γ fbase        (Fin.suc i) a =
        ≈-trans (∘-cong (T-δA-ext.fib-el-refl* (inj₁ (Fin.suc i)) (lift tt) a) ≈-refl) id-left
      compare-apply-fam γ (fbind Q fm) Fin.zero    a = compare-reindex-fam {Q = Q} γ fm a
      compare-apply-fam γ (fbind Q fm) (Fin.suc v) a = compare-apply-fam γ fm v a

  unique : (h : Mor (Fam-P.prod Γ (μ-fam P δ)) A) → IsFold h → h ≃ FoldDef.foldMor {n} {Γ} {A} {P} {δ} alg
  unique h H = go
    where
    module E = Unique h H

    go : h ≃ FoldDef.foldMor {n} {Γ} {A} {P} {δ} alg
    go .idxf-eq .func-eq {γ₁ , t₁} {γ₂ , t₂} (γ≈ , t≈) =
      A .idx .isEquivalence .trans (E.uniq-idx γ₁ t₁) (FoldDef-alg.fold-idx-resp γ≈ {t₁} {t₂} t≈)
    go .famf-eq .transf-eq {γ , t} = E.uniq-fam γ t

module Bridge {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (h : Mor (Fam-P.prod Γ (μ-fam P δ)) A) where
  open FoldBase {n} {Γ} {A} {P} {δ}
  private
    module InMapDef-P = InMapDef P δ
    module T-δ' = Tree InMapDef-P.δ'
    module RX = Reindex InMapDef-P.δ' (extend δ A)

  open ApplyDef {n} {Γ} {A} {P} {δ} h public

  mutual
    apply-shape-fam-natural : (Q : Poly (suc n)) → ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {x x'}
                              (p : T-δ.shape≈ ∣ Q ∣ (η₀ ∣ P ∣) x x') →
                              (apply-shape-fam Q γ₂ x'
                               ∘ prod-m (Γ .fam .subst γ≈) (T-δ.fib-shape-subst Q (T-δ.deco-ext P (λ i → lift tt)) p))
                              ≈ (fobj μ-fam Q (extend δ A) .fam .subst (apply-shape-idx-resp Q γ≈ p) ∘ apply-shape-fam Q γ₁ x)
    apply-shape-fam-natural (const A')        γ≈ p = pair-p₂ _ _
    apply-shape-fam-natural (var Fin.zero)    γ≈ {x} {x'} p = h .famf .natural (γ≈ , p)
    apply-shape-fam-natural (var (Fin.suc i)) γ≈ p = pair-p₂ _ _
    apply-shape-fam-natural (Q₁ + Q₂) {γ₁} {γ₂} γ≈ {inj₁ x} {inj₁ x'} p =
      strong-Lmap-natural (Γ .fam .subst γ≈)
        (T-δ.fib-shape-subst Q₁ (T-δ.deco-ext P (λ i → lift tt)) p)
        (fobj μ-fam Q₁ (extend δ A) .fam .subst (apply-shape-idx-resp Q₁ γ≈ p))
        (apply-shape-fam Q₁ γ₁ x) (apply-shape-fam Q₁ γ₂ x')
        (apply-shape-fam-natural Q₁ γ≈ p)
    apply-shape-fam-natural (Q₁ + Q₂) {γ₁} {γ₂} γ≈ {inj₂ y} {inj₂ y'} p =
      strong-Lmap-natural (Γ .fam .subst γ≈)
        (T-δ.fib-shape-subst Q₂ (T-δ.deco-ext P (λ i → lift tt)) p)
        (fobj μ-fam Q₂ (extend δ A) .fam .subst (apply-shape-idx-resp Q₂ γ≈ p))
        (apply-shape-fam Q₂ γ₁ y) (apply-shape-fam Q₂ γ₂ y')
        (apply-shape-fam-natural Q₂ γ≈ p)
    apply-shape-fam-natural (Q₁ × Q₂) {γ₁} {γ₂} γ≈ {x₁ , x₂} {x₁' , x₂'} (p₁p , p₂p) =
      strong-Lmap-natural (Γ .fam .subst γ≈)
        (prod-m (T-δ.fib-shape-subst Q₁ (T-δ.deco-ext P (λ i → lift tt)) p₁p)
                (T-δ.fib-shape-subst Q₂ (T-δ.deco-ext P (λ i → lift tt)) p₂p))
        (prod-m (fobj μ-fam Q₁ (extend δ A) .fam .subst (apply-shape-idx-resp Q₁ γ≈ p₁p))
                (fobj μ-fam Q₂ (extend δ A) .fam .subst (apply-shape-idx-resp Q₂ γ≈ p₂p)))
        (strong-prod-m (apply-shape-fam Q₁ γ₁ x₁) (apply-shape-fam Q₂ γ₁ x₂))
        (strong-prod-m (apply-shape-fam Q₁ γ₂ x₁') (apply-shape-fam Q₂ γ₂ x₂'))
        (strong-prod-m-natural (apply-shape-fam-natural Q₁ γ≈ p₁p) (apply-shape-fam-natural Q₂ γ≈ p₂p))
    apply-shape-fam-natural (μ Q')    γ≈ {x} {x'} p = apply-reindex-fam-natural {Q = Q'} γ≈ fbase {x} {x'} p

    apply-reindex-fam-natural : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂)
                                (md : FMor ρ ρ' d d') {t t' : T-δ.W ∣ Q ∣ ρ} (p : T-δ.W-≈ t t') →
                                (apply-reindex-fam γ₂ md t' ∘ prod-m (Γ .fam .subst γ≈) (T-δ.fib-subst Q d {x = t} {y = t'} p))
                                ≈ (T-δA-ext.fib-subst Q d' {x = apply-reindex γ₁ md t} {y = apply-reindex γ₂ md t'}
                                                 (apply-reindex-resp γ≈ md {t} {t'} p) ∘ apply-reindex-fam γ₁ md t)
    apply-reindex-fam-natural {Q = Q} γ≈ md {T-δ.sup x} {T-δ.sup y} p =
      apply-reindex-shape-fam-natural γ≈ Q (fbind Q md) {x} {y} p

    apply-reindex-shape-fam-natural : ∀ {j} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (R : Poly j) {ηA ηB dA dB}
                                      (md : FMor ηA ηB dA dB) {a a' : T-δ.⟦ ∣ R ∣ ⟧shape ηA} (p : T-δ.shape≈ ∣ R ∣ ηA a a') →
                                      (apply-reindex-shape-fam γ₂ R md a' ∘ prod-m (Γ .fam .subst γ≈) (T-δ.fib-shape-subst R dA p))
                                      ≈ (T-δA-ext.fib-shape-subst R dB (apply-reindex-shape-resp γ≈ R md p) ∘ apply-reindex-shape-fam γ₁ R md a)
    apply-reindex-shape-fam-natural γ≈ (const A') md p = pair-p₂ _ _
    apply-reindex-shape-fam-natural γ≈ (var v)    md p = apply-apply-fam-natural γ≈ md v p
    apply-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' + Q') {dA = dA} {dB} md {inj₁ a} {inj₁ a'} p =
      strong-Lmap-natural (Γ .fam .subst γ≈)
        (T-δ.fib-shape-subst P' dA p)
        (T-δA-ext.fib-shape-subst P' dB (apply-reindex-shape-resp γ≈ P' md p))
        (apply-reindex-shape-fam γ₁ P' md a) (apply-reindex-shape-fam γ₂ P' md a')
        (apply-reindex-shape-fam-natural γ≈ P' md p)
    apply-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' + Q') {dA = dA} {dB} md {inj₂ b} {inj₂ b'} p =
      strong-Lmap-natural (Γ .fam .subst γ≈)
        (T-δ.fib-shape-subst Q' dA p)
        (T-δA-ext.fib-shape-subst Q' dB (apply-reindex-shape-resp γ≈ Q' md p))
        (apply-reindex-shape-fam γ₁ Q' md b) (apply-reindex-shape-fam γ₂ Q' md b')
        (apply-reindex-shape-fam-natural γ≈ Q' md p)
    apply-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' × Q') {dA = dA} {dB} md {a₁ , a₂} {a₁' , a₂'} (p₁p , p₂p) =
      strong-Lmap-natural (Γ .fam .subst γ≈)
        (prod-m (T-δ.fib-shape-subst P' dA p₁p) (T-δ.fib-shape-subst Q' dA p₂p))
        (prod-m (T-δA-ext.fib-shape-subst P' dB (apply-reindex-shape-resp γ≈ P' md p₁p))
                (T-δA-ext.fib-shape-subst Q' dB (apply-reindex-shape-resp γ≈ Q' md p₂p)))
        (strong-prod-m (apply-reindex-shape-fam γ₁ P' md a₁) (apply-reindex-shape-fam γ₁ Q' md a₂))
        (strong-prod-m (apply-reindex-shape-fam γ₂ P' md a₁') (apply-reindex-shape-fam γ₂ Q' md a₂'))
        (strong-prod-m-natural (apply-reindex-shape-fam-natural γ≈ P' md p₁p)
                               (apply-reindex-shape-fam-natural γ≈ Q' md p₂p))
    apply-reindex-shape-fam-natural γ≈ (μ Q'')   md {a} {a'} p = apply-reindex-fam-natural {Q = Q''} γ≈ md {a} {a'} p

    apply-apply-fam-natural : ∀ {k} {ρ ρ' d d'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (md : FMor ρ ρ' d d') (v : Fin k)
                              {a a'} (p : T-δ.elEq (ρ v) a a') →
                              (apply-apply-fam γ₂ md v a' ∘ prod-m (Γ .fam .subst γ≈) (T-δ.fib-el-subst (ρ v) (d v) p))
                              ≈ (T-δA-ext.fib-el-subst (ρ' v) (d' v) (apply-apply-resp γ≈ md v p) ∘ apply-apply-fam γ₁ md v a)
    apply-apply-fam-natural γ≈ fbase        Fin.zero    {a} {a'} p = h .famf .natural (γ≈ , p)
    apply-apply-fam-natural γ≈ fbase        (Fin.suc i) p = pair-p₂ _ _
    apply-apply-fam-natural γ≈ (fbind Q md) Fin.zero    {a} {a'} p = apply-reindex-fam-natural {Q = Q} γ≈ md {a} {a'} p
    apply-apply-fam-natural γ≈ (fbind Q md) (Fin.suc v) p = apply-apply-fam-natural γ≈ md v p

  fs : ∀ i → Mor (Fam-P.prod Γ (InMapDef-P.δ' i)) (extend δ A i)
  fs = strong-extend-mor (λ i → Fam-P.p₂) h

  imor : Γ .idx .Carrier → RX.IMorD (λ v → inj₁ v) (λ v → inj₁ v)
  imor γ = RX.ibase (λ { Fin.zero t → h-idx γ t ; (Fin.suc i) a → a })
                   (λ { Fin.zero p → h-resp (Γ .idx .isEquivalence .refl) p ; (Fin.suc i) p → p })

  agree : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (InMapDef-P.δ' i .idx) a₁ a₂) →
         _≈s_ (extend δ A i .idx) (RX.iapply (imor γ₁) i a₁) (fs i .idxf .func (γ₂ , a₂))
  agree Fin.zero    γ≈ {a₁} {a₂} a≈ = h-resp γ≈ {a₁} {a₂} a≈
  agree (Fin.suc i) γ≈ a≈ = a≈

  module Comp (γ : Γ .idx .Carrier) where
    private module FRX = FReindex {δA = InMapDef-P.δ'} {δB = extend δ A} (Γ .fam .fm γ)

    act : FRX.FAct (imor γ) (λ v → lift tt) (λ v → lift tt)
    act = FRX.abase (λ { Fin.zero t → h-fam γ t ; (Fin.suc i) a → p₂ })

    corr-fam : ∀ i {a} →
               (extend δ A i .fam .subst (agree i (Γ .idx .isEquivalence .refl) (InMapDef-P.δ' i .idx .isEquivalence .refl {a}))
                ∘ FRX.aapply act i a)
               ≈ fs i .famf .transf (γ , a)
    corr-fam Fin.zero    = ≈-trans (∘-cong (A .fam .refl*) ≈-refl) id-left
    corr-fam (Fin.suc i) = ≈-trans (∘-cong (δ i .fam .refl*) ≈-refl) id-left

    data CRel : ∀ {j} {ρX : Fin j → Fin (suc n) ⊎ Sort (suc n)} {ρ : Fin j → Fin n ⊎ Sort n}
                {ρ' : Fin j → Fin (suc n) ⊎ Sort (suc n)}
                {dX : ∀ v → T-δ'.DecoAssign (ρX v)} {d : ∀ v → T-δ.DecoAssign (ρ v)} {d' : ∀ v → T-δA-ext.DecoAssign (ρ' v)} →
                FMor ρ ρ' d d' → InMapDef-P.MorD ρX ρ dX d → (im : RX.IMorD ρX ρ') → FRX.FAct im dX d' →
                Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      cbase : CRel fbase InMapDef-P.mor₀ (imor γ) act
      cbind : ∀ {j} {ρX ρ ρ' dX d d'} {fm : FMor {j} ρ ρ' d d'} {md : InMapDef-P.MorD ρX ρ dX d} {im} {am : FRX.FAct im dX d'}
              (Q : Poly (suc j)) → CRel fm md im am →
              CRel (fbind Q fm) (InMapDef-P.bind Q md) (RX.ibind ∣ Q ∣ im) (FRX.abind Q im am)

    mutual
      comp-W : ∀ {j} {Q̂ : Poly (suc j)} {ρX ρ ρ' dX d d'} {fm : FMor ρ ρ' d d'} {md : InMapDef-P.MorD ρX ρ dX d} {im}
               {am : FRX.FAct im dX d'} → CRel fm md im am → (t : T-δ'.W ∣ Q̂ ∣ ρX) →
               T-δA-ext.W-≈ (apply-reindex {Q = Q̂} γ fm (InMapDef-P.reindex md t)) (RX.ireindex im t)
      comp-W {Q̂ = Q̂} rel (T-δ'.sup x) = comp-shape Q̂ (cbind Q̂ rel) x

      comp-shape : ∀ {j} (S : Poly j) {ρX ρ ρ' dX d d'} {fm : FMor ρ ρ' d d'} {md : InMapDef-P.MorD ρX ρ dX d} {im}
                   {am : FRX.FAct im dX d'} → CRel fm md im am → (a : T-δ'.⟦ ∣ S ∣ ⟧shape ρX) →
                   T-δA-ext.shape≈ ∣ S ∣ ρ' (apply-reindex-shape γ S fm (InMapDef-P.reindex-shape ∣ S ∣ md a)) (RX.ireindex-shape ∣ S ∣ im a)
      comp-shape (const A') rel a = A' .idx .isEquivalence .refl
      comp-shape (var v)    rel a = comp-el rel v a
      comp-shape (P' + Q') rel (inj₁ a) = comp-shape P' rel a
      comp-shape (P' + Q') rel (inj₂ b) = comp-shape Q' rel b
      comp-shape (P' × Q') rel (a , b) = comp-shape P' rel a , comp-shape Q' rel b
      comp-shape (μ Q'')   rel t = comp-W {Q̂ = Q''} rel t

      comp-el : ∀ {j} {ρX ρ ρ' dX d d'} {fm : FMor {j} ρ ρ' d d'} {md : InMapDef-P.MorD ρX ρ dX d} {im}
                {am : FRX.FAct im dX d'} → CRel fm md im am → (v : Fin j) (a : T-δ'.El (ρX v)) →
                T-δA-ext.elEq (ρ' v) (apply-apply γ fm v (InMapDef-P.apply md v a)) (RX.iapply im v a)
      comp-el cbase          Fin.zero    t = A .idx .isEquivalence .refl
      comp-el cbase          (Fin.suc i) a = T-δA-ext.elEq-refl (inj₁ (Fin.suc i)) a
      comp-el (cbind Q rel)  Fin.zero    a = comp-W {Q̂ = Q} rel a
      comp-el (cbind Q rel)  (Fin.suc v) a = comp-el rel v a

    mutual
      comp-W-fam : ∀ {j} {Q̂ : Poly (suc j)} {ρX ρ ρ' dX d d'} {fm : FMor ρ ρ' d d'} {md : InMapDef-P.MorD ρX ρ dX d} {im}
                   {am : FRX.FAct im dX d'} (rel : CRel fm md im am) (t : T-δ'.W ∣ Q̂ ∣ ρX) →
                   (T-δA-ext.fib-subst Q̂ d' {x = apply-reindex {Q = Q̂} γ fm (InMapDef-P.reindex md t)} {y = RX.ireindex im t}
                      (comp-W rel t)
                    ∘ (apply-reindex-fam {Q = Q̂} γ fm (InMapDef-P.reindex md t)
                       ∘ prod-m (id _) (InMapDef-P.reindex-fam-W {Q = Q̂} md {t})))
                   ≈ FRX.freindex-fam {Q = Q̂} am {t}
      comp-W-fam {Q̂ = Q̂} rel (T-δ'.sup x) = comp-shape-fam Q̂ (cbind Q̂ rel) x

      comp-shape-fam : ∀ {j} (S : Poly j) {ρX ρ ρ' dX d d'} {fm : FMor ρ ρ' d d'} {md : InMapDef-P.MorD ρX ρ dX d} {im}
                       {am : FRX.FAct im dX d'} (rel : CRel fm md im am) (a : T-δ'.⟦ ∣ S ∣ ⟧shape ρX) →
                       (T-δA-ext.fib-shape-subst S d' (comp-shape S rel a)
                        ∘ (apply-reindex-shape-fam γ S fm (InMapDef-P.reindex-shape ∣ S ∣ md a)
                           ∘ prod-m (id _) (InMapDef-P.reindex-fam S md {a})))
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

      comp-el-fam : ∀ {j} {ρX ρ ρ' dX d d'} {fm : FMor {j} ρ ρ' d d'} {md : InMapDef-P.MorD ρX ρ dX d} {im}
                    {am : FRX.FAct im dX d'} (rel : CRel fm md im am) (v : Fin j) (a : T-δ'.El (ρX v)) →
                    (T-δA-ext.fib-el-subst (ρ' v) (d' v) (comp-el rel v a)
                     ∘ (apply-apply-fam γ fm v (InMapDef-P.apply md v a) ∘ prod-m (id _) (InMapDef-P.apply-fam md v a)))
                    ≈ FRX.aapply am v a
      comp-el-fam cbase          Fin.zero    t =
        ≈-trans (∘-cong (A .fam .refl*) ≈-refl)
                (≈-trans id-left (≈-trans (∘-cong ≈-refl prod-m-id) id-right))
      comp-el-fam cbase          (Fin.suc i) a =
        ≈-trans (∘-cong (T-δA-ext.fib-el-refl* (inj₁ (Fin.suc i)) (lift tt) a) ≈-refl)
                (≈-trans id-left (≈-trans (pair-p₂ _ _) id-left))
      comp-el-fam (cbind Q rel)  Fin.zero    a = comp-W-fam {Q̂ = Q} rel a
      comp-el-fam (cbind Q rel)  (Fin.suc v) a = comp-el-fam rel v a

  bridge-idx : ∀ (Q : Poly (suc n)) γ (y : fobj μ-fam Q InMapDef-P.δ' .idx .Carrier) →
               _≈s_ (fobj μ-fam Q (extend δ A) .idx)
                 (apply-shape-idx Q γ (InMapDef-P.reindex-shape ∣ Q ∣ InMapDef-P.mor₀ (InMapDef-P.embed-idx Q y)))
                 (strong-fmor Q fs .idxf .func (γ , y))
  bridge-idx (const A')        γ a = A' .idx .isEquivalence .refl
  bridge-idx (var Fin.zero)    γ t = A .idx .isEquivalence .refl
  bridge-idx (var (Fin.suc i)) γ a = δ i .idx .isEquivalence .refl
  bridge-idx (Q₁ + Q₂) γ (inj₁ y) = bridge-idx Q₁ γ y
  bridge-idx (Q₁ + Q₂) γ (inj₂ y) = bridge-idx Q₂ γ y
  bridge-idx (Q₁ × Q₂) γ (y₁ , y₂) = bridge-idx Q₁ γ y₁ , bridge-idx Q₂ γ y₂
  bridge-idx (μ Q') γ t =
    T-δA-ext.W-≈-trans {x = apply-reindex {Q = Q'} γ fbase (InMapDef-P.reindex InMapDef-P.mor₀ t)} {y = RX.ireindex (imor γ) t}
      (comp-W cbase t)
      (fuse-idx {Γ = Γ} {sₛ = InMapDef-P.δ'} {sₜ = extend δ A} Q' imor fs agree
         (Γ .idx .isEquivalence .refl) {m₁ = t} {m₂ = t} (T-δ'.W-≈-refl t))
    where open Comp γ

  bridge-fam : ∀ (Q : Poly (suc n)) γ (y : fobj μ-fam Q InMapDef-P.δ' .idx .Carrier) →
               (fobj μ-fam Q (extend δ A) .fam .subst (bridge-idx Q γ y)
                ∘ (apply-shape-fam Q γ (InMapDef-P.reindex-shape ∣ Q ∣ InMapDef-P.mor₀ (InMapDef-P.embed-idx Q y))
                   ∘ prod-m (id _) (InMapDef-P.reindex-fam Q InMapDef-P.mor₀ ∘ InMapDef-P.embed-fam Q y)))
               ≈ strong-fmor Q fs .famf .transf (γ , y)
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
             (≈-sym (≈-trans id-left (≈-trans id-left (strong-Lf-map-transf (strong-fmor Q₁ fs))))))))
  bridge-fam (Q₁ + Q₂) γ (inj₂ y) =
    ≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (prod-m-cong ≈-refl (≈-sym (Lmap-comp _ _)))))
    (≈-trans (∘-cong ≈-refl (strong-Lmap-pre (id _) _ _))
    (≈-trans (strong-Lmap-post _ _)
    (≈-trans (strong-Lmap-cong (bridge-fam Q₂ γ y))
             (≈-sym (≈-trans id-left (≈-trans id-left (strong-Lf-map-transf (strong-fmor Q₂ fs))))))))
  bridge-fam (Q₁ × Q₂) γ (y₁ , y₂) =
    ≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (prod-m-cong ≈-refl
               (≈-trans (≈-sym (Lmap-comp _ _)) (Lmap-cong (≈-sym (prod-m-comp _ _ _ _)))))))
    (≈-trans (∘-cong ≈-refl (strong-Lmap-pre (id _) _ _))
    (≈-trans (strong-Lmap-post _ _)
    (≈-trans (strong-Lmap-cong
               (≈-trans (∘-cong ≈-refl (strong-prod-m-pre _ _ _ _ _))
               (≈-trans (strong-prod-m-post _ _ _ _)
                        (strong-prod-m-cong (bridge-fam Q₁ γ y₁) (bridge-fam Q₂ γ y₂)))))
             (≈-sym (≈-trans (strong-Lf-map-transf (Fam-P.strong-prod-m (strong-fmor Q₁ fs) (strong-fmor Q₂ fs)))
                             (strong-Lmap-cong
                               (strong-prod-m-transf (strong-fmor Q₁ fs) (strong-fmor Q₂ fs) {γ} {y₁} {y₂})))))))
  bridge-fam (μ Q') γ t =
    ≈-trans (∘-cong (T-δA-ext.fib-trans* Q' (λ v → lift tt)
                       {x = apply-reindex {Q = Q'} γ fbase (InMapDef-P.reindex InMapDef-P.mor₀ t)}
                       {y = RX.ireindex (imor γ) t}
                       {z = strong-fmor (μ Q') fs .idxf .func (γ , t)}
                       (fuse-idx {Γ = Γ} {sₛ = InMapDef-P.δ'} {sₜ = extend δ A} Q' imor fs agree
                          (Γ .idx .isEquivalence .refl) {m₁ = t} {m₂ = t} (T-δ'.W-≈-refl t))
                       (comp-W cbase t))
                    ≈-refl)
    (≈-trans (tail-cong (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (prod-m-cong ≈-refl id-right)))
                                 (comp-W-fam cbase t)))
              (fuse-fam γ Q' imor act fs agree corr-fam {t}))
    where open Comp γ

module Beta {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (alg : Mor (Fam-P.prod Γ (fobj μ-fam P (extend δ A))) A) where
  private
    module InMapDef-P = InMapDef P δ
    module L = Laws {n} {Γ} {A} {P} {δ} alg
    module FoldDef-alg = L.FoldDef-alg
  open Bridge {n} {Γ} {A} {P} {δ} FoldDef-alg.foldMor

  private
    sf = strong-fmor P fs
    F = fobj μ-fam P (extend δ A)

  β-idx : ∀ γ y → _≈s_ (A .idx)
            (FoldDef-alg.fold-idx γ (InMapDef-P.inMor .idxf .func y))
            (alg .idxf .func (γ , sf .idxf .func (γ , y)))
  β-idx γ y =
    alg .idxf .func-resp-≈
      (Γ .idx .isEquivalence .refl ,
       F .idx .isEquivalence .trans
         (L.agree-shape P γ (InMapDef-P.reindex-shape ∣ P ∣ InMapDef-P.mor₀ (InMapDef-P.embed-idx P y)))
         (bridge-idx P γ y))

  β-fam : ∀ γ y →
          (A .fam .subst (β-idx γ y)
           ∘ (FoldDef-alg.fold-fam γ (InMapDef-P.inMor .idxf .func y) ∘ pair p₁ (InMapDef-P.inMor .famf .transf y ∘ p₂)))
          ≈ (alg .famf .transf (γ , sf .idxf .func (γ , y)) ∘ pair p₁ (sf .famf .transf (γ , y)))
  β-fam γ y =
    ≈-trans (∘-cong ≈-refl (assoc _ _ _))
    (≈-trans (head-cong (≈-sym (alg .famf .natural (Γ .idx .isEquivalence .refl , e′))))
             (tail-cong (≈-trans (∘-cong ≈-refl
                                         (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) ≈-refl)))
                        (≈-trans (pair-compose _ _ _ _)
                        (pair-cong (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left)
                          (≈-trans (∘-cong (F .fam .trans* (bridge-idx P γ y) (L.agree-shape P γ x))
                                           (∘-cong ≈-refl (pair-cong (≈-sym id-left) ≈-refl)))
                          (≈-trans (tail-cong (head-cong (L.agree-shape-fam P γ x)))
                                    (bridge-fam P γ y))))))))
    where
      x = InMapDef-P.reindex-shape ∣ P ∣ InMapDef-P.mor₀ (InMapDef-P.embed-idx P y)
      e′ = F .idx .isEquivalence .trans (L.agree-shape P γ x) (bridge-idx P γ y)

  ⦅⦆-β : (hasMu.⦅ alg ⦆ ∘co (hasMu.inMap P δ Fam-cat.∘ Fam-P.p₂))
         ≃ (alg ∘co strong-fmor P (strong-extend-mor (λ i → Fam-P.p₂) hasMu.⦅ alg ⦆))
  ⦅⦆-β .idxf-eq .func-eq {γ₁ , y₁} {γ₂ , y₂} (γ≈ , y≈) =
    A .idx .isEquivalence .trans (β-idx γ₁ y₁)
      (alg .idxf .func-resp-≈ (γ≈ , sf .idxf .func-resp-≈ (γ≈ , y≈)))
  ⦅⦆-β .famf-eq .transf-eq {γ , y} =
    ≈-trans (∘-cong ≈-refl (≈-trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left))))
            (≈-trans (β-fam γ y) (≈-sym id-left))

module Eta {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (alg : Mor (Fam-P.prod Γ (fobj μ-fam P (extend δ A))) A)
    (h : Mor (Fam-P.prod Γ (μ-fam P δ)) A)
    (H : (h ∘co (hasMu.inMap P δ Fam-cat.∘ Fam-P.p₂))
         ≃ (alg ∘co strong-fmor P (strong-extend-mor (λ i → Fam-P.p₂) h))) where
  private
    module InMapDef-P = InMapDef P δ
    module LambekDef-P = LambekDef P δ
    module L = Laws {n} {Γ} {A} {P} {δ} alg
  open FoldBase {n} {Γ} {A} {P} {δ}
  open Bridge {n} {Γ} {A} {P} {δ} h

  private
    sf = strong-fmor P fs
    F = fobj μ-fam P (extend δ A)
    μF = μ-fam P δ .fam

  module _ (γ : Γ .idx .Carrier) (x : T-δ.⟦ ∣ P ∣ ⟧shape (η₀ ∣ P ∣)) where
    private
      y  = LambekDef-P.u-idx (T-δ.sup x)
      x' = InMapDef-P.reindex-shape ∣ P ∣ InMapDef-P.mor₀ (InMapDef-P.embed-idx P y)
      rt : T-δ.W-≈ {Q = ∣ P ∣} {ρ = λ i → inj₁ i} (T-δ.sup x') (T-δ.sup x)
      rt = LambekDef-P.inMor-outMor .idxf-eq .func-eq {T-δ.sup x} {T-δ.sup x} (T-δ.W-≈-refl {Q = ∣ P ∣} {ρ = λ i → inj₁ i} (T-δ.sup x))
      tr : T-δ.W-≈ {Q = ∣ P ∣} {ρ = λ i → inj₁ i} (T-δ.sup x) (T-δ.sup x')
      tr = T-δ.W-≈-sym {Q = ∣ P ∣} {ρ = λ i → inj₁ i} {x = T-δ.sup x'} {y = T-δ.sup x} rt
      Hi : _≈s_ (A .idx) (h-idx γ (T-δ.sup x')) (alg .idxf .func (γ , sf .idxf .func (γ , y)))
      Hi = H .idxf-eq .func-eq {γ , y} {γ , y}
             (Γ .idx .isEquivalence .refl , fobj μ-fam P InMapDef-P.δ' .idx .isEquivalence .refl)
      ex : _≈s_ (F .idx) (apply-shape-idx P γ x) (sf .idxf .func (γ , y))
      ex = F .idx .isEquivalence .trans (apply-shape-idx-resp P (Γ .idx .isEquivalence .refl) {x} {x'} tr) (bridge-idx P γ y)

    is-idx : _≈s_ (A .idx) (h-idx γ (T-δ.sup x)) (alg .idxf .func (γ , apply-shape-idx P γ x))
    is-idx =
      A .idx .isEquivalence .trans (h-resp (Γ .idx .isEquivalence .refl) tr)
      (A .idx .isEquivalence .trans Hi
        (alg .idxf .func-resp-≈ (Γ .idx .isEquivalence .refl , F .idx .isEquivalence .sym ex)))

    private
      ι = InMapDef-P.inMor .famf .transf y
      υ = LambekDef-P.u-fam (T-δ.sup x)
      s  = μF .subst {T-δ.sup x'} {T-δ.sup x} rt
      s⁻ = μF .subst {T-δ.sup x} {T-δ.sup x'} tr
      hx' = h-fam γ (T-δ.sup x')
      asf = apply-shape-fam P γ x
      sft = sf .famf .transf (γ , y)
      algT = alg .famf .transf (γ , sf .idxf .func (γ , y))

      inv : (s ∘ (ι ∘ υ)) ≈ id _
      inv = ≈-trans (∘-cong ≈-refl (≈-sym id-left)) (LambekDef-P.inMor-outMor .famf-eq .transf-eq {T-δ.sup x})

      ιυ : (ι ∘ υ) ≈ s⁻
      ιυ = ≈-trans (≈-sym id-left) (≈-trans (∘-cong (≈-sym (fam-subst-iso₂ μF rt)) ≈-refl) (tail-cancel inv))

      ιυs : (ι ∘ (υ ∘ s)) ≈ id _
      ιυs = ≈-trans (head-cong ιυ) (fam-subst-iso₂ μF rt)

      Hf : (A .fam .subst Hi ∘ (hx' ∘ pair p₁ (ι ∘ p₂))) ≈ (algT ∘ pair p₁ sft)
      Hf = ≈-trans (∘-cong ≈-refl (≈-sym (≈-trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left)))))
           (≈-trans (H .famf-eq .transf-eq {γ , y}) id-left)

      step : (hx' ∘ prod-m (id _) s⁻)
             ≈ (A .fam .subst (A .idx .isEquivalence .sym Hi)
                ∘ (A .fam .subst (alg .idxf .func-resp-≈ (Γ .idx .isEquivalence .refl , ex))
                   ∘ (alg .famf .transf (γ , apply-shape-idx P γ x) ∘ pair p₁ asf)))
      step =
        ≈-trans (∘-cong (≈-sym (≈-trans (∘-cong ≈-refl (≈-trans (pair-cong ≈-refl (≈-trans (∘-cong ιυs ≈-refl) id-left)) pair-ext0)) id-right)) ≈-refl)
        (≈-trans (∘-cong (≈-trans (∘-cong ≈-refl (≈-sym PP))
                                  (head-cong (≈-trans (≈-sym id-left)
                                               (≈-trans (∘-cong (≈-sym (fam-subst-iso₂ (A .fam) Hi)) ≈-refl)
                                               (tail-cong Hf))))) ≈-refl)
         (≈-trans (tail-cong QQ)
          (tail-cong (≈-trans (tail-cong (≈-trans (pair-natural _ _ _)
                     (≈-trans (pair-cong (pair-p₁ _ _) sfυ)
                     (≈-trans (pair-cong (≈-sym (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left)) ≈-refl)
                              (≈-sym (pair-compose _ _ _ _))))))
                     (head-cong-assoc (alg .famf .natural (Γ .idx .isEquivalence .refl , ex)))))))
        where
          PP : (pair p₁ (ι ∘ p₂) ∘ pair p₁ ((υ ∘ s) ∘ p₂)) ≈ pair p₁ ((ι ∘ (υ ∘ s)) ∘ p₂)
          PP = ≈-trans (pair-natural _ _ _)
               (pair-cong (pair-p₁ _ _) (tail-cong-assoc (pair-p₂ _ _)))
          QQ : (pair p₁ ((υ ∘ s) ∘ p₂) ∘ prod-m (id _) s⁻) ≈ pair p₁ (υ ∘ p₂)
          QQ = ≈-trans (pair-natural _ _ _)
               (pair-cong (≈-trans (pair-p₁ _ _) id-left)
                          (≈-trans (tail-cong (pair-p₂ _ _))
                           (tail-cong (head-cancel (fam-subst-iso₁ μF rt)))))
          sfυ : (sft ∘ pair p₁ (υ ∘ p₂)) ≈ (F .fam .subst ex ∘ asf)
          sfυ = ≈-trans (∘-cong (≈-sym (bridge-fam P γ y)) ≈-refl)
                (≈-trans (tail-cong (≈-trans (tail-cong (≈-trans (pair-compose _ _ _ _)
                                                                 (pair-cong (∘-cong (≈-sym (Γ .fam .refl*))
                                                                                    ≈-refl)
                                                                            (head-cong ιυ))))
                                              (apply-shape-fam-natural P (Γ .idx .isEquivalence .refl) {x}
                                                                       {x'}
                                                                       tr)))
                         (head-cong (≈-sym (F .fam .trans* (bridge-idx P γ y)
                                             (apply-shape-idx-resp P (Γ .idx .isEquivalence .refl) {x} {x'}
                                                                   tr)))))

    is-fam : h-fam γ (T-δ.sup x)
             ≈ (A .fam .subst (A .idx .isEquivalence .sym is-idx)
                ∘ (alg .famf .transf (γ , apply-shape-idx P γ x) ∘ pair p₁ asf))
    is-fam =
      ≈-trans (≈-sym (≈-trans (∘-cong ≈-refl (prod-m-iso (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left)
                                                          (fam-subst-iso₁ μF rt)))
                              id-right))
      (≈-trans (head-cong (h .famf .natural {γ , T-δ.sup x'} {γ , T-δ.sup x}
                             (Γ .idx .isEquivalence .refl , rt)))
       (≈-trans (tail-cong step)
        (≈-trans (head-cong (≈-sym (A .fam .trans* (h-resp (Γ .idx .isEquivalence .refl) rt)
                                      (A .idx .isEquivalence .sym Hi))))
        (head-cong (≈-sym (A .fam .trans*
                            (A .idx .isEquivalence .trans (A .idx .isEquivalence .sym Hi) (h-resp (Γ .idx .isEquivalence .refl) rt))
                            (alg .idxf .func-resp-≈ (Γ .idx .isEquivalence .refl , ex))))))))

  is-fold : L.IsFold h
  is-fold .L.IsFold.is-idx = is-idx
  is-fold .L.IsFold.is-fam = is-fam

  ⦅⦆-η : h ≃ hasMu.⦅ alg ⦆
  ⦅⦆-η = L.unique h is-fold

hasMuLaws : HasMuLaws hasMu
hasMuLaws .HasMuLaws.⦅⦆-β alg = Beta.⦅⦆-β alg
hasMuLaws .HasMuLaws.⦅⦆-η alg h H = Eta.⦅⦆-η alg h H

-- The functorial action and the map between μ-carriers need a terminal object, to enter a fold
-- from the empty context.
module WithTerminal (T : HasTerminal 𝒞) where
  open HasMu.WithTerminal hasMu (terminal T) public using (fmor; μ-map)
  open HasMuLaws.WithTerminal hasMuLaws (terminal T) public
    using (fmor-cong; fmor-id; fmor-comp; fmor-const; fmor-var; fmor-+; fmor-×; fmor-μ;
           μ-map-cong; μ-map-id; μ-map-in; μ-map-comp; strong-fmor-weaken; μ-map-weaken)

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
    alg : Mor (Fam-P.prod (HasTerminal.witness (terminal T))
                (fobj μ-fam P (extend δ (μ-fam Q δ'))))
              (μ-fam Q δ')
    alg = (hasMu .HasMu.inMap Q δ' Fam-cat.∘ u) Fam-cat.∘ Fam-P.p₂
