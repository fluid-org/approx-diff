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

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Nat using (suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤) renaming (tt to ttS)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import commutative-monoid using (CommutativeMonoid)
import lifting
open import prop-setoid using (IsEquivalence; Setoid; module ≈-Reasoning)
open import indexed-family using (Fam; _⇒f_)
import fam
import fam-functor
open import functor using (StrongFunctor)
import polynomial-functor
import fam-mu-lifting.sort
import fam-mu-lifting.fibre

module fam-mu-lifting.carrier {o m e} (os es : Level) {𝒞 : Category o m e}
    (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    (𝟙c : Category.obj 𝒞) where

open Category 𝒞 public
open IsEquivalence public

P : HasProducts 𝒞
P = biproducts→products CM BP

open HasProducts P public

private
  module Lc = lifting CM BP 𝟙c
open Lc public
  using (L; root; inj; copair-root; copair-inj; lifting-ext;
         Lmap; Lmap-cong; Lmap-id; Lmap-comp; Lmap-root; Lmap-inj;
         L-elem; L-elem-cong; L-elem-natural;
         strong-Lmap; strong-Lmap-cong; strong-Lmap-natural; strong-Lmap-pre; strong-Lmap-post; strong-Lmap-co; strong-Lmap-p₂;
         elim-root; elim-root-cong; elim-root-natural)
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
module Srt = fam-mu-lifting.sort os es
open Srt public using (Sort; mkSort)
open fam-mu-lifting.fibre os es CM BP 𝟙c public using (Idx; ∣_∣; module Fibre; μ-fam)

-- The lifting on families: the fibrewise strong endofunctor induced by the lifting.
private
  LfS : StrongFunctor products
  LfS = fam-functor.FamF-strong os (os ⊔ es) P Lc.L-strong
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
  μ-section P Pc .at t = fib-unit P (λ i → lift ttS) Pc (λ i → lift ttS) t
  μ-section P Pc .at-natural {t} {t'} e =
    fib-unit-natural P (λ i → lift ttS) Pc (λ i → lift ttS) {t} {t'} e
