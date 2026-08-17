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
         L-const; L-const-cong; L-const-natural;
         under-root; under-root-cong; under-root-natural; under-root-post; under-root-co;
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

-- The fibrewise lift of a family: same index, each fibre lifted, transports under the action.
Lf : Obj → Obj
Lf X .idx = X .idx
Lf X .fam .fm x = L (X .fam .fm x)
Lf X .fam .subst e = Lmap (X .fam .subst e)
Lf X .fam .refl* = ≈-trans (Lmap-cong (X .fam .refl*)) Lmap-id
Lf X .fam .trans* q p = ≈-trans (Lmap-cong (X .fam .trans* q p)) (Lmap-comp _ _)

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

-- The transport across the lifting as a family morphism: fibrewise under-root.
under-rootF : ∀ {Γ X Y : Obj} → Mor (Fam𝒞-P.prod Γ X) Y → Mor (Fam𝒞-P.prod Γ (Lf X)) (Lf Y)
under-rootF f .idxf = f .idxf
under-rootF f .famf ._⇒f_.transf (γ , x) = under-root (f .famf ._⇒f_.transf (γ , x))
under-rootF {Γ} {X} {Y} f .famf ._⇒f_.natural {γ₁ , x₁} {γ₂ , x₂} (γ≈ , x≈) =
  under-root-natural (Γ .fam .subst γ≈) (X .fam .subst x≈)
    (Y .fam .subst (f .idxf .prop-setoid._⇒_.func-resp-≈ (γ≈ , x≈)))
    (f .famf ._⇒f_.transf (γ₁ , x₁)) (f .famf ._⇒f_.transf (γ₂ , x₂))
    (f .famf ._⇒f_.natural (γ≈ , x≈))

under-rootF-cong : ∀ {Γ X Y : Obj} {f g : Mor (Fam𝒞-P.prod Γ X) Y} →
                   f ≃ g → under-rootF f ≃ under-rootF g
under-rootF-cong E ._≃_.idxf-eq = E ._≃_.idxf-eq
under-rootF-cong E ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , x} =
  ≈-trans (under-root-post _ _) (under-root-cong (E ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , x}))

open polynomial-functor.Interp products strongCoproducts Lf under-rootF public
  using (fobj; HasMu; HasMuLaws; _∘co_)

private
  module CME = CMonEnriched CM

-- The fibrewise action of the lifting on a family morphism.
Lf-map : ∀ {X Y : Obj} → Mor X Y → Mor (Lf X) (Lf Y)
Lf-map f .idxf = f .idxf
Lf-map f .famf ._⇒f_.transf x = Lmap (f .famf ._⇒f_.transf x)
Lf-map f .famf ._⇒f_.natural e =
  ≈-trans (≈-sym (Lmap-comp _ _)) (≈-trans (Lmap-cong (f .famf ._⇒f_.natural e)) (Lmap-comp _ _))

-- The payload injection, fibrewise.
injF : ∀ {X : Obj} → Mor X (Lf X)
injF .idxf = prop-setoid.idS _
injF {X} .famf ._⇒f_.transf x = inj
injF {X} .famf ._⇒f_.natural {x₁} {x₂} e =
  ≈-sym (Lmap-inj (X .fam .subst e))

-- A constant at every fibre, natural under the transports: what an eliminator writes when it
-- consumes a root.
record Constant (X : Obj) : Set (o ⊔ m ⊔ e ⊔ os ⊔ es) where
  field
    at         : ∀ x → 𝟙c ⇒ X .fam .fm x
    at-natural : ∀ {x₁ x₂} (e : _≈s_ (X .idx) x₁ x₂) → (X .fam .subst e ∘ at x₁) ≈ at x₂

open Constant public

-- Constants are structural: simple families are constant at any chosen morphism, and constants
-- close under the lifting, coproducts and products, with unit weight at each root the lifting
-- adjoins.
simple-constant : ∀ {A : Setoid os (os ⊔ es)} {x : obj} → (𝟙c ⇒ x) → Constant simple[ A , x ]
simple-constant c .at _ = c
simple-constant c .at-natural _ = id-left

Lf-constant : ∀ {X : Obj} → Constant X → Constant (Lf X)
Lf-constant c .at x = L-const (c .at x)
Lf-constant {X} c .at-natural e =
  ≈-trans (L-const-natural (X .fam .subst e) (c .at _)) (L-const-cong (c .at-natural e))

Lf-root : ∀ {X : Obj} → Constant (Lf X)
Lf-root .at x = root
Lf-root {X} .at-natural e = Lmap-root (X .fam .subst e)

coprod-constant : ∀ {X Y : Obj} → Constant X → Constant Y →
                  Constant (HasCoproducts.coprod coproducts X Y)
coprod-constant c d .at (inj₁ x) = c .at x
coprod-constant c d .at (inj₂ y) = d .at y
coprod-constant c d .at-natural {inj₁ _} {inj₁ _} e = c .at-natural e
coprod-constant c d .at-natural {inj₂ _} {inj₂ _} e = d .at-natural e

prod-constant : ∀ {X Y : Obj} → Constant X → Constant Y → Constant (Fam𝒞-P.prod X Y)
prod-constant c d .at (x , y) = pair (c .at x) (d .at y)
prod-constant c d .at-natural (e₁ , e₂) =
  ≈-trans (pair-compose _ _ _ _) (pair-cong (c .at-natural e₁) (d .at-natural e₂))

-- Scaling a constant by an endomorphism of the unit object.
scale-const : ∀ {X : Obj} → (𝟙c ⇒ 𝟙c) → Constant X → Constant X
scale-const w c .at x = c .at x ∘ w
scale-const w c .at-natural e =
  ≈-trans (≈-sym (assoc _ _ _)) (∘-cong (c .at-natural e) ≈-refl)

-- Eliminating a root in context: the payload continues, and the root produces the target's
-- constant.
elimF : ∀ {Γ X C : Obj} → Constant C → Mor (Fam𝒞-P.prod Γ X) C → Mor (Fam𝒞-P.prod Γ (Lf X)) C
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

-- A constant for a polynomial: one at every constant leaf.
PolyConst : ∀ {n} → Poly n → Set (o ⊔ m ⊔ e ⊔ os ⊔ es)
PolyConst (const A) = Constant A
PolyConst (var i)   = Lift (o ⊔ m ⊔ e ⊔ os ⊔ es) ⊤
PolyConst (P' + Q') = PolyConst P' ×T PolyConst Q'
PolyConst (P' × Q') = PolyConst P' ×T PolyConst Q'
PolyConst (μ P')    = PolyConst P'

-- The unit constant of a μ-carrier, by recursion over trees: constants for the polynomial and
-- the environment determine a constant at every fibre, natural in the tree, with unit weight at
-- each root.
module MuUnit {n} (δ : Fin n → Obj) (δ-const : ∀ i → Constant (δ i)) where
  open Tree δ

  DecoAssignConst : ∀ {r} → DecoAssign r → Set (o ⊔ m ⊔ e ⊔ os ⊔ es)
  DecoConst : ∀ {s} → Deco s → Set (o ⊔ m ⊔ e ⊔ os ⊔ es)
  DecoAssignConst {inj₁ _} _ = Lift (o ⊔ m ⊔ e ⊔ os ⊔ es) ⊤
  DecoAssignConst {inj₂ _} d = DecoConst d
  DecoConst (mkDeco Q d) = PolyConst Q ×T (∀ i → DecoAssignConst (d i))

  deco-ext-const : ∀ {k} (Q : Poly (Data.Nat.suc k)) {ρ̄ : Fin k → Fin n ⊎ Srt.Sort n}
                   {d : ∀ i → DecoAssign (ρ̄ i)} →
                   PolyConst Q → (∀ i → DecoAssignConst (d i)) →
                   ∀ i → DecoAssignConst (deco-ext Q d i)
  deco-ext-const Q Qc dc Fin.zero    = Qc , dc
  deco-ext-const Q Qc dc (Fin.suc i) = dc i

  mutual
    fib-unit : ∀ {k} (Q : Poly (Data.Nat.suc k)) {ρ̄ : Fin k → Fin n ⊎ Srt.Sort n}
               (d : ∀ i → DecoAssign (ρ̄ i)) → PolyConst Q → (∀ i → DecoAssignConst (d i)) →
               (t : W ∣ Q ∣ ρ̄) → 𝟙c ⇒ fib Q d t
    fib-unit Q d Qc dc (sup x) = fib-shape-unit Q (deco-ext Q d) Qc (deco-ext-const Q Qc dc) x

    fib-shape-unit : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Srt.Sort n}
                     (d : ∀ i → DecoAssign (η̄ i)) → PolyConst Q → (∀ i → DecoAssignConst (d i)) →
                     (x : ⟦ ∣ Q ∣ ⟧shape η̄) → 𝟙c ⇒ fib-shape Q d x
    fib-shape-unit (const A) d Ac dc x = Ac .at x
    fib-shape-unit (var i)   d _ dc x = fib-el-unit _ (d i) (dc i) x
    fib-shape-unit (P' + Q') d (Pc , Qc) dc (inj₁ x) = L-const (fib-shape-unit P' d Pc dc x)
    fib-shape-unit (P' + Q') d (Pc , Qc) dc (inj₂ y) = L-const (fib-shape-unit Q' d Qc dc y)
    fib-shape-unit (P' × Q') d (Pc , Qc) dc (x , y) =
      L-const (pair (fib-shape-unit P' d Pc dc x) (fib-shape-unit Q' d Qc dc y))
    fib-shape-unit (μ Q')    d Qc dc x = fib-unit Q' d Qc dc x

    fib-el-unit : ∀ (r : Fin n ⊎ Srt.Sort n) (dr : DecoAssign r) → DecoAssignConst dr →
                  (x : El r) → 𝟙c ⇒ fib-el r dr x
    fib-el-unit (inj₁ p) _ _ x = δ-const p .at x
    fib-el-unit (inj₂ _) (mkDeco Q ρd) (Qc , ρdc) x = fib-unit Q ρd Qc ρdc x

  mutual
    fib-unit-natural : ∀ {k} (Q : Poly (Data.Nat.suc k)) {ρ̄ : Fin k → Fin n ⊎ Srt.Sort n}
                       (d : ∀ i → DecoAssign (ρ̄ i)) (Qc : PolyConst Q)
                       (dc : ∀ i → DecoAssignConst (d i))
                       {t t' : W ∣ Q ∣ ρ̄} (p : W-≈ t t') →
                       (fib-subst Q d {x = t} {y = t'} p ∘ fib-unit Q d Qc dc t)
                         ≈ fib-unit Q d Qc dc t'
    fib-unit-natural Q d Qc dc {sup x} {sup y} p =
      fib-shape-unit-natural Q (deco-ext Q d) Qc (deco-ext-const Q Qc dc) p

    fib-shape-unit-natural : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Srt.Sort n}
                             (d : ∀ i → DecoAssign (η̄ i)) (Qc : PolyConst Q)
                             (dc : ∀ i → DecoAssignConst (d i))
                             {x y : ⟦ ∣ Q ∣ ⟧shape η̄} (p : shape≈ ∣ Q ∣ η̄ x y) →
                             (fib-shape-subst Q d p ∘ fib-shape-unit Q d Qc dc x)
                               ≈ fib-shape-unit Q d Qc dc y
    fib-shape-unit-natural (const A) d Ac dc p = Ac .at-natural p
    fib-shape-unit-natural (var i)   d _ dc p = fib-el-unit-natural _ (d i) (dc i) p
    fib-shape-unit-natural (P' + Q') d (Pc , Qc) dc {inj₁ _} {inj₁ _} p =
      ≈-trans (L-const-natural _ _) (L-const-cong (fib-shape-unit-natural P' d Pc dc p))
    fib-shape-unit-natural (P' + Q') d (Pc , Qc) dc {inj₂ _} {inj₂ _} p =
      ≈-trans (L-const-natural _ _) (L-const-cong (fib-shape-unit-natural Q' d Qc dc p))
    fib-shape-unit-natural (P' × Q') d (Pc , Qc) dc {_ , _} {_ , _} (p₁ , p₂) =
      ≈-trans (L-const-natural _ _)
        (L-const-cong (≈-trans (pair-compose _ _ _ _)
          (pair-cong (fib-shape-unit-natural P' d Pc dc p₁)
                     (fib-shape-unit-natural Q' d Qc dc p₂))))
    fib-shape-unit-natural (μ Q')    d Qc dc {x} {y} p =
      fib-unit-natural Q' d Qc dc {x} {y} p

    fib-el-unit-natural : ∀ (r : Fin n ⊎ Srt.Sort n) (dr : DecoAssign r)
                          (drc : DecoAssignConst dr) {x y : El r} (p : elEq r x y) →
                          (fib-el-subst r dr p ∘ fib-el-unit r dr drc x) ≈ fib-el-unit r dr drc y
    fib-el-unit-natural (inj₁ p) _ _ e = δ-const p .at-natural e
    fib-el-unit-natural (inj₂ _) (mkDeco Q ρd) (Qc , ρdc) {x} {y} e =
      fib-unit-natural Q ρd Qc ρdc {x} {y} e

  μ-unit : ∀ (P : Poly (Data.Nat.suc n)) → PolyConst P → Constant (μ-fam P δ)
  μ-unit P Pc .at t = fib-unit P (λ i → lift ttS) Pc (λ i → lift ttS) t
  μ-unit P Pc .at-natural {t} {t'} e =
    fib-unit-natural P (λ i → lift ttS) Pc (λ i → lift ttS) {t} {t'} e
