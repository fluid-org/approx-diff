{-# OPTIONS --prop --postfix-projections --safe #-}

-- The supported realisation of a position order: its selection semimodule, with the join of the
-- coordinates as the support. No morphism increases the support, so the realisation is the
-- identity on morphisms, the bound coming from the presentation. Realising a lifted order gives
-- the lift of the realisation: a selection of Lp P is exactly a scalar dominating a selection,
-- which is an element of the supported lift. This is the object-level comparison between the
-- lifting on position orders and the lifting on supported semimodules.
open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_; _×_)
open import prop using (_∧_; ∃ₛ) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category; HasTerminal; IsTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct; biproduct-iso)
open import functor using (Functor)
import matrix
import semimodule
import order-idempotent
import order-idempotent-freeness
import supported-semimod

module order-idempotent-supported
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let module S = CommutativeSemiring S)
  (∨-idem    : ∀ {x} → (x S.+ x) S.≈ x)
  (∧-idem    : ∀ {x} → (x S.· x) S.≈ x)
  (⊤-add-top : ∀ {x} → (S.ι S.+ x) S.≈ S.ι)
  where

module M = matrix.Mat S
module OI = order-idempotent S ∨-idem ∧-idem ⊤-add-top
module OF = order-idempotent-freeness S ∨-idem ∧-idem ⊤-add-top
module SemiMod = semimodule S
module SS = supported-semimod S ∨-idem

open OI using (Pos; dim; ord; Lp)
open SemiMod using (Semimodule; 𝕀; _⇒_)
open Semimodule
open SemiMod._⇒_
open SemiMod._≈m_

-- The support of a selection: the join of the coordinates, linear by the Σ laws.
supp-𝓥 : ∀ P → OI.𝒟 P ⇒ 𝕀
supp-𝓥 P .*→* .prop-setoid._⇒_.func (u ,ₚ _) = OI.supp {P .dim} u
supp-𝓥 P .*→* .prop-setoid._⇒_.func-resp-≈ {u ,ₚ _} {v ,ₚ _} e = M.Σ-cong e
supp-𝓥 P .preserve-ze = M.Σ-ε {P .dim}
supp-𝓥 P .preserve-+ {u ,ₚ _} {v ,ₚ _} = OI.supp-+ u v
supp-𝓥 P .preserve-· {s} {u ,ₚ _} = OI.supp-· s u

-- The supported object of a position order.
𝓥 : Pos → SS.Sup.Obj
𝓥 P .SS.Sup.carrier = OI.𝒟 P
𝓥 P .SS.Sup.supp = supp-𝓥 P

private
  cons : ∀ {n} → Setoid.Carrier A → M.Vec n → M.Vec (suc n)
  cons a u zero    = a
  cons a u (suc i) = u i

-- Realising a lifted order is lifting the realisation: head and tail against pairing.
𝓥-Lp-fwd : ∀ P → SS.Sup.Mor (𝓥 (Lp P)) (SS.Ls (𝓥 P))
𝓥-Lp-fwd P .SS.Sup.mor .*→* .prop-setoid._⇒_.func (v ,ₚ fx) =
  (v zero , (OI.tail v ,ₚ OI.Lp-fixed-tail P v fx)) ,ₚ OI.Lp-fixed-root P v fx
𝓥-Lp-fwd P .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ e = e zero ,ₚ λ i → e (suc i)
𝓥-Lp-fwd P .SS.Sup.mor .preserve-ze = S.refl ,ₚ λ i → S.refl
𝓥-Lp-fwd P .SS.Sup.mor .preserve-+ = S.refl ,ₚ λ i → S.refl
𝓥-Lp-fwd P .SS.Sup.mor .preserve-· = S.refl ,ₚ λ i → S.refl
𝓥-Lp-fwd P .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e =
  S.trans (OI.L.Σ-ub v₁ zero) (M.Σ-cong e)

𝓥-Lp-bwd : ∀ P → SS.Sup.Mor (SS.Ls (𝓥 P)) (𝓥 (Lp P))
𝓥-Lp-bwd P .SS.Sup.mor .*→* .prop-setoid._⇒_.func ((a , (u ,ₚ fu)) ,ₚ dom) =
  cons a u ,ₚ OI.Lp-fixed P (cons a u) fu dom
𝓥-Lp-bwd P .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ (e₁ ,ₚ e₂) = λ where
  zero    → e₁
  (suc i) → e₂ i
𝓥-Lp-bwd P .SS.Sup.mor .preserve-ze = λ where
  zero    → S.refl
  (suc i) → S.refl
𝓥-Lp-bwd P .SS.Sup.mor .preserve-+ = λ where
  zero    → S.refl
  (suc i) → S.refl
𝓥-Lp-bwd P .SS.Sup.mor .preserve-· = λ where
  zero    → S.refl
  (suc i) → S.refl
𝓥-Lp-bwd P .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq
    {(a₁ , (u₁ ,ₚ _)) ,ₚ _} {(a₂ , (u₂ ,ₚ _)) ,ₚ dom₂} (e₁ ,ₚ e₂) =
  S.trans S.+-comm
  (S.trans (S.sym S.+-assoc)
  (S.trans (S.+-cong ∨-idem S.refl)
  (S.trans S.+-comm
  (S.trans (S.+-cong (M.Σ-cong e₂) e₁) dom₂))))

𝓥-Lp-iso : ∀ P → Category.Iso SS.Sup.cat (𝓥 (Lp P)) (SS.Ls (𝓥 P))
𝓥-Lp-iso P .Category.Iso.fwd = 𝓥-Lp-fwd P
𝓥-Lp-iso P .Category.Iso.bwd = 𝓥-Lp-bwd P
𝓥-Lp-iso P .Category.Iso.fwd∘bwd≈id .*≈* .prop-setoid._≃m_.func-eq e = e
𝓥-Lp-iso P .Category.Iso.bwd∘fwd≈id .*≈* .prop-setoid._≃m_.func-eq e = λ where
  zero    → e zero
  (suc i) → e (suc i)

-- The realised morphism is the morphism itself; the bound is the support theorem.
𝓥₁ : ∀ {P Q} → P OI.⇒ Q → SS.Sup.Mor (𝓥 P) (𝓥 Q)
𝓥₁ {P} {Q} f .SS.Sup.mor = f
𝓥₁ {P} {Q} f .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ fx₁} {v₂ ,ₚ _} e =
  S.trans (OI.mor-supp f (v₁ ,ₚ fx₁)) (M.Σ-cong e)

-- The one-position order realises as the scalars.
ι1-fwd : SS.Sup.Mor (𝓥 OF.𝟙p) SS.𝟙s
ι1-fwd .SS.Sup.mor .*→* .prop-setoid._⇒_.func (v ,ₚ _) = v zero
ι1-fwd .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ e = e zero
ι1-fwd .SS.Sup.mor .preserve-ze = S.refl
ι1-fwd .SS.Sup.mor .preserve-+ = S.refl
ι1-fwd .SS.Sup.mor .preserve-· = S.refl
ι1-fwd .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e =
  S.trans (S.sym S.+-assoc)
          (S.trans (S.+-cong ∨-idem S.refl) (S.+-cong (e zero) S.refl))

ι1-bwd : SS.Sup.Mor SS.𝟙s (𝓥 OF.𝟙p)
ι1-bwd .SS.Sup.mor .*→* .prop-setoid._⇒_.func s = OF.scalar s
ι1-bwd .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ e i = e
ι1-bwd .SS.Sup.mor .preserve-ze i = S.refl
ι1-bwd .SS.Sup.mor .preserve-+ i = S.refl
ι1-bwd .SS.Sup.mor .preserve-· i = S.refl
ι1-bwd .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq e =
  S.trans (S.+-cong (S.trans (S.+-cong S.refl (M.Σ-ε {0})) (S.trans S.+-comm S.+-lunit)) S.refl)
          (S.trans ∨-idem e)

private
  module SC = Category SS.Sup.cat

-- The comparison intertwines the two liftings: the root, the injection and the assembly on
-- position orders realise as those of the supported lift.
root-intertwine : ∀ P →
  SC._≈_ (SC._∘_ (𝓥-Lp-iso P .Category.Iso.fwd) (𝓥₁ (OF.root {P})))
         (SC._∘_ (SS.root-s {𝓥 P}) ι1-fwd)
root-intertwine P .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e =
  e zero ,ₚ λ i → S.refl

inj-intertwine : ∀ P →
  SC._≈_ (SC._∘_ (𝓥-Lp-iso P .Category.Iso.fwd) (𝓥₁ (OF.inj {P})))
         (SS.inj-s {𝓥 P})
inj-intertwine P .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e =
  M.Σ-cong e ,ₚ e

affine-intertwine : ∀ {P C} (c : OF.𝟙p OI.⇒ C) (Mm : P OI.⇒ C) →
  SC._≈_ (SC._∘_ (𝓥₁ (OF.affine {P} {C} c Mm)) (𝓥-Lp-iso P .Category.Iso.bwd))
         (SS.affine-s (SC._∘_ (𝓥₁ c) ι1-bwd) (𝓥₁ Mm))
affine-intertwine {P} {C} c Mm .*≈* .prop-setoid._≃m_.func-eq
    {(a₁ , (u₁ ,ₚ _)) ,ₚ _} {(a₂ , (u₂ ,ₚ _)) ,ₚ _} (e₁ ,ₚ e₂) q =
  S.+-cong (c .func-resp-≈ (λ i → e₁) q) (Mm .func-resp-≈ e₂ q)

-- The lifted action also intertwines: both sides keep the root and map the payload.
Lmap-intertwine : ∀ {P Q} (f : P OI.⇒ Q) →
  SC._≈_ (SC._∘_ (𝓥-Lp-iso Q .Category.Iso.fwd) (𝓥₁ (OI.Lp-map f)))
         (SC._∘_ (SS.Lmap-s (𝓥₁ f)) (𝓥-Lp-iso P .Category.Iso.fwd))
Lmap-intertwine {P} {Q} f .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e =
  e zero ,ₚ f .func-resp-≈ (λ i → e (suc i))

-- The realisation packaged as a functor: the identity on morphisms.
𝓥F : Functor OI.cat SS.Sup.cat
𝓥F .Functor.fobj = 𝓥
𝓥F .Functor.fmor = 𝓥₁
𝓥F .Functor.fmor-cong h = h
𝓥F .Functor.fmor-id {P} = OI.≈p-refl {f = OI.id P}
𝓥F .Functor.fmor-comp f g = OI.≈p-refl {f = OI._∘_ f g}

-- The empty order realises as the terminal supported object.
Sup-terminal : HasTerminal SS.Sup.cat
Sup-terminal = SS.Sup.terminal-s SemiMod.terminal

private
  module MC = Category SemiMod.cat
  T𝟘 = SemiMod.terminal .HasTerminal.witness
  to-T : ∀ (X : Semimodule) → X ⇒ T𝟘
  to-T X = SemiMod.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal {X}

𝓥-𝟘-fwd : SS.Sup.Mor (𝓥 OI.𝟘p) (Sup-terminal .HasTerminal.witness)
𝓥-𝟘-fwd .SS.Sup.mor = to-T (OI.𝒟 OI.𝟘p)
𝓥-𝟘-fwd .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq e = S.+-lunit

𝓥-𝟘-bwd : SS.Sup.Mor (Sup-terminal .HasTerminal.witness) (𝓥 OI.𝟘p)
𝓥-𝟘-bwd .SS.Sup.mor .*→* .prop-setoid._⇒_.func _ = (λ ()) ,ₚ λ ()
𝓥-𝟘-bwd .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ _ = λ ()
𝓥-𝟘-bwd .SS.Sup.mor .preserve-ze = λ ()
𝓥-𝟘-bwd .SS.Sup.mor .preserve-+ = λ ()
𝓥-𝟘-bwd .SS.Sup.mor .preserve-· = λ ()
𝓥-𝟘-bwd .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq e = S.+-lunit

𝓥-𝟘-iso : Category.Iso SS.Sup.cat (𝓥 OI.𝟘p) (Sup-terminal .HasTerminal.witness)
𝓥-𝟘-iso .Category.Iso.fwd = 𝓥-𝟘-fwd
𝓥-𝟘-iso .Category.Iso.bwd = 𝓥-𝟘-bwd
𝓥-𝟘-iso .Category.Iso.fwd∘bwd≈id =
  MC.≈-trans (MC.≈-sym (SemiMod.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext _))
             (SemiMod.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext _)
𝓥-𝟘-iso .Category.Iso.bwd∘fwd≈id .*≈* .prop-setoid._≃m_.func-eq e = λ ()

private
  module SCM = CMonEnriched SS.Sup.cmon

-- The realisation is additive on the nose.
𝓥-additive : ∀ {P Q} (f g : P OI.⇒ Q) →
             SC._≈_ (𝓥₁ (OI._+p_ f g)) (SCM._+m_ (𝓥₁ f) (𝓥₁ g))
𝓥-additive f g = OI.≈p-refl {f = OI._+p_ f g}

𝓥-zero : ∀ {P Q} → SC._≈_ (𝓥₁ (OI.εp {P} {Q})) (SCM.εm {𝓥 P} {𝓥 Q})
𝓥-zero {P} {Q} = OI.≈p-refl {f = OI.εp {P} {Q}}

-- The realised biproduct structure on the realisation of a block order: the laws are those of the
-- position-order biproduct.
𝓥-image-biproduct : ∀ P Q → Biproduct SS.Sup.cmon (𝓥 P) (𝓥 Q)
𝓥-image-biproduct P Q .Biproduct.prod = 𝓥 (P OI.⊕ Q)
𝓥-image-biproduct P Q .Biproduct.p₁ = 𝓥₁ (OI.π₁ P Q)
𝓥-image-biproduct P Q .Biproduct.p₂ = 𝓥₁ (OI.π₂ P Q)
𝓥-image-biproduct P Q .Biproduct.in₁ = 𝓥₁ (OI.ι₁ P Q)
𝓥-image-biproduct P Q .Biproduct.in₂ = 𝓥₁ (OI.ι₂ P Q)
𝓥-image-biproduct P Q .Biproduct.id-1 = OI.biproduct P Q .Biproduct.id-1
𝓥-image-biproduct P Q .Biproduct.id-2 = OI.biproduct P Q .Biproduct.id-2
𝓥-image-biproduct P Q .Biproduct.zero-1 = OI.biproduct P Q .Biproduct.zero-1
𝓥-image-biproduct P Q .Biproduct.zero-2 = OI.biproduct P Q .Biproduct.zero-2
𝓥-image-biproduct P Q .Biproduct.id-+ = OI.biproduct P Q .Biproduct.id-+

-- The chosen supported biproducts, and the canonical comparison with the realised structure.
Sup-biproduct : ∀ X Y → Biproduct SS.Sup.cmon X Y
Sup-biproduct = SS.Sup.biproduct-s SemiMod.biproduct

𝓥-⊕-iso : ∀ P Q → Category.Iso SS.Sup.cat (𝓥 (P OI.⊕ Q))
                    (Biproduct.prod (Sup-biproduct (𝓥 P) (𝓥 Q)))
𝓥-⊕-iso P Q =
  SC.IsIso→Iso (biproduct-iso SS.Sup.cmon (𝓥-image-biproduct P Q) (Sup-biproduct (𝓥 P) (𝓥 Q)))

-- Both sides of the model carry the fused fold: the position orders and their supported
-- realisations instantiate the engine.
import lifting-fold
module PosFold = lifting-fold OI.cmon OI.biproduct OF.Lp-lifting
module SupFold = lifting-fold SS.Sup.cmon Sup-biproduct SS.supported-lifting
