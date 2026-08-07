{-# OPTIONS --prop --postfix-projections --safe #-}

-- Freeness of the lifting. Reading the root of a selection and dropping the root are both
-- morphisms out of a lifted order, and every morphism out of one is the sum of a constant read at
-- the root and a linear part on the payload: the assembly of branch data. The injection of P into
-- Lp P places a selection under a full root; it is a morphism, but it is not natural in P, which
-- is why the lifting has no unit and no strength.
open import Level using (0ℓ)
open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import prop using (∃ₛ) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid) renaming (_⇒_ to _⇒s_; _≃m_ to _≃s_)
open import commutative-semiring using (CommutativeSemiring)
open import basics using (IsPreorder; IsBottom)
open import categories using (Category)
open import cmon-enriched using (Biproduct)
open import lifting using (Lifting)
import matrix
import semimodule
import order-idempotent

module order-idempotent-freeness
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open matrix.Mat S using (Vec; Σ; Σ-cong; Σ-ε; Σ-unit)
open order-idempotent S ∨-idem ∧-idem ⊤-add-top
open IsPreorder L.≤-isPreorder using () renaming (refl to ≤-refl; trans to ≤-trans)
open SemiMod._⇒_
open SemiMod._≈m_

private
  cons : ∀ {n} → Setoid.Carrier A → Vec n → Vec (suc n)
  cons a u zero    = a
  cons a u (suc i) = u i

-- One position, so a selection of it is a scalar and a morphism out of it is a selection of the
-- target's positions.
𝟙p : Pos
𝟙p = disc 1

-- Discrete orders fix every vector.
disc-fixed : ∀ {n} (v : Vec n) → Fixed (disc n) v
disc-fixed v i = Σ-unit i v

-- A scalar as a selection of the one-position order.
scalar : Setoid.Carrier A → ∃ₛ (Vec 1) (Fixed 𝟙p)
scalar a = (λ _ → a) ,ₚ disc-fixed (λ _ → a)

-- Reading the root of a selection, and the payload under it: dropping the root is down-closed, so
-- both are morphisms.
tag : ∀ {P} → Lp P ⇒ 𝟙p
tag {P} .*→* ._⇒s_.func (v ,ₚ _) = scalar (head v)
tag {P} .*→* ._⇒s_.func-resp-≈ {v₁ ,ₚ _} {v₂ ,ₚ _} e i = e zero
tag {P} .preserve-ze i = refl
tag {P} .preserve-+ {u ,ₚ _} {v ,ₚ _} i = refl
tag {P} .preserve-· {s} {u ,ₚ _} i = refl

payload : ∀ {P} → Lp P ⇒ P
payload {P} .*→* ._⇒s_.func (v ,ₚ fx) = tail v ,ₚ Lp-fixed-tail P v fx
payload {P} .*→* ._⇒s_.func-resp-≈ {v₁ ,ₚ _} {v₂ ,ₚ _} e i = e (suc i)
payload {P} .preserve-ze i = refl
payload {P} .preserve-+ {u ,ₚ _} {v ,ₚ _} i = refl
payload {P} .preserve-· {s} {u ,ₚ _} i = refl

-- Selecting the root alone: a scalar becomes a root entry over an empty payload.
root : ∀ {P} → 𝟙p ⇒ Lp P
root {P} .*→* ._⇒s_.func (v ,ₚ _) =
  cons (head v) (λ _ → ε) ,ₚ
  Lp-fixed P _ (λ i → app-ε (P .ord) i)
    (≤-trans (L.≈→≤ (Σ-ε {P .dim})) (IsBottom.≤-bottom L.⊥-isBottom))
root {P} .*→* ._⇒s_.func-resp-≈ {v₁ ,ₚ _} {v₂ ,ₚ _} e = λ where
  zero    → e zero
  (suc i) → refl
root {P} .preserve-ze = λ where
  zero    → refl
  (suc i) → refl
root {P} .preserve-+ {u ,ₚ _} {v ,ₚ _} = λ where
  zero    → refl
  (suc i) → sym +-lunit
root {P} .preserve-· {s} {u ,ₚ _} = λ where
  zero    → refl
  (suc i) → sym ε-annihilᵣ

-- The injection of a position order into its lifting: the selection under a root that dominates
-- it, which its support is. It is a morphism, but at the zero morphism the two sides of the
-- naturality square differ on the root.
inj : ∀ {P} → P ⇒ Lp P
inj {P} .*→* ._⇒s_.func (v ,ₚ fx) =
  cons (supp {P .dim} v) v ,ₚ Lp-fixed P _ fx ≤-refl
inj {P} .*→* ._⇒s_.func-resp-≈ {v₁ ,ₚ _} {v₂ ,ₚ _} e = λ where
  zero    → Σ-cong e
  (suc i) → e i
inj {P} .preserve-ze = λ where
  zero    → Σ-ε {P .dim}
  (suc i) → refl
inj {P} .preserve-+ {u ,ₚ _} {v ,ₚ _} = λ where
  zero    → supp-+ u v
  (suc i) → refl
inj {P} .preserve-· {s} {u ,ₚ _} = λ where
  zero    → supp-· s u
  (suc i) → refl

-- The support of a position order: what a selection contributes to a constant.
spt-p : ∀ {P} → P ⇒ 𝟙p
spt-p {P} .*→* ._⇒s_.func (v ,ₚ _) = scalar (supp {P .dim} v)
spt-p {P} .*→* ._⇒s_.func-resp-≈ {v₁ ,ₚ _} {v₂ ,ₚ _} e i = Σ-cong e
spt-p {P} .preserve-ze i = Σ-ε {P .dim}
spt-p {P} .preserve-+ {u ,ₚ _} {v ,ₚ _} i = supp-+ u v
spt-p {P} .preserve-· {s} {u ,ₚ _} i = supp-· s u

-- A constant and a linear part assemble into a morphism out of the lifting: the constant read at
-- the root, joined with the linear part on the payload.
affine : ∀ {P C} → 𝟙p ⇒ C → P ⇒ C → Lp P ⇒ C
affine {P} {C} c M = (c ∘ tag {P}) +p (M ∘ payload {P})

affine-cong : ∀ {P C} {c c' : 𝟙p ⇒ C} {M M' : P ⇒ C} →
              c ≈p c' → M ≈p M' → affine c M ≈p affine c' M'
affine-cong {P} {C} ec eM =
  +p-cong (∘p-cong ec (≈p-refl {f = tag {P}})) (∘p-cong eM (≈p-refl {f = payload {P}}))

-- The constant a morphism out of a lifting determines, and its linear part.
tag-of : ∀ {P C} → Lp P ⇒ C → 𝟙p ⇒ C
tag-of {P} h = h ∘ root {P}

body-of : ∀ {P C} → Lp P ⇒ C → P ⇒ C
body-of {P} h = h ∘ inj {P}

root-tag : ∀ {P C} (h : Lp P ⇒ C) → (h ∘ root {P}) ≈p tag-of h
root-tag h = ≈p-refl

inj-body : ∀ {P C} (h : Lp P ⇒ C) → (h ∘ inj {P}) ≈p body-of h
inj-body h = ≈p-refl

tag-of-cong : ∀ {P C} {h k : Lp P ⇒ C} → h ≈p k → tag-of h ≈p tag-of k
tag-of-cong {P} {C} e = ∘p-cong e (≈p-refl {f = root {P}})

body-of-cong : ∀ {P C} {h k : Lp P ⇒ C} → h ≈p k → body-of h ≈p body-of k
body-of-cong {P} {C} e = ∘p-cong e (≈p-refl {f = inj {P}})

-- The root recovers the constant: the payload of a root selection is empty.
affine-root : ∀ {P C} (c : 𝟙p ⇒ C) (M : P ⇒ C) → (affine {P} c M ∘ root {P}) ≈p c
affine-root {P} {C} c M .*≈* ._≃s_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e q =
  trans (+-cong (c .func-resp-≈ (λ { zero → e zero }) q) (M .preserve-ze q))
        (trans +-comm +-lunit)

affine-tag : ∀ {P C} (c : 𝟙p ⇒ C) (M : P ⇒ C) → tag-of (affine {P} c M) ≈p c
affine-tag = affine-root

-- Every morphism out of a lifting is assembled from its own constant and linear part: the root
-- selection over the empty payload and the payload under its support sum to the selection itself,
-- since the root dominates the support. This is the extensionality law that copairing with strict
-- branch data fails: there the constant is lost.
affine-η : ∀ {P C} (h : Lp P ⇒ C) → affine (tag-of h) (body-of h) ≈p h
affine-η {P} {C} h .*≈* ._≃s_.func-eq {v₁ ,ₚ fx₁} {v₂ ,ₚ fx₂} e q =
  trans (sym (h .preserve-+ q)) (h .func-resp-≈ assemble q)
  where
  assemble : ∀ i → cons (head v₁) (λ _ → ε) i + cons (supp {P .dim} (tail v₁)) (tail v₁) i ≈ v₂ i
  assemble zero    = trans (trans +-comm (Lp-fixed-root P v₁ fx₁)) (e zero)
  assemble (suc i) = trans +-lunit (e (suc i))

-- Restricting an assembly along the injection joins the constant in over the support.
affine-inj : ∀ {P C} (c : 𝟙p ⇒ C) (M : P ⇒ C) →
             (affine {P} c M ∘ inj {P}) ≈p ((c ∘ spt-p {P}) +p M)
affine-inj {P} {C} c M .*≈* ._≃s_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e q =
  +-cong (c .func-resp-≈ (λ i → Σ-cong e) q) (M .func-resp-≈ e q)

-- Two restrictions determine a morphism out of a lifting: the root gives the constant, the payload
-- gives the linear part with the constant joined in. This is the uniqueness principle a fused
-- initial-algebra law needs, and it is why one clause along the payload alone does not suffice.
lifting-ext : ∀ {P C} (h k : Lp P ⇒ C) →
              (h ∘ root {P}) ≈p (k ∘ root {P}) → (h ∘ inj {P}) ≈p (k ∘ inj {P}) → h ≈p k
lifting-ext h k re ie =
  ≈p-trans (≈p-sym (affine-η h)) (≈p-trans (affine-cong re ie) (affine-η k))

-- A map out of a lifting whose constant vanishes is the assembly of its linear part alone, so the
-- root then determines nothing on its own. An evaluation map is of this kind: applying a function
-- determines only what the function and the argument determine, the function's own constant being
-- carried by its denotation rather than by the application.
constant-free : ∀ {P C} (h : Lp P ⇒ C) → tag-of h ≈p εp {𝟙p} {C} →
                affine (εp {𝟙p} {C}) (body-of h) ≈p h
constant-free {P} {C} h e =
  ≈p-trans (affine-cong {c = εp {𝟙p} {C}} {c' = tag-of h}
              {M = body-of h} {M' = body-of h}
              (≈p-sym e) (≈p-refl {f = body-of h}))
           (affine-η h)

-- The lifted action fixes the root: it keeps the root entry and maps the empty payload to itself.
Lp-map-root : ∀ {P Q} (f : P ⇒ Q) → ((Lp-map f) ∘ root {P}) ≈p root {Q}
Lp-map-root {P} {Q} f .*≈* ._≃s_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e = λ where
  zero    → e zero
  (suc i) → f .preserve-ze i

-- The injection and the support are natural at isomorphisms, which is all the transports along
-- bisimilarity need: an isomorphism preserves the support, by antisymmetry from the two mor-supp
-- bounds.
Lp-map-inj : ∀ {P Q} {f : P ⇒ Q} {g : Q ⇒ P} →
             (f ∘ g) ≈p id Q → (g ∘ f) ≈p id P → (Lp-map f ∘ inj {P}) ≈p (inj {Q} ∘ f)
Lp-map-inj {P} {Q} {f} {g} e₁ e₂ .*≈* ._≃s_.func-eq {v₁ ,ₚ fx₁} {v₂ ,ₚ fx₂} e = λ where
  zero    →
    trans (Σ-cong e)
          (≤-antisym
            (≤-trans (L.≈→≤ (Σ-cong (λ i → sym (e₂ .func-eq {v₂ ,ₚ fx₂} {v₂ ,ₚ fx₂} (λ j → refl) i))))
                     (mor-supp g (f .func (v₂ ,ₚ fx₂))))
            (mor-supp f (v₂ ,ₚ fx₂)))
  (suc i) → f .func-resp-≈ e i

spt-natural : ∀ {P Q} {f : P ⇒ Q} {g : Q ⇒ P} →
              (f ∘ g) ≈p id Q → (g ∘ f) ≈p id P → (spt-p {Q} ∘ f) ≈p spt-p {P}
spt-natural {P} {Q} {f} {g} e₁ e₂ .*≈* ._≃s_.func-eq {v₁ ,ₚ fx₁} {v₂ ,ₚ fx₂} e i =
  trans (Σ-cong (f .func-resp-≈ e))
        (sym (≤-antisym
               (≤-trans (L.≈→≤ (Σ-cong (λ i' → sym (e₂ .func-eq {v₂ ,ₚ fx₂} {v₂ ,ₚ fx₂} (λ j → refl) i'))))
                        (mor-supp g (f .func (v₂ ,ₚ fx₂))))
               (mor-supp f (v₂ ,ₚ fx₂))))

-- Branch data for a case: a context part, a constant, and a linear part. The constant carries no
-- context, which is forced rather than a restriction: what the root determines with nothing of the
-- context selected cannot mention the context, and context-dependence arrives through the separate
-- context factor of the biproduct.
branch : ∀ {W P C} → W ⇒ C → 𝟙p ⇒ C → P ⇒ C → (W ⊕ Lp P) ⇒ C
branch {W} {P} u c M = Biproduct.copair (biproduct W (Lp P)) u (affine c M)

branch-ι₁ : ∀ {W P C} (u : W ⇒ C) (c : 𝟙p ⇒ C) (M : P ⇒ C) →
            (branch u c M ∘ ι₁ W (Lp P)) ≈p u
branch-ι₁ {W} {P} u c M = Biproduct.copair-in₁ (biproduct W (Lp P)) u (affine c M)

branch-ι₂ : ∀ {W P C} (u : W ⇒ C) (c : 𝟙p ⇒ C) (M : P ⇒ C) →
            (branch u c M ∘ ι₂ W (Lp P)) ≈p affine c M
branch-ι₂ {W} {P} u c M = Biproduct.copair-in₂ (biproduct W (Lp P)) u (affine c M)

-- Every morphism out of a context paired with a lifting is such branch data, so the case rule loses
-- nothing: the context part, the constant and the linear part determine it.
branch-η : ∀ {W P C} (h : (W ⊕ Lp P) ⇒ C) →
           branch (h ∘ ι₁ W (Lp P)) (tag-of (h ∘ ι₂ W (Lp P))) (body-of (h ∘ ι₂ W (Lp P))) ≈p h
branch-η {W} {P} h = ≈p-trans step (Biproduct.copair-ext (biproduct W (Lp P)) h)
  where
  step : branch (h ∘ ι₁ W (Lp P)) (tag-of (h ∘ ι₂ W (Lp P))) (body-of (h ∘ ι₂ W (Lp P)))
         ≈p Biproduct.copair (biproduct W (Lp P)) (h ∘ ι₁ W (Lp P)) (h ∘ ι₂ W (Lp P))
  step = Biproduct.copair-cong (biproduct W (Lp P))
           {f₁ = h ∘ ι₁ W (Lp P)} {f₂ = h ∘ ι₁ W (Lp P)}
           {g₁ = affine (tag-of (h ∘ ι₂ W (Lp P))) (body-of (h ∘ ι₂ W (Lp P)))}
           {g₂ = h ∘ ι₂ W (Lp P)}
           (≈p-refl {f = h ∘ ι₁ W (Lp P)}) (affine-η (h ∘ ι₂ W (Lp P)))

-- The lifting as the interpretation needs it: the root supplies the constant, the injection the
-- payload, and every map out of a lifted order is its own assembly.
Lp-lifting : Lifting cmon 𝟙p
Lp-lifting .Lifting.L = Lp
Lp-lifting .Lifting.root {P} = root {P}
Lp-lifting .Lifting.inj {P} = inj {P}
Lp-lifting .Lifting.affine {P} {C} = affine {P} {C}
Lp-lifting .Lifting.affine-cong {P} {C} {c} {c'} {M} {M'} = affine-cong {P} {C} {c} {c'} {M} {M'}
Lp-lifting .Lifting.affine-root {P} {C} = affine-root {P} {C}
Lp-lifting .Lifting.affine-η {P} {C} = affine-η {P} {C}
Lp-lifting .Lifting.Lmap = Lp-map
Lp-lifting .Lifting.Lmap-cong {P} {Q} {f} {g} = Lp-map-cong {P} {Q} {f} {g}
Lp-lifting .Lifting.Lmap-id {P} = Lp-map-id P
Lp-lifting .Lifting.Lmap-comp = Lp-map-comp
Lp-lifting .Lifting.Lmap-root {P} {Q} f = Lp-map-root {P} {Q} f
Lp-lifting .Lifting.spt {P} = spt-p {P}
Lp-lifting .Lifting.affine-inj {P} {C} = affine-inj {P} {C}
Lp-lifting .Lifting.Lmap-inj {P} {Q} {f} {g} = Lp-map-inj {P} {Q} {f} {g}
Lp-lifting .Lifting.spt-natural {P} {Q} {f} {g} = spt-natural {P} {Q} {f} {g}
