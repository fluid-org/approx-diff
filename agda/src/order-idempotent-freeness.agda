{-# OPTIONS --prop --postfix-projections --safe #-}

-- Freeness of the lifting. A morphism out of Lp P is exactly a constant together with a linear
-- part above it: the root column records what the root alone determines, and absorption puts that
-- column below every other one, since the root is an ancestor of every position. So the maps out of
-- a lifting are the join-preserving maps out of P that need not preserve the empty selection, with
-- the constant as the image of the empty selection. The injection of P into Lp P is a morphism, but
-- it is not natural in P, which is why the lifting has no unit and no strength.
open import Level using (0ℓ)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import basics using (IsPreorder; IsTop)
open import cmon-enriched using (Biproduct)
import matrix
import order-idempotent

module order-idempotent-freeness
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open matrix.Mat S using (Matrix; _≈ₘ_; Σ; Σ-cong; Σ-ε; Σ-+; Σ-·-distribₗ; ∘-cong; id-right)
  renaming (_∘_ to _∘ₘ_)
open order-idempotent S ∨-idem ∧-idem ⊤-add-top
open IsPreorder L.≤-isPreorder using () renaming (trans to ≤-trans)

-- One position, so a morphism out of it is a selection of the target's positions.
𝟙p : Pos
𝟙p = disc 1

-- Each column of an order matrix joins to ι, by reflexivity and topness of ι.
col-ι : ∀ (P : Pos) (p : Fin (P .dim)) → Σ {P .dim} (λ p' → P .ord p' p) ≈ ι
col-ι P p =
  ≤-antisym (IsTop.≤-top L.⊤-isTop)
            (≤-trans (L.≈→≤ (sym (≤-antisym (IsTop.≤-top L.⊤-isTop) (P .ord-refl p))))
                     (L.Σ-ub (λ p' → P .ord p' p) p))

const-col : ∀ (P : Pos) (x : Setoid.Carrier A) (p : Fin (P .dim)) →
            Σ {P .dim} (λ p' → x · P .ord p' p) ≈ x
const-col P x p =
  trans (sym (Σ-·-distribₗ x (λ p' → P .ord p' p)))
        (trans (·-cong refl (col-ι P p)) (trans ·-comm ·-lunit))

-- The root column of a morphism out of a lifting: what the root alone determines.
tag-mat : ∀ {P C} → Lp P ⇒ C → Matrix (C .dim) 1
tag-mat h q _ = h .mat q zero

tag-of : ∀ {P C} → Lp P ⇒ C → 𝟙p ⇒ C
tag-of h .mat = tag-mat h
tag-of {P} {C} h .absorbed =
  ≈ₘ-trans (id-right {M = C .ord ∘ₘ tag-mat h}) (λ q j → absorb-left h q zero)

-- Absorption puts the root column below every other column.
tag-below : ∀ {P C} (h : Lp P ⇒ C) (q : Fin (C .dim)) (p : Fin (P .dim)) →
            h .mat q zero L.≤ h .mat q (suc p)
tag-below {P} {C} h q p =
  ≤-trans (L.≈→≤ (sym (trans ·-comm ·-lunit)))
  (≤-trans (L.Σ-ub (λ k → h .mat q k · Lp P .ord k (suc p)) zero)
           (L.≈→≤ (absorb-right h q (suc p))))

-- The linear part, on the positions of P.
body-mat : ∀ {P C} → Lp P ⇒ C → Matrix (C .dim) (P .dim)
body-mat h q p = h .mat q (suc p)

body-of : ∀ {P C} → Lp P ⇒ C → P ⇒ C
body-of h .mat = body-mat h
body-of {P} {C} h .absorbed =
  ≈ₘ-trans (∘-cong left (≈ₘ-refl {M = P .ord})) right
  where
  left : (C .ord ∘ₘ body-mat h) ≈ₘ body-mat h
  left q p = absorb-left h q (suc p)

  -- The root column is below the p-th column, which the diagonal of P's order carries into the sum,
  -- so it is absorbed and only the linear part survives.
  below : ∀ q p → (h .mat q zero · ι) L.≤ (body-mat h ∘ₘ P .ord) q p
  below q p =
    ≤-trans (L.≈→≤ (trans ·-comm ·-lunit))
    (≤-trans (tag-below h q p)
    (≤-trans (L.≈→≤ (sym (trans ·-comm ·-lunit)))
    (≤-trans (L.∧-monoʳ (P .ord-refl p))
             (L.Σ-ub (λ p' → h .mat q (suc p') · P .ord p' p) p))))

  right : (body-mat h ∘ₘ P .ord) ≈ₘ body-mat h
  right q p = trans (sym (below q p)) (absorb-right h q (suc p))

-- A constant and a linear part assemble into a morphism out of the lifting: the root column is the
-- constant, and every other column joins it with the linear part, as absorption requires.
affine-mat : ∀ {P C} → 𝟙p ⇒ C → P ⇒ C → Matrix (C .dim) (suc (P .dim))
affine-mat c M q zero    = c .mat q zero
affine-mat c M q (suc p) = c .mat q zero + M .mat q p

affine : ∀ {P C} → 𝟙p ⇒ C → P ⇒ C → Lp P ⇒ C
affine c M .mat = affine-mat c M
affine {P} {C} c M .absorbed = ≈ₘ-trans (∘-cong left (≈ₘ-refl {M = Lp P .ord})) right
  where
  left : (C .ord ∘ₘ affine-mat c M) ≈ₘ affine-mat c M
  left q zero    = absorb-left c q zero
  left q (suc p) =
    trans (Σ-cong {C .dim} (λ r → ·-+-distribₗ))
    (trans (sym (Σ-+ (λ r → C .ord q r · c .mat r zero) (λ r → C .ord q r · M .mat r p)))
           (+-cong (absorb-left c q zero) (absorb-left M q p)))

  right : (affine-mat c M ∘ₘ Lp P .ord) ≈ₘ affine-mat c M
  right q zero =
    trans (+-cong (trans ·-comm ·-lunit)
                  (trans (Σ-cong {P .dim} (λ p' → ε-annihilᵣ)) (Σ-ε {P .dim})))
          (trans +-comm +-lunit)
  right q (suc p) =
    trans (+-cong (trans ·-comm ·-lunit) (Σ-cong {P .dim} (λ p' → ·-+-distribᵣ)))
    (trans (+-cong refl
             (sym (Σ-+ (λ p' → c .mat q zero · P .ord p' p)
                       (λ p' → M .mat q p' · P .ord p' p))))
    (trans (+-cong refl (+-cong (const-col P (c .mat q zero) p) (absorb-right M q p)))
    (trans (sym +-assoc) (+-cong ∨-idem refl))))

affine-tag : ∀ {P C} (c : 𝟙p ⇒ C) (M : P ⇒ C) → tag-of (affine {P} c M) ≈p c
affine-tag c M q zero = refl

-- The linear part read back is the constant joined with the one supplied, so the two agree exactly
-- when the constant is already below every column.
affine-body : ∀ {P C} (c : 𝟙p ⇒ C) (M : P ⇒ C) →
              (∀ q p → c .mat q zero L.≤ M .mat q p) → body-of (affine {P} c M) ≈p M
affine-body c M below q p = below q p

-- Every morphism out of a lifting is assembled from its own constant and linear part, so the two
-- constructions are inverse. This is the extensionality law that copairing with strict branch data
-- fails: there the constant is lost.
affine-η : ∀ {P C} (h : Lp P ⇒ C) → affine (tag-of h) (body-of h) ≈p h
affine-η h q zero    = refl
affine-η h q (suc p) = tag-below h q p

-- The injection of a position order into its lifting. It is a morphism, sending the empty selection
-- to itself, but it is not natural in P: at the zero morphism the two sides of the naturality square
-- differ on the root row.
inj-mat : ∀ (P : Pos) → Matrix (suc (P .dim)) (P .dim)
inj-mat P zero    p = ι
inj-mat P (suc q) p = P .ord q p

inj : ∀ {P} → P ⇒ Lp P
inj {P} .mat = inj-mat P
inj {P} .absorbed = ≈ₘ-trans (∘-cong left (≈ₘ-refl {M = P .ord})) right
  where
  left : (Lp P .ord ∘ₘ inj-mat P) ≈ₘ inj-mat P
  left zero    p = trans (+-cong ·-lunit refl) ⊤-add-top
  left (suc q) p = trans (+-cong ε-annihilₗ refl) (trans +-lunit (ord-idem P q p))

  right : (inj-mat P ∘ₘ P .ord) ≈ₘ inj-mat P
  right zero    p = const-col P ι p
  right (suc q) p = ord-idem P q p

-- Restricting an assembled morphism along the injection recovers the linear part with the constant
-- joined in, which is the branch's affine map on non-empty selections. This is the computation law
-- for a case on a known constructor.
affine-inj : ∀ {P C} (c : 𝟙p ⇒ C) (M : P ⇒ C) →
             (affine {P} c M ∘ inj) ≈p body-of (affine {P} c M)
affine-inj {P} {C} c M q p =
  trans (+-cong (trans ·-comm ·-lunit)
                (Σ-cong {P .dim} (λ p' → ·-+-distribᵣ)))
  (trans (+-cong refl
           (sym (Σ-+ (λ p' → c .mat q zero · P .ord p' p)
                     (λ p' → M .mat q p' · P .ord p' p))))
  (trans (+-cong refl (+-cong (const-col P (c .mat q zero) p) (absorb-right M q p)))
         (trans (sym +-assoc) (+-cong ∨-idem refl))))

tag-of-cong : ∀ {P C} {h k : Lp P ⇒ C} → h ≈p k → tag-of h ≈p tag-of k
tag-of-cong e q j = e q zero

body-of-cong : ∀ {P C} {h k : Lp P ⇒ C} → h ≈p k → body-of h ≈p body-of k
body-of-cong e q p = e q (suc p)

affine-cong : ∀ {P C} {c c' : 𝟙p ⇒ C} {M M' : P ⇒ C} →
              c ≈p c' → M ≈p M' → affine c M ≈p affine c' M'
affine-cong ec eM q zero    = ec q zero
affine-cong ec eM q (suc p) = +-cong (ec q zero) (eM q p)

-- A map out of a lifting whose constant vanishes is the assembly of its linear part alone, so the
-- root then determines nothing on its own. An evaluation map is of this kind: applying a function
-- determines only what the function and the argument determine, the function's own constant being
-- carried by its denotation rather than by the application.
constant-free : ∀ {P C} (h : Lp P ⇒ C) → tag-of h ≈p εp {𝟙p} {C} →
                affine (εp {𝟙p} {C}) (body-of h) ≈p h
constant-free h e =
  ≈ₘ-trans (affine-cong {c = εp {𝟙p} {_}} {c' = tag-of h}
              {M = body-of h} {M' = body-of h}
              (≈ₘ-sym e) (≈ₘ-refl {M = body-of h .mat}))
           (affine-η h)

-- Selecting the root alone. Composing with it reads off the constant, so a morphism out of a
-- lifting is determined by its behaviour on the root and on the payload.
root-mat : ∀ (P : Pos) → Matrix (suc (P .dim)) 1
root-mat P zero    _ = ι
root-mat P (suc q) _ = ε

root : ∀ {P} → 𝟙p ⇒ Lp P
root {P} .mat = root-mat P
root {P} .absorbed = ≈ₘ-trans (id-right {M = Lp P .ord ∘ₘ root-mat P}) left
  where
  left : (Lp P .ord ∘ₘ root-mat P) ≈ₘ root-mat P
  left zero    j = trans (+-cong ·-lunit refl) ⊤-add-top
  left (suc q) j =
    trans (+-cong ε-annihilₗ
            (trans (Σ-cong {P .dim} (λ q' → ε-annihilᵣ)) (Σ-ε {P .dim})))
          +-lunit

root-tag : ∀ {P C} (h : Lp P ⇒ C) → (h ∘ root {P}) ≈p tag-of h
root-tag {P} h q j =
  trans (+-cong (trans ·-comm ·-lunit)
                (trans (Σ-cong {P .dim} (λ p → ε-annihilᵣ)) (Σ-ε {P .dim})))
        (trans +-comm +-lunit)

inj-body : ∀ {P C} (h : Lp P ⇒ C) → (h ∘ inj {P}) ≈p body-of h
inj-body {P} h q p =
  trans (+-cong (trans ·-comm ·-lunit) (absorb-right (body-of h) q p)) (tag-below h q p)

-- Two restrictions determine a morphism out of a lifting: the root gives the constant, the payload
-- gives the linear part with the constant joined in. This is the uniqueness principle a fused
-- initial-algebra law needs, and it is why one clause along the payload alone does not suffice.
lifting-ext : ∀ {P C} (h k : Lp P ⇒ C) →
              (h ∘ root {P}) ≈p (k ∘ root {P}) → (h ∘ inj {P}) ≈p (k ∘ inj {P}) → h ≈p k
lifting-ext h k re ie q zero =
  trans (sym (root-tag h q zero)) (trans (re q zero) (root-tag k q zero))
lifting-ext h k re ie q (suc p) =
  trans (sym (inj-body h q p)) (trans (ie q p) (inj-body k q p))

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
branch-η {W} {P} h = ≈ₘ-trans step (Biproduct.copair-ext (biproduct W (Lp P)) h)
  where
  step : branch (h ∘ ι₁ W (Lp P)) (tag-of (h ∘ ι₂ W (Lp P))) (body-of (h ∘ ι₂ W (Lp P)))
         ≈p Biproduct.copair (biproduct W (Lp P)) (h ∘ ι₁ W (Lp P)) (h ∘ ι₂ W (Lp P))
  step = Biproduct.copair-cong (biproduct W (Lp P))
           {f₁ = h ∘ ι₁ W (Lp P)} {f₂ = h ∘ ι₁ W (Lp P)}
           {g₁ = affine (tag-of (h ∘ ι₂ W (Lp P))) (body-of (h ∘ ι₂ W (Lp P)))}
           {g₂ = h ∘ ι₂ W (Lp P)}
           (≈ₘ-refl {M = (h ∘ ι₁ W (Lp P)) .mat}) (affine-η (h ∘ ι₂ W (Lp P)))
