{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- HasMu instance for the Fam construction, against the polynomial-functor-2
-- interface (n-ary kinding contexts + nested μ). Builds initial algebras
-- (μ-types) for polynomial functors over Fam(𝒞) using setoid-indexed W-types.
--
-- Successor to fam-mu-types, which targets the single-variable, μ-free
-- polynomial-functor interface; that module is retained for reference.
--
-- Abbott, Altenkirch, Ghani. Containers: constructing strictly positive types. TCS 342(1), 2005.
-- Abbott, Altenkirch, Ghani. Representing nested inductive types using W-types. ICALP 2004.
-- Emmenegger. W-types in setoids. arXiv:1809.02375, 2018.
------------------------------------------------------------------------------

open import Level using (_⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_; tt)
open import Data.Unit using (tt) renaming (⊤ to 𝟙S)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts; strong-coproducts→coproducts;
         coKleisli-prod)
open import prop-setoid as PS
  using (IsEquivalence; Setoid; module ≈-Reasoning)
open import indexed-family using (Fam; _⇒f_; changeCat)
import fam
import polynomial-functor-2

open Setoid using (Carrier; isEquivalence) renaming (_≈_ to _≈s_)

module fam-mu-types-2 where

------------------------------------------------------------------------------
-- HasMu instance for the Fam construction.
module WFam {o m e} (os es : _) {𝒞 : Category o m e} (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where
  open Category 𝒞
  open IsEquivalence
  open HasTerminal
  open HasProducts P
  open fam.CategoryOfFamilies os (os ⊔ es) 𝒞
  open Obj
  open Mor
  open Fam
  private module Fam𝒞 = Category cat
  open products P  -- Fam-level products
  private module Fam𝒞-P = HasProducts products
  open _⇒f_
  open polynomial-functor-2 (terminal T) products strongCoproducts
    using (Poly; const; var; _+_; _×_; μ; extend; fobj; HasMu; HasMuLaws)

  open import Data.Sum using (_⊎_)
  open import Data.Product using () renaming (_×_ to _×T_)
  open import prop using (_∧_; ⊥)

  ------------------------------------------------------------------------------
  -- Indexed-W encoding of (nested) μ. A `Sort` is a defunctionalised μ-binder: a
  -- μ-body `Q` together with a resolution of each of its free variables to either
  -- an ambient parameter slot (Fin n) or another sort. The whole nested polynomial
  -- becomes one family indexed by `Sort`, tying the outer/inner-μ knot inductively
  -- rather than through a recursive environment of types.
  data Sort (n : ℕ) : Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    mkSort : ∀ {k} → Poly (suc k) → (Fin k → Fin n ⊎ Sort n) → Sort n

  -- Abstract the freshly-bound recursion variable (slot 0 of a suc-n context) into
  -- a given sort, contracting the context to n. Used to translate `fobj`'s nested
  -- μ (recursion-as-parameter) into our representation (recursion-as-sort).
  mutual
    abs-ref : ∀ {n} → Sort n → Fin (suc n) ⊎ Sort (suc n) → Fin n ⊎ Sort n
    abs-ref rec (inj₁ Fin.zero)    = inj₂ rec
    abs-ref rec (inj₁ (Fin.suc i)) = inj₁ i
    abs-ref rec (inj₂ s)           = inj₂ (abs-sort rec s)

    abs-sort : ∀ {n} → Sort n → Sort (suc n) → Sort n
    abs-sort rec (mkSort R ρ) = mkSort R (λ i → abs-ref rec (ρ i))

  -- The carrier of the μ-type: trees indexed by sort. `⟦_⟧shape` interprets a body
  -- into a Set, resolving variables through `El`; nested μ lands at a fresh sort. The
  -- three are mutually recursive (induction-recursion), with `W` strictly positive.
  module Tree {n} (δ : Fin n → Obj) where
    mutual
      data W {k} (Q : Poly (suc k)) (ρ : Fin k → Fin n ⊎ Sort n) : Set os where
        sup : ⟦ Q ⟧shape (extend ρ (inj₂ (mkSort Q ρ))) → W Q ρ

      ⟦_⟧shape : ∀ {k} → Poly k → (Fin k → Fin n ⊎ Sort n) → Set os
      ⟦ const A ⟧shape η = A .idx .Carrier
      ⟦ var j   ⟧shape η = El (η j)
      ⟦ P + Q   ⟧shape η = ⟦ P ⟧shape η ⊎ ⟦ Q ⟧shape η
      ⟦ P × Q   ⟧shape η = ⟦ P ⟧shape η ×T ⟦ Q ⟧shape η
      ⟦ μ Q'    ⟧shape η = W Q' η

      El : Fin n ⊎ Sort n → Set os
      El (inj₁ p)            = δ p .idx .Carrier
      El (inj₂ (mkSort Q ρ)) = W Q ρ

    -- Bisimilarity of trees: equal roots with equal subtrees on equal branches. The
    -- environment is syntactic, so `shape≈` carries no relation to thread; nested-μ and
    -- recursive positions recurse straight to `W-≈` on structurally-smaller subtrees.
    mutual
      W-≈ : ∀ {k} {Q : Poly (suc k)} {ρ : Fin k → Fin n ⊎ Sort n} → W Q ρ → W Q ρ → Prop (os ⊔ es)
      W-≈ {Q = Q} {ρ = ρ} (sup x) (sup y) = shape≈ Q (extend ρ (inj₂ (mkSort Q ρ))) x y

      shape≈ : ∀ {j} (Q : Poly j) (η : Fin j → Fin n ⊎ Sort n) →
               ⟦ Q ⟧shape η → ⟦ Q ⟧shape η → Prop (os ⊔ es)
      shape≈ (const A) η x y = _≈s_ (A .idx) x y
      shape≈ (var j)   η x y = elEq (η j) x y
      shape≈ (P + Q) η (inj₁ x) (inj₁ y) = shape≈ P η x y
      shape≈ (P + Q) η (inj₁ _) (inj₂ _) = ⊥
      shape≈ (P + Q) η (inj₂ _) (inj₁ _) = ⊥
      shape≈ (P + Q) η (inj₂ x) (inj₂ y) = shape≈ Q η x y
      shape≈ (P × Q) η (x₁ , x₂) (y₁ , y₂) = shape≈ P η x₁ y₁ ∧ shape≈ Q η x₂ y₂
      shape≈ (μ Q') η x y = W-≈ x y

      elEq : (r : Fin n ⊎ Sort n) → El r → El r → Prop (os ⊔ es)
      elEq (inj₁ p)            x y = _≈s_ (δ p .idx) x y
      elEq (inj₂ (mkSort Q ρ)) x y = W-≈ x y

    mutual
      W-≈-refl : ∀ {k} {Q : Poly (suc k)} {ρ} (x : W Q ρ) → W-≈ x x
      W-≈-refl {Q = Q} {ρ = ρ} (sup x) = shape≈-refl Q (extend ρ (inj₂ (mkSort Q ρ))) x

      shape≈-refl : ∀ {j} (Q : Poly j) (η : Fin j → Fin n ⊎ Sort n) (x : ⟦ Q ⟧shape η) → shape≈ Q η x x
      shape≈-refl (const A) η x = A .idx .isEquivalence .refl
      shape≈-refl (var j)   η x = elEq-refl (η j) x
      shape≈-refl (P + Q) η (inj₁ x) = shape≈-refl P η x
      shape≈-refl (P + Q) η (inj₂ y) = shape≈-refl Q η y
      shape≈-refl (P × Q) η (x₁ , x₂) = shape≈-refl P η x₁ , shape≈-refl Q η x₂
      shape≈-refl (μ Q') η x = W-≈-refl x

      elEq-refl : (r : Fin n ⊎ Sort n) (x : El r) → elEq r x x
      elEq-refl (inj₁ p)            x = δ p .idx .isEquivalence .refl
      elEq-refl (inj₂ (mkSort Q ρ)) x = W-≈-refl x

    mutual
      W-≈-sym : ∀ {k} {Q : Poly (suc k)} {ρ} {x y : W Q ρ} → W-≈ x y → W-≈ y x
      W-≈-sym {Q = Q} {ρ = ρ} {sup x} {sup y} p = shape≈-sym Q (extend ρ (inj₂ (mkSort Q ρ))) p

      shape≈-sym : ∀ {j} (Q : Poly j) (η : Fin j → Fin n ⊎ Sort n) {x y : ⟦ Q ⟧shape η} →
                   shape≈ Q η x y → shape≈ Q η y x
      shape≈-sym (const A) η p = A .idx .isEquivalence .sym p
      shape≈-sym (var j)   η p = elEq-sym (η j) p
      shape≈-sym (P + Q) η {inj₁ _} {inj₁ _} p = shape≈-sym P η p
      shape≈-sym (P + Q) η {inj₂ _} {inj₂ _} p = shape≈-sym Q η p
      shape≈-sym (P × Q) η {_ , _} {_ , _} (p₁ , p₂) = shape≈-sym P η p₁ , shape≈-sym Q η p₂
      shape≈-sym (μ Q') η {x} {y} p = W-≈-sym {x = x} {y = y} p

      elEq-sym : (r : Fin n ⊎ Sort n) {x y : El r} → elEq r x y → elEq r y x
      elEq-sym (inj₁ p)            e = δ p .idx .isEquivalence .sym e
      elEq-sym (inj₂ (mkSort Q ρ)) {x} {y} e = W-≈-sym {x = x} {y = y} e

    mutual
      W-≈-trans : ∀ {k} {Q : Poly (suc k)} {ρ} {x y z : W Q ρ} → W-≈ x y → W-≈ y z → W-≈ x z
      W-≈-trans {Q = Q} {ρ = ρ} {sup x} {sup y} {sup z} p q = shape≈-trans Q (extend ρ (inj₂ (mkSort Q ρ))) p q

      shape≈-trans : ∀ {j} (Q : Poly j) (η : Fin j → Fin n ⊎ Sort n) {x y z : ⟦ Q ⟧shape η} →
                     shape≈ Q η x y → shape≈ Q η y z → shape≈ Q η x z
      shape≈-trans (const A) η p q = A .idx .isEquivalence .trans p q
      shape≈-trans (var j)   η p q = elEq-trans (η j) p q
      shape≈-trans (P + Q) η {inj₁ _} {inj₁ _} {inj₁ _} p q = shape≈-trans P η p q
      shape≈-trans (P + Q) η {inj₂ _} {inj₂ _} {inj₂ _} p q = shape≈-trans Q η p q
      shape≈-trans (P × Q) η {_ , _} {_ , _} {_ , _} (p₁ , p₂) (q₁ , q₂) =
        shape≈-trans P η p₁ q₁ , shape≈-trans Q η p₂ q₂
      shape≈-trans (μ Q') η {x} {y} {z} p q = W-≈-trans {x = x} {y = y} {z = z} p q

      elEq-trans : (r : Fin n ⊎ Sort n) {x y z : El r} → elEq r x y → elEq r y z → elEq r x z
      elEq-trans (inj₁ p)            e f = δ p .idx .isEquivalence .trans e f
      elEq-trans (inj₂ (mkSort Q ρ)) {x} {y} {z} e f = W-≈-trans {x = x} {y = y} {z = z} e f

    -- The carrier setoid of the μ-type at sort (Q , ρ).
    WSetoid : ∀ {k} (Q : Poly (suc k)) (ρ : Fin k → Fin n ⊎ Sort n) → Setoid os (os ⊔ es)
    WSetoid Q ρ .Carrier = W Q ρ
    WSetoid Q ρ ._≈s_ = W-≈
    WSetoid Q ρ .isEquivalence .refl {x} = W-≈-refl x
    WSetoid Q ρ .isEquivalence .sym {x} {y} = W-≈-sym {x = x} {y = y}
    WSetoid Q ρ .isEquivalence .trans {x} {y} {z} = W-≈-trans {x = x} {y = y} {z = z}

    -- The fibre object at each tree: 𝒞-products at ×, parameter/const fibres at the leaves.
    mutual
      fib : ∀ {k} {Q : Poly (suc k)} {ρ} → W Q ρ → obj
      fib {Q = Q} {ρ = ρ} (sup x) = fib-shape Q (extend ρ (inj₂ (mkSort Q ρ))) x

      fib-shape : ∀ {j} (Q : Poly j) (η : Fin j → Fin n ⊎ Sort n) → ⟦ Q ⟧shape η → obj
      fib-shape (const A) η x = A .fam .fm x
      fib-shape (var j)   η x = fib-el (η j) x
      fib-shape (P + Q) η (inj₁ x) = fib-shape P η x
      fib-shape (P + Q) η (inj₂ y) = fib-shape Q η y
      fib-shape (P × Q) η (x , y) = prod (fib-shape P η x) (fib-shape Q η y)
      fib-shape (μ Q') η x = fib x

      fib-el : (r : Fin n ⊎ Sort n) → El r → obj
      fib-el (inj₁ p)            x = δ p .fam .fm x
      fib-el (inj₂ (mkSort Q ρ)) x = fib x

    -- Transport of fibres along bisimilarity, by recursion on the W-≈ proof.
    mutual
      fib-subst : ∀ {k} {Q : Poly (suc k)} {ρ} {x y : W Q ρ} → W-≈ x y → fib x ⇒ fib y
      fib-subst {Q = Q} {ρ = ρ} {sup x} {sup y} p = fib-shape-subst Q (extend ρ (inj₂ (mkSort Q ρ))) p

      fib-shape-subst : ∀ {j} (Q : Poly j) (η : Fin j → Fin n ⊎ Sort n) {x y : ⟦ Q ⟧shape η} →
                        shape≈ Q η x y → fib-shape Q η x ⇒ fib-shape Q η y
      fib-shape-subst (const A) η p = A .fam .subst p
      fib-shape-subst (var j)   η p = fib-el-subst (η j) p
      fib-shape-subst (P + Q) η {inj₁ _} {inj₁ _} p = fib-shape-subst P η p
      fib-shape-subst (P + Q) η {inj₂ _} {inj₂ _} p = fib-shape-subst Q η p
      fib-shape-subst (P × Q) η {_ , _} {_ , _} (p₁ , p₂) =
        prod-m (fib-shape-subst P η p₁) (fib-shape-subst Q η p₂)
      fib-shape-subst (μ Q') η {x} {y} p = fib-subst {x = x} {y = y} p

      fib-el-subst : (r : Fin n ⊎ Sort n) {x y : El r} → elEq r x y → fib-el r x ⇒ fib-el r y
      fib-el-subst (inj₁ p)            e = δ p .fam .subst e
      fib-el-subst (inj₂ (mkSort Q ρ)) {x} {y} e = fib-subst {x = x} {y = y} e

    -- Transport along reflexivity is the identity.
    mutual
      fib-refl* : ∀ {k} {Q : Poly (suc k)} {ρ} (x : W Q ρ) →
                  fib-subst {x = x} {y = x} (W-≈-refl x) ≈ id (fib x)
      fib-refl* {Q = Q} {ρ = ρ} (sup x) = fib-shape-refl* Q (extend ρ (inj₂ (mkSort Q ρ))) x

      fib-shape-refl* : ∀ {j} (Q : Poly j) (η : Fin j → Fin n ⊎ Sort n) (x : ⟦ Q ⟧shape η) →
                        fib-shape-subst Q η (shape≈-refl Q η x) ≈ id (fib-shape Q η x)
      fib-shape-refl* (const A) η x = A .fam .refl*
      fib-shape-refl* (var j)   η x = fib-el-refl* (η j) x
      fib-shape-refl* (P + Q) η (inj₁ x) = fib-shape-refl* P η x
      fib-shape-refl* (P + Q) η (inj₂ y) = fib-shape-refl* Q η y
      fib-shape-refl* (P × Q) η (x , y) =
        ≈-trans (prod-m-cong (fib-shape-refl* P η x) (fib-shape-refl* Q η y)) prod-m-id
      fib-shape-refl* (μ Q') η x = fib-refl* x

      fib-el-refl* : (r : Fin n ⊎ Sort n) (x : El r) →
                     fib-el-subst r (elEq-refl r x) ≈ id (fib-el r x)
      fib-el-refl* (inj₁ p)            x = δ p .fam .refl*
      fib-el-refl* (inj₂ (mkSort Q ρ)) x = fib-refl* x

    -- Transport is functorial: a composite is the composite of the transports.
    mutual
      fib-trans* : ∀ {k} {Q : Poly (suc k)} {ρ} {x y z : W Q ρ} (q : W-≈ y z) (p : W-≈ x y) →
                   fib-subst {x = x} {y = z} (W-≈-trans {x = x} {y = y} {z = z} p q)
                     ≈ (fib-subst {x = y} {y = z} q ∘ fib-subst {x = x} {y = y} p)
      fib-trans* {Q = Q} {ρ = ρ} {sup x} {sup y} {sup z} q p =
        fib-shape-trans* Q (extend ρ (inj₂ (mkSort Q ρ))) q p

      fib-shape-trans* : ∀ {j} (Q : Poly j) (η : Fin j → Fin n ⊎ Sort n) {x y z : ⟦ Q ⟧shape η}
                         (q : shape≈ Q η y z) (p : shape≈ Q η x y) →
                         fib-shape-subst Q η (shape≈-trans Q η p q) ≈ (fib-shape-subst Q η q ∘ fib-shape-subst Q η p)
      fib-shape-trans* (const A) η q p = A .fam .trans* q p
      fib-shape-trans* (var j)   η q p = fib-el-trans* (η j) q p
      fib-shape-trans* (P + Q) η {inj₁ _} {inj₁ _} {inj₁ _} q p = fib-shape-trans* P η q p
      fib-shape-trans* (P + Q) η {inj₂ _} {inj₂ _} {inj₂ _} q p = fib-shape-trans* Q η q p
      fib-shape-trans* (P × Q) η {_ , _} {_ , _} {_ , _} (q₁ , q₂) (p₁ , p₂) =
        ≈-trans (prod-m-cong (fib-shape-trans* P η q₁ p₁) (fib-shape-trans* Q η q₂ p₂))
                (prod-m-comp _ _ _ _)
      fib-shape-trans* (μ Q') η {x} {y} {z} q p = fib-trans* {x = x} {y = y} {z = z} q p

      fib-el-trans* : (r : Fin n ⊎ Sort n) {x y z : El r} (q : elEq r y z) (p : elEq r x y) →
                      fib-el-subst r (elEq-trans r p q) ≈ (fib-el-subst r q ∘ fib-el-subst r p)
      fib-el-trans* (inj₁ i)            q p = δ i .fam .trans* q p
      fib-el-trans* (inj₂ (mkSort Q ρ)) {x} {y} {z} q p = fib-trans* {x = x} {y = y} {z = z} q p

    -- The fibre family of the μ-type at sort (Q , ρ).
    WFam : ∀ {k} (Q : Poly (suc k)) (ρ : Fin k → Fin n ⊎ Sort n) → Fam (WSetoid Q ρ) 𝒞
    WFam Q ρ .fm = fib
    WFam Q ρ .subst {x} {y} = fib-subst {x = x} {y = y}
    WFam Q ρ .refl* {x} = fib-refl* x
    WFam Q ρ .trans* {x} {y} {z} e₁ e₂ = fib-trans* {x = x} {y = y} {z = z} e₁ e₂

  open Tree

  -- Reindex a tree from one parameter context to another along a context morphism.
  -- The morphism is first-order data: `base` carries the leaf maps (applied only at
  -- leaves), `bind` records one binder. So `reindex`'s recursive calls are syntactically
  -- direct and structurally terminating — no closure, no fuel.
  module Reidx {nA nB} (δA : Fin nA → Obj) (δB : Fin nB → Obj) where
    private
      module TA = Tree δA
      module TB = Tree δB

    data MorD : ∀ {k} → (Fin k → Fin nA ⊎ Sort nA) → (Fin k → Fin nB ⊎ Sort nB) →
                Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      base : ∀ {k} {ρA ρB} (f : ∀ v → TA.El (ρA v) → TB.El (ρB v))
             (f-resp : ∀ v {a a'} → TA.elEq (ρA v) a a' → TB.elEq (ρB v) (f v a) (f v a'))
             (ffam : ∀ v a → TA.fib-el (ρA v) a ⇒ TB.fib-el (ρB v) (f v a)) →
             (∀ v {a a'} (p : TA.elEq (ρA v) a a') →
                (ffam v a' ∘ TA.fib-el-subst (ρA v) p) ≈ (TB.fib-el-subst (ρB v) (f-resp v p) ∘ ffam v a)) →
             MorD {k} ρA ρB
      bind : ∀ {k} {ρA ρB} (Q : Poly (suc k)) → MorD ρA ρB →
             MorD (extend ρA (inj₂ (mkSort Q ρA))) (extend ρB (inj₂ (mkSort Q ρB)))

    mutual
      reindex : ∀ {k} {Q : Poly (suc k)} {ρA ρB} (md : MorD ρA ρB) → TA.W Q ρA → TB.W Q ρB
      reindex {Q = Q} md (TA.sup x) = TB.sup (reindex-shape Q (bind Q md) x)

      reindex-shape : ∀ {j} (R : Poly j) {ηA ηB} (md : MorD ηA ηB) → TA.⟦ R ⟧shape ηA → TB.⟦ R ⟧shape ηB
      reindex-shape (const A) md a = a
      reindex-shape (var v)   md a = apply md v a
      reindex-shape (P + Q) md (inj₁ a) = inj₁ (reindex-shape P md a)
      reindex-shape (P + Q) md (inj₂ b) = inj₂ (reindex-shape Q md b)
      reindex-shape (P × Q) md (a , b) = reindex-shape P md a , reindex-shape Q md b
      reindex-shape (μ Q') md t = reindex md t

      apply : ∀ {k} {ρA ρB} (md : MorD {k} ρA ρB) (v : Fin k) → TA.El (ρA v) → TB.El (ρB v)
      apply (base f _ _ _) v        a = f v a
      apply (bind Q md) Fin.zero    a = reindex md a
      apply (bind Q md) (Fin.suc v) a = apply md v a

    -- `reindex` respects bisimilarity.
    mutual
      reindex-resp : ∀ {k} {Q : Poly (suc k)} {ρA ρB} (md : MorD ρA ρB) {t t' : TA.W Q ρA} →
                     TA.W-≈ t t' → TB.W-≈ (reindex md t) (reindex md t')
      reindex-resp {Q = Q} md {TA.sup x} {TA.sup y} p = reindex-shape-resp Q (bind Q md) {x} {y} p

      reindex-shape-resp : ∀ {j} (R : Poly j) {ηA ηB} (md : MorD ηA ηB) {a a' : TA.⟦ R ⟧shape ηA} →
                           TA.shape≈ R ηA a a' → TB.shape≈ R ηB (reindex-shape R md a) (reindex-shape R md a')
      reindex-shape-resp (const A) md p = p
      reindex-shape-resp (var v)   md p = apply-resp md v p
      reindex-shape-resp (P + Q) md {inj₁ _} {inj₁ _} p = reindex-shape-resp P md p
      reindex-shape-resp (P + Q) md {inj₂ _} {inj₂ _} p = reindex-shape-resp Q md p
      reindex-shape-resp (P × Q) md {_ , _} {_ , _} (p₁ , p₂) =
        reindex-shape-resp P md p₁ , reindex-shape-resp Q md p₂
      reindex-shape-resp (μ Q') md {a} {a'} p = reindex-resp md {a} {a'} p

      apply-resp : ∀ {k} {ρA ρB} (md : MorD {k} ρA ρB) (v : Fin k) {a a'} →
                   TA.elEq (ρA v) a a' → TB.elEq (ρB v) (apply md v a) (apply md v a')
      apply-resp (base f f-resp _ _) v       p = f-resp v p
      apply-resp (bind Q md)     Fin.zero    {a} {a'} p = reindex-resp md {a} {a'} p
      apply-resp (bind Q md)     (Fin.suc v) p = apply-resp md v p

    -- The fibre side of `reindex`: a 𝒞-morphism into the reindexed fibre.
    mutual
      reindex-fam : ∀ {j} (R : Poly j) {ηA ηB} (md : MorD ηA ηB) {a : TA.⟦ R ⟧shape ηA} →
                    TA.fib-shape R ηA a ⇒ TB.fib-shape R ηB (reindex-shape R md a)
      reindex-fam (const A) md = id _
      reindex-fam (var v)   md {a} = apply-fam md v a
      reindex-fam (P + Q) md {inj₁ a} = reindex-fam P md
      reindex-fam (P + Q) md {inj₂ b} = reindex-fam Q md
      reindex-fam (P × Q) md {a , b} = prod-m (reindex-fam P md) (reindex-fam Q md)
      reindex-fam (μ Q') md {t} = reindex-fam-W md {t}

      reindex-fam-W : ∀ {k} {Q : Poly (suc k)} {ρA ρB} (md : MorD ρA ρB) {t : TA.W Q ρA} →
                      TA.fib t ⇒ TB.fib (reindex md t)
      reindex-fam-W {Q = Q} md {TA.sup x} = reindex-fam Q (bind Q md)

      apply-fam : ∀ {k} {ρA ρB} (md : MorD {k} ρA ρB) (v : Fin k) (a : TA.El (ρA v)) →
                  TA.fib-el (ρA v) a ⇒ TB.fib-el (ρB v) (apply md v a)
      apply-fam (base _ _ ffam _) v         a = ffam v a
      apply-fam (bind Q md)     Fin.zero    a = reindex-fam-W md {a}
      apply-fam (bind Q md)     (Fin.suc v) a = apply-fam md v a

    -- The fibre reindex commutes with subst (naturality).
    mutual
      reindex-fam-nat : ∀ {j} (R : Poly j) {ηA ηB} (md : MorD ηA ηB)
                        {a a' : TA.⟦ R ⟧shape ηA} (p : TA.shape≈ R ηA a a') →
                        (reindex-fam R md {a'} ∘ TA.fib-shape-subst R ηA p)
                          ≈ (TB.fib-shape-subst R ηB (reindex-shape-resp R md p) ∘ reindex-fam R md {a})
      reindex-fam-nat (const A) md p = ≈-trans id-left (≈-sym id-right)
      reindex-fam-nat (var v)   md {a} {a'} p = apply-fam-nat md v {a} {a'} p
      reindex-fam-nat (P + Q) md {inj₁ a} {inj₁ a'} p = reindex-fam-nat P md p
      reindex-fam-nat (P + Q) md {inj₂ b} {inj₂ b'} p = reindex-fam-nat Q md p
      reindex-fam-nat (P × Q) md {a , b} {a' , b'} (p₁ , p₂) =
        ≈-trans (≈-sym (prod-m-comp _ _ _ _))
        (≈-trans (prod-m-cong (reindex-fam-nat P md p₁) (reindex-fam-nat Q md p₂))
                 (prod-m-comp _ _ _ _))
      reindex-fam-nat (μ Q') md {t} {t'} p = reindex-fam-W-nat md {t} {t'} p

      reindex-fam-W-nat : ∀ {k} {Q : Poly (suc k)} {ρA ρB} (md : MorD ρA ρB)
                          {t t' : TA.W Q ρA} (p : TA.W-≈ t t') →
                          (reindex-fam-W md {t'} ∘ TA.fib-subst {x = t} {y = t'} p)
                            ≈ (TB.fib-subst {x = reindex md t} {y = reindex md t'}
                                            (reindex-resp md {t} {t'} p) ∘ reindex-fam-W md {t})
      reindex-fam-W-nat {Q = Q} md {TA.sup x} {TA.sup y} p = reindex-fam-nat Q (bind Q md) {x} {y} p

      apply-fam-nat : ∀ {k} {ρA ρB} (md : MorD {k} ρA ρB) (v : Fin k) {a a'}
                      (p : TA.elEq (ρA v) a a') →
                      (apply-fam md v a' ∘ TA.fib-el-subst (ρA v) p)
                        ≈ (TB.fib-el-subst (ρB v) (apply-resp md v p) ∘ apply-fam md v a)
      apply-fam-nat (base _ _ _ ffam-nat) v p = ffam-nat v p
      apply-fam-nat (bind Q md) Fin.zero    {a} {a'} p = reindex-fam-W-nat md {a} {a'} p
      apply-fam-nat (bind Q md) (Fin.suc v) p = apply-fam-nat md v p

  μObj : ∀ {n} → Poly (suc n) → (Fin n → Obj) → Obj
  μObj P δ .idx = WSetoid δ P (λ i → inj₁ i)
  μObj P δ .fam = WFam δ P (λ i → inj₁ i)

  -- The fold (catamorphism) for the μ-type, lifted to a standalone module so its
  -- mutual recursion is termination-checked independently of the `hasMu` copattern.
  module FoldDef {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
                 (alg : Mor (Fam𝒞-P.prod Γ (fobj μObj P (extend δ A))) A) where
      μo = μObj
      module Tδ = Tree δ
      module TA' = Tree (extend δ A)
      η₀ : Fin (suc n) → Fin n ⊎ Sort n
      η₀ = extend (λ i → inj₁ i) (inj₂ (mkSort P (λ i → inj₁ i)))
      -- Fold-specific reindex morphism (first-order, like `MorD`): `fbase` sends the outer
      -- recursion slot to the fold and parameters to themselves; `fbind` records a binder.
      data FMor : ∀ {k} → (Fin k → Fin n ⊎ Sort n) → (Fin k → Fin (suc n) ⊎ Sort (suc n)) →
                  Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
        fbase : FMor η₀ (λ v → inj₁ v)
        fbind : ∀ {k} {ρ ρ'} (Q : Poly (suc k)) → FMor ρ ρ' →
                FMor (extend ρ (inj₂ (mkSort Q ρ))) (extend ρ' (inj₂ (mkSort Q ρ')))
      -- Fold the outer μ via `alg`; nested μ are reindexed into the `extend δ A` context,
      -- the recursion slot carrying the fold itself (inlined, so every call is structural).
      mutual
        fold-idx : Γ .idx .Carrier → Tδ.W P (λ i → inj₁ i) → A .idx .Carrier
        fold-idx γ (Tδ.sup x) = alg .idxf .PS._⇒_.func (γ , foldShape-idx P γ x)

        foldShape-idx : (Q : Poly (suc n)) → Γ .idx .Carrier → Tδ.⟦ Q ⟧shape η₀ →
                        fobj μo Q (extend δ A) .idx .Carrier
        foldShape-idx (const A')        γ a = a
        foldShape-idx (var Fin.zero)    γ t = fold-idx γ t
        foldShape-idx (var (Fin.suc i)) γ a = a
        foldShape-idx (Q₁ + Q₂) γ (inj₁ x) = inj₁ (foldShape-idx Q₁ γ x)
        foldShape-idx (Q₁ + Q₂) γ (inj₂ y) = inj₂ (foldShape-idx Q₂ γ y)
        foldShape-idx (Q₁ × Q₂) γ (x , y) = foldShape-idx Q₁ γ x , foldShape-idx Q₂ γ y
        foldShape-idx (μ Q')    γ t = fold-reindex γ fbase t

        fold-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ') →
                       Tδ.W Q ρ → TA'.W Q ρ'
        fold-reindex {Q = Q} γ fm (Tδ.sup x) = TA'.sup (fold-reindex-shape γ Q (fbind Q fm) x)

        fold-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB} (fm : FMor ηA ηB) →
                             Tδ.⟦ R ⟧shape ηA → TA'.⟦ R ⟧shape ηB
        fold-reindex-shape γ (const A') fm a = a
        fold-reindex-shape γ (var v)    fm a = fold-apply γ fm v a
        fold-reindex-shape γ (P' + Q') fm (inj₁ a) = inj₁ (fold-reindex-shape γ P' fm a)
        fold-reindex-shape γ (P' + Q') fm (inj₂ b) = inj₂ (fold-reindex-shape γ Q' fm b)
        fold-reindex-shape γ (P' × Q') fm (a , b) = fold-reindex-shape γ P' fm a , fold-reindex-shape γ Q' fm b
        fold-reindex-shape γ (μ Q'')   fm t = fold-reindex γ fm t

        fold-apply : ∀ {k} {ρ ρ'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ') (v : Fin k) →
                     Tδ.El (ρ v) → TA'.El (ρ' v)
        fold-apply γ fbase        Fin.zero    t = fold-idx γ t
        fold-apply γ fbase        (Fin.suc i) a = a
        fold-apply γ (fbind Q fm) Fin.zero    a = fold-reindex γ fm a
        fold-apply γ (fbind Q fm) (Fin.suc v) a = fold-apply γ fm v a

      -- The index fold respects ≈ (in both Γ and the tree).
      mutual
        fold-idx-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : Tδ.W-≈ t t') →
                        _≈s_ (A .idx) (fold-idx γ t) (fold-idx γ' t')
        fold-idx-resp γ≈ {Tδ.sup x} {Tδ.sup y} p = alg .idxf .PS._⇒_.func-resp-≈ (γ≈ , foldShape-idx-resp P γ≈ p)

        foldShape-idx-resp : (Q : Poly (suc n)) → ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {x x'}
                             (p : Tδ.shape≈ Q η₀ x x') →
                             _≈s_ (fobj μo Q (extend δ A) .idx) (foldShape-idx Q γ x) (foldShape-idx Q γ' x')
        foldShape-idx-resp (const A')        γ≈ p = p
        foldShape-idx-resp (var Fin.zero)    γ≈ {x} {x'} p = fold-idx-resp γ≈ {x} {x'} p
        foldShape-idx-resp (var (Fin.suc i)) γ≈ p = p
        foldShape-idx-resp (Q₁ + Q₂) γ≈ {inj₁ _} {inj₁ _} p = foldShape-idx-resp Q₁ γ≈ p
        foldShape-idx-resp (Q₁ + Q₂) γ≈ {inj₂ _} {inj₂ _} p = foldShape-idx-resp Q₂ γ≈ p
        foldShape-idx-resp (Q₁ × Q₂) γ≈ {_ , _} {_ , _} (p₁ , p₂) =
          foldShape-idx-resp Q₁ γ≈ p₁ , foldShape-idx-resp Q₂ γ≈ p₂
        foldShape-idx-resp (μ Q')    γ≈ {x} {x'} p = fold-reindex-resp γ≈ fbase {x} {x'} p

        fold-reindex-resp : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (fm : FMor ρ ρ')
                            {t t' : Tδ.W Q ρ} (p : Tδ.W-≈ t t') →
                            TA'.W-≈ (fold-reindex γ fm t) (fold-reindex γ' fm t')
        fold-reindex-resp {Q = Q} γ≈ fm {Tδ.sup x} {Tδ.sup y} p = fold-reindex-shape-resp γ≈ Q (fbind Q fm) {x} {y} p

        fold-reindex-shape-resp : ∀ {j} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (R : Poly j) {ηA ηB} (fm : FMor ηA ηB)
                                  {a a' : Tδ.⟦ R ⟧shape ηA} (p : Tδ.shape≈ R ηA a a') →
                                  TA'.shape≈ R ηB (fold-reindex-shape γ R fm a) (fold-reindex-shape γ' R fm a')
        fold-reindex-shape-resp γ≈ (const A') fm p = p
        fold-reindex-shape-resp γ≈ (var v)    fm p = fold-apply-resp γ≈ fm v p
        fold-reindex-shape-resp γ≈ (P' + Q') fm {inj₁ _} {inj₁ _} p = fold-reindex-shape-resp γ≈ P' fm p
        fold-reindex-shape-resp γ≈ (P' + Q') fm {inj₂ _} {inj₂ _} p = fold-reindex-shape-resp γ≈ Q' fm p
        fold-reindex-shape-resp γ≈ (P' × Q') fm {_ , _} {_ , _} (p₁ , p₂) =
          fold-reindex-shape-resp γ≈ P' fm p₁ , fold-reindex-shape-resp γ≈ Q' fm p₂
        fold-reindex-shape-resp γ≈ (μ Q'')   fm {a} {a'} p = fold-reindex-resp γ≈ fm {a} {a'} p

        fold-apply-resp : ∀ {k} {ρ ρ'} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (fm : FMor ρ ρ') (v : Fin k)
                          {a a'} (p : Tδ.elEq (ρ v) a a') →
                          TA'.elEq (ρ' v) (fold-apply γ fm v a) (fold-apply γ' fm v a')
        fold-apply-resp γ≈ fbase        Fin.zero    {a} {a'} p = fold-idx-resp γ≈ {a} {a'} p
        fold-apply-resp γ≈ fbase        (Fin.suc i) p = p
        fold-apply-resp γ≈ (fbind Q fm) Fin.zero    {a} {a'} p = fold-reindex-resp γ≈ fm {a} {a'} p
        fold-apply-resp γ≈ (fbind Q fm) (Fin.suc v) p = fold-apply-resp γ≈ fm v p

      -- The fibre fold: collapse the tree's fibre via `alg.famf`, threading the Γ-fibre.
      mutual
        fold-fam : (γ : Γ .idx .Carrier) (t : Tδ.W P (λ i → inj₁ i)) →
                   prod (Γ .fam .fm γ) (Tδ.fib t) ⇒ A .fam .fm (fold-idx γ t)
        fold-fam γ (Tδ.sup x) =
          alg .famf ._⇒f_.transf (γ , foldShape-idx P γ x) ∘ pair p₁ (foldShape-fam P γ x)

        foldShape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ Q ⟧shape η₀) →
                        prod (Γ .fam .fm γ) (Tδ.fib-shape Q η₀ x) ⇒ fobj μo Q (extend δ A) .fam .fm (foldShape-idx Q γ x)
        foldShape-fam (const A')        γ a = p₂
        foldShape-fam (var Fin.zero)    γ t = fold-fam γ t
        foldShape-fam (var (Fin.suc i)) γ a = p₂
        foldShape-fam (Q₁ + Q₂) γ (inj₁ x) = foldShape-fam Q₁ γ x
        foldShape-fam (Q₁ + Q₂) γ (inj₂ y) = foldShape-fam Q₂ γ y
        foldShape-fam (Q₁ × Q₂) γ (x , y) =
          pair (foldShape-fam Q₁ γ x ∘ pair p₁ (p₁ ∘ p₂)) (foldShape-fam Q₂ γ y ∘ pair p₁ (p₂ ∘ p₂))
        foldShape-fam (μ Q')    γ t = fold-reindex-fam γ fbase t

        fold-reindex-fam : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ') (t : Tδ.W Q ρ) →
                           prod (Γ .fam .fm γ) (Tδ.fib t) ⇒ TA'.fib (fold-reindex γ md t)
        fold-reindex-fam {Q = Q} γ md (Tδ.sup x) = fold-reindex-shape-fam γ Q (fbind Q md) x

        fold-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB} (md : FMor ηA ηB) (a : Tδ.⟦ R ⟧shape ηA) →
                                 prod (Γ .fam .fm γ) (Tδ.fib-shape R ηA a) ⇒ TA'.fib-shape R ηB (fold-reindex-shape γ R md a)
        fold-reindex-shape-fam γ (const A') md a = p₂
        fold-reindex-shape-fam γ (var v)    md a = fold-apply-fam γ md v a
        fold-reindex-shape-fam γ (P' + Q') md (inj₁ a) = fold-reindex-shape-fam γ P' md a
        fold-reindex-shape-fam γ (P' + Q') md (inj₂ b) = fold-reindex-shape-fam γ Q' md b
        fold-reindex-shape-fam γ (P' × Q') md (a , b) =
          pair (fold-reindex-shape-fam γ P' md a ∘ pair p₁ (p₁ ∘ p₂)) (fold-reindex-shape-fam γ Q' md b ∘ pair p₁ (p₂ ∘ p₂))
        fold-reindex-shape-fam γ (μ Q'')   md t = fold-reindex-fam γ md t

        fold-apply-fam : ∀ {k} {ρ ρ'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ') (v : Fin k) (a : Tδ.El (ρ v)) →
                         prod (Γ .fam .fm γ) (Tδ.fib-el (ρ v) a) ⇒ TA'.fib-el (ρ' v) (fold-apply γ md v a)
        fold-apply-fam γ fbase        Fin.zero    t = fold-fam γ t
        fold-apply-fam γ fbase        (Fin.suc i) a = p₂
        fold-apply-fam γ (fbind Q md) Fin.zero    a = fold-reindex-fam γ md a
        fold-apply-fam γ (fbind Q md) (Fin.suc v) a = fold-apply-fam γ md v a



      -- The fibre fold is natural: it commutes with `subst` (in both Γ and the tree).
      mutual
        fold-fam-nat : ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {t t'} (p : Tδ.W-≈ t t') →
                       (fold-fam γ₂ t' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-subst {x = t} {y = t'} p))
                         ≈ (A .fam .subst (fold-idx-resp γ≈ {t} {t'} p) ∘ fold-fam γ₁ t)
        fold-fam-nat {γ₁} {γ₂} γ≈ {Tδ.sup x} {Tδ.sup y} p =
          ≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl (pair-natural _ _ _))
          (≈-trans (∘-cong ≈-refl (pair-cong (pair-p₁ _ _) (foldShape-fam-nat P γ≈ {x} {y} p)))
          (≈-trans (∘-cong ≈-refl (≈-sym (pair-compose _ _ _ _)))
          (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong (alg .famf ._⇒f_.natural (γ≈ , foldShape-idx-resp P γ≈ {x} {y} p)) ≈-refl)
                   (assoc _ _ _))))))

        foldShape-fam-nat : (Q : Poly (suc n)) → ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {x x'}
                            (p : Tδ.shape≈ Q η₀ x x') →
                            (foldShape-fam Q γ₂ x' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-shape-subst Q η₀ p))
                              ≈ (fobj μo Q (extend δ A) .fam .subst (foldShape-idx-resp Q γ≈ p) ∘ foldShape-fam Q γ₁ x)
        foldShape-fam-nat (const A')        γ≈ p = pair-p₂ _ _
        foldShape-fam-nat (var Fin.zero)    γ≈ {x} {x'} p = fold-fam-nat γ≈ {x} {x'} p
        foldShape-fam-nat (var (Fin.suc i)) γ≈ p = pair-p₂ _ _
        foldShape-fam-nat (Q₁ + Q₂) γ≈ {inj₁ _} {inj₁ _} p = foldShape-fam-nat Q₁ γ≈ p
        foldShape-fam-nat (Q₁ + Q₂) γ≈ {inj₂ _} {inj₂ _} p = foldShape-fam-nat Q₂ γ≈ p
        foldShape-fam-nat (Q₁ × Q₂) γ≈ {x₁ , x₂} {x₁' , x₂'} (p₁p , p₂p) =
          ≈-trans (pair-natural _ _ _)
          (≈-trans (pair-cong (assoc _ _ _) (assoc _ _ _))
          (≈-trans (pair-cong (∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (pair-p₁ _ _) ≈-refl) (assoc _ _ _)))))))) (∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (pair-p₂ _ _) ≈-refl) (assoc _ _ _)))))))))
          (≈-trans (pair-cong (∘-cong ≈-refl (≈-sym (pair-compose _ _ _ _))) (∘-cong ≈-refl (≈-sym (pair-compose _ _ _ _))))
          (≈-trans (pair-cong (≈-sym (assoc _ _ _)) (≈-sym (assoc _ _ _)))
          (≈-trans (pair-cong (∘-cong (foldShape-fam-nat Q₁ γ≈ p₁p) ≈-refl) (∘-cong (foldShape-fam-nat Q₂ γ≈ p₂p) ≈-refl))
          (≈-trans (pair-cong (assoc _ _ _) (assoc _ _ _))
                   (≈-sym (pair-compose _ _ _ _))))))))
        foldShape-fam-nat (μ Q')    γ≈ {x} {x'} p = fold-reindex-fam-nat γ≈ fbase {x} {x'} p

        fold-reindex-fam-nat : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂)
                               (md : FMor ρ ρ') {t t' : Tδ.W Q ρ} (p : Tδ.W-≈ t t') →
                               (fold-reindex-fam γ₂ md t' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-subst {x = t} {y = t'} p))
                                 ≈ (TA'.fib-subst {x = fold-reindex γ₁ md t} {y = fold-reindex γ₂ md t'}
                                                  (fold-reindex-resp γ≈ md {t} {t'} p) ∘ fold-reindex-fam γ₁ md t)
        fold-reindex-fam-nat {Q = Q} γ≈ md {Tδ.sup x} {Tδ.sup y} p = fold-reindex-shape-fam-nat γ≈ Q (fbind Q md) {x} {y} p

        fold-reindex-shape-fam-nat : ∀ {j} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (R : Poly j) {ηA ηB} (md : FMor ηA ηB)
                                     {a a' : Tδ.⟦ R ⟧shape ηA} (p : Tδ.shape≈ R ηA a a') →
                                     (fold-reindex-shape-fam γ₂ R md a' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-shape-subst R ηA p))
                                       ≈ (TA'.fib-shape-subst R ηB (fold-reindex-shape-resp γ≈ R md p) ∘ fold-reindex-shape-fam γ₁ R md a)
        fold-reindex-shape-fam-nat γ≈ (const A') md p = pair-p₂ _ _
        fold-reindex-shape-fam-nat γ≈ (var v)    md p = fold-apply-fam-nat γ≈ md v p
        fold-reindex-shape-fam-nat γ≈ (P' + Q') md {inj₁ _} {inj₁ _} p = fold-reindex-shape-fam-nat γ≈ P' md p
        fold-reindex-shape-fam-nat γ≈ (P' + Q') md {inj₂ _} {inj₂ _} p = fold-reindex-shape-fam-nat γ≈ Q' md p
        fold-reindex-shape-fam-nat γ≈ (P' × Q') md {a₁ , a₂} {a₁' , a₂'} (p₁p , p₂p) =
          ≈-trans (pair-natural _ _ _)
          (≈-trans (pair-cong (assoc _ _ _) (assoc _ _ _))
          (≈-trans (pair-cong (∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (pair-p₁ _ _) ≈-refl) (assoc _ _ _)))))))) (∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (pair-p₂ _ _) ≈-refl) (assoc _ _ _)))))))))
          (≈-trans (pair-cong (∘-cong ≈-refl (≈-sym (pair-compose _ _ _ _))) (∘-cong ≈-refl (≈-sym (pair-compose _ _ _ _))))
          (≈-trans (pair-cong (≈-sym (assoc _ _ _)) (≈-sym (assoc _ _ _)))
          (≈-trans (pair-cong (∘-cong (fold-reindex-shape-fam-nat γ≈ P' md p₁p) ≈-refl) (∘-cong (fold-reindex-shape-fam-nat γ≈ Q' md p₂p) ≈-refl))
          (≈-trans (pair-cong (assoc _ _ _) (assoc _ _ _))
                   (≈-sym (pair-compose _ _ _ _))))))))
        fold-reindex-shape-fam-nat γ≈ (μ Q'')   md {a} {a'} p = fold-reindex-fam-nat γ≈ md {a} {a'} p

        fold-apply-fam-nat : ∀ {k} {ρ ρ'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (md : FMor ρ ρ') (v : Fin k)
                             {a a'} (p : Tδ.elEq (ρ v) a a') →
                             (fold-apply-fam γ₂ md v a' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-el-subst (ρ v) p))
                               ≈ (TA'.fib-el-subst (ρ' v) (fold-apply-resp γ≈ md v p) ∘ fold-apply-fam γ₁ md v a)
        fold-apply-fam-nat γ≈ fbase        Fin.zero    {a} {a'} p = fold-fam-nat γ≈ {a} {a'} p
        fold-apply-fam-nat γ≈ fbase        (Fin.suc i) p = pair-p₂ _ _
        fold-apply-fam-nat γ≈ (fbind Q md) Fin.zero    {a} {a'} p = fold-reindex-fam-nat γ≈ md {a} {a'} p
        fold-apply-fam-nat γ≈ (fbind Q md) (Fin.suc v) p = fold-apply-fam-nat γ≈ md v p

      foldMor : Mor (Fam𝒞-P.prod Γ (μo P δ)) A
      foldMor .idxf .PS._⇒_.func (γ , t) = fold-idx γ t
      foldMor .idxf .PS._⇒_.func-resp-≈ {γ , t} {γ' , t'} (γ≈ , t≈) = fold-idx-resp γ≈ {t} {t'} t≈
      foldMor .famf ._⇒f_.transf (γ , t) = fold-fam γ t
      foldMor .famf ._⇒f_.natural {γ₁ , t₁} {γ₂ , t₂} (γ≈ , t≈) = fold-fam-nat γ≈ {t₁} {t₂} t≈

  -- α's reconstruction machinery, lifted to a named module so the β/η laws can
  -- reference embed-idx / embed-fam / mor₀ (the fold and Reidx are already named).
  module AlphaDef {n} (P : Poly (suc n)) (δ : Fin n → Obj) where
      μo = μObj
      δ' = extend δ (μo P δ)
      module Tδ = Tree δ
      module TX = Tree δ'
      module R  = Reidx δ' δ
      η₀ : Fin (suc n) → Fin n ⊎ Sort n
      η₀ = extend (λ i → inj₁ i) (inj₂ (mkSort P (λ i → inj₁ i)))
      -- Bridge `fobj`'s native structure to our `⟦_⟧shape` (identity at leaves and μ).
      embed-idx : (Q : Poly (suc n)) → fobj μo Q δ' .idx .Carrier → TX.⟦ Q ⟧shape (λ v → inj₁ v)
      embed-idx (const A) a = a
      embed-idx (var v)   a = a
      embed-idx (Q₁ + Q₂) (inj₁ x) = inj₁ (embed-idx Q₁ x)
      embed-idx (Q₁ + Q₂) (inj₂ y) = inj₂ (embed-idx Q₂ y)
      embed-idx (Q₁ × Q₂) (x , y) = embed-idx Q₁ x , embed-idx Q₂ y
      embed-idx (μ Q')    t = t
      embed-idx-resp : (Q : Poly (suc n)) {x y : fobj μo Q δ' .idx .Carrier} →
                       _≈s_ (fobj μo Q δ' .idx) x y → TX.shape≈ Q (λ v → inj₁ v) (embed-idx Q x) (embed-idx Q y)
      embed-idx-resp (const A) p = p
      embed-idx-resp (var v)   p = p
      embed-idx-resp (Q₁ + Q₂) {inj₁ _} {inj₁ _} p = embed-idx-resp Q₁ p
      embed-idx-resp (Q₁ + Q₂) {inj₂ _} {inj₂ _} p = embed-idx-resp Q₂ p
      embed-idx-resp (Q₁ × Q₂) {_ , _} {_ , _} (p₁ , p₂) = embed-idx-resp Q₁ p₁ , embed-idx-resp Q₂ p₂
      embed-idx-resp (μ Q')    p = p
      m₀ : ∀ v → TX.El (inj₁ v) → Tδ.El (η₀ v)
      m₀ Fin.zero    a = a
      m₀ (Fin.suc i) a = a
      m₀-resp : ∀ v {a a'} → TX.elEq (inj₁ v) a a' → Tδ.elEq (η₀ v) (m₀ v a) (m₀ v a')
      m₀-resp Fin.zero    p = p
      m₀-resp (Fin.suc i) p = p
      m₀-fam : ∀ v (a : TX.El (inj₁ v)) → TX.fib-el (inj₁ v) a ⇒ Tδ.fib-el (η₀ v) (m₀ v a)
      m₀-fam Fin.zero    a = id _
      m₀-fam (Fin.suc i) a = id _
      m₀-fam-nat : ∀ v {a a'} (p : TX.elEq (inj₁ v) a a') →
                   (m₀-fam v a' ∘ TX.fib-el-subst (inj₁ v) p) ≈ (Tδ.fib-el-subst (η₀ v) (m₀-resp v p) ∘ m₀-fam v a)
      m₀-fam-nat Fin.zero    p = ≈-trans id-left (≈-sym id-right)
      m₀-fam-nat (Fin.suc i) p = ≈-trans id-left (≈-sym id-right)
      mor₀ : R.MorD (λ v → inj₁ v) η₀
      mor₀ = R.base m₀ m₀-resp m₀-fam m₀-fam-nat
      -- Fibre bridge: `fobj`'s fibre to our `fib-shape` (identity at leaves, products at ×).
      embed-fam : (Q : Poly (suc n)) (x : fobj μo Q δ' .idx .Carrier) →
                  fobj μo Q δ' .fam .fm x ⇒ TX.fib-shape Q (λ v → inj₁ v) (embed-idx Q x)
      embed-fam (const A) a = id _
      embed-fam (var v)   a = id _
      embed-fam (Q₁ + Q₂) (inj₁ x) = embed-fam Q₁ x
      embed-fam (Q₁ + Q₂) (inj₂ y) = embed-fam Q₂ y
      embed-fam (Q₁ × Q₂) (x , y) = prod-m (embed-fam Q₁ x) (embed-fam Q₂ y)
      embed-fam (μ Q')    t = id _
      embed-fam-natural : (Q : Poly (suc n)) {x y : fobj μo Q δ' .idx .Carrier} (e : _≈s_ (fobj μo Q δ' .idx) x y) →
                          (embed-fam Q y ∘ fobj μo Q δ' .fam .subst e)
                            ≈ (TX.fib-shape-subst Q (λ v → inj₁ v) (embed-idx-resp Q e) ∘ embed-fam Q x)
      embed-fam-natural (const A) e = ≈-trans id-left (≈-sym id-right)
      embed-fam-natural (var v)   e = ≈-trans id-left (≈-sym id-right)
      embed-fam-natural (Q₁ + Q₂) {inj₁ _} {inj₁ _} e = embed-fam-natural Q₁ e
      embed-fam-natural (Q₁ + Q₂) {inj₂ _} {inj₂ _} e = embed-fam-natural Q₂ e
      embed-fam-natural (Q₁ × Q₂) {_ , _} {_ , _} (e₁ , e₂) =
        ≈-trans (≈-sym (prod-m-comp _ _ _ _))
        (≈-trans (prod-m-cong (embed-fam-natural Q₁ e₁) (embed-fam-natural Q₂ e₂)) (prod-m-comp _ _ _ _))
      embed-fam-natural (μ Q')    e = ≈-trans id-left (≈-sym id-right)
      αmor : Mor (fobj μo P δ') (μo P δ)
      αmor .idxf .PS._⇒_.func i = Tδ.sup (R.reindex-shape P mor₀ (embed-idx P i))
      αmor .idxf .PS._⇒_.func-resp-≈ x≈y = R.reindex-shape-resp P mor₀ (embed-idx-resp P x≈y)
      αmor .famf ._⇒f_.transf x = R.reindex-fam P mor₀ ∘ embed-fam P x
      αmor .famf ._⇒f_.natural e =
        ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (embed-fam-natural P e))
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong₁ (R.reindex-fam-nat P mor₀ (embed-idx-resp P e)))
                 (assoc _ _ _))))

  hasMu : HasMu
  hasMu .HasMu.μ-obj = μObj
  hasMu .HasMu.α P δ = AlphaDef.αmor P δ
  hasMu .HasMu.⦅_⦆ alg = FoldDef.foldMor alg

  -- β/η proof machinery: the fusion of `α`'s reconstruction with the fold equals the
  -- strong functorial action of `⦅ alg ⦆`. References both AlphaDef and FoldDef internals.
  module BetaDef {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
                 (alg : Mor (Fam𝒞-P.prod Γ (fobj μObj P (extend δ A))) A) where
    open HasMu hasMu using (strong-fmor; strong-extend-mor; ⦅_⦆; α)
    module Aα = AlphaDef P δ
    module Fα = FoldDef {Γ = Γ} {A = A} {P = P} {δ = δ} alg
    μo = μObj
    δ' = extend δ (μo P δ)
    fs : ∀ i → Mor (Fam𝒞-P.prod Γ (δ' i)) (extend δ A i)
    fs = strong-extend-mor (λ i → Fam𝒞-P.p₂) Fα.foldMor

    -- The nested algebra `β = α ∘ strong-fmor` and its α/fold instances, per μ-body Q'.
    -- (RHS of the fusion: strong-μ-fmor Q' fs = ⦅ β ⦆ unfolds through these.)
    module Nested (Q' : Poly (suc (suc n))) where
      module Aβ = AlphaDef Q' (extend δ A)
      fs' : ∀ i → Mor (Fam𝒞-P.prod Γ (extend δ' (μo Q' (extend δ A)) i)) (extend (extend δ A) (μo Q' (extend δ A)) i)
      fs' = strong-extend-mor fs Fam𝒞-P.p₂
      β : Mor (Fam𝒞-P.prod Γ (fobj μo Q' (extend δ' (μo Q' (extend δ A))))) (μo Q' (extend δ A))
      β = Mor-∘ Aβ.αmor (strong-fmor Q' fs')
      module Fβ = FoldDef {Γ = Γ} {A = μo Q' (extend δ A)} {P = Q'} {δ = δ'} β

    -- PROBE: can the FMor-reindex composed with the MorD-reindex collapse to a single MorD-reindex?
    module Rcomb = Reidx δ' (extend δ A)
    combine : (γ : Γ .idx .Carrier) → ∀ {k} {ρA ρB ρC} → Aα.R.MorD {k} ρA ρB → Fα.FMor {k} ρB ρC → Rcomb.MorD {k} ρA ρC
    combine γ md fm = Rcomb.base (λ v a → Fα.fold-apply γ fm v (Aα.R.apply md v a)) {!!} {!!} {!!}

    mutual
      -- Defunctionalised relation "these two Rcomb.MorDs are combine-lemma-related under binders".
      data Rel : ∀ {k} {ρA ρB} → Rcomb.MorD {k} ρA ρB → Rcomb.MorD {k} ρA ρB →
                 Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
        rcomb : ∀ {k} {ρA ρB ρC} (γ : Γ .idx .Carrier) (Q : Poly (suc k))
                (md : Aα.R.MorD ρA ρB) (fm : Fα.FMor ρB ρC) →
                Rel (combine γ (Aα.R.bind Q md) (Fα.fbind Q fm)) (Rcomb.bind Q (combine γ md fm))
        rbind : ∀ {k} {ρA ρB} {md₁ md₂ : Rcomb.MorD ρA ρB} (Q : Poly (suc k)) →
                Rel md₁ md₂ → Rel (Rcomb.bind Q md₁) (Rcomb.bind Q md₂)

      -- reindex respects Rel-related morphisms; the binder recursion is structural on Rel.
      reindex-mcong : ∀ {k} {Q : Poly (suc k)} {ρA ρB} {md₁ md₂ : Rcomb.MorD ρA ρB}
                      (r : Rel md₁ md₂) (t : Aα.TX.W Q ρA) →
                      Fα.TA'.W-≈ (Rcomb.reindex md₁ t) (Rcomb.reindex md₂ t)
      reindex-mcong {Q = Q} r (Aα.TX.sup y) = reindex-mcong-shape Q (rbind Q r) y

      reindex-mcong-shape : ∀ {j} (R : Poly j) {ρA ρB} {md₁ md₂ : Rcomb.MorD ρA ρB}
                            (r : Rel md₁ md₂) (y : Aα.TX.⟦ R ⟧shape ρA) →
                            Fα.TA'.shape≈ R ρB (Rcomb.reindex-shape R md₁ y) (Rcomb.reindex-shape R md₂ y)
      reindex-mcong-shape (const A') r y = A' .idx .isEquivalence .refl
      reindex-mcong-shape (var v)    r y = mrel-apply r v
      reindex-mcong-shape (P + P') r (inj₁ y) = reindex-mcong-shape P r y
      reindex-mcong-shape (P + P') r (inj₂ z) = reindex-mcong-shape P' r z
      reindex-mcong-shape (P × P') r (y , z) = reindex-mcong-shape P r y , reindex-mcong-shape P' r z
      reindex-mcong-shape (μ R'') r y = reindex-mcong r y

      mrel-apply : ∀ {k} {ρA ρB} {md₁ md₂ : Rcomb.MorD ρA ρB} (r : Rel md₁ md₂) (v : Fin k) {a} →
                   Fα.TA'.elEq (ρB v) (Rcomb.apply md₁ v a) (Rcomb.apply md₂ v a)
      mrel-apply (rcomb γ Q md fm)            Fin.zero     {a} = combine-lemma γ md fm a
      mrel-apply (rcomb {ρC = ρC} γ Q md fm) (Fin.suc v')      = Fα.TA'.elEq-refl (ρC v') _
      mrel-apply (rbind Q r)                  Fin.zero     {a} = reindex-mcong r a
      mrel-apply (rbind Q r)                 (Fin.suc v')      = mrel-apply r v'

      combine-lemma : ∀ {k} {Q : Poly (suc k)} {ρA ρB ρC} (γ : Γ .idx .Carrier)
                      (md : Aα.R.MorD ρA ρB) (fm : Fα.FMor ρB ρC) (t : Aα.TX.W Q ρA) →
                      Fα.TA'.W-≈ (Fα.fold-reindex γ fm (Aα.R.reindex md t)) (Rcomb.reindex (combine γ md fm) t)
      combine-lemma {Q = Q} γ md fm (Aα.TX.sup x) = combine-lemma-shape Q Q γ md fm x

      combine-lemma-shape : ∀ {k} (Q : Poly (suc k)) (R : Poly (suc k)) {ρA ρB ρC} (γ : Γ .idx .Carrier)
                            (md : Aα.R.MorD ρA ρB) (fm : Fα.FMor ρB ρC)
                            (x : Aα.TX.⟦ R ⟧shape (extend ρA (inj₂ (mkSort Q ρA)))) →
                            Fα.TA'.shape≈ R (extend ρC (inj₂ (mkSort Q ρC)))
                              (Fα.fold-reindex-shape γ R (Fα.fbind Q fm) (Aα.R.reindex-shape R (Aα.R.bind Q md) x))
                              (Rcomb.reindex-shape R (Rcomb.bind Q (combine γ md fm)) x)
      combine-lemma-shape Q (const A')              γ md fm x = A' .idx .isEquivalence .refl
      combine-lemma-shape Q (var Fin.zero)          γ md fm x = combine-lemma γ md fm x
      combine-lemma-shape Q (var (Fin.suc v)) {ρC = ρC} γ md fm x = Fα.TA'.elEq-refl (ρC v) _
      combine-lemma-shape Q (P + Q') γ md fm (inj₁ x) = combine-lemma-shape Q P γ md fm x
      combine-lemma-shape Q (P + Q') γ md fm (inj₂ y) = combine-lemma-shape Q Q' γ md fm y
      combine-lemma-shape Q (P × Q') γ md fm (x , y) =
        combine-lemma-shape Q P γ md fm x , combine-lemma-shape Q Q' γ md fm y
      combine-lemma-shape Q (μ R'') γ md fm x =
        Fα.TA'.W-≈-trans {x = Fα.fold-reindex γ (Fα.fbind Q fm) (Aα.R.reindex (Aα.R.bind Q md) x)}
                         {y = Rcomb.reindex (combine γ (Aα.R.bind Q md) (Fα.fbind Q fm)) x}
                         (combine-lemma γ (Aα.R.bind Q md) (Fα.fbind Q fm) x)
                         (reindex-mcong (rcomb γ Q md fm) x)

    -- Nested-μ fusion: the double reindex (α's mor₀ then the fold's fbase) equals the nested
    -- catamorphism (strong-μ-fmor = ⦅ α ∘ strong-fmor ⦆). `μ-fuse-idx` reduces `sup` on both
    -- sides to the shape-level body equality `μ-fuse-shape`, which inducts on the μ-body.
    module FuseM (Q' : Poly (suc (suc n))) where
      module Nβ = Nested Q'
      ηb : Fin (suc (suc n)) → Fin (suc n) ⊎ Sort (suc n)
      ηb = extend (λ v → inj₁ v) (inj₂ (mkSort Q' (λ v → inj₁ v)))
      mutual
        μ-fuse-idx : ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {m₁ m₂}
                     (m≈ : _≈s_ (fobj μo (μ Q') δ' .idx) m₁ m₂) →
                     _≈s_ (fobj μo (μ Q') (extend δ A) .idx)
                          (Fα.foldShape-idx (μ Q') γ₁ (Aα.R.reindex-shape (μ Q') Aα.mor₀ (Aα.embed-idx (μ Q') m₁)))
                          (strong-fmor (μ Q') fs .idxf .PS._⇒_.func (γ₂ , m₂))
        μ-fuse-idx γ≈ {Aα.TX.sup x₁} {Aα.TX.sup x₂} m≈ = μ-fuse-shape Q' γ≈ {x₁} {x₂} m≈

        μ-fuse-shape : (R : Poly (suc (suc n))) → ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {x₁ x₂}
                       (x≈ : Aα.TX.shape≈ R ηb x₁ x₂) →
                       Fα.TA'.shape≈ R ηb
                         (Fα.fold-reindex-shape γ₁ R (Fα.fbind Q' Fα.fbase) (Aα.R.reindex-shape R (Aα.R.MorD.bind Q' Aα.mor₀) x₁))
                         (Nβ.Aβ.R.reindex-shape R Nβ.Aβ.mor₀
                          (Nβ.Aβ.embed-idx R (strong-fmor R Nβ.fs' .idxf .PS._⇒_.func (γ₂ , Nβ.Fβ.foldShape-idx R γ₂ x₂))))
        μ-fuse-shape (const A')                   γ≈ x≈ = x≈
        μ-fuse-shape (var Fin.zero)               γ≈ {x₁} {x₂} x≈ = μ-fuse-idx γ≈ {x₁} {x₂} x≈
        μ-fuse-shape (var (Fin.suc Fin.zero))     γ≈ {x₁} {x₂} x≈ = Fα.fold-idx-resp γ≈ {x₁} {x₂} x≈
        μ-fuse-shape (var (Fin.suc (Fin.suc j)))  γ≈ x≈ = x≈
        μ-fuse-shape (R₁ + R₂) γ≈ {inj₁ _} {inj₁ _} x≈ = μ-fuse-shape R₁ γ≈ x≈
        μ-fuse-shape (R₁ + R₂) γ≈ {inj₂ _} {inj₂ _} x≈ = μ-fuse-shape R₂ γ≈ x≈
        μ-fuse-shape (R₁ × R₂) γ≈ {_ , _} {_ , _} (x≈₁ , x≈₂) = μ-fuse-shape R₁ γ≈ x≈₁ , μ-fuse-shape R₂ γ≈ x≈₂
        μ-fuse-shape (μ R'')   γ≈ x≈ = {!!}

    -- foldShape-idx ∘ reindex-shape ∘ embed-idx ≈ strong-fmor's idx action of the fold.
    β-idx : (R : Poly (suc n)) → ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {m₁ m₂}
            (m≈ : _≈s_ (fobj μo R δ' .idx) m₁ m₂) →
            _≈s_ (fobj μo R (extend δ A) .idx)
                 (Fα.foldShape-idx R γ₁ (Aα.R.reindex-shape R Aα.mor₀ (Aα.embed-idx R m₁)))
                 (strong-fmor R fs .idxf .PS._⇒_.func (γ₂ , m₂))
    β-idx (const A')        γ≈ m≈ = m≈
    β-idx (var Fin.zero)    γ≈ {m₁} {m₂} m≈ = Fα.fold-idx-resp γ≈ {m₁} {m₂} m≈
    β-idx (var (Fin.suc j)) γ≈ m≈ = m≈
    β-idx (Q₁ + Q₂) γ≈ {inj₁ _} {inj₁ _} m≈ = β-idx Q₁ γ≈ m≈
    β-idx (Q₁ + Q₂) γ≈ {inj₂ _} {inj₂ _} m≈ = β-idx Q₂ γ≈ m≈
    β-idx (Q₁ × Q₂) γ≈ {_ , _} {_ , _} (m≈₁ , m≈₂) = β-idx Q₁ γ≈ m≈₁ , β-idx Q₂ γ≈ m≈₂
    β-idx (μ Q')            γ≈ {m₁} {m₂} m≈ = FuseM.μ-fuse-idx Q' γ≈ {m₁} {m₂} m≈

  -- Probe: external function instantiating BetaDef and delegating to its FuseM.
  μ-fuse-idx-ext : ∀ {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
                   (alg : Mor (Fam𝒞-P.prod Γ (fobj μObj P (extend δ A))) A)
                   (Q' : Poly (suc (suc n))) →
                   let module B = BetaDef {Γ = Γ} {A = A} {P = P} {δ = δ} alg in
                   ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {m₁ m₂}
                   (m≈ : _≈s_ (fobj μObj (μ Q') (B.δ') .idx) m₁ m₂) →
                   _≈s_ (fobj μObj (μ Q') (extend δ A) .idx)
                        (B.Fα.foldShape-idx (μ Q') γ₁ (B.Aα.R.reindex-shape (μ Q') B.Aα.mor₀ (B.Aα.embed-idx (μ Q') m₁)))
                        (HasMu.strong-fmor hasMu (μ Q') B.fs .idxf .PS._⇒_.func (γ₂ , m₂))
  μ-fuse-idx-ext {Γ = Γ} {A = A} {P = P} {δ = δ} alg Q' γ≈ {m₁} {m₂} m≈ =
    BetaDef.FuseM.μ-fuse-idx {Γ = Γ} {A = A} {P = P} {δ = δ} alg Q' γ≈ {m₁} {m₂} m≈

  hasMuLaws : HasMuLaws hasMu
  hasMuLaws .HasMuLaws.⦅⦆-β {P = P} alg ._≃_.idxf-eq .PS._≃m_.func-eq (γ≈ , m≈) =
    alg .idxf .PS._⇒_.func-resp-≈ (γ≈ , BetaDef.β-idx alg P γ≈ m≈)
  hasMuLaws .HasMuLaws.⦅⦆-β alg ._≃_.famf-eq = {!!}
  hasMuLaws .HasMuLaws.⦅⦆-η alg h eq = {!!}
