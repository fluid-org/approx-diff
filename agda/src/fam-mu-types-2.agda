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
    -- PARKED: typechecks structurally but the non-injective `W-≈`/`fib` in the types
    -- generate cascading unsolved implicits at the `μ`/W level; needs per-occurrence pinning.
    {-
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
                          (reindex-fam-W md {t'} ∘ TA.fib-subst p)
                            ≈ (TB.fib-subst (reindex-resp md {t} {t'} p) ∘ reindex-fam-W md {t})
      reindex-fam-W-nat {Q = Q} md {TA.sup x} {TA.sup y} p = reindex-fam-nat Q (bind Q md) {x} {y} p

      apply-fam-nat : ∀ {k} {ρA ρB} (md : MorD {k} ρA ρB) (v : Fin k) {a a'}
                      (p : TA.elEq (ρA v) a a') →
                      (apply-fam md v a' ∘ TA.fib-el-subst (ρA v) p)
                        ≈ (TB.fib-el-subst (ρB v) (apply-resp md v p) ∘ apply-fam md v a)
      apply-fam-nat (base _ _ _ ffam-nat) v p = ffam-nat v p
      apply-fam-nat (bind Q md) Fin.zero    {a} {a'} p = reindex-fam-W-nat md {a} {a'} p
      apply-fam-nat (bind Q md) (Fin.suc v) p = apply-fam-nat md v p
    -}

  μObj : ∀ {n} → Poly (suc n) → (Fin n → Obj) → Obj
  μObj P δ .idx = WSetoid δ P (λ i → inj₁ i)
  μObj P δ .fam = WFam δ P (λ i → inj₁ i)

  hasMu : HasMu
  hasMu .HasMu.μ-obj = μObj
  hasMu .HasMu.α {n} P δ = αmor
    where
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
      αmor : Mor (fobj μo P δ') (μo P δ)
      αmor .idxf .PS._⇒_.func i = Tδ.sup (R.reindex-shape P mor₀ (embed-idx P i))
      αmor .idxf .PS._⇒_.func-resp-≈ x≈y = R.reindex-shape-resp P mor₀ (embed-idx-resp P x≈y)
      αmor .famf ._⇒f_.transf x = R.reindex-fam P mor₀ ∘ embed-fam P x
      αmor .famf ._⇒f_.natural e = {!!}
  hasMu .HasMu.⦅_⦆ alg        = {!!}

  hasMuLaws : HasMuLaws hasMu
  hasMuLaws .HasMuLaws.⦅⦆-β alg     = {!!}
  hasMuLaws .HasMuLaws.⦅⦆-η alg h eq = {!!}
