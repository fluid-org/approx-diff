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

open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts)
open import prop-setoid as PS
  using (IsEquivalence; Setoid)
open import indexed-family using (Fam; _⇒f_)
import fam
import polynomial-functor-2

open Setoid using (Carrier; isEquivalence) renaming (_≈_ to _≈s_)

module fam-mu-types-2 where

------------------------------------------------------------------------------
-- HasMu instance for the Fam construction.
module WFam {o m e} (os es : _) {𝒞 : Category o m e} (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where
  open Category 𝒞
  open IsEquivalence
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

  -- The body environment of a μ-binder: slot 0 is the binder's own sort, the
  -- rest are the ambient parameters.
  η₀ : ∀ {n} → Poly (suc n) → Fin (suc n) → Fin n ⊎ Sort n
  η₀ P = extend (λ i → inj₁ i) (inj₂ (mkSort P (λ i → inj₁ i)))

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
  module Reindex {nA nB} (δA : Fin nA → Obj) (δB : Fin nB → Obj) where
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

    -- Index-only reindex: the index action of a context morphism, with no fibre data.
    -- Carries both `MorD`'s index side (via `erase` below) and the fusion morphisms
    -- (`combine`), whose Γ-dependent fibre action lives externally in `FReindex`.
    data IMorD : ∀ {k} → (Fin k → Fin nA ⊎ Sort nA) → (Fin k → Fin nB ⊎ Sort nB) →
                 Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      ibase : ∀ {k} {ρA ρB} (f : ∀ v → TA.El (ρA v) → TB.El (ρB v))
              (f-resp : ∀ v {a a'} → TA.elEq (ρA v) a a' → TB.elEq (ρB v) (f v a) (f v a')) →
              IMorD {k} ρA ρB
      ibind : ∀ {k} {ρA ρB} (Q : Poly (suc k)) → IMorD ρA ρB →
              IMorD (extend ρA (inj₂ (mkSort Q ρA))) (extend ρB (inj₂ (mkSort Q ρB)))

    mutual
      ireindex : ∀ {k} {Q : Poly (suc k)} {ρA ρB} (md : IMorD ρA ρB) → TA.W Q ρA → TB.W Q ρB
      ireindex {Q = Q} md (TA.sup x) = TB.sup (ireindex-shape Q (ibind Q md) x)

      ireindex-shape : ∀ {j} (R : Poly j) {ηA ηB} (md : IMorD ηA ηB) → TA.⟦ R ⟧shape ηA → TB.⟦ R ⟧shape ηB
      ireindex-shape (const A) md a = a
      ireindex-shape (var v)   md a = iapply md v a
      ireindex-shape (P + Q) md (inj₁ a) = inj₁ (ireindex-shape P md a)
      ireindex-shape (P + Q) md (inj₂ b) = inj₂ (ireindex-shape Q md b)
      ireindex-shape (P × Q) md (a , b) = ireindex-shape P md a , ireindex-shape Q md b
      ireindex-shape (μ Q') md t = ireindex md t

      iapply : ∀ {k} {ρA ρB} (md : IMorD {k} ρA ρB) (v : Fin k) → TA.El (ρA v) → TB.El (ρB v)
      iapply (ibase f _) v        a = f v a
      iapply (ibind Q md) Fin.zero    a = ireindex md a
      iapply (ibind Q md) (Fin.suc v) a = iapply md v a

    mutual
      ireindex-resp : ∀ {k} {Q : Poly (suc k)} {ρA ρB} (md : IMorD ρA ρB) {t t' : TA.W Q ρA} →
                      TA.W-≈ t t' → TB.W-≈ (ireindex md t) (ireindex md t')
      ireindex-resp {Q = Q} md {TA.sup x} {TA.sup y} p = ireindex-shape-resp Q (ibind Q md) {x} {y} p

      ireindex-shape-resp : ∀ {j} (R : Poly j) {ηA ηB} (md : IMorD ηA ηB) {a a' : TA.⟦ R ⟧shape ηA} →
                            TA.shape≈ R ηA a a' → TB.shape≈ R ηB (ireindex-shape R md a) (ireindex-shape R md a')
      ireindex-shape-resp (const A) md p = p
      ireindex-shape-resp (var v)   md p = iapply-resp md v p
      ireindex-shape-resp (P + Q) md {inj₁ _} {inj₁ _} p = ireindex-shape-resp P md p
      ireindex-shape-resp (P + Q) md {inj₂ _} {inj₂ _} p = ireindex-shape-resp Q md p
      ireindex-shape-resp (P × Q) md {_ , _} {_ , _} (p₁ , p₂) = ireindex-shape-resp P md p₁ , ireindex-shape-resp Q md p₂
      ireindex-shape-resp (μ Q') md {a} {a'} p = ireindex-resp md {a} {a'} p

      iapply-resp : ∀ {k} {ρA ρB} (md : IMorD {k} ρA ρB) (v : Fin k) {a a'} →
                    TA.elEq (ρA v) a a' → TB.elEq (ρB v) (iapply md v a) (iapply md v a')
      iapply-resp (ibase f f-resp) v       p = f-resp v p
      iapply-resp (ibind Q md)     Fin.zero    {a} {a'} p = ireindex-resp md {a} {a'} p
      iapply-resp (ibind Q md)     (Fin.suc v) p = iapply-resp md v p

    -- Erase the fibre fields; `MorD`'s index-level operations are `IMorD`'s.
    erase : ∀ {k} {ρA ρB} → MorD {k} ρA ρB → IMorD ρA ρB
    erase (base f f-resp _ _) = ibase f f-resp
    erase (bind Q md) = ibind Q (erase md)

    reindex : ∀ {k} {Q : Poly (suc k)} {ρA ρB} → MorD ρA ρB → TA.W Q ρA → TB.W Q ρB
    reindex md = ireindex (erase md)

    reindex-shape : ∀ {j} (R : Poly j) {ηA ηB} → MorD ηA ηB → TA.⟦ R ⟧shape ηA → TB.⟦ R ⟧shape ηB
    reindex-shape R md = ireindex-shape R (erase md)

    apply : ∀ {k} {ρA ρB} (md : MorD {k} ρA ρB) (v : Fin k) → TA.El (ρA v) → TB.El (ρB v)
    apply md = iapply (erase md)

    reindex-resp : ∀ {k} {Q : Poly (suc k)} {ρA ρB} (md : MorD ρA ρB) {t t' : TA.W Q ρA} →
                   TA.W-≈ t t' → TB.W-≈ (reindex md t) (reindex md t')
    reindex-resp md {t} {t'} = ireindex-resp (erase md) {t} {t'}

    reindex-shape-resp : ∀ {j} (R : Poly j) {ηA ηB} (md : MorD ηA ηB) {a a' : TA.⟦ R ⟧shape ηA} →
                         TA.shape≈ R ηA a a' → TB.shape≈ R ηB (reindex-shape R md a) (reindex-shape R md a')
    reindex-shape-resp R md {a} {a'} = ireindex-shape-resp R (erase md) {a} {a'}

    apply-resp : ∀ {k} {ρA ρB} (md : MorD {k} ρA ρB) (v : Fin k) {a a'} →
                 TA.elEq (ρA v) a a' → TB.elEq (ρB v) (apply md v a) (apply md v a')
    apply-resp md v {a} {a'} = iapply-resp (erase md) v {a} {a'}

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
      reindex-fam-natural : ∀ {j} (R : Poly j) {ηA ηB} (md : MorD ηA ηB)
                        {a a' : TA.⟦ R ⟧shape ηA} (p : TA.shape≈ R ηA a a') →
                        (reindex-fam R md {a'} ∘ TA.fib-shape-subst R ηA p)
                          ≈ (TB.fib-shape-subst R ηB (reindex-shape-resp R md p) ∘ reindex-fam R md {a})
      reindex-fam-natural (const A) md p = ≈-trans id-left (≈-sym id-right)
      reindex-fam-natural (var v)   md {a} {a'} p = apply-fam-natural md v {a} {a'} p
      reindex-fam-natural (P + Q) md {inj₁ a} {inj₁ a'} p = reindex-fam-natural P md p
      reindex-fam-natural (P + Q) md {inj₂ b} {inj₂ b'} p = reindex-fam-natural Q md p
      reindex-fam-natural (P × Q) md {a , b} {a' , b'} (p₁ , p₂) =
        ≈-trans (≈-sym (prod-m-comp _ _ _ _))
        (≈-trans (prod-m-cong (reindex-fam-natural P md p₁) (reindex-fam-natural Q md p₂))
                 (prod-m-comp _ _ _ _))
      reindex-fam-natural (μ Q') md {t} {t'} p = reindex-fam-W-natural md {t} {t'} p

      reindex-fam-W-natural : ∀ {k} {Q : Poly (suc k)} {ρA ρB} (md : MorD ρA ρB)
                          {t t' : TA.W Q ρA} (p : TA.W-≈ t t') →
                          (reindex-fam-W md {t'} ∘ TA.fib-subst {x = t} {y = t'} p)
                            ≈ (TB.fib-subst {x = reindex md t} {y = reindex md t'}
                                            (reindex-resp md {t} {t'} p) ∘ reindex-fam-W md {t})
      reindex-fam-W-natural {Q = Q} md {TA.sup x} {TA.sup y} p = reindex-fam-natural Q (bind Q md) {x} {y} p

      apply-fam-natural : ∀ {k} {ρA ρB} (md : MorD {k} ρA ρB) (v : Fin k) {a a'}
                      (p : TA.elEq (ρA v) a a') →
                      (apply-fam md v a' ∘ TA.fib-el-subst (ρA v) p)
                        ≈ (TB.fib-el-subst (ρB v) (apply-resp md v p) ∘ apply-fam md v a)
      apply-fam-natural (base _ _ _ ffam-natural) v p = ffam-natural v p
      apply-fam-natural (bind Q md) Fin.zero    {a} {a'} p = reindex-fam-W-natural md {a} {a'} p
      apply-fam-natural (bind Q md) (Fin.suc v) p = apply-fam-natural md v p

  μObj : ∀ {n} → Poly (suc n) → (Fin n → Obj) → Obj
  μObj P δ .idx = WSetoid δ P (λ i → inj₁ i)
  μObj P δ .fam = WFam δ P (λ i → inj₁ i)

  -- The fold (catamorphism) for the μ-type, lifted to a standalone module so its
  -- mutual recursion is termination-checked independently of the `hasMu` copattern.
  module FoldDef {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
                 (alg : Mor (Fam𝒞-P.prod Γ (fobj μObj P (extend δ A))) A) where
      module Tδ = Tree δ
      module TA' = Tree (extend δ A)
      -- Fold-specific reindex morphism (first-order, like `MorD`): `fbase` sends the outer
      -- recursion slot to the fold and parameters to themselves; `fbind` records a binder.
      data FMor : ∀ {k} → (Fin k → Fin n ⊎ Sort n) → (Fin k → Fin (suc n) ⊎ Sort (suc n)) →
                  Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
        fbase : FMor (η₀ P) (λ v → inj₁ v)
        fbind : ∀ {k} {ρ ρ'} (Q : Poly (suc k)) → FMor ρ ρ' →
                FMor (extend ρ (inj₂ (mkSort Q ρ))) (extend ρ' (inj₂ (mkSort Q ρ')))
      -- Fold the outer μ via `alg`; nested μ are reindexed into the `extend δ A` context,
      -- the recursion slot carrying the fold itself (inlined, so every call is structural).
      mutual
        fold-idx : Γ .idx .Carrier → Tδ.W P (λ i → inj₁ i) → A .idx .Carrier
        fold-idx γ (Tδ.sup x) = alg .idxf .PS._⇒_.func (γ , fold-shape-idx P γ x)

        fold-shape-idx : (Q : Poly (suc n)) → Γ .idx .Carrier → Tδ.⟦ Q ⟧shape (η₀ P) →
                        fobj μObj Q (extend δ A) .idx .Carrier
        fold-shape-idx (const A')        γ a = a
        fold-shape-idx (var Fin.zero)    γ t = fold-idx γ t
        fold-shape-idx (var (Fin.suc i)) γ a = a
        fold-shape-idx (Q₁ + Q₂) γ (inj₁ x) = inj₁ (fold-shape-idx Q₁ γ x)
        fold-shape-idx (Q₁ + Q₂) γ (inj₂ y) = inj₂ (fold-shape-idx Q₂ γ y)
        fold-shape-idx (Q₁ × Q₂) γ (x , y) = fold-shape-idx Q₁ γ x , fold-shape-idx Q₂ γ y
        fold-shape-idx (μ Q')    γ t = fold-reindex γ fbase t

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
        fold-idx-resp γ≈ {Tδ.sup x} {Tδ.sup y} p = alg .idxf .PS._⇒_.func-resp-≈ (γ≈ , fold-shape-idx-resp P γ≈ p)

        fold-shape-idx-resp : (Q : Poly (suc n)) → ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {x x'}
                             (p : Tδ.shape≈ Q (η₀ P) x x') →
                             _≈s_ (fobj μObj Q (extend δ A) .idx) (fold-shape-idx Q γ x) (fold-shape-idx Q γ' x')
        fold-shape-idx-resp (const A')        γ≈ p = p
        fold-shape-idx-resp (var Fin.zero)    γ≈ {x} {x'} p = fold-idx-resp γ≈ {x} {x'} p
        fold-shape-idx-resp (var (Fin.suc i)) γ≈ p = p
        fold-shape-idx-resp (Q₁ + Q₂) γ≈ {inj₁ _} {inj₁ _} p = fold-shape-idx-resp Q₁ γ≈ p
        fold-shape-idx-resp (Q₁ + Q₂) γ≈ {inj₂ _} {inj₂ _} p = fold-shape-idx-resp Q₂ γ≈ p
        fold-shape-idx-resp (Q₁ × Q₂) γ≈ {_ , _} {_ , _} (p₁ , p₂) =
          fold-shape-idx-resp Q₁ γ≈ p₁ , fold-shape-idx-resp Q₂ γ≈ p₂
        fold-shape-idx-resp (μ Q')    γ≈ {x} {x'} p = fold-reindex-resp γ≈ fbase {x} {x'} p

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
          alg .famf ._⇒f_.transf (γ , fold-shape-idx P γ x) ∘ pair p₁ (fold-shape-fam P γ x)

        fold-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ Q ⟧shape (η₀ P)) →
                        prod (Γ .fam .fm γ) (Tδ.fib-shape Q (η₀ P) x) ⇒ fobj μObj Q (extend δ A) .fam .fm (fold-shape-idx Q γ x)
        fold-shape-fam (const A')        γ a = p₂
        fold-shape-fam (var Fin.zero)    γ t = fold-fam γ t
        fold-shape-fam (var (Fin.suc i)) γ a = p₂
        fold-shape-fam (Q₁ + Q₂) γ (inj₁ x) = fold-shape-fam Q₁ γ x
        fold-shape-fam (Q₁ + Q₂) γ (inj₂ y) = fold-shape-fam Q₂ γ y
        fold-shape-fam (Q₁ × Q₂) γ (x , y) = strong-prod-m (fold-shape-fam Q₁ γ x) (fold-shape-fam Q₂ γ y)
        fold-shape-fam (μ Q')    γ t = fold-reindex-fam γ fbase t

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
          strong-prod-m (fold-reindex-shape-fam γ P' md a) (fold-reindex-shape-fam γ Q' md b)
        fold-reindex-shape-fam γ (μ Q'')   md t = fold-reindex-fam γ md t

        fold-apply-fam : ∀ {k} {ρ ρ'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ') (v : Fin k) (a : Tδ.El (ρ v)) →
                         prod (Γ .fam .fm γ) (Tδ.fib-el (ρ v) a) ⇒ TA'.fib-el (ρ' v) (fold-apply γ md v a)
        fold-apply-fam γ fbase        Fin.zero    t = fold-fam γ t
        fold-apply-fam γ fbase        (Fin.suc i) a = p₂
        fold-apply-fam γ (fbind Q md) Fin.zero    a = fold-reindex-fam γ md a
        fold-apply-fam γ (fbind Q md) (Fin.suc v) a = fold-apply-fam γ md v a



      -- The fibre fold is natural: it commutes with `subst` (in both Γ and the tree).
      mutual
        fold-fam-natural : ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {t t'} (p : Tδ.W-≈ t t') →
                       (fold-fam γ₂ t' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-subst {x = t} {y = t'} p))
                         ≈ (A .fam .subst (fold-idx-resp γ≈ {t} {t'} p) ∘ fold-fam γ₁ t)
        fold-fam-natural {γ₁} {γ₂} γ≈ {Tδ.sup x} {Tδ.sup y} p =
          ≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl (pair-natural _ _ _))
          (≈-trans (∘-cong ≈-refl (pair-cong (pair-p₁ _ _) (fold-shape-fam-natural P γ≈ {x} {y} p)))
          (≈-trans (∘-cong ≈-refl (≈-sym (pair-compose _ _ _ _)))
          (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong (alg .famf ._⇒f_.natural (γ≈ , fold-shape-idx-resp P γ≈ {x} {y} p)) ≈-refl)
                   (assoc _ _ _))))))

        fold-shape-fam-natural : (Q : Poly (suc n)) → ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {x x'}
                            (p : Tδ.shape≈ Q (η₀ P) x x') →
                            (fold-shape-fam Q γ₂ x' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-shape-subst Q (η₀ P) p))
                              ≈ (fobj μObj Q (extend δ A) .fam .subst (fold-shape-idx-resp Q γ≈ p) ∘ fold-shape-fam Q γ₁ x)
        fold-shape-fam-natural (const A')        γ≈ p = pair-p₂ _ _
        fold-shape-fam-natural (var Fin.zero)    γ≈ {x} {x'} p = fold-fam-natural γ≈ {x} {x'} p
        fold-shape-fam-natural (var (Fin.suc i)) γ≈ p = pair-p₂ _ _
        fold-shape-fam-natural (Q₁ + Q₂) γ≈ {inj₁ _} {inj₁ _} p = fold-shape-fam-natural Q₁ γ≈ p
        fold-shape-fam-natural (Q₁ + Q₂) γ≈ {inj₂ _} {inj₂ _} p = fold-shape-fam-natural Q₂ γ≈ p
        fold-shape-fam-natural (Q₁ × Q₂) γ≈ {x₁ , x₂} {x₁' , x₂'} (p₁p , p₂p) =
          strong-prod-m-natural (fold-shape-fam-natural Q₁ γ≈ p₁p) (fold-shape-fam-natural Q₂ γ≈ p₂p)
        fold-shape-fam-natural (μ Q')    γ≈ {x} {x'} p = fold-reindex-fam-natural γ≈ fbase {x} {x'} p

        fold-reindex-fam-natural : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂)
                               (md : FMor ρ ρ') {t t' : Tδ.W Q ρ} (p : Tδ.W-≈ t t') →
                               (fold-reindex-fam γ₂ md t' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-subst {x = t} {y = t'} p))
                                 ≈ (TA'.fib-subst {x = fold-reindex γ₁ md t} {y = fold-reindex γ₂ md t'}
                                                  (fold-reindex-resp γ≈ md {t} {t'} p) ∘ fold-reindex-fam γ₁ md t)
        fold-reindex-fam-natural {Q = Q} γ≈ md {Tδ.sup x} {Tδ.sup y} p = fold-reindex-shape-fam-natural γ≈ Q (fbind Q md) {x} {y} p

        fold-reindex-shape-fam-natural : ∀ {j} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (R : Poly j) {ηA ηB} (md : FMor ηA ηB)
                                     {a a' : Tδ.⟦ R ⟧shape ηA} (p : Tδ.shape≈ R ηA a a') →
                                     (fold-reindex-shape-fam γ₂ R md a' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-shape-subst R ηA p))
                                       ≈ (TA'.fib-shape-subst R ηB (fold-reindex-shape-resp γ≈ R md p) ∘ fold-reindex-shape-fam γ₁ R md a)
        fold-reindex-shape-fam-natural γ≈ (const A') md p = pair-p₂ _ _
        fold-reindex-shape-fam-natural γ≈ (var v)    md p = fold-apply-fam-natural γ≈ md v p
        fold-reindex-shape-fam-natural γ≈ (P' + Q') md {inj₁ _} {inj₁ _} p = fold-reindex-shape-fam-natural γ≈ P' md p
        fold-reindex-shape-fam-natural γ≈ (P' + Q') md {inj₂ _} {inj₂ _} p = fold-reindex-shape-fam-natural γ≈ Q' md p
        fold-reindex-shape-fam-natural γ≈ (P' × Q') md {a₁ , a₂} {a₁' , a₂'} (p₁p , p₂p) =
          strong-prod-m-natural (fold-reindex-shape-fam-natural γ≈ P' md p₁p) (fold-reindex-shape-fam-natural γ≈ Q' md p₂p)
        fold-reindex-shape-fam-natural γ≈ (μ Q'')   md {a} {a'} p = fold-reindex-fam-natural γ≈ md {a} {a'} p

        fold-apply-fam-natural : ∀ {k} {ρ ρ'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (md : FMor ρ ρ') (v : Fin k)
                             {a a'} (p : Tδ.elEq (ρ v) a a') →
                             (fold-apply-fam γ₂ md v a' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-el-subst (ρ v) p))
                               ≈ (TA'.fib-el-subst (ρ' v) (fold-apply-resp γ≈ md v p) ∘ fold-apply-fam γ₁ md v a)
        fold-apply-fam-natural γ≈ fbase        Fin.zero    {a} {a'} p = fold-fam-natural γ≈ {a} {a'} p
        fold-apply-fam-natural γ≈ fbase        (Fin.suc i) p = pair-p₂ _ _
        fold-apply-fam-natural γ≈ (fbind Q md) Fin.zero    {a} {a'} p = fold-reindex-fam-natural γ≈ md {a} {a'} p
        fold-apply-fam-natural γ≈ (fbind Q md) (Fin.suc v) p = fold-apply-fam-natural γ≈ md v p

      foldMor : Mor (Fam𝒞-P.prod Γ (μObj P δ)) A
      foldMor .idxf .PS._⇒_.func (γ , t) = fold-idx γ t
      foldMor .idxf .PS._⇒_.func-resp-≈ {γ , t} {γ' , t'} (γ≈ , t≈) = fold-idx-resp γ≈ {t} {t'} t≈
      foldMor .famf ._⇒f_.transf (γ , t) = fold-fam γ t
      foldMor .famf ._⇒f_.natural {γ₁ , t₁} {γ₂ , t₂} (γ≈ , t≈) = fold-fam-natural γ≈ {t₁} {t₂} t≈

  -- α's reconstruction machinery, lifted to a named module so the β/η laws can
  -- reference embed-idx / embed-fam / mor₀ (the fold and Reindex are already named).
  module AlphaDef {n} (P : Poly (suc n)) (δ : Fin n → Obj) where
      δ' = extend δ (μObj P δ)
      module Tδ = Tree δ
      module TX = Tree δ'
      module R  = Reindex δ' δ
      -- Bridge `fobj`'s native structure to our `⟦_⟧shape` (identity at leaves and μ).
      embed-idx : (Q : Poly (suc n)) → fobj μObj Q δ' .idx .Carrier → TX.⟦ Q ⟧shape (λ v → inj₁ v)
      embed-idx (const A) a = a
      embed-idx (var v)   a = a
      embed-idx (Q₁ + Q₂) (inj₁ x) = inj₁ (embed-idx Q₁ x)
      embed-idx (Q₁ + Q₂) (inj₂ y) = inj₂ (embed-idx Q₂ y)
      embed-idx (Q₁ × Q₂) (x , y) = embed-idx Q₁ x , embed-idx Q₂ y
      embed-idx (μ Q')    t = t
      embed-idx-resp : (Q : Poly (suc n)) {x y : fobj μObj Q δ' .idx .Carrier} →
                       _≈s_ (fobj μObj Q δ' .idx) x y → TX.shape≈ Q (λ v → inj₁ v) (embed-idx Q x) (embed-idx Q y)
      embed-idx-resp (const A) p = p
      embed-idx-resp (var v)   p = p
      embed-idx-resp (Q₁ + Q₂) {inj₁ _} {inj₁ _} p = embed-idx-resp Q₁ p
      embed-idx-resp (Q₁ + Q₂) {inj₂ _} {inj₂ _} p = embed-idx-resp Q₂ p
      embed-idx-resp (Q₁ × Q₂) {_ , _} {_ , _} (p₁ , p₂) = embed-idx-resp Q₁ p₁ , embed-idx-resp Q₂ p₂
      embed-idx-resp (μ Q')    p = p
      -- Inverse bridge: `⟦_⟧shape` over the fresh context back to `fobj`'s native
      -- structure (identity at leaves and μ, like `embed-idx`).
      unembed-idx : (Q : Poly (suc n)) → TX.⟦ Q ⟧shape (λ v → inj₁ v) → fobj μObj Q δ' .idx .Carrier
      unembed-idx (const A) a = a
      unembed-idx (var v)   a = a
      unembed-idx (Q₁ + Q₂) (inj₁ x) = inj₁ (unembed-idx Q₁ x)
      unembed-idx (Q₁ + Q₂) (inj₂ y) = inj₂ (unembed-idx Q₂ y)
      unembed-idx (Q₁ × Q₂) (x , y) = unembed-idx Q₁ x , unembed-idx Q₂ y
      unembed-idx (μ Q')    t = t

      unembed-idx-resp : (Q : Poly (suc n)) {x y : TX.⟦ Q ⟧shape (λ v → inj₁ v)} →
                         TX.shape≈ Q (λ v → inj₁ v) x y →
                         _≈s_ (fobj μObj Q δ' .idx) (unembed-idx Q x) (unembed-idx Q y)
      unembed-idx-resp (const A) p = p
      unembed-idx-resp (var v)   p = p
      unembed-idx-resp (Q₁ + Q₂) {inj₁ _} {inj₁ _} p = unembed-idx-resp Q₁ p
      unembed-idx-resp (Q₁ + Q₂) {inj₂ _} {inj₂ _} p = unembed-idx-resp Q₂ p
      unembed-idx-resp (Q₁ × Q₂) {_ , _} {_ , _} (p₁ , p₂) = unembed-idx-resp Q₁ p₁ , unembed-idx-resp Q₂ p₂
      unembed-idx-resp (μ Q')    p = p

      -- Embedding after unembedding is the identity.
      embed-unembed : (Q : Poly (suc n)) (x : TX.⟦ Q ⟧shape (λ v → inj₁ v)) →
                      TX.shape≈ Q (λ v → inj₁ v) (embed-idx Q (unembed-idx Q x)) x
      embed-unembed (const A) a = A .idx .isEquivalence .refl
      embed-unembed (var v)   a = TX.elEq-refl (inj₁ v) a
      embed-unembed (Q₁ + Q₂) (inj₁ x) = embed-unembed Q₁ x
      embed-unembed (Q₁ + Q₂) (inj₂ y) = embed-unembed Q₂ y
      embed-unembed (Q₁ × Q₂) (x , y) = embed-unembed Q₁ x , embed-unembed Q₂ y
      embed-unembed (μ Q')    t = TX.W-≈-refl t

      m₀ : ∀ v → TX.El (inj₁ v) → Tδ.El (η₀ P v)
      m₀ Fin.zero    a = a
      m₀ (Fin.suc i) a = a
      m₀-resp : ∀ v {a a'} → TX.elEq (inj₁ v) a a' → Tδ.elEq (η₀ P v) (m₀ v a) (m₀ v a')
      m₀-resp Fin.zero    p = p
      m₀-resp (Fin.suc i) p = p
      m₀-fam : ∀ v (a : TX.El (inj₁ v)) → TX.fib-el (inj₁ v) a ⇒ Tδ.fib-el (η₀ P v) (m₀ v a)
      m₀-fam Fin.zero    a = id _
      m₀-fam (Fin.suc i) a = id _
      m₀-fam-natural : ∀ v {a a'} (p : TX.elEq (inj₁ v) a a') →
                   (m₀-fam v a' ∘ TX.fib-el-subst (inj₁ v) p) ≈ (Tδ.fib-el-subst (η₀ P v) (m₀-resp v p) ∘ m₀-fam v a)
      m₀-fam-natural Fin.zero    p = ≈-trans id-left (≈-sym id-right)
      m₀-fam-natural (Fin.suc i) p = ≈-trans id-left (≈-sym id-right)
      mor₀ : R.MorD (λ v → inj₁ v) (η₀ P)
      mor₀ = R.base m₀ m₀-resp m₀-fam m₀-fam-natural
      -- Fibre bridge: `fobj`'s fibre to our `fib-shape` (identity at leaves, products at ×).
      embed-fam : (Q : Poly (suc n)) (x : fobj μObj Q δ' .idx .Carrier) →
                  fobj μObj Q δ' .fam .fm x ⇒ TX.fib-shape Q (λ v → inj₁ v) (embed-idx Q x)
      embed-fam (const A) a = id _
      embed-fam (var v)   a = id _
      embed-fam (Q₁ + Q₂) (inj₁ x) = embed-fam Q₁ x
      embed-fam (Q₁ + Q₂) (inj₂ y) = embed-fam Q₂ y
      embed-fam (Q₁ × Q₂) (x , y) = prod-m (embed-fam Q₁ x) (embed-fam Q₂ y)
      embed-fam (μ Q')    t = id _
      embed-fam-naturalural : (Q : Poly (suc n)) {x y : fobj μObj Q δ' .idx .Carrier} (e : _≈s_ (fobj μObj Q δ' .idx) x y) →
                          (embed-fam Q y ∘ fobj μObj Q δ' .fam .subst e)
                            ≈ (TX.fib-shape-subst Q (λ v → inj₁ v) (embed-idx-resp Q e) ∘ embed-fam Q x)
      embed-fam-naturalural (const A) e = ≈-trans id-left (≈-sym id-right)
      embed-fam-naturalural (var v)   e = ≈-trans id-left (≈-sym id-right)
      embed-fam-naturalural (Q₁ + Q₂) {inj₁ _} {inj₁ _} e = embed-fam-naturalural Q₁ e
      embed-fam-naturalural (Q₁ + Q₂) {inj₂ _} {inj₂ _} e = embed-fam-naturalural Q₂ e
      embed-fam-naturalural (Q₁ × Q₂) {_ , _} {_ , _} (e₁ , e₂) =
        ≈-trans (≈-sym (prod-m-comp _ _ _ _))
        (≈-trans (prod-m-cong (embed-fam-naturalural Q₁ e₁) (embed-fam-naturalural Q₂ e₂)) (prod-m-comp _ _ _ _))
      embed-fam-naturalural (μ Q')    e = ≈-trans id-left (≈-sym id-right)
      αmor : Mor (fobj μObj P δ') (μObj P δ)
      αmor .idxf .PS._⇒_.func i = Tδ.sup (R.reindex-shape P mor₀ (embed-idx P i))
      αmor .idxf .PS._⇒_.func-resp-≈ x≈y = R.reindex-shape-resp P mor₀ (embed-idx-resp P x≈y)
      αmor .famf ._⇒f_.transf x = R.reindex-fam P mor₀ ∘ embed-fam P x
      αmor .famf ._⇒f_.natural e =
        ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (embed-fam-naturalural P e))
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong₁ (R.reindex-fam-natural P mor₀ (embed-idx-resp P e)))
                 (assoc _ _ _))))

  hasMu : HasMu
  hasMu .HasMu.μ-obj = μObj
  hasMu .HasMu.α P δ = AlphaDef.αmor P δ
  hasMu .HasMu.⦅_⦆ alg = FoldDef.foldMor alg

  -- Fibre reindex over an index-only reindex `cmb`, driven by an EXTERNAL per-variable
  -- action `act`: a fold's fibre action is Γ-dependent (`prod Γ -` on the source), so it
  -- cannot live in a reindex morphism and is carried separately. The ambient Γ-fibre is `G`.
  module FReindex {nA nB} {δA : Fin nA → Obj} {δB : Fin nB → Obj} (G : obj) where
    private
      module TA = Tree δA
      module TB = Tree δB
    open Reindex δA δB using (IMorD; ireindex; ireindex-shape; iapply; ibind)

    -- Defunctionalised action: `abase` supplies all var fibres directly (a Γ-dependent fold);
    -- `abind` extends across a binder. Data (not a function) so the recursion stays structural.
    data FAct : ∀ {k} {ρA ρB} → IMorD {k} ρA ρB → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      abase : ∀ {k} {ρA ρB} {cmb : IMorD {k} ρA ρB}
              (afib : ∀ v (a : TA.El (ρA v)) → prod G (TA.fib-el (ρA v) a) ⇒ TB.fib-el (ρB v) (iapply cmb v a)) →
              FAct cmb
      abind : ∀ {k} {ρA ρB} (Q : Poly (suc k)) (cmb : IMorD ρA ρB) → FAct cmb → FAct (ibind Q cmb)

    mutual
      freindex-fam : ∀ {k} {Q : Poly (suc k)} {ρA ρB} {cmb : IMorD ρA ρB} (act : FAct cmb)
                     {t : TA.W Q ρA} → prod G (TA.fib t) ⇒ TB.fib (ireindex cmb t)
      freindex-fam {Q = Q} {cmb = cmb} act {TA.sup x} = freindex-shape-fam Q (abind Q cmb act) {x}

      freindex-shape-fam : ∀ {j} (R : Poly j) {ηA ηB} {cmb : IMorD ηA ηB} (act : FAct cmb)
                           {a : TA.⟦ R ⟧shape ηA} →
                           prod G (TA.fib-shape R ηA a) ⇒ TB.fib-shape R ηB (ireindex-shape R cmb a)
      freindex-shape-fam (const A') act = p₂
      freindex-shape-fam (var v)    act {a} = aapply act v a
      freindex-shape-fam (P + Q) act {inj₁ a} = freindex-shape-fam P act {a}
      freindex-shape-fam (P + Q) act {inj₂ b} = freindex-shape-fam Q act {b}
      freindex-shape-fam (P × Q) act {a , b} =
        strong-prod-m (freindex-shape-fam P act {a}) (freindex-shape-fam Q act {b})
      freindex-shape-fam (μ Q') act {t} = freindex-fam act {t}

      aapply : ∀ {k} {ρA ρB} {cmb : IMorD {k} ρA ρB} (act : FAct cmb) (v : Fin k) (a : TA.El (ρA v)) →
               prod G (TA.fib-el (ρA v) a) ⇒ TB.fib-el (ρB v) (iapply cmb v a)
      aapply (abase afib)     v           a = afib v a
      aapply (abind Q cmb act) Fin.zero    a = freindex-fam act {a}
      aapply (abind Q cmb act) (Fin.suc v) a = aapply act v a

  -- General free-family fusion: a single reindex (the collapsed double-reindex, via combine-lemma)
  -- equals the functorial map. Families sₛ/sₜ are FREE so the nested-μ recursion's family fits.
  fuse-idx : ∀ {n} {Γ : Obj} {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
                 let module Rs = Reindex sₛ sₜ in
                 (cmb : Γ .idx .Carrier → Rs.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
                 (fsk : ∀ i → Mor (Fam𝒞-P.prod Γ (sₛ i)) (sₜ i))
                 (corr : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                         _≈s_ (sₜ i .idx) (Rs.iapply (cmb γ₁) i a₁) (fsk i .idxf .PS._⇒_.func (γ₂ , a₂))) →
                 ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {m₁ m₂}
                 (m≈ : _≈s_ (μObj Q sₛ .idx) m₁ m₂) →
                 _≈s_ (μObj Q sₜ .idx)
                   (Rs.ireindex (cmb γ₁) m₁)
                   (HasMu.strong-fmor hasMu (μ Q) fsk .idxf .PS._⇒_.func (γ₂ , m₂))
  fuse-shape : ∀ {n} {Γ : Obj} {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
                   let module Rs = Reindex sₛ sₜ
                       module Ts = Tree sₛ
                       module Tt = Tree sₜ
                       module At = AlphaDef Q sₜ in
                   (cmb : Γ .idx .Carrier → Rs.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
                   (fsk : ∀ i → Mor (Fam𝒞-P.prod Γ (sₛ i)) (sₜ i))
                   (corr : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                           _≈s_ (sₜ i .idx) (Rs.iapply (cmb γ₁) i a₁) (fsk i .idxf .PS._⇒_.func (γ₂ , a₂))) →
                   let module Ft = FoldDef {Γ = Γ} {A = μObj Q sₜ} {P = Q} {δ = sₛ}
                                     (Mor-∘ At.αmor (HasMu.strong-fmor hasMu Q (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂))) in
                   (R : Poly (suc n)) →
                   ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {x₁ x₂}
                   (x≈ : Ts.shape≈ R (η₀ Q) x₁ x₂) →
                   Tt.shape≈ R (η₀ Q)
                     (Rs.ireindex-shape R (Rs.ibind Q (cmb γ₁)) x₁)
                     (At.R.reindex-shape R At.mor₀
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
    Tt.W-≈-trans {x = Rs.ireindex-shape (μ R'') (Rs.ibind Q (cmb γ₁)) x₁}
                 {z = At.R.reindex-shape (μ R'') At.mor₀ (At.embed-idx (μ R'')
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
      module At = AlphaDef Q sₜ
      module Rs = Reindex sₛ sₜ
      module Rs' = Reindex (extend sₛ (μObj Q sₜ)) (extend sₜ (μObj Q sₜ))
      module Ft = FoldDef {Γ = Γ} {A = μObj Q sₜ} {P = Q} {δ = sₛ}
                    (Mor-∘ At.αmor (HasMu.strong-fmor hasMu Q (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)))
      wm₁ = Ft.fold-reindex γ₁ Ft.fbase x₁
      w   = Ft.fold-reindex γ₂ Ft.fbase x₂
      cmb' : Γ .idx .Carrier → Rs'.IMorD (λ v → inj₁ v) (λ v → inj₁ v)
      cmb' γ = Rs'.ibase (λ { Fin.zero a → a ; (Fin.suc i) a → Rs.iapply (cmb γ) i a })
                         (λ { Fin.zero p → p ; (Fin.suc i) p → Rs.iapply-resp (cmb γ) i p })
      rec : _≈s_ (μObj R'' (extend sₜ (μObj Q sₜ)) .idx)
                 (Rs'.ireindex (cmb' γ₁) wm₁)
                 (HasMu.strong-fmor hasMu (μ R'') (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂) .idxf .PS._⇒_.func (γ₂ , w))
      rec = fuse-idx R'' cmb' (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)
              (λ { Fin.zero γ≈ a≈ → a≈ ; (Fin.suc j) γ≈ a≈ → corr j γ≈ a≈ })
              γ≈ {m₁ = wm₁} {m₂ = w}
              (Ft.fold-reindex-resp γ≈ Ft.fbase {x₁} {x₂} x≈)
      mutual
        data TeleRel : ∀ {j} {ηA ηB ηC ηD} →
                       Rs.IMorD {j} ηA ηB → At.R.MorD {j} ηC ηB → Rs'.IMorD {j} ηD ηC → Ft.FMor {j} ηA ηD →
                       Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
          tbase : TeleRel (Rs.ibind Q (cmb γ₁)) At.mor₀ (cmb' γ₁) Ft.fbase
          tbind : ∀ {j} {ηA ηB ηC ηD} {md mdA md' fm} (S' : Poly (suc j)) →
                  TeleRel {j} {ηA} {ηB} {ηC} {ηD} md mdA md' fm →
                  TeleRel (Rs.ibind S' md) (At.R.bind S' mdA) (Rs'.ibind S' md') (Ft.fbind S' fm)

        tele-shape : ∀ {j} (S : Poly j) {ηA ηB ηC ηD}
                     {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD}
                     (rel : TeleRel md mdA md' fm) (z : Ft.Tδ.⟦ S ⟧shape ηA) →
                     Tt.shape≈ S ηB
                       (Rs.ireindex-shape S md z)
                       (At.R.reindex-shape S mdA (Rs'.ireindex-shape S md' (Ft.fold-reindex-shape γ₁ S fm z)))
        tele-shape (const A') rel z = A' .idx .isEquivalence .refl
        tele-shape (var v) rel z = tele-apply rel v
        tele-shape (S₁ + S₂) rel (inj₁ z) = tele-shape S₁ rel z
        tele-shape (S₁ + S₂) rel (inj₂ z) = tele-shape S₂ rel z
        tele-shape (S₁ × S₂) rel (z₁ , z₂) = tele-shape S₁ rel z₁ , tele-shape S₂ rel z₂
        tele-shape (μ S') rel (Ts.sup z') = tele-shape S' (tbind S' rel) z'

        tele-apply : ∀ {j} {ηA ηB ηC ηD} {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD}
                     (rel : TeleRel md mdA md' fm) (v : Fin j) {z} →
                     Tt.elEq (ηB v) (Rs.iapply md v z) (At.R.apply mdA v (Rs'.iapply md' v (Ft.fold-apply γ₁ fm v z)))
        tele-apply (tbind S' r) Fin.zero    {z} = tele-shape (μ S') r z
        tele-apply (tbind S' r) (Fin.suc v)     = tele-apply r v
        tele-apply tbase Fin.zero    {z} =
          fuse-idx Q cmb fsk corr (Γ .idx .isEquivalence .refl {γ₁}) {m₁ = z} {m₂ = z}
            (μObj Q sₛ .idx .isEquivalence .refl {z})
        tele-apply tbase (Fin.suc i) {z} = Tt.elEq-refl (inj₁ i) (Rs.iapply (cmb γ₁) i z)

      telescope : Tt.W-≈ (Rs.ireindex-shape (μ R'') (Rs.ibind Q (cmb γ₁)) x₁)
                         (At.R.reindex At.mor₀ (Rs'.ireindex (cmb' γ₁) wm₁))
      telescope = tele-shape (μ R'') tbase x₁

  -- Fibre analogue of `fuse-idx`: the fibre reindex (via the external fold action `act`)
  -- equals the strong functorial action's fibre, transported along the index fusion.
  -- Mirrors `fuse-idx`'s interface (function `cmb`, general `corr`) so the μ-recursion can
  -- build nested index equations, plus the fibre `act`/`corr-fam` (at the fixed `γ`).
  fuse-fam : ∀ {n} {Γ : Obj} (γ : Γ .idx .Carrier) {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
                 let module Rs = Reindex sₛ sₜ
                     module FR = FReindex {δA = sₛ} {δB = sₜ} (Γ .fam .fm γ) in
                 (cmb : Γ .idx .Carrier → Rs.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
                 (act : FR.FAct (cmb γ))
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
                   (μObj Q sₜ .fam .subst {x = Rs.ireindex (cmb γ) m}
                      (fuse-idx Q cmb fsk corr (Γ .idx .isEquivalence .refl)
                        {m} {m} (μObj Q sₛ .idx .isEquivalence .refl {m}))
                    ∘ FR.freindex-fam act {m})
                   (HasMu.strong-fmor hasMu (μ Q) fsk .famf ._⇒f_.transf (γ , m))
  -- Shape-level recursion for `fuse-fam` (mirrors `fuse-shape`): the fibre reindex of
  -- the μ-body sub-poly `R` equals the embed ∘ reindex ∘ strong ∘ fold fibre composite.
  fuse-shape-fam : ∀ {n} {Γ : Obj} (γ : Γ .idx .Carrier) {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
                       let module Rs = Reindex sₛ sₜ
                           module Ts = Tree sₛ
                           module Tt = Tree sₜ
                           module At = AlphaDef Q sₜ
                           module FR = FReindex {δA = sₛ} {δB = sₜ} (Γ .fam .fm γ) in
                       (cmb : Γ .idx .Carrier → Rs.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
                       (act : FR.FAct (cmb γ))
                       (fsk : ∀ i → Mor (Fam𝒞-P.prod Γ (sₛ i)) (sₜ i))
                       (corr : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                               _≈s_ (sₜ i .idx) (Rs.iapply (cmb γ₁) i a₁) (fsk i .idxf .PS._⇒_.func (γ₂ , a₂)))
                       (corr-fam : ∀ i {a} →
                          Category._≈_ 𝒞
                            (sₜ i .fam .subst (corr i (Γ .idx .isEquivalence .refl) (sₛ i .idx .isEquivalence .refl {a}))
                             ∘ FR.aapply act i a)
                            (fsk i .famf ._⇒f_.transf (γ , a))) →
                       let module Ft = FoldDef {Γ = Γ} {A = μObj Q sₜ} {P = Q} {δ = sₛ}
                                         (Mor-∘ At.αmor (HasMu.strong-fmor hasMu Q (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)))
                           fsk' = HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂ in
                       (R : Poly (suc n))
                       {x : Ts.⟦ R ⟧shape (η₀ Q)} →
                       Category._≈_ 𝒞
                         (Tt.fib-shape-subst R (η₀ Q)
                            (fuse-shape Q cmb fsk corr R (Γ .idx .isEquivalence .refl)
                              (Ts.shape≈-refl R (η₀ Q) x))
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
    ≈-trans (fuse-shape-fam γ Q cmb act fsk corr corr-fam R₁ {a})
      (∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (≈-sym (≈-trans id-left id-left)) ≈-refl)))
  fuse-shape-fam γ Q cmb act fsk corr corr-fam (R₁ + R₂) {inj₂ b} =
    ≈-trans (fuse-shape-fam γ Q cmb act fsk corr corr-fam R₂ {b})
      (∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (≈-sym (≈-trans id-left id-left)) ≈-refl)))
  fuse-shape-fam γ Q cmb act fsk corr corr-fam (R₁ × R₂) {a , b} =
    ≈-trans (pair-compose _ _ _ _)
      (≈-trans (pair-cong
                 (≈-trans (≈-sym (assoc _ _ _))
                   (≈-trans (∘-cong (fuse-shape-fam γ Q cmb act fsk corr corr-fam R₁ {a}) ≈-refl)
                     (≈-trans (assoc _ _ _)
                       (∘-cong ≈-refl
                         (≈-trans (assoc _ _ _)
                           (∘-cong ≈-refl
                             (≈-trans (assoc _ _ _)
                               (≈-trans (∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) ≈-refl)))
                                 (≈-sym
                                   (≈-trans (∘-cong id-left ≈-refl)
                                     (≈-trans (assoc _ _ _)
                                       (∘-cong ≈-refl
                                         (≈-trans (pair-natural _ _ _)
                                           (pair-cong (pair-p₁ _ _)
                                             (≈-trans (∘-cong id-left ≈-refl)
                                               (≈-trans (assoc _ _ _)
                                                 (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (pair-p₁ _ _))))))))))))))))))
                 (≈-trans (≈-sym (assoc _ _ _))
                   (≈-trans (∘-cong (fuse-shape-fam γ Q cmb act fsk corr corr-fam R₂ {b}) ≈-refl)
                     (≈-trans (assoc _ _ _)
                       (∘-cong ≈-refl
                         (≈-trans (assoc _ _ _)
                           (∘-cong ≈-refl
                             (≈-trans (assoc _ _ _)
                               (≈-trans (∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) ≈-refl)))
                                 (≈-sym
                                   (≈-trans (∘-cong id-left ≈-refl)
                                     (≈-trans (assoc _ _ _)
                                       (∘-cong ≈-refl
                                         (≈-trans (pair-natural _ _ _)
                                           (pair-cong (pair-p₁ _ _)
                                             (≈-trans (∘-cong id-left ≈-refl)
                                               (≈-trans (assoc _ _ _)
                                                 (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (pair-p₂ _ _)))))))))))))))))))
        (≈-sym (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (pair-natural _ _ _)))
                  (≈-trans (∘-cong ≈-refl (pair-compose _ _ _ _))
                    (pair-compose _ _ _ _)))))
  fuse-shape-fam {Γ = Γ} γ {sₛ = sₛ} {sₜ = sₜ} Q cmb act fsk corr corr-fam (μ R'') {x} =
    ≈-trans (∘-cong (Tt.fib-trans*
                       {x = Rs.ireindex-shape (μ R'') (Rs.ibind Q (cmb γ)) x}
                       {y = At.R.reindex At.mor₀ (Rs'.ireindex (cmb' γ) wm₁)}
                       {z = At.R.reindex At.mor₀ (HasMu.strong-fmor hasMu (μ R'') fsk' .idxf .PS._⇒_.func (γ , wm₁))}
                       (At.R.reindex-resp At.mor₀
                          {Rs'.ireindex (cmb' γ) wm₁}
                          {HasMu.strong-fmor hasMu (μ R'') fsk' .idxf .PS._⇒_.func (γ , wm₁)}
                          rec-idx)
                       (tele-shape (μ R'') tbase x)) ≈-refl)
      (≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (tele-shape-fam (μ R'') tbase x))
          (≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong (≈-sym (At.R.reindex-fam-W-natural At.mor₀
                                       {Rs'.ireindex (cmb' γ) wm₁}
                                       {HasMu.strong-fmor hasMu (μ R'') fsk' .idxf .PS._⇒_.func (γ , wm₁)}
                                       rec-idx)) ≈-refl)
              (≈-trans (assoc _ _ _)
                (∘-cong ≈-refl
                  (≈-trans (≈-sym (assoc _ _ _))
                    (≈-trans (∘-cong rec-fam ≈-refl) (≈-sym id-left)))))))))
    where
      module Tt = Tree sₜ
      module Ts = Tree sₛ
      module At = AlphaDef Q sₜ
      module Rs = Reindex sₛ sₜ
      module Rs' = Reindex (extend sₛ (μObj Q sₜ)) (extend sₜ (μObj Q sₜ))
      module FR = FReindex {δA = sₛ} {δB = sₜ} (Γ .fam .fm γ)
      module FR' = FReindex {δA = extend sₛ (μObj Q sₜ)} {δB = extend sₜ (μObj Q sₜ)} (Γ .fam .fm γ)
      module Ft = FoldDef {Γ = Γ} {A = μObj Q sₜ} {P = Q} {δ = sₛ}
                    (Mor-∘ At.αmor (HasMu.strong-fmor hasMu Q (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)))
      fsk' = HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂
      wm₁ = Ft.fold-reindex γ Ft.fbase x
      cmb' : Γ .idx .Carrier → Rs'.IMorD (λ v → inj₁ v) (λ v → inj₁ v)
      cmb' γ' = Rs'.ibase (λ { Fin.zero a → a ; (Fin.suc i) a → Rs.iapply (cmb γ') i a })
                          (λ { Fin.zero p → p ; (Fin.suc i) p → Rs.iapply-resp (cmb γ') i p })
      act' : FR'.FAct (cmb' γ)
      act' = FR'.abase (λ { Fin.zero a → p₂ ; (Fin.suc i) a → FR.aapply act i a })
      corr' : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (extend sₛ (μObj Q sₜ) i .idx) a₁ a₂) →
              _≈s_ (extend sₜ (μObj Q sₜ) i .idx) (Rs'.iapply (cmb' γ₁) i a₁) (fsk' i .idxf .PS._⇒_.func (γ₂ , a₂))
      corr' Fin.zero    γ≈ a≈ = a≈
      corr' (Fin.suc j) γ≈ a≈ = corr j γ≈ a≈
      corr-fam' : ∀ i {a} → Category._≈_ 𝒞
                    (extend sₜ (μObj Q sₜ) i .fam .subst
                       (corr' i (Γ .idx .isEquivalence .refl) (extend sₛ (μObj Q sₜ) i .idx .isEquivalence .refl {a}))
                     ∘ FR'.aapply act' i a)
                    (fsk' i .famf ._⇒f_.transf (γ , a))
      corr-fam' Fin.zero {a} = ≈-trans (∘-cong (μObj Q sₜ .fam .refl* {a}) ≈-refl) id-left
      corr-fam' (Fin.suc j) = corr-fam j
      rec-fam : Category._≈_ 𝒞
                  (μObj R'' (extend sₜ (μObj Q sₜ)) .fam .subst {x = Rs'.ireindex (cmb' γ) wm₁}
                     (fuse-idx R'' cmb' fsk' corr' (Γ .idx .isEquivalence .refl)
                       {wm₁} {wm₁} (μObj R'' (extend sₛ (μObj Q sₜ)) .idx .isEquivalence .refl {wm₁}))
                   ∘ FR'.freindex-fam act' {wm₁})
                  (HasMu.strong-fmor hasMu (μ R'') fsk' .famf ._⇒f_.transf (γ , wm₁))
      rec-fam = fuse-fam γ R'' cmb' act' fsk' corr' corr-fam' {wm₁}
      rec-idx = fuse-idx R'' cmb' fsk' corr' (Γ .idx .isEquivalence .refl)
                  {wm₁} {wm₁} (μObj R'' (extend sₛ (μObj Q sₜ)) .idx .isEquivalence .refl {wm₁})
      mutual
        data TeleRel : ∀ {j} {ηA ηB ηC ηD}
                       (md : Rs.IMorD {j} ηA ηB) (mdA : At.R.MorD {j} ηC ηB) (md' : Rs'.IMorD {j} ηD ηC) (fm : Ft.FMor {j} ηA ηD) →
                       FR.FAct md → FR'.FAct md' → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
          tbase : TeleRel (Rs.ibind Q (cmb γ)) At.mor₀ (cmb' γ) Ft.fbase (FR.abind Q (cmb γ) act) act'
          tbind : ∀ {j} {ηA ηB ηC ηD} {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD}
                  {am : FR.FAct md} {am' : FR'.FAct md'} (S' : Poly (suc j)) →
                  TeleRel md mdA md' fm am am' →
                  TeleRel (Rs.ibind S' md) (At.R.bind S' mdA) (Rs'.ibind S' md') (Ft.fbind S' fm)
                          (FR.abind S' md am) (FR'.abind S' md' am')

        tele-shape : ∀ {j} (S : Poly j) {ηA ηB ηC ηD}
                     {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD}
                     {am : FR.FAct md} {am' : FR'.FAct md'}
                     (rel : TeleRel md mdA md' fm am am') (z : Ft.Tδ.⟦ S ⟧shape ηA) →
                     Tt.shape≈ S ηB
                       (Rs.ireindex-shape S md z)
                       (At.R.reindex-shape S mdA (Rs'.ireindex-shape S md' (Ft.fold-reindex-shape γ S fm z)))
        tele-shape (const A') rel z = A' .idx .isEquivalence .refl
        tele-shape (var v) rel z = tele-apply rel v
        tele-shape (S₁ + S₂) rel (inj₁ z) = tele-shape S₁ rel z
        tele-shape (S₁ + S₂) rel (inj₂ z) = tele-shape S₂ rel z
        tele-shape (S₁ × S₂) rel (z₁ , z₂) = tele-shape S₁ rel z₁ , tele-shape S₂ rel z₂
        tele-shape (μ S') rel (Ts.sup z') = tele-shape S' (tbind S' rel) z'

        tele-apply : ∀ {j} {ηA ηB ηC ηD} {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD}
                     {am : FR.FAct md} {am' : FR'.FAct md'}
                     (rel : TeleRel md mdA md' fm am am') (v : Fin j) {z} →
                     Tt.elEq (ηB v) (Rs.iapply md v z) (At.R.apply mdA v (Rs'.iapply md' v (Ft.fold-apply γ fm v z)))
        tele-apply (tbind S' r) Fin.zero    {z} = tele-shape (μ S') r z
        tele-apply (tbind S' r) (Fin.suc v)     = tele-apply r v
        tele-apply tbase Fin.zero    {z} =
          fuse-idx Q cmb fsk corr (Γ .idx .isEquivalence .refl {γ}) {m₁ = z} {m₂ = z}
            (μObj Q sₛ .idx .isEquivalence .refl {z})
        tele-apply tbase (Fin.suc i) {z} = Tt.elEq-refl (inj₁ i) (Rs.iapply (cmb γ) i z)

        tele-shape-fam : ∀ {j} (S : Poly j) {ηA ηB ηC ηD}
                         {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD}
                         {am : FR.FAct md} {am' : FR'.FAct md'}
                         (rel : TeleRel md mdA md' fm am am') (z : Ft.Tδ.⟦ S ⟧shape ηA) →
                         (Tt.fib-shape-subst S ηB (tele-shape S rel z) ∘ FR.freindex-shape-fam S am {z})
                         ≈ (At.R.reindex-fam S mdA
                            ∘ (FR'.freindex-shape-fam S am' {Ft.fold-reindex-shape γ S fm z}
                               ∘ pair p₁ (Ft.fold-reindex-shape-fam γ S fm z)))
        tele-shape-fam (const A') rel z =
          ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) (≈-trans id-left (≈-sym (≈-trans id-left (pair-p₂ _ _))))
        tele-shape-fam (var v) rel z = tele-apply-fam rel v
        tele-shape-fam (S₁ + S₂) rel (inj₁ z) = tele-shape-fam S₁ rel z
        tele-shape-fam (S₁ + S₂) rel (inj₂ z) = tele-shape-fam S₂ rel z
        tele-shape-fam (S₁ × S₂) rel (z₁ , z₂) =
          ≈-trans (strong-prod-m-post _ _ _ _)
            (≈-trans (strong-prod-m-cong (tele-shape-fam S₁ rel z₁) (tele-shape-fam S₂ rel z₂))
              (≈-sym (≈-trans (∘-cong ≈-refl (strong-prod-m-comp _ _ _ _)) (strong-prod-m-post _ _ _ _))))
        tele-shape-fam (μ S') rel (Ts.sup z') = tele-shape-fam S' (tbind S' rel) z'

        tele-apply-fam : ∀ {j} {ηA ηB ηC ηD}
                         {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD}
                         {am : FR.FAct md} {am' : FR'.FAct md'}
                         (rel : TeleRel md mdA md' fm am am') (v : Fin j) {z} →
                         (Tt.fib-el-subst (ηB v) (tele-apply rel v {z}) ∘ FR.aapply am v z)
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

  -- β/η proof machinery: the fusion of `α`'s reconstruction with the fold equals the
  -- strong functorial action of `⦅ alg ⦆`. References both AlphaDef and FoldDef internals.
  module BetaDef {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
                 (alg : Mor (Fam𝒞-P.prod Γ (fobj μObj P (extend δ A))) A) where
    open HasMu hasMu using (strong-fmor; strong-extend-mor; ⦅_⦆; α)
    module Aα = AlphaDef P δ
    module Fα = FoldDef {Γ = Γ} {A = A} {P = P} {δ = δ} alg
    δ' = extend δ (μObj P δ)
    fs : ∀ i → Mor (Fam𝒞-P.prod Γ (δ' i)) (extend δ A i)
    fs = strong-extend-mor (λ i → Fam𝒞-P.p₂) Fα.foldMor

    -- Collapse the α-reconstruction reindex followed by the fold's reindex into one
    -- index-only reindex, so the fusion lemmas can treat them as a single morphism.
    module Rcomb = Reindex δ' (extend δ A)
    combine : (γ : Γ .idx .Carrier) → ∀ {k} {ρA ρB ρC} → Aα.R.MorD {k} ρA ρB → Fα.FMor {k} ρB ρC → Rcomb.IMorD {k} ρA ρC
    combine γ md fm = Rcomb.ibase (λ v a → Fα.fold-apply γ fm v (Aα.R.apply md v a))
      (λ v {a} {a'} p → Fα.fold-apply-resp (Γ .idx .isEquivalence .refl) fm v
        (Aα.R.apply-resp md v {a} {a'} p))

    mutual
      -- Defunctionalised relation "these two Rcomb.IMorDs are combine-lemma-related under binders".
      data Rel : ∀ {k} {ρA ρB} → Rcomb.IMorD {k} ρA ρB → Rcomb.IMorD {k} ρA ρB →
                 Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
        rcomb : ∀ {k} {ρA ρB ρC} (γ : Γ .idx .Carrier) (Q : Poly (suc k))
                (md : Aα.R.MorD ρA ρB) (fm : Fα.FMor ρB ρC) →
                Rel (combine γ (Aα.R.bind Q md) (Fα.fbind Q fm)) (Rcomb.ibind Q (combine γ md fm))
        rbind : ∀ {k} {ρA ρB} {md₁ md₂ : Rcomb.IMorD ρA ρB} (Q : Poly (suc k)) →
                Rel md₁ md₂ → Rel (Rcomb.ibind Q md₁) (Rcomb.ibind Q md₂)

      -- reindex respects Rel-related morphisms; the binder recursion is structural on Rel.
      reindex-mcong : ∀ {k} {Q : Poly (suc k)} {ρA ρB} {md₁ md₂ : Rcomb.IMorD ρA ρB}
                      (r : Rel md₁ md₂) (t : Aα.TX.W Q ρA) →
                      Fα.TA'.W-≈ (Rcomb.ireindex md₁ t) (Rcomb.ireindex md₂ t)
      reindex-mcong {Q = Q} r (Aα.TX.sup y) = reindex-mcong-shape Q (rbind Q r) y

      reindex-mcong-shape : ∀ {j} (R : Poly j) {ρA ρB} {md₁ md₂ : Rcomb.IMorD ρA ρB}
                            (r : Rel md₁ md₂) (y : Aα.TX.⟦ R ⟧shape ρA) →
                            Fα.TA'.shape≈ R ρB (Rcomb.ireindex-shape R md₁ y) (Rcomb.ireindex-shape R md₂ y)
      reindex-mcong-shape (const A') r y = A' .idx .isEquivalence .refl
      reindex-mcong-shape (var v)    r y = mrel-apply r v
      reindex-mcong-shape (P + P') r (inj₁ y) = reindex-mcong-shape P r y
      reindex-mcong-shape (P + P') r (inj₂ z) = reindex-mcong-shape P' r z
      reindex-mcong-shape (P × P') r (y , z) = reindex-mcong-shape P r y , reindex-mcong-shape P' r z
      reindex-mcong-shape (μ R'') r y = reindex-mcong r y

      mrel-apply : ∀ {k} {ρA ρB} {md₁ md₂ : Rcomb.IMorD ρA ρB} (r : Rel md₁ md₂) (v : Fin k) {a} →
                   Fα.TA'.elEq (ρB v) (Rcomb.iapply md₁ v a) (Rcomb.iapply md₂ v a)
      mrel-apply (rcomb γ Q md fm)            Fin.zero     {a} = combine-lemma γ md fm a
      mrel-apply (rcomb {ρC = ρC} γ Q md fm) (Fin.suc v')      = Fα.TA'.elEq-refl (ρC v') _
      mrel-apply (rbind Q r)                  Fin.zero     {a} = reindex-mcong r a
      mrel-apply (rbind Q r)                 (Fin.suc v')      = mrel-apply r v'

      combine-lemma : ∀ {k} {Q : Poly (suc k)} {ρA ρB ρC} (γ : Γ .idx .Carrier)
                      (md : Aα.R.MorD ρA ρB) (fm : Fα.FMor ρB ρC) (t : Aα.TX.W Q ρA) →
                      Fα.TA'.W-≈ (Fα.fold-reindex γ fm (Aα.R.reindex md t)) (Rcomb.ireindex (combine γ md fm) t)
      combine-lemma {Q = Q} γ md fm (Aα.TX.sup x) = combine-lemma-shape Q Q γ md fm x

      combine-lemma-shape : ∀ {k} (Q : Poly (suc k)) (R : Poly (suc k)) {ρA ρB ρC} (γ : Γ .idx .Carrier)
                            (md : Aα.R.MorD ρA ρB) (fm : Fα.FMor ρB ρC)
                            (x : Aα.TX.⟦ R ⟧shape (extend ρA (inj₂ (mkSort Q ρA)))) →
                            Fα.TA'.shape≈ R (extend ρC (inj₂ (mkSort Q ρC)))
                              (Fα.fold-reindex-shape γ R (Fα.fbind Q fm) (Aα.R.reindex-shape R (Aα.R.bind Q md) x))
                              (Rcomb.ireindex-shape R (Rcomb.ibind Q (combine γ md fm)) x)
      combine-lemma-shape Q (const A')              γ md fm x = A' .idx .isEquivalence .refl
      combine-lemma-shape Q (var Fin.zero)          γ md fm x = combine-lemma γ md fm x
      combine-lemma-shape Q (var (Fin.suc v)) {ρC = ρC} γ md fm x = Fα.TA'.elEq-refl (ρC v) _
      combine-lemma-shape Q (P + Q') γ md fm (inj₁ x) = combine-lemma-shape Q P γ md fm x
      combine-lemma-shape Q (P + Q') γ md fm (inj₂ y) = combine-lemma-shape Q Q' γ md fm y
      combine-lemma-shape Q (P × Q') γ md fm (x , y) =
        combine-lemma-shape Q P γ md fm x , combine-lemma-shape Q Q' γ md fm y
      combine-lemma-shape Q (μ R'') γ md fm x =
        Fα.TA'.W-≈-trans {x = Fα.fold-reindex γ (Fα.fbind Q fm) (Aα.R.reindex (Aα.R.bind Q md) x)}
                         {y = Rcomb.ireindex (combine γ (Aα.R.bind Q md) (Fα.fbind Q fm)) x}
                         (combine-lemma γ (Aα.R.bind Q md) (Fα.fbind Q fm) x)
                         (reindex-mcong (rcomb γ Q md fm) x)

    -- Fibre mirror of the collapse, at a fixed γ: `combine-act` is combine's Γ-dependent
    -- fibre action, and the lemmas transport the fibre composites along the corresponding
    -- index proofs, mirroring `Rel`/`reindex-mcong`/`combine-lemma` clause by clause.
    module CombineFam (γ : Γ .idx .Carrier) where
      module FR = FReindex {δA = δ'} {δB = extend δ A} (Γ .fam .fm γ)

      combine-act : ∀ {k} {ρA ρB ρC} (md : Aα.R.MorD {k} ρA ρB) (fm : Fα.FMor {k} ρB ρC) →
                    FR.FAct (combine γ md fm)
      combine-act md fm =
        FR.abase (λ v a → Fα.fold-apply-fam γ fm v (Aα.R.apply md v a)
                          ∘ prod-m (id (Fam.fm (Γ .fam) γ)) (Aα.R.apply-fam md v a))

      mutual
        -- Fibre actions over Rel-related morphisms, related constructor by constructor.
        data RelAct : ∀ {k} {ρA ρB} {md₁ md₂ : Rcomb.IMorD {k} ρA ρB} →
                      Rel md₁ md₂ → FR.FAct md₁ → FR.FAct md₂ → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
          rcombA : ∀ {k} {ρA ρB ρC} (Q : Poly (suc k)) (md : Aα.R.MorD ρA ρB) (fm : Fα.FMor ρB ρC) →
                   RelAct (rcomb γ Q md fm) (combine-act (Aα.R.bind Q md) (Fα.fbind Q fm))
                          (FR.abind Q (combine γ md fm) (combine-act md fm))
          rbindA : ∀ {k} {ρA ρB} {md₁ md₂ : Rcomb.IMorD ρA ρB} {r : Rel md₁ md₂}
                   {a₁ : FR.FAct md₁} {a₂ : FR.FAct md₂} (Q : Poly (suc k)) →
                   RelAct r a₁ a₂ → RelAct (rbind Q r) (FR.abind Q md₁ a₁) (FR.abind Q md₂ a₂)

        reindex-mcong-fam : ∀ {k} {Q : Poly (suc k)} {ρA ρB} {md₁ md₂ : Rcomb.IMorD ρA ρB}
                            {r : Rel md₁ md₂} {a₁ : FR.FAct md₁} {a₂ : FR.FAct md₂}
                            (ra : RelAct r a₁ a₂) (t : Aα.TX.W Q ρA) →
                            (Fα.TA'.fib-subst {x = Rcomb.ireindex md₁ t} {y = Rcomb.ireindex md₂ t}
                               (reindex-mcong r t)
                             ∘ FR.freindex-fam a₁ {t})
                            ≈ FR.freindex-fam a₂ {t}
        reindex-mcong-fam {Q = Q} ra (Aα.TX.sup y) = reindex-mcong-shape-fam Q (rbindA Q ra) y

        reindex-mcong-shape-fam : ∀ {j} (R : Poly j) {ρA ρB} {md₁ md₂ : Rcomb.IMorD ρA ρB}
                                  {r : Rel md₁ md₂} {a₁ : FR.FAct md₁} {a₂ : FR.FAct md₂}
                                  (ra : RelAct r a₁ a₂) (y : Aα.TX.⟦ R ⟧shape ρA) →
                                  (Fα.TA'.fib-shape-subst R ρB (reindex-mcong-shape R r y)
                                   ∘ FR.freindex-shape-fam R a₁ {y})
                                  ≈ FR.freindex-shape-fam R a₂ {y}
        reindex-mcong-shape-fam (const A') ra y =
          ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
        reindex-mcong-shape-fam (var v) ra y = mrel-apply-fam ra v
        reindex-mcong-shape-fam (P + P') ra (inj₁ y) = reindex-mcong-shape-fam P ra y
        reindex-mcong-shape-fam (P + P') ra (inj₂ z) = reindex-mcong-shape-fam P' ra z
        reindex-mcong-shape-fam (P × P') ra (y , z) =
          ≈-trans (strong-prod-m-post _ _ _ _)
            (strong-prod-m-cong (reindex-mcong-shape-fam P ra y) (reindex-mcong-shape-fam P' ra z))
        reindex-mcong-shape-fam (μ R'') ra y = reindex-mcong-fam ra y

        mrel-apply-fam : ∀ {k} {ρA ρB} {md₁ md₂ : Rcomb.IMorD ρA ρB}
                         {r : Rel md₁ md₂} {a₁ : FR.FAct md₁} {a₂ : FR.FAct md₂}
                         (ra : RelAct r a₁ a₂) (v : Fin k) {z} →
                         (Fα.TA'.fib-el-subst (ρB v) (mrel-apply r v {z}) ∘ FR.aapply a₁ v z)
                         ≈ FR.aapply a₂ v z
        mrel-apply-fam (rcombA Q md fm) Fin.zero {z} = combine-lemma-fam md fm z
        mrel-apply-fam (rcombA {ρC = ρC} Q md fm) (Fin.suc v') {z} =
          ≈-trans (∘-cong (Fα.TA'.fib-el-refl* (ρC v') _) ≈-refl) id-left
        mrel-apply-fam (rbindA Q ra) Fin.zero {z} = reindex-mcong-fam ra z
        mrel-apply-fam (rbindA Q ra) (Fin.suc v') = mrel-apply-fam ra v'

        combine-lemma-fam : ∀ {k} {Q : Poly (suc k)} {ρA ρB ρC}
                            (md : Aα.R.MorD ρA ρB) (fm : Fα.FMor ρB ρC) (t : Aα.TX.W Q ρA) →
                            (Fα.TA'.fib-subst {x = Fα.fold-reindex γ fm (Aα.R.reindex md t)}
                                              {y = Rcomb.ireindex (combine γ md fm) t}
                               (combine-lemma γ md fm t)
                             ∘ (Fα.fold-reindex-fam γ fm (Aα.R.reindex md t)
                                ∘ prod-m (id _) (Aα.R.reindex-fam-W md {t})))
                            ≈ FR.freindex-fam (combine-act md fm) {t}
        combine-lemma-fam {Q = Q} md fm (Aα.TX.sup x) = combine-lemma-shape-fam Q Q md fm x

        combine-lemma-shape-fam : ∀ {k} (Q : Poly (suc k)) (R : Poly (suc k)) {ρA ρB ρC}
                                  (md : Aα.R.MorD ρA ρB) (fm : Fα.FMor ρB ρC)
                                  (x : Aα.TX.⟦ R ⟧shape (extend ρA (inj₂ (mkSort Q ρA)))) →
                                  (Fα.TA'.fib-shape-subst R (extend ρC (inj₂ (mkSort Q ρC)))
                                     (combine-lemma-shape Q R γ md fm x)
                                   ∘ (Fα.fold-reindex-shape-fam γ R (Fα.fbind Q fm)
                                        (Aα.R.reindex-shape R (Aα.R.bind Q md) x)
                                      ∘ prod-m (id _) (Aα.R.reindex-fam R (Aα.R.bind Q md) {x})))
                                  ≈ FR.freindex-shape-fam R (FR.abind Q (combine γ md fm) (combine-act md fm)) {x}
        combine-lemma-shape-fam Q (const A') md fm x =
          ≈-trans (∘-cong (A' .fam .refl*) ≈-refl)
            (≈-trans id-left (≈-trans (pair-p₂ _ _) id-left))
        combine-lemma-shape-fam Q (var Fin.zero) md fm x = combine-lemma-fam md fm x
        combine-lemma-shape-fam Q (var (Fin.suc v)) {ρC = ρC} md fm x =
          ≈-trans (∘-cong (Fα.TA'.fib-el-refl* (ρC v) _) ≈-refl) id-left
        combine-lemma-shape-fam Q (P + Q') md fm (inj₁ x) = combine-lemma-shape-fam Q P md fm x
        combine-lemma-shape-fam Q (P + Q') md fm (inj₂ y) = combine-lemma-shape-fam Q Q' md fm y
        combine-lemma-shape-fam Q (P × Q') md fm (x , y) =
          ≈-trans (∘-cong ≈-refl (strong-prod-m-pre _ _ _ _ _))
            (≈-trans (strong-prod-m-post _ _ _ _)
              (strong-prod-m-cong (combine-lemma-shape-fam Q P md fm x) (combine-lemma-shape-fam Q Q' md fm y)))
        combine-lemma-shape-fam Q (μ R'') md fm x =
          ≈-trans (∘-cong (Fα.TA'.fib-trans*
                             {x = Fα.fold-reindex γ (Fα.fbind Q fm) (Aα.R.reindex (Aα.R.bind Q md) x)}
                             {y = Rcomb.ireindex (combine γ (Aα.R.bind Q md) (Fα.fbind Q fm)) x}
                             {z = Rcomb.ireindex (Rcomb.ibind Q (combine γ md fm)) x}
                             (reindex-mcong (rcomb γ Q md fm) x)
                             (combine-lemma γ (Aα.R.bind Q md) (Fα.fbind Q fm) x)) ≈-refl)
            (≈-trans (assoc _ _ _)
              (≈-trans (∘-cong ≈-refl (combine-lemma-fam (Aα.R.bind Q md) (Fα.fbind Q fm) x))
                (reindex-mcong-fam (rcombA Q md fm) x)))

    -- Correspondence hypothesis for the fuse instances: `combine mor₀ fbase` acts as
    -- the fold at the recursion slot and as the identity at the parameter slots.
    corr-fs : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (δ' i .idx) a₁ a₂) →
              _≈s_ (extend δ A i .idx)
                   (Rcomb.iapply (combine γ₁ Aα.mor₀ Fα.fbase) i a₁)
                   (fs i .idxf .PS._⇒_.func (γ₂ , a₂))
    corr-fs Fin.zero γ≈ {a₁} {a₂} a≈ = Fα.fold-idx-resp γ≈ {a₁} {a₂} a≈
    corr-fs (Fin.suc j) γ≈ a≈ = a≈

    -- fold-shape-idx ∘ reindex-shape ∘ embed-idx ≈ strong-fmor's idx action of the fold.
    β-idx : (R : Poly (suc n)) → ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {m₁ m₂}
            (m≈ : _≈s_ (fobj μObj R δ' .idx) m₁ m₂) →
            _≈s_ (fobj μObj R (extend δ A) .idx)
                 (Fα.fold-shape-idx R γ₁ (Aα.R.reindex-shape R Aα.mor₀ (Aα.embed-idx R m₁)))
                 (strong-fmor R fs .idxf .PS._⇒_.func (γ₂ , m₂))
    β-idx (const A')        γ≈ m≈ = m≈
    β-idx (var Fin.zero)    γ≈ {m₁} {m₂} m≈ = Fα.fold-idx-resp γ≈ {m₁} {m₂} m≈
    β-idx (var (Fin.suc j)) γ≈ m≈ = m≈
    β-idx (Q₁ + Q₂) γ≈ {inj₁ _} {inj₁ _} m≈ = β-idx Q₁ γ≈ m≈
    β-idx (Q₁ + Q₂) γ≈ {inj₂ _} {inj₂ _} m≈ = β-idx Q₂ γ≈ m≈
    β-idx (Q₁ × Q₂) γ≈ {_ , _} {_ , _} (m≈₁ , m≈₂) = β-idx Q₁ γ≈ m≈₁ , β-idx Q₂ γ≈ m≈₂
    β-idx (μ Q') {γ₁} {γ₂} γ≈ {m₁} {m₂} m≈ =
      Fα.TA'.W-≈-trans
        {x = Fα.fold-shape-idx (μ Q') γ₁ (Aα.R.reindex-shape (μ Q') Aα.mor₀ (Aα.embed-idx (μ Q') m₁))}
        {y = Rcomb.ireindex (combine γ₁ Aα.mor₀ Fα.fbase) m₁}
        {z = strong-fmor (μ Q') fs .idxf .PS._⇒_.func (γ₂ , m₂)}
        (combine-lemma γ₁ Aα.mor₀ Fα.fbase m₁)
        (fuse-idx {n = suc n} {Γ = Γ} {sₛ = δ'} {sₜ = extend δ A} Q'
          (λ γ → combine γ Aα.mor₀ Fα.fbase) fs corr-fs γ≈ {m₁} {m₂} m≈)

    -- Fibre analogue of `β-idx`: the fibre transformations agree (modulo transport along β-idx).
    β-fam : (R : Poly (suc n)) → ∀ {γ} {m} →
            Category._≈_ 𝒞
              (fobj μObj R (extend δ A) .fam .subst
                 (β-idx R (Γ .idx .isEquivalence .refl) (fobj μObj R δ' .idx .isEquivalence .refl))
               ∘ (Fα.fold-shape-fam R γ (Aα.R.reindex-shape R Aα.mor₀ (Aα.embed-idx R m))
                  ∘ prod-m (id _) (Aα.R.reindex-fam R Aα.mor₀ ∘ Aα.embed-fam R m)))
              (strong-fmor R fs .famf ._⇒f_.transf (γ , m))
    β-fam (const A') = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) (≈-trans id-left (≈-trans (∘-cong ≈-refl (≈-trans (prod-m-cong ≈-refl id-left) prod-m-id)) id-right))
    β-fam (var Fin.zero) = ≈-trans (∘-cong (A .fam .refl*) ≈-refl) (≈-trans id-left (≈-trans (∘-cong ≈-refl (≈-trans (prod-m-cong ≈-refl id-left) prod-m-id)) id-right))
    β-fam (var (Fin.suc i)) = ≈-trans (∘-cong (δ i .fam .refl*) ≈-refl) (≈-trans id-left (≈-trans (∘-cong ≈-refl (≈-trans (prod-m-cong ≈-refl id-left) prod-m-id)) id-right))
    β-fam (R₁ + R₂) {m = inj₁ m'} = ≈-trans (β-fam R₁) (≈-sym (≈-trans id-left id-left))
    β-fam (R₁ + R₂) {m = inj₂ m'} = ≈-trans (β-fam R₂) (≈-sym (≈-trans id-left id-left))
    β-fam (R₁ × R₂) {m = m₁' , m₂'} =
      ≈-trans (∘-cong ≈-refl (pair-natural _ _ _))
        (≈-trans (pair-compose _ _ _ _)
          (pair-cong
            (≈-trans (∘-cong ≈-refl
                       (≈-trans (assoc _ _ _)
                         (≈-trans (∘-cong ≈-refl
                                    (≈-trans (∘-cong ≈-refl (prod-m-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _))))
                                      (strong-p₁-natural (id _) _ _)))
                           (≈-sym (assoc _ _ _)))))
              (≈-trans (≈-sym (assoc _ _ _))
                (≈-trans (∘-cong (β-fam R₁) ≈-refl)
                  (≈-trans (∘-cong ≈-refl (pair-cong ≈-refl (≈-sym id-left))) (≈-sym id-left)))))
            (≈-trans (∘-cong ≈-refl
                       (≈-trans (assoc _ _ _)
                         (≈-trans (∘-cong ≈-refl
                                    (≈-trans (∘-cong ≈-refl (prod-m-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _))))
                                      (strong-p₂-natural (id _) _ _)))
                           (≈-sym (assoc _ _ _)))))
              (≈-trans (≈-sym (assoc _ _ _))
                (≈-trans (∘-cong (β-fam R₂) ≈-refl)
                  (≈-trans (∘-cong ≈-refl (pair-cong ≈-refl (≈-sym id-left))) (≈-sym id-left)))))))
    β-fam (μ Q') {γ} {m} =
      ≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (prod-m-cong ≈-refl id-right)))
        (≈-trans (∘-cong (Fα.TA'.fib-trans*
                            {x = Fα.fold-reindex γ Fα.fbase (Aα.R.reindex Aα.mor₀ m)}
                            {y = Rcomb.ireindex (combine γ Aα.mor₀ Fα.fbase) m}
                            {z = strong-fmor (μ Q') fs .idxf .PS._⇒_.func (γ , m)}
                            (fuse-idx {n = suc n} {Γ = Γ} {sₛ = δ'} {sₜ = extend δ A} Q'
                              (λ γ' → combine γ' Aα.mor₀ Fα.fbase) fs corr-fs
                              (Γ .idx .isEquivalence .refl) {m} {m}
                              (μObj Q' δ' .idx .isEquivalence .refl {m}))
                            (combine-lemma γ Aα.mor₀ Fα.fbase m)) ≈-refl)
          (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl (Cγ.combine-lemma-fam Aα.mor₀ Fα.fbase m))
              (fuse-fam γ Q' (λ γ' → combine γ' Aα.mor₀ Fα.fbase)
                (Cγ.combine-act Aα.mor₀ Fα.fbase) fs corr-fs corr-fs-fam {m}))))
      where
        module Cγ = CombineFam γ
        corr-fs-fam : ∀ i {a} →
                      (extend δ A i .fam .subst
                         (corr-fs i (Γ .idx .isEquivalence .refl) (δ' i .idx .isEquivalence .refl {a}))
                       ∘ Cγ.FR.aapply (Cγ.combine-act Aα.mor₀ Fα.fbase) i a)
                      ≈ (fs i .famf ._⇒f_.transf (γ , a))
        corr-fs-fam Fin.zero {a} =
          ≈-trans (∘-cong (A .fam .refl*) ≈-refl)
            (≈-trans id-left (≈-trans (∘-cong ≈-refl prod-m-id) id-right))
        corr-fs-fam (Fin.suc j) {a} =
          ≈-trans (∘-cong (δ j .fam .refl*) ≈-refl)
            (≈-trans id-left (≈-trans (∘-cong ≈-refl prod-m-id) id-right))

  -- η/uniqueness machinery: any h satisfying the β square agrees with the fold,
  -- pointwise by tree induction. The nested-μ case collapses h's strong action to an
  -- index-only reindex (`cmb-hs`, via fuse-idx) and telescopes it against the fold.
  module EtaDef {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
                (alg : Mor (Fam𝒞-P.prod Γ (fobj μObj P (extend δ A))) A)
                (h : Mor (Fam𝒞-P.prod Γ (μObj P δ)) A)
                (eq : Fam𝒞._≈_
                        (Fam𝒞._∘_ h (Fam𝒞-P.pair Fam𝒞-P.p₁ (Fam𝒞._∘_ (AlphaDef.αmor P δ) Fam𝒞-P.p₂)))
                        (Fam𝒞._∘_ alg (Fam𝒞-P.pair Fam𝒞-P.p₁
                          (HasMu.strong-fmor hasMu P (HasMu.strong-extend-mor hasMu (λ i → Fam𝒞-P.p₂) h))))) where
    open HasMu hasMu using (strong-fmor; strong-extend-mor)
    module Aα = AlphaDef P δ
    module Fα = FoldDef {Γ = Γ} {A = A} {P = P} {δ = δ} alg
    δ' = extend δ (μObj P δ)
    hs : ∀ i → Mor (Fam𝒞-P.prod Γ (δ' i)) (extend δ A i)
    hs = strong-extend-mor (λ i → Fam𝒞-P.p₂) h

    -- Context shift δ → δ': the μ-binder slot of `η₀ P` is exactly the fresh δ' slot.
    module Rδ = Reindex δ δ'
    imor₀ : Rδ.IMorD (η₀ P) (λ v → inj₁ v)
    imor₀ = Rδ.ibase (λ { Fin.zero a → a ; (Fin.suc i) a → a })
                     (λ { Fin.zero p → p ; (Fin.suc i) p → p })

    -- Round trip: shifting into δ' and reindexing back along mor₀ is the identity.
    mutual
      data RT : ∀ {j} {ρD : Fin j → Fin n ⊎ Sort n} {ρX : Fin j → Fin (suc n) ⊎ Sort (suc n)} →
                Rδ.IMorD ρD ρX → Aα.R.IMorD ρX ρD → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
        rtbase : RT imor₀ (Aα.R.erase Aα.mor₀)
        rtbind : ∀ {j} {ρD ρX} {md : Rδ.IMorD {j} ρD ρX} {md' : Aα.R.IMorD ρX ρD} (Q : Poly (suc j)) →
                 RT md md' → RT (Rδ.ibind Q md) (Aα.R.ibind Q md')

      rt-shape : ∀ {j} (S : Poly j) {ρD ρX} {md : Rδ.IMorD ρD ρX} {md' : Aα.R.IMorD ρX ρD}
                 (rt : RT md md') (z : Fα.Tδ.⟦ S ⟧shape ρD) →
                 Fα.Tδ.shape≈ S ρD (Aα.R.ireindex-shape S md' (Rδ.ireindex-shape S md z)) z
      rt-shape (const A') rt z = A' .idx .isEquivalence .refl
      rt-shape (var v) rt z = rt-apply rt v
      rt-shape (S₁ + S₂) rt (inj₁ z) = rt-shape S₁ rt z
      rt-shape (S₁ + S₂) rt (inj₂ z) = rt-shape S₂ rt z
      rt-shape (S₁ × S₂) rt (z₁ , z₂) = rt-shape S₁ rt z₁ , rt-shape S₂ rt z₂
      rt-shape (μ S') rt (Fα.Tδ.sup z) = rt-shape S' (rtbind S' rt) z

      rt-apply : ∀ {j} {ρD ρX} {md : Rδ.IMorD {j} ρD ρX} {md' : Aα.R.IMorD ρX ρD}
                 (rt : RT md md') (v : Fin j) {z} →
                 Fα.Tδ.elEq (ρD v) (Aα.R.iapply md' v (Rδ.iapply md v z)) z
      rt-apply rtbase Fin.zero {z} = Fα.Tδ.W-≈-refl z
      rt-apply rtbase (Fin.suc i) {z} = δ i .idx .isEquivalence .refl
      rt-apply (rtbind S' rt) Fin.zero {z} = rt-shape (μ S') rt z
      rt-apply (rtbind S' rt) (Fin.suc v) = rt-apply rt v

    -- h's strong action collapsed to an index-only reindex, and its fuse-idx hypothesis.
    module Rcomb = Reindex δ' (extend δ A)
    cmb-hs : Γ .idx .Carrier → Rcomb.IMorD (λ v → inj₁ v) (λ v → inj₁ v)
    cmb-hs γ = Rcomb.ibase (λ { Fin.zero a → h .idxf .PS._⇒_.func (γ , a) ; (Fin.suc i) a → a })
                           (λ { Fin.zero p → h .idxf .PS._⇒_.func-resp-≈ (Γ .idx .isEquivalence .refl , p)
                              ; (Fin.suc i) p → p })

    corr-hs : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (δ' i .idx) a₁ a₂) →
              _≈s_ (extend δ A i .idx) (Rcomb.iapply (cmb-hs γ₁) i a₁) (hs i .idxf .PS._⇒_.func (γ₂ , a₂))
    corr-hs Fin.zero γ≈ a≈ = h .idxf .PS._⇒_.func-resp-≈ (γ≈ , a≈)
    corr-hs (Fin.suc j) γ≈ a≈ = a≈

    mutual
      -- h agrees with the fold, pointwise. At sup, round-trip through α's
      -- reconstruction so the β square `eq` applies, then push through the shape.
      η-idx : ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {t₁ t₂ : Fα.Tδ.W P (λ i → inj₁ i)}
              (t≈ : Fα.Tδ.W-≈ t₁ t₂) →
              _≈s_ (A .idx) (h .idxf .PS._⇒_.func (γ₁ , t₁)) (Fα.fold-idx γ₂ t₂)
      η-idx {γ₁} {γ₂} γ≈ {Fα.Tδ.sup x₁} {Fα.Tδ.sup x₂} t≈ =
        A .idx .isEquivalence .trans
          (h .idxf .PS._⇒_.func-resp-≈
            (Γ .idx .isEquivalence .refl {γ₁} ,
             Fα.Tδ.W-≈-sym
               {x = Aα.αmor .idxf .PS._⇒_.func (Aα.unembed-idx P (Rδ.ireindex-shape P imor₀ x₁))}
               {y = Fα.Tδ.sup x₁}
               (Fα.Tδ.shape≈-trans P (η₀ P)
                 (Aα.R.ireindex-shape-resp P (Aα.R.erase Aα.mor₀)
                   (Aα.embed-unembed P (Rδ.ireindex-shape P imor₀ x₁)))
                 (rt-shape P rtbase x₁))))
          (A .idx .isEquivalence .trans
            (eq ._≃_.idxf-eq .PS._≃m_.func-eq
              (γ≈ , Aα.unembed-idx-resp P (Rδ.ireindex-shape-resp P imor₀ t≈)))
            (alg .idxf .PS._⇒_.func-resp-≈ (Γ .idx .isEquivalence .refl {γ₂} , η-shape P γ₂ x₂)))

      -- h's strong action at the unembedded shift agrees with the fold's shape action.
      η-shape : (R : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Fα.Tδ.⟦ R ⟧shape (η₀ P)) →
                _≈s_ (fobj μObj R (extend δ A) .idx)
                     (strong-fmor R hs .idxf .PS._⇒_.func
                        (γ , Aα.unembed-idx R (Rδ.ireindex-shape R imor₀ x)))
                     (Fα.fold-shape-idx R γ x)
      η-shape (const A') γ x = A' .idx .isEquivalence .refl
      η-shape (var Fin.zero) γ x = η-idx (Γ .idx .isEquivalence .refl {γ}) (Fα.Tδ.W-≈-refl x)
      η-shape (var (Fin.suc j)) γ x = δ j .idx .isEquivalence .refl
      η-shape (R₁ + R₂) γ (inj₁ x) = η-shape R₁ γ x
      η-shape (R₁ + R₂) γ (inj₂ y) = η-shape R₂ γ y
      η-shape (R₁ × R₂) γ (x , y) = η-shape R₁ γ x , η-shape R₂ γ y
      η-shape (μ Q') γ x =
        Fα.TA'.W-≈-trans
          {x = strong-fmor (μ Q') hs .idxf .PS._⇒_.func (γ , Rδ.ireindex imor₀ x)}
          {y = Rcomb.ireindex (cmb-hs γ) (Rδ.ireindex imor₀ x)}
          {z = Fα.fold-reindex γ Fα.fbase x}
          (Fα.TA'.W-≈-sym
            {x = Rcomb.ireindex (cmb-hs γ) (Rδ.ireindex imor₀ x)}
            {y = strong-fmor (μ Q') hs .idxf .PS._⇒_.func (γ , Rδ.ireindex imor₀ x)}
            (fuse-idx {n = suc n} {Γ = Γ} {sₛ = δ'} {sₜ = extend δ A} Q' cmb-hs hs corr-hs
              (Γ .idx .isEquivalence .refl {γ}) {Rδ.ireindex imor₀ x} {Rδ.ireindex imor₀ x}
              (μObj Q' δ' .idx .isEquivalence .refl {Rδ.ireindex imor₀ x})))
          (htele-shape (μ Q') hbase x)
        where
        mutual
          -- Telescope: reindexing by h after the context shift is the fold's reindex,
          -- by the outer induction at the recursion slots.
          data HRel : ∀ {j} {ρD : Fin j → Fin n ⊎ Sort n} {ρX ρC : Fin j → Fin (suc n) ⊎ Sort (suc n)} →
                      Rδ.IMorD ρD ρX → Rcomb.IMorD ρX ρC → Fα.FMor ρD ρC →
                      Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
            hbase : HRel imor₀ (cmb-hs γ) Fα.fbase
            hbind : ∀ {j} {ρD ρX ρC} {md : Rδ.IMorD {j} ρD ρX} {mdc : Rcomb.IMorD ρX ρC}
                    {fm : Fα.FMor ρD ρC} (S' : Poly (suc j)) → HRel md mdc fm →
                    HRel (Rδ.ibind S' md) (Rcomb.ibind S' mdc) (Fα.fbind S' fm)

          htele-shape : ∀ {j} (S : Poly j) {ρD ρX ρC} {md : Rδ.IMorD ρD ρX} {mdc : Rcomb.IMorD ρX ρC}
                        {fm : Fα.FMor ρD ρC} (rel : HRel md mdc fm) (z : Fα.Tδ.⟦ S ⟧shape ρD) →
                        Fα.TA'.shape≈ S ρC (Rcomb.ireindex-shape S mdc (Rδ.ireindex-shape S md z))
                          (Fα.fold-reindex-shape γ S fm z)
          htele-shape (const A') rel z = A' .idx .isEquivalence .refl
          htele-shape (var v) rel z = htele-apply rel v
          htele-shape (S₁ + S₂) rel (inj₁ z) = htele-shape S₁ rel z
          htele-shape (S₁ + S₂) rel (inj₂ z) = htele-shape S₂ rel z
          htele-shape (S₁ × S₂) rel (z₁ , z₂) = htele-shape S₁ rel z₁ , htele-shape S₂ rel z₂
          htele-shape (μ S') rel (Fα.Tδ.sup z) = htele-shape S' (hbind S' rel) z

          htele-apply : ∀ {j} {ρD ρX ρC} {md : Rδ.IMorD {j} ρD ρX} {mdc : Rcomb.IMorD ρX ρC}
                        {fm : Fα.FMor ρD ρC} (rel : HRel md mdc fm) (v : Fin j) {z} →
                        Fα.TA'.elEq (ρC v) (Rcomb.iapply mdc v (Rδ.iapply md v z)) (Fα.fold-apply γ fm v z)
          htele-apply hbase Fin.zero {z} = η-idx (Γ .idx .isEquivalence .refl {γ}) (Fα.Tδ.W-≈-refl z)
          htele-apply hbase (Fin.suc i) {z} = δ i .idx .isEquivalence .refl
          htele-apply (hbind S' rel) Fin.zero {z} = htele-shape (μ S') rel z
          htele-apply (hbind S' rel) (Fin.suc v) = htele-apply rel v

  hasMuLaws : HasMuLaws hasMu
  hasMuLaws .HasMuLaws.⦅⦆-β {P = P} alg ._≃_.idxf-eq .PS._≃m_.func-eq (γ≈ , m≈) =
    alg .idxf .PS._⇒_.func-resp-≈ (γ≈ , BetaDef.β-idx alg P γ≈ m≈)
  hasMuLaws .HasMuLaws.⦅⦆-β {Γ = Γ} {P = P} {δ = δ} alg ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , m} =
    ≈-trans (∘-cong ≈-refl id-left)
      (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (pair-cong ≈-refl id-left)))
        (≈-trans (∘-cong ≈-refl (assoc _ _ _))
          (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl
                     (≈-trans (pair-natural _ _ _)
                       (pair-cong (pair-p₁ _ _) (∘-cong ≈-refl (pair-cong (≈-sym id-left) ≈-refl))))))
            (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong (≈-sym (alg .famf ._⇒f_.natural
                                         (Γ .idx .isEquivalence .refl ,
                                          B.β-idx P (Γ .idx .isEquivalence .refl)
                                            (fobj μObj P B.δ' .idx .isEquivalence .refl)))) ≈-refl)
                (≈-trans (assoc _ _ _)
                  (≈-trans (∘-cong ≈-refl (pair-compose _ _ _ _))
                    (≈-trans (∘-cong ≈-refl
                               (pair-cong (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left) (B.β-fam P)))
                      (≈-sym id-left)))))))))
    where
      module B = BetaDef {P = P} {δ = δ} alg
  hasMuLaws .HasMuLaws.⦅⦆-η {Γ = Γ} {P = P} {δ = δ} alg h eq ._≃_.idxf-eq .PS._≃m_.func-eq (γ≈ , t≈) =
    EtaDef.η-idx {P = P} {δ = δ} alg h eq γ≈ t≈
  hasMuLaws .HasMuLaws.⦅⦆-η alg h eq ._≃_.famf-eq = {!!}
