{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Carrier of μ-types for the Fam construction: nested μ reduced to a single
-- sort-indexed W-type in setoids, with the fibre family computed by structural
-- recursion over trees. First layer of fam-mu-types-2; the full interface is
-- re-exported by fam-mu-types-2.laws.
--
-- Abbott, Altenkirch, Ghani. Containers: constructing strictly positive types. TCS 342(1), 2005.
-- Abbott, Altenkirch, Ghani. Representing nested inductive types using W-types. ICALP 2004.
-- Emmenegger. W-types in setoids. arXiv:1809.02375, 2018.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts)
open import prop-setoid using (IsEquivalence; Setoid)
open import indexed-family using (Fam; _⇒f_)
import fam
import polynomial-functor-2

module fam-mu-types-2.carrier {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where

open Category 𝒞 public
open IsEquivalence public
open HasProducts P public
open fam.CategoryOfFamilies os (os ⊔ es) 𝒞 public
open Obj public
open Mor public
open Fam public
module Fam𝒞 = Category cat
open products P public  -- Fam-level products
module Fam𝒞-P = HasProducts products
open _⇒f_ public
open polynomial-functor-2 (terminal T) products strongCoproducts public
  using (Poly; const; var; _+_; _×_; μ; extend; fobj; HasMu; HasMuLaws)
open Setoid using (Carrier; isEquivalence) renaming (_≈_ to _≈s_) public

open import Data.Sum using (_⊎_) public
open import Data.Product using () renaming (_×_ to _×T_) public
open import prop using (_∧_; ⊥) public

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

μObj : ∀ {n} → Poly (suc n) → (Fin n → Obj) → Obj
μObj P δ .idx = WSetoid δ P (λ i → inj₁ i)
μObj P δ .fam = WFam δ P (λ i → inj₁ i)
