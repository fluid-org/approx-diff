{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Fibre layer of the Fam μ-type construction, over the category-free sort
-- layer. A decoration of a sort is a μ-body erasing to it, together with
-- decorations of the sorts in its assignment; the fibre of a tree reads the
-- decoration's constants and the environment's fibres by structural recursion
-- on the tree.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Nat using (suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts)
open import functor using (Functor)
open import indexed-family using (Fam; _⇒f_)
open import prop-setoid using (Setoid)
import setoid-cat
import fam
import polynomial-functor
import fam-mu-types.sort

module fam-mu-types.fibre {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where

open Category 𝒞
open Functor
open HasProducts P
open fam.CategoryOfFamilies os (os ⊔ es) 𝒞
open Obj
open Mor
open Fam
open _≃_
module Sh = fam-mu-types.sort os es
open Sh using (mkSort)

Poly-C = polynomial-functor.Poly cat
open polynomial-functor.Poly
open polynomial-functor using (extend; Poly-map)

private module SC = Category (setoid-cat.SetoidCat os (os ⊔ es))

-- The index functor: a family to its index setoid, a morphism to its index map.
Idx : Functor cat (setoid-cat.SetoidCat os (os ⊔ es))
Idx .fobj X = X .idx
Idx .fmor f = f .idxf
Idx .fmor-cong e = e .idxf-eq
Idx .fmor-id = SC.≈-refl
Idx .fmor-comp f g = SC.≈-refl

∣_∣ : ∀ {n} → Poly-C n → Sh.Poly n
∣_∣ = Poly-map Idx

private
  ℓD : Level
  ℓD = o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es

module Fibre {n} (δ : Fin n → Obj) where
  open Sh.Tree (λ i → δ i .idx)

  -- A decoration of a sort: a μ-body erasing to it, with the sorts in its
  -- assignment decorated in turn. The sort is recovered by projection.
  data Deco : Sh.Sort n → Set ℓD

  DecoAssign : Fin n ⊎ Sh.Sort n → Set ℓD
  DecoAssign (inj₁ _) = Lift ℓD ⊤
  DecoAssign (inj₂ s) = Deco s

  data Deco where
    mkDeco : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n} →
             ((i : Fin k) → DecoAssign (ρ̄ i)) → Deco (mkSort ∣ Q ∣ ρ̄)

  -- The body environment of a decorated μ-binder: slot 0 is the binder's own
  -- decoration, the rest are the ambient ones.
  deco-ext : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
             (d : ∀ i → DecoAssign (ρ̄ i)) →
             ∀ i → DecoAssign (extend ρ̄ (inj₂ (mkSort ∣ Q ∣ ρ̄)) i)
  deco-ext Q d Fin.zero = mkDeco Q d
  deco-ext Q d (Fin.suc i) = d i

  -- The fibre object at each tree: 𝒞-products at ×, parameter/const fibres at
  -- the leaves, the decoration supplying the constants.
  mutual
    fib : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
          (d : ∀ i → DecoAssign (ρ̄ i)) → W ∣ Q ∣ ρ̄ → obj
    fib Q d (sup x) = fib-shape Q (deco-ext Q d) x

    fib-shape : ∀ {j} (Q : Poly-C j) {η̄ : Fin j → Fin n ⊎ Sh.Sort n}
                (d : ∀ i → DecoAssign (η̄ i)) → ⟦ ∣ Q ∣ ⟧shape η̄ → obj
    fib-shape (const A) d x = A .fam .fm x
    fib-shape (var i)   d x = fib-el _ (d i) x
    fib-shape (P + Q) d (inj₁ x) = fib-shape P d x
    fib-shape (P + Q) d (inj₂ y) = fib-shape Q d y
    fib-shape (P × Q) d (x , y) = prod (fib-shape P d x) (fib-shape Q d y)
    fib-shape (μ Q') d x = fib Q' d x

    fib-el : (r : Fin n ⊎ Sh.Sort n) → DecoAssign r → El r → obj
    fib-el (inj₁ p) _ x = δ p .fam .fm x
    fib-el (inj₂ _) (mkDeco Q ρd) x = fib Q ρd x

  -- Transport of fibres along bisimilarity, by recursion on the W-≈ proof.
  mutual
    fib-subst : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
                (d : ∀ i → DecoAssign (ρ̄ i)) {x y : W ∣ Q ∣ ρ̄} →
                W-≈ x y → fib Q d x ⇒ fib Q d y
    fib-subst Q d {sup x} {sup y} p = fib-shape-subst Q (deco-ext Q d) p

    fib-shape-subst : ∀ {j} (Q : Poly-C j) {η̄ : Fin j → Fin n ⊎ Sh.Sort n}
                      (d : ∀ i → DecoAssign (η̄ i)) {x y : ⟦ ∣ Q ∣ ⟧shape η̄} →
                      shape≈ ∣ Q ∣ η̄ x y → fib-shape Q d x ⇒ fib-shape Q d y
    fib-shape-subst (const A) d p = A .fam .subst p
    fib-shape-subst (var i)   d p = fib-el-subst _ (d i) p
    fib-shape-subst (P + Q) d {inj₁ _} {inj₁ _} p = fib-shape-subst P d p
    fib-shape-subst (P + Q) d {inj₂ _} {inj₂ _} p = fib-shape-subst Q d p
    fib-shape-subst (P × Q) d {_ , _} {_ , _} (p₁ , p₂) =
      prod-m (fib-shape-subst P d p₁) (fib-shape-subst Q d p₂)
    fib-shape-subst (μ Q') d {x} {y} p = fib-subst Q' d {x = x} {y = y} p

    fib-el-subst : (r : Fin n ⊎ Sh.Sort n) (dr : DecoAssign r) {x y : El r} →
                   elEq r x y → fib-el r dr x ⇒ fib-el r dr y
    fib-el-subst (inj₁ p) _ e = δ p .fam .subst e
    fib-el-subst (inj₂ _) (mkDeco Q ρd) {x} {y} e = fib-subst Q ρd {x = x} {y = y} e

  -- Transport along reflexivity is the identity.
  mutual
    fib-refl* : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
                (d : ∀ i → DecoAssign (ρ̄ i)) (x : W ∣ Q ∣ ρ̄) →
                fib-subst Q d {x = x} {y = x} (W-≈-refl x) ≈ id (fib Q d x)
    fib-refl* Q d (sup x) = fib-shape-refl* Q (deco-ext Q d) x

    fib-shape-refl* : ∀ {j} (Q : Poly-C j) {η̄ : Fin j → Fin n ⊎ Sh.Sort n}
                      (d : ∀ i → DecoAssign (η̄ i)) (x : ⟦ ∣ Q ∣ ⟧shape η̄) →
                      fib-shape-subst Q d (shape≈-refl ∣ Q ∣ η̄ x) ≈ id (fib-shape Q d x)
    fib-shape-refl* (const A) d x = A .fam .refl*
    fib-shape-refl* (var i)   d x = fib-el-refl* _ (d i) x
    fib-shape-refl* (P + Q) d (inj₁ x) = fib-shape-refl* P d x
    fib-shape-refl* (P + Q) d (inj₂ y) = fib-shape-refl* Q d y
    fib-shape-refl* (P × Q) d (x , y) =
      ≈-trans (prod-m-cong (fib-shape-refl* P d x) (fib-shape-refl* Q d y)) prod-m-id
    fib-shape-refl* (μ Q') d x = fib-refl* Q' d x

    fib-el-refl* : (r : Fin n ⊎ Sh.Sort n) (dr : DecoAssign r) (x : El r) →
                   fib-el-subst r dr (elEq-refl r x) ≈ id (fib-el r dr x)
    fib-el-refl* (inj₁ p) _ x = δ p .fam .refl*
    fib-el-refl* (inj₂ _) (mkDeco Q ρd) x = fib-refl* Q ρd x

  -- Transport is functorial: a composite is the composite of the transports.
  mutual
    fib-trans* : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
                 (d : ∀ i → DecoAssign (ρ̄ i)) {x y z : W ∣ Q ∣ ρ̄}
                 (q : W-≈ y z) (p : W-≈ x y) →
                 fib-subst Q d {x = x} {y = z} (W-≈-trans {x = x} {y = y} {z = z} p q)
                   ≈ (fib-subst Q d {x = y} {y = z} q ∘ fib-subst Q d {x = x} {y = y} p)
    fib-trans* Q d {sup x} {sup y} {sup z} q p = fib-shape-trans* Q (deco-ext Q d) q p

    fib-shape-trans* : ∀ {j} (Q : Poly-C j) {η̄ : Fin j → Fin n ⊎ Sh.Sort n}
                       (d : ∀ i → DecoAssign (η̄ i)) {x y z : ⟦ ∣ Q ∣ ⟧shape η̄}
                       (q : shape≈ ∣ Q ∣ η̄ y z) (p : shape≈ ∣ Q ∣ η̄ x y) →
                       fib-shape-subst Q d (shape≈-trans ∣ Q ∣ η̄ p q)
                         ≈ (fib-shape-subst Q d q ∘ fib-shape-subst Q d p)
    fib-shape-trans* (const A) d q p = A .fam .trans* q p
    fib-shape-trans* (var i)   d q p = fib-el-trans* _ (d i) q p
    fib-shape-trans* (P + Q) d {inj₁ _} {inj₁ _} {inj₁ _} q p = fib-shape-trans* P d q p
    fib-shape-trans* (P + Q) d {inj₂ _} {inj₂ _} {inj₂ _} q p = fib-shape-trans* Q d q p
    fib-shape-trans* (P × Q) d {_ , _} {_ , _} {_ , _} (q₁ , q₂) (p₁ , p₂) =
      ≈-trans (prod-m-cong (fib-shape-trans* P d q₁ p₁) (fib-shape-trans* Q d q₂ p₂))
              (prod-m-comp _ _ _ _)
    fib-shape-trans* (μ Q') d {x} {y} {z} q p = fib-trans* Q' d {x = x} {y = y} {z = z} q p

    fib-el-trans* : (r : Fin n ⊎ Sh.Sort n) (dr : DecoAssign r) {x y z : El r}
                    (q : elEq r y z) (p : elEq r x y) →
                    fib-el-subst r dr (elEq-trans r p q)
                      ≈ (fib-el-subst r dr q ∘ fib-el-subst r dr p)
    fib-el-trans* (inj₁ i) _ q p = δ i .fam .trans* q p
    fib-el-trans* (inj₂ _) (mkDeco Q ρd) {x} {y} {z} q p = fib-trans* Q ρd {x = x} {y = y} {z = z} q p

  -- The fibre family of the μ-type at a decorated sort.
  WFam : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
         (d : ∀ i → DecoAssign (ρ̄ i)) → Fam (WSetoid ∣ Q ∣ ρ̄) 𝒞
  WFam Q d .fm = fib Q d
  WFam Q d .subst {x} {y} = fib-subst Q d {x = x} {y = y}
  WFam Q d .refl* {x} = fib-refl* Q d x
  WFam Q d .trans* {x} {y} {z} e₁ e₂ = fib-trans* Q d {x = x} {y = y} {z = z} e₁ e₂

-- The μ-type at the root sort: index by the category-free sort layer, fibres
-- by the canonical decoration, which resolves the μ-body's free variables to
-- the parameters.
μObj : ∀ {n} → Poly-C (suc n) → (Fin n → Obj) → Obj
μObj P δ .idx = Sh.Tree.WSetoid (λ i → δ i .idx) ∣ P ∣ (λ i → inj₁ i)
μObj P δ .fam = Fibre.WFam δ P {ρ̄ = λ i → inj₁ i} (λ i → lift tt)
