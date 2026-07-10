{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Fibre layer of the Fam μ-type construction. The shape layer
-- (fam-mu-types-2.shape) is category-free, built over index-erased polynomials.
-- A decoration of a sort is a μ-body erasing to it, together with decorations of
-- the sorts in its resolution; the fibre of a tree reads the decoration's
-- constants and the environment's fibres by structural recursion on the tree.
--
-- Objects only; transport and its laws are added separately.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import categories using (Category; HasTerminal; HasProducts)
open import functor using (Functor)
open import indexed-family using (Fam; _⇒f_)
open import prop-setoid using (Setoid)
import setoid-cat
import fam
import polynomial-functor-2
import fam-mu-types-2.shape

module fam-mu-types-2.fibre {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where

open Category 𝒞
open HasProducts P
open fam.CategoryOfFamilies os (os ⊔ es) 𝒞
open Obj
open Mor
open Fam
open _≃_
module Sh = fam-mu-types-2.shape os es
open Sh using (mkSort)

Poly-C = polynomial-functor-2.Poly cat
open polynomial-functor-2.Poly
open polynomial-functor-2 using (extend; Poly-map)

private module SC = Category (setoid-cat.SetoidCat os (os ⊔ es))

-- The index functor: a family to its index setoid, a morphism to its index map.
Idx : Functor cat (setoid-cat.SetoidCat os (os ⊔ es))
Idx .Functor.fobj X = X .idx
Idx .Functor.fmor f = f .idxf
Idx .Functor.fmor-cong e = e .idxf-eq
Idx .Functor.fmor-id = SC.≈-refl
Idx .Functor.fmor-comp f g = SC.≈-refl

∣_∣ : ∀ {n} → Poly-C n → Sh.Poly n
∣_∣ = Poly-map Idx

private
  ℓD : Level
  ℓD = o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es

module Fibre {n} (δ : Fin n → Obj) where
  open Sh.Tree (λ i → δ i .idx)

  -- A decoration of a sort: a μ-body erasing to it, with the sorts in its
  -- resolution decorated in turn. The sort is recovered by projection.
  data Deco : Sh.Sort n → Set ℓD

  DecoRes : Fin n ⊎ Sh.Sort n → Set ℓD
  DecoRes (inj₁ _) = Lift ℓD ⊤
  DecoRes (inj₂ s) = Deco s

  data Deco where
    mkDeco : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n} →
             ((i : Fin k) → DecoRes (ρ̄ i)) → Deco (mkSort ∣ Q ∣ ρ̄)

  -- The body environment of a decorated μ-binder: slot 0 is the binder's own
  -- decoration, the rest are the ambient ones.
  deco-ext : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
             (d : ∀ i → DecoRes (ρ̄ i)) →
             ∀ i → DecoRes (extend ρ̄ (inj₂ (mkSort ∣ Q ∣ ρ̄)) i)
  deco-ext Q d Fin.zero = mkDeco Q d
  deco-ext Q d (Fin.suc i) = d i

  -- The fibre object at each tree: 𝒞-products at ×, parameter/const fibres at
  -- the leaves, the decoration supplying the constants.
  mutual
    fib : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
          (d : ∀ i → DecoRes (ρ̄ i)) → W ∣ Q ∣ ρ̄ → obj
    fib Q d (sup x) = fib-shape Q (deco-ext Q d) x

    fib-shape : ∀ {j} (Q : Poly-C j) {η̄ : Fin j → Fin n ⊎ Sh.Sort n}
                (d : ∀ i → DecoRes (η̄ i)) → ⟦ ∣ Q ∣ ⟧shape η̄ → obj
    fib-shape (const A) d x = A .fam .fm x
    fib-shape (var i)   d x = fib-el _ (d i) x
    fib-shape (P + Q) d (inj₁ x) = fib-shape P d x
    fib-shape (P + Q) d (inj₂ y) = fib-shape Q d y
    fib-shape (P × Q) d (x , y) = prod (fib-shape P d x) (fib-shape Q d y)
    fib-shape (μ Q') d x = fib Q' d x

    fib-el : (r : Fin n ⊎ Sh.Sort n) → DecoRes r → El r → obj
    fib-el (inj₁ p) _ x = δ p .fam .fm x
    fib-el (inj₂ _) (mkDeco Q ρd) x = fib Q ρd x
