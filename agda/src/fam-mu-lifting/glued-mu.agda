{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Definability decorations of the rooted μ-carriers: given predicates at the
-- const leaves of the polynomial and at the environment, every tree fibre
-- carries a glued object, by the same recursion that computes the fibre.
-- Leaves reindex the given predicates along the inclusion of the fibre in
-- question, each root wraps its payload with the glued lifting, and pairs
-- take the glued product beneath the root. Index setoids are fixed at the
-- bottom level so that the carrier of trees can index a join of predicates.
------------------------------------------------------------------------------

open import Level using (Level; 0ℓ; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import prop-setoid as PS using ()
open import categories using (Category; HasTerminal; HasProducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import lifting using (Lifting)
open import functor using (Functor)
open import predicate-system using (PredicateSystem)
open import indexed-family using (_⇒f_)
import fam-mu-lifting.laws
import fam-mu-lifting.glued

module fam-mu-lifting.glued-mu {o m e} {𝒞 : Category o m e}
  (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
  {𝟙c : Category.obj 𝒞} (Lft : Lifting CM 𝟙c)
  (let module R = fam-mu-lifting.laws 0ℓ 0ℓ T CM BP Lft)
  {o₂ m₂ e₂} (𝒫 : Category o₂ m₂ e₂) (𝒫P : HasProducts 𝒫)
  (system : PredicateSystem 𝒫 𝒫P)
  (G : Functor R.cat 𝒫)
  (let open PredicateSystem system)
  (Rt : ∀ (C : R.Obj) → Predicate (Functor.fobj G (R.Lf C)))
  where

open Functor

open fam-mu-lifting.glued 0ℓ 0ℓ T CM BP Lft 𝒫 𝒫P system G Rt public

open R hiding (fobj)
open Gl.Obj

private
  ℓpred : Level
  ℓpred = lsuc o₂ ⊔ lsuc m₂ ⊔ lsuc e₂

-- Pair a carrier with a predicate on its image.
glue : (c : Obj) → Predicate (G .fobj c) → Gl.Obj
glue c P' .carrier = c
glue c P' .pred = P'

-- The inclusion of one fibre of a family, over the unit index.
elem-in : (X : Obj) (x : X .idx .Carrier) → Mor simple[ PS.𝟙 , X .fam .fm x ] X
elem-in X x .idxf .PS._⇒_.func _ = x
elem-in X x .idxf .PS._⇒_.func-resp-≈ _ = X .idx .isEquivalence .refl
elem-in X x .famf ._⇒f_.transf _ = id _
elem-in X x .famf ._⇒f_.natural _ =
  ≈-trans id-left (≈-sym (≈-trans id-right (X .fam .refl*)))

-- A predicate assignment for a polynomial: a predicate on the image of each const leaf.
PolyPred : ∀ {j} → Poly j → Set ℓpred
PolyPred (const A) = Predicate (G .fobj A)
PolyPred (var i)   = Lift ℓpred ⊤
PolyPred (P' + Q') = PolyPred P' ×T PolyPred Q'
PolyPred (P' × Q') = PolyPred P' ×T PolyPred Q'
PolyPred (μ Q')    = PolyPred Q'

module MuPred {n} (δGl : Fin n → Gl.Obj) where
  private
    δc : Fin n → Obj
    δc i = δGl i .carrier

  open Tree δc

  -- Predicate assignments for decorations, mirroring the decoration structure.
  DecoPred : ∀ {s} → Deco s → Set ℓpred
  DecoAssignPred : ∀ (r : Fin n ⊎ Sort n) → DecoAssign r → Set ℓpred

  DecoAssignPred (inj₁ p) _  = Lift ℓpred ⊤
  DecoAssignPred (inj₂ s) dd = DecoPred dd

  DecoPred (mkDeco Q d) = PolyPred Q ×T (∀ i → DecoAssignPred _ (d i))

  deco-ext-pred : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
                  {d : ∀ i → DecoAssign (ρ̄ i)}
                  (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i)) →
                  ∀ i → DecoAssignPred (extend ρ̄ (inj₂ (mkSort ∣ Q ∣ ρ̄)) i) (deco-ext Q d i)
  deco-ext-pred Q pQ pd Fin.zero    = pQ , pd
  deco-ext-pred Q pQ pd (Fin.suc i) = pd i

  -- The glued object of each tree fibre, by the fibre's own recursion.
  mutual
    fib-Gl : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
             (d : ∀ i → DecoAssign (ρ̄ i))
             (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
             (t : W ∣ Q ∣ ρ̄) → Gl.Obj
    fib-Gl Q d pQ pd (sup x) = fib-shape-Gl Q (deco-ext Q d) pQ (deco-ext-pred Q pQ pd) x

    fib-shape-Gl : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
                   (d : ∀ i → DecoAssign (η̄ i))
                   (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (η̄ i) (d i))
                   (x : ⟦ ∣ Q ∣ ⟧shape η̄) → Gl.Obj
    fib-shape-Gl (const A) d pA pd x =
      glue simple[ PS.𝟙 , A .fam .fm x ] (pA [ G .fmor (elem-in A x) ])
    fib-shape-Gl (var i)   d pQ pd x = fib-el-Gl _ (d i) (pd i) x
    fib-shape-Gl (P' + Q') d (pP , pQ) pd (inj₁ x) = Lf-Gl (fib-shape-Gl P' d pP pd x)
    fib-shape-Gl (P' + Q') d (pP , pQ) pd (inj₂ y) = Lf-Gl (fib-shape-Gl Q' d pQ pd y)
    fib-shape-Gl (P' × Q') d (pP , pQ) pd (x , y) =
      Lf-Gl (fib-shape-Gl P' d pP pd x [×] fib-shape-Gl Q' d pQ pd y)
    fib-shape-Gl (μ Q')    d pQ' pd t = fib-Gl Q' d pQ' pd t

    fib-el-Gl : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPred r dr)
                (x : El r) → Gl.Obj
    fib-el-Gl (inj₁ p) _ _ x =
      glue simple[ PS.𝟙 , δc p .fam .fm x ] (δGl p .pred [ G .fmor (elem-in (δc p) x) ])
    fib-el-Gl (inj₂ s) (mkDeco Q ρd) (pQ , pρ) x = fib-Gl Q ρd pQ pρ x
