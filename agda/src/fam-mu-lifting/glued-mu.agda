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
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import prop-setoid as PS using ()
open import categories using (Category; HasTerminal; HasProducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import lifting using (Lifting)
open import functor using (Functor)
open import predicate-system using (PredicateSystem; ClosureOp)
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
  (Cl : ClosureOp 𝒫 𝒫P system)
  (let open ClosureOp Cl)
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

  -- The carrier of each fibre's glued object maps onto the fibre itself: fibrewise the identity,
  -- packaged along the recursion since the carrier's index setoid follows the shape.
  mutual
    in-fib : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
             (d : ∀ i → DecoAssign (ρ̄ i))
             (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
             (t : W ∣ Q ∣ ρ̄) (ι : fib-Gl Q d pQ pd t .carrier .idx .Carrier) →
             fib-Gl Q d pQ pd t .carrier .fam .fm ι ⇒ fib Q d t
    in-fib Q d pQ pd (sup x) ι = in-shape Q (deco-ext Q d) pQ (deco-ext-pred Q pQ pd) x ι

    in-shape : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
               (d : ∀ i → DecoAssign (η̄ i))
               (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (η̄ i) (d i))
               (x : ⟦ ∣ Q ∣ ⟧shape η̄) (ι : fib-shape-Gl Q d pQ pd x .carrier .idx .Carrier) →
               fib-shape-Gl Q d pQ pd x .carrier .fam .fm ι ⇒ fib-shape Q d x
    in-shape (const A) d pA pd x ι = id _
    in-shape (var i)   d pQ pd x ι = in-el _ (d i) (pd i) x ι
    in-shape (P' + Q') d (pP , pQ) pd (inj₁ x) ι = Lmap (in-shape P' d pP pd x ι)
    in-shape (P' + Q') d (pP , pQ) pd (inj₂ y) ι = Lmap (in-shape Q' d pQ pd y ι)
    in-shape (P' × Q') d (pP , pQ) pd (x , y) (ι₁ , ι₂) =
      Lmap (prod-m (in-shape P' d pP pd x ι₁) (in-shape Q' d pQ pd y ι₂))
    in-shape (μ Q')    d pQ' pd t ι = in-fib Q' d pQ' pd t ι

    in-el : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPred r dr)
            (x : El r) (ι : fib-el-Gl r dr pr x .carrier .idx .Carrier) →
            fib-el-Gl r dr pr x .carrier .fam .fm ι ⇒ fib-el r dr x
    in-el (inj₁ p) _ _ x ι = id _
    in-el (inj₂ s) (mkDeco Q ρd) (pQ , pρ) x ι = in-fib Q ρd pQ pρ x ι

  -- The inclusions absorb the carriers' transports, which are all isomorphic to the identity.
  mutual
    in-fib-natural : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
                     (d : ∀ i → DecoAssign (ρ̄ i))
                     (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
                     (t : W ∣ Q ∣ ρ̄) {ι₁ ι₂ : fib-Gl Q d pQ pd t .carrier .idx .Carrier}
                     (e : _≈s_ (fib-Gl Q d pQ pd t .carrier .idx) ι₁ ι₂) →
                     (in-fib Q d pQ pd t ι₂ ∘ fib-Gl Q d pQ pd t .carrier .fam .subst e)
                       ≈ in-fib Q d pQ pd t ι₁
    in-fib-natural Q d pQ pd (sup x) e =
      in-shape-natural Q (deco-ext Q d) pQ (deco-ext-pred Q pQ pd) x e

    in-shape-natural : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
                       (d : ∀ i → DecoAssign (η̄ i))
                       (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (η̄ i) (d i))
                       (x : ⟦ ∣ Q ∣ ⟧shape η̄)
                       {ι₁ ι₂ : fib-shape-Gl Q d pQ pd x .carrier .idx .Carrier}
                       (e : _≈s_ (fib-shape-Gl Q d pQ pd x .carrier .idx) ι₁ ι₂) →
                       (in-shape Q d pQ pd x ι₂ ∘ fib-shape-Gl Q d pQ pd x .carrier .fam .subst e)
                         ≈ in-shape Q d pQ pd x ι₁
    in-shape-natural (const A) d pA pd x e = id-left
    in-shape-natural (var i)   d pQ pd x e = in-el-natural _ (d i) (pd i) x e
    in-shape-natural (P' + Q') d (pP , pQ) pd (inj₁ x) e =
      ≈-trans (≈-sym (Lmap-comp _ _)) (Lmap-cong (in-shape-natural P' d pP pd x e))
    in-shape-natural (P' + Q') d (pP , pQ) pd (inj₂ y) e =
      ≈-trans (≈-sym (Lmap-comp _ _)) (Lmap-cong (in-shape-natural Q' d pQ pd y e))
    in-shape-natural (P' × Q') d (pP , pQ) pd (x , y) {_ , _} {_ , _} (e₁ , e₂) =
      ≈-trans (≈-sym (Lmap-comp _ _))
        (Lmap-cong
          (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                   (prod-m-cong (in-shape-natural P' d pP pd x e₁)
                                (in-shape-natural Q' d pQ pd y e₂))))
    in-shape-natural (μ Q')    d pQ' pd t e = in-fib-natural Q' d pQ' pd t e

    in-el-natural : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPred r dr)
                    (x : El r) {ι₁ ι₂ : fib-el-Gl r dr pr x .carrier .idx .Carrier}
                    (e : _≈s_ (fib-el-Gl r dr pr x .carrier .idx) ι₁ ι₂) →
                    (in-el r dr pr x ι₂ ∘ fib-el-Gl r dr pr x .carrier .fam .subst e)
                      ≈ in-el r dr pr x ι₁
    in-el-natural (inj₁ p) _ _ x e = id-left
    in-el-natural (inj₂ s) (mkDeco Q ρd) (pQ , pρ) x e = in-fib-natural Q ρd pQ pρ x e

  -- The inclusion of a fibre's carrier at its tree, over the constant index map.
  tree-in : (P' : Poly (suc n)) (pP : PolyPred P') (t : W ∣ P' ∣ (λ i → inj₁ i)) →
            Mor (fib-Gl P' (λ i → lift tt) pP (λ i → lift tt) t .carrier) (μObj P' δc)
  tree-in P' pP t .idxf .PS._⇒_.func _ = t
  tree-in P' pP t .idxf .PS._⇒_.func-resp-≈ _ = W-≈-refl t
  tree-in P' pP t .famf ._⇒f_.transf ι = in-fib P' (λ i → lift tt) pP (λ i → lift tt) t ι
  tree-in P' pP t .famf ._⇒f_.natural {ι₁} {ι₂} e =
    ≈-trans (in-fib-natural P' (λ i → lift tt) pP (λ i → lift tt) t e)
            (≈-sym (≈-trans (∘-cong (fib-refl* P' (λ i → lift tt) t) ≈-refl) id-left))

  -- The μ-carrier decorated with the closed join over trees of the fibre predicates. The closure
  -- is needed because an element of the carrier factors through a single tree's inclusion only
  -- after its stage has been refined along a cover splitting the index choice.
  μ-Gl : (P' : Poly (suc n)) (pP : PolyPred P') → Gl.Obj
  μ-Gl P' pP .carrier = μObj P' δc
  μ-Gl P' pP .pred =
    𝐂 (⋁ (W ∣ P' ∣ (λ i → inj₁ i))
         (λ t → fib-Gl P' (λ i → lift tt) pP (λ i → lift tt) t .pred ⟨ G .fmor (tree-in P' pP t) ⟩))

private module GlCP = Gl.coproducts coproducts

-- The glued interpretation of a polynomial: the carrier interpretation with the matching glued
-- former at every node, the μ case supplying the closed join.
fobj-Gl : ∀ {j} (Q : Poly j) (pQ : PolyPred Q) (δGl : Fin j → Gl.Obj) → Gl.Obj
fobj-Gl (const A) pA δGl = glue A pA
fobj-Gl (var i)   _  δGl = δGl i
fobj-Gl (P' + Q') (pP , pQ) δGl =
  GlCP._[+]_ (Lf-Gl (fobj-Gl P' pP δGl)) (Lf-Gl (fobj-Gl Q' pQ δGl))
fobj-Gl (P' × Q') (pP , pQ) δGl = Lf-Gl (fobj-Gl P' pP δGl [×] fobj-Gl Q' pQ δGl)
fobj-Gl (μ Q')    pQ' δGl = MuPred.μ-Gl δGl Q' pQ'
