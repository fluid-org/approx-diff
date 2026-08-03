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
open Gl._=>_

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

-- The inclusions at equal indices differ by the family's transport.
elem-in-natural : ∀ (X : Obj) {x y : X .idx .Carrier} (p : _≈s_ (X .idx) x y) →
                  Fam𝒞._≈_ (elem-in X x)
                           (Fam𝒞._∘_ (elem-in X y) simplef[ PS.idS PS.𝟙 , X .fam .subst p ])
elem-in-natural X p ._≃_.idxf-eq .PS._≃m_.func-eq _ = p
elem-in-natural X p ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans id-right (≈-sym (≈-trans id-left id-left))

-- Glued morphisms with fibrewise inverses: what the lifted and product formers act on, the
-- inverses feeding the injection's naturality square and the root transport.
record _=>ᵢ_ (X Y : Gl.Obj) : Set (o ⊔ m ⊔ e ⊔ lsuc 0ℓ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  field
    mor  : X Gl.=> Y
    inv  : ∀ x → Y .carrier .fam .fm (mor .morph .idxf .PS._⇒_.func x) ⇒ X .carrier .fam .fm x
    inv₁ : ∀ x → (mor .morph .famf ._⇒f_.transf x ∘ inv x) ≈ id _
    inv₂ : ∀ x → (inv x ∘ mor .morph .famf ._⇒f_.transf x) ≈ id _

open _=>ᵢ_ public

-- The functorial actions extend to the inverses.
Lf-Glᵢ : ∀ {X Y} (f : X =>ᵢ Y) →
         (Rt (X .carrier) ⊑ (Rt (Y .carrier) [ G .fmor (Lf-map (f .mor .morph)) ])) →
         Lf-Gl X =>ᵢ Lf-Gl Y
Lf-Glᵢ f rt .mor =
  Lf-Gl-map (f .mor) (injF-natural (f .mor .morph) (f .inv) (f .inv₁) (f .inv₂)) rt
Lf-Glᵢ f rt .inv x = Lmap (f .inv x)
Lf-Glᵢ f rt .inv₁ x =
  ≈-trans (≈-sym (Lmap-comp _ _)) (≈-trans (Lmap-cong (f .inv₁ x)) Lmap-id)
Lf-Glᵢ f rt .inv₂ x =
  ≈-trans (≈-sym (Lmap-comp _ _)) (≈-trans (Lmap-cong (f .inv₂ x)) Lmap-id)

idᵢ : ∀ {X} → X =>ᵢ X
idᵢ .mor = Gl.id _
idᵢ .inv x = id _
idᵢ .inv₁ x = id-left
idᵢ .inv₂ x = id-left

_∘ᵢ_ : ∀ {X Y Z} → Y =>ᵢ Z → X =>ᵢ Y → X =>ᵢ Z
(f ∘ᵢ g) .mor = Gl._∘_ (f .mor) (g .mor)
(f ∘ᵢ g) .inv x = g .inv x ∘ f .inv (g .mor .morph .idxf .PS._⇒_.func x)
(f ∘ᵢ g) .inv₁ x =
  ≈-trans (∘-cong id-left ≈-refl)
  (≈-trans (assoc _ _ _)
  (≈-trans (∘-cong ≈-refl
             (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong (g .inv₁ x) ≈-refl) id-left)))
           (f .inv₁ _)))
(f ∘ᵢ g) .inv₂ x =
  ≈-trans (∘-cong ≈-refl id-left)
  (≈-trans (assoc _ _ _)
  (≈-trans (∘-cong ≈-refl
             (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong (f .inv₂ _) ≈-refl) id-left)))
           (g .inv₂ x)))

[×]ᵢ : ∀ {X X' Y Y'} → X =>ᵢ X' → Y =>ᵢ Y' → (X [×] Y) =>ᵢ (X' [×] Y')
[×]ᵢ f g .mor = [×]-map (f .mor) (g .mor)
[×]ᵢ f g .inv (x , y) = prod-m (f .inv x) (g .inv y)
[×]ᵢ f g .inv₁ (x , y) =
  ≈-trans (∘-cong (pair-cong id-left id-left) ≈-refl) (pm-iso (f .inv₁ x) (g .inv₁ y))
[×]ᵢ f g .inv₂ (x , y) =
  ≈-trans (∘-cong ≈-refl (pair-cong id-left id-left)) (pm-iso (f .inv₂ x) (g .inv₂ y))

-- The transport of a reindexed leaf between equal indices.
elem-iso : ∀ (X : Obj) (P' : Predicate (G .fobj X)) {x y : X .idx .Carrier}
           (p : _≈s_ (X .idx) x y) →
           glue simple[ PS.𝟙 , X .fam .fm x ] (P' [ G .fmor (elem-in X x) ])
             =>ᵢ glue simple[ PS.𝟙 , X .fam .fm y ] (P' [ G .fmor (elem-in X y) ])
elem-iso X P' p .mor .morph = simplef[ PS.idS PS.𝟙 , X .fam .subst p ]
elem-iso X P' p .mor .presv =
  ⊑-trans ([]-cong (G .fmor-cong (elem-in-natural X p)))
  (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _))
elem-iso X P' p .inv _ = X .fam .subst (X .idx .isEquivalence .sym p)
elem-iso X P' p .inv₁ _ = fam-subst-iso₁ (X .fam) p
elem-iso X P' p .inv₂ _ = fam-subst-iso₂ (X .fam) p

-- A predicate assignment for a polynomial: a predicate on the image of each const leaf.
PolyPred : ∀ {j} → Poly j → Set ℓpred
PolyPred (const A) = Predicate (G .fobj A)
PolyPred (var i)   = Lift ℓpred ⊤
PolyPred (P' + Q') = PolyPred P' ×T PolyPred Q'
PolyPred (P' × Q') = PolyPred P' ×T PolyPred Q'
PolyPred (μ Q')    = PolyPred Q'

-- The environment enters as a carrier assignment and a predicate assignment separately, not as
-- glued objects: the extended environment of the one-step algebra must agree definitionally with
-- the one the reindexing machinery uses, and projecting carriers from glued objects only reduces
-- at applied positions.
module MuPred {n} (δ : Fin n → Obj) (δP : ∀ i → Predicate (G .fobj (δ i))) where

  open Tree δ

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
      glue simple[ PS.𝟙 , δ p .fam .fm x ] (δP p [ G .fmor (elem-in (δ p) x) ])
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

  -- The canonical index of a fibre carrier: trivial at every component.
  mutual
    fib-ix : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
             (d : ∀ i → DecoAssign (ρ̄ i))
             (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
             (t : W ∣ Q ∣ ρ̄) → fib-Gl Q d pQ pd t .carrier .idx .Carrier
    fib-ix Q d pQ pd (sup x) = shape-ix Q (deco-ext Q d) pQ (deco-ext-pred Q pQ pd) x

    shape-ix : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
               (d : ∀ i → DecoAssign (η̄ i))
               (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (η̄ i) (d i))
               (x : ⟦ ∣ Q ∣ ⟧shape η̄) → fib-shape-Gl Q d pQ pd x .carrier .idx .Carrier
    shape-ix (const A) d pA pd x = lift tt
    shape-ix (var i)   d pQ pd x = el-ix _ (d i) (pd i) x
    shape-ix (P' + Q') d (pP , pQ) pd (inj₁ x) = shape-ix P' d pP pd x
    shape-ix (P' + Q') d (pP , pQ) pd (inj₂ y) = shape-ix Q' d pQ pd y
    shape-ix (P' × Q') d (pP , pQ) pd (x , y) = shape-ix P' d pP pd x , shape-ix Q' d pQ pd y
    shape-ix (μ Q')    d pQ' pd t = fib-ix Q' d pQ' pd t

    el-ix : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPred r dr)
            (x : El r) → fib-el-Gl r dr pr x .carrier .idx .Carrier
    el-ix (inj₁ p) _ _ x = lift tt
    el-ix (inj₂ s) (mkDeco Q ρd) (pQ , pρ) x = fib-ix Q ρd pQ pρ x

  -- The reverse inclusions, from the fibre back onto the carrier's fibre at any index.
  mutual
    out-fib : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
              (d : ∀ i → DecoAssign (ρ̄ i))
              (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
              (t : W ∣ Q ∣ ρ̄) (ι : fib-Gl Q d pQ pd t .carrier .idx .Carrier) →
              fib Q d t ⇒ fib-Gl Q d pQ pd t .carrier .fam .fm ι
    out-fib Q d pQ pd (sup x) ι = out-shape Q (deco-ext Q d) pQ (deco-ext-pred Q pQ pd) x ι

    out-shape : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
                (d : ∀ i → DecoAssign (η̄ i))
                (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (η̄ i) (d i))
                (x : ⟦ ∣ Q ∣ ⟧shape η̄) (ι : fib-shape-Gl Q d pQ pd x .carrier .idx .Carrier) →
                fib-shape Q d x ⇒ fib-shape-Gl Q d pQ pd x .carrier .fam .fm ι
    out-shape (const A) d pA pd x ι = id _
    out-shape (var i)   d pQ pd x ι = out-el _ (d i) (pd i) x ι
    out-shape (P' + Q') d (pP , pQ) pd (inj₁ x) ι = Lmap (out-shape P' d pP pd x ι)
    out-shape (P' + Q') d (pP , pQ) pd (inj₂ y) ι = Lmap (out-shape Q' d pQ pd y ι)
    out-shape (P' × Q') d (pP , pQ) pd (x , y) (ι₁ , ι₂) =
      Lmap (prod-m (out-shape P' d pP pd x ι₁) (out-shape Q' d pQ pd y ι₂))
    out-shape (μ Q')    d pQ' pd t ι = out-fib Q' d pQ' pd t ι

    out-el : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPred r dr)
             (x : El r) (ι : fib-el-Gl r dr pr x .carrier .idx .Carrier) →
             fib-el r dr x ⇒ fib-el-Gl r dr pr x .carrier .fam .fm ι
    out-el (inj₁ p) _ _ x ι = id _
    out-el (inj₂ s) (mkDeco Q ρd) (pQ , pρ) x ι = out-fib Q ρd pQ pρ x ι

  -- The inclusions are two-sided inverses.
  mutual
    in-out-fib : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
                 (d : ∀ i → DecoAssign (ρ̄ i))
                 (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
                 (t : W ∣ Q ∣ ρ̄) (ι : fib-Gl Q d pQ pd t .carrier .idx .Carrier) →
                 (in-fib Q d pQ pd t ι ∘ out-fib Q d pQ pd t ι) ≈ id (fib Q d t)
    in-out-fib Q d pQ pd (sup x) ι =
      in-out-shape Q (deco-ext Q d) pQ (deco-ext-pred Q pQ pd) x ι

    in-out-shape : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
                   (d : ∀ i → DecoAssign (η̄ i))
                   (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (η̄ i) (d i))
                   (x : ⟦ ∣ Q ∣ ⟧shape η̄) (ι : fib-shape-Gl Q d pQ pd x .carrier .idx .Carrier) →
                   (in-shape Q d pQ pd x ι ∘ out-shape Q d pQ pd x ι) ≈ id (fib-shape Q d x)
    in-out-shape (const A) d pA pd x ι = id-left
    in-out-shape (var i)   d pQ pd x ι = in-out-el _ (d i) (pd i) x ι
    in-out-shape (P' + Q') d (pP , pQ) pd (inj₁ x) ι =
      ≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (in-out-shape P' d pP pd x ι)) Lmap-id)
    in-out-shape (P' + Q') d (pP , pQ) pd (inj₂ y) ι =
      ≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (in-out-shape Q' d pQ pd y ι)) Lmap-id)
    in-out-shape (P' × Q') d (pP , pQ) pd (x , y) (ι₁ , ι₂) =
      ≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong
                   (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                     (≈-trans (prod-m-cong (in-out-shape P' d pP pd x ι₁)
                                           (in-out-shape Q' d pQ pd y ι₂))
                              prod-m-id)))
                 Lmap-id)
    in-out-shape (μ Q')    d pQ' pd t ι = in-out-fib Q' d pQ' pd t ι

    in-out-el : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPred r dr)
                (x : El r) (ι : fib-el-Gl r dr pr x .carrier .idx .Carrier) →
                (in-el r dr pr x ι ∘ out-el r dr pr x ι) ≈ id (fib-el r dr x)
    in-out-el (inj₁ p) _ _ x ι = id-left
    in-out-el (inj₂ s) (mkDeco Q ρd) (pQ , pρ) x ι = in-out-fib Q ρd pQ pρ x ι

  mutual
    out-in-fib : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
                 (d : ∀ i → DecoAssign (ρ̄ i))
                 (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
                 (t : W ∣ Q ∣ ρ̄) (ι : fib-Gl Q d pQ pd t .carrier .idx .Carrier) →
                 (out-fib Q d pQ pd t ι ∘ in-fib Q d pQ pd t ι)
                   ≈ id (fib-Gl Q d pQ pd t .carrier .fam .fm ι)
    out-in-fib Q d pQ pd (sup x) ι =
      out-in-shape Q (deco-ext Q d) pQ (deco-ext-pred Q pQ pd) x ι

    out-in-shape : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
                   (d : ∀ i → DecoAssign (η̄ i))
                   (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (η̄ i) (d i))
                   (x : ⟦ ∣ Q ∣ ⟧shape η̄) (ι : fib-shape-Gl Q d pQ pd x .carrier .idx .Carrier) →
                   (out-shape Q d pQ pd x ι ∘ in-shape Q d pQ pd x ι)
                     ≈ id (fib-shape-Gl Q d pQ pd x .carrier .fam .fm ι)
    out-in-shape (const A) d pA pd x ι = id-left
    out-in-shape (var i)   d pQ pd x ι = out-in-el _ (d i) (pd i) x ι
    out-in-shape (P' + Q') d (pP , pQ) pd (inj₁ x) ι =
      ≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (out-in-shape P' d pP pd x ι)) Lmap-id)
    out-in-shape (P' + Q') d (pP , pQ) pd (inj₂ y) ι =
      ≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (out-in-shape Q' d pQ pd y ι)) Lmap-id)
    out-in-shape (P' × Q') d (pP , pQ) pd (x , y) (ι₁ , ι₂) =
      ≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong
                   (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                     (≈-trans (prod-m-cong (out-in-shape P' d pP pd x ι₁)
                                           (out-in-shape Q' d pQ pd y ι₂))
                              prod-m-id)))
                 Lmap-id)
    out-in-shape (μ Q')    d pQ' pd t ι = out-in-fib Q' d pQ' pd t ι

    out-in-el : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPred r dr)
                (x : El r) (ι : fib-el-Gl r dr pr x .carrier .idx .Carrier) →
                (out-el r dr pr x ι ∘ in-el r dr pr x ι)
                  ≈ id (fib-el-Gl r dr pr x .carrier .fam .fm ι)
    out-in-el (inj₁ p) _ _ x ι = id-left
    out-in-el (inj₂ s) (mkDeco Q ρd) (pQ , pρ) x ι = out-in-fib Q ρd pQ pρ x ι

  -- The inclusion of a fibre's carrier at its tree, over the constant index map.
  tree-in : (P' : Poly (suc n)) (pP : PolyPred P') (t : W ∣ P' ∣ (λ i → inj₁ i)) →
            Mor (fib-Gl P' (λ i → lift tt) pP (λ i → lift tt) t .carrier) (μObj P' δ)
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
  μ-Gl P' pP .carrier = μObj P' δ
  μ-Gl P' pP .pred =
    𝐂 (⋁ (W ∣ P' ∣ (λ i → inj₁ i))
         (λ t → fib-Gl P' (λ i → lift tt) pP (λ i → lift tt) t .pred ⟨ G .fmor (tree-in P' pP t) ⟩))

  -- Transport of the fibre glued objects along bisimilarity, by the fibre transport's own
  -- recursion: nodes are the functorial actions, leaves the transports of the reindexed
  -- predicates. The root predicate's transport along fibrewise isomorphisms is instance
  -- knowledge, so it is a parameter.
  module Transport
      (Rt-iso : ∀ {C D : Obj} (h : Mor C D)
                (hinv : ∀ x → D .fam .fm (h .idxf .PS._⇒_.func x) ⇒ C .fam .fm x) →
                (∀ x → (h .famf ._⇒f_.transf x ∘ hinv x) ≈ id _) →
                (∀ x → (hinv x ∘ h .famf ._⇒f_.transf x) ≈ id _) →
                Rt C ⊑ (Rt D [ G .fmor (Lf-map h) ]))
      where

    private
      Lf-Glᵢ' : ∀ {X Y} → X =>ᵢ Y → Lf-Gl X =>ᵢ Lf-Gl Y
      Lf-Glᵢ' f =
        Lf-Glᵢ f (Rt-iso (f .mor .morph) (f .inv) (f .inv₁) (f .inv₂))

    mutual
      subst-fib : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
                  (d : ∀ i → DecoAssign (ρ̄ i))
                  (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
                  {t t' : W ∣ Q ∣ ρ̄} (p : W-≈ t t') →
                  fib-Gl Q d pQ pd t =>ᵢ fib-Gl Q d pQ pd t'
      subst-fib Q d pQ pd {sup x} {sup y} p =
        subst-shape Q (deco-ext Q d) pQ (deco-ext-pred Q pQ pd) {x} {y} p

      subst-shape : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
                    (d : ∀ i → DecoAssign (η̄ i))
                    (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (η̄ i) (d i))
                    {x y : ⟦ ∣ Q ∣ ⟧shape η̄} (p : shape≈ ∣ Q ∣ η̄ x y) →
                    fib-shape-Gl Q d pQ pd x =>ᵢ fib-shape-Gl Q d pQ pd y
      subst-shape (const A) d pA pd p = elem-iso A pA p
      subst-shape (var i)   d pQ pd p = subst-el _ (d i) (pd i) p
      subst-shape (P' + Q') d (pP , pQ) pd {inj₁ _} {inj₁ _} p =
        Lf-Glᵢ' (subst-shape P' d pP pd p)
      subst-shape (P' + Q') d (pP , pQ) pd {inj₂ _} {inj₂ _} p =
        Lf-Glᵢ' (subst-shape Q' d pQ pd p)
      subst-shape (P' × Q') d (pP , pQ) pd {_ , _} {_ , _} (p₁ , p₂) =
        Lf-Glᵢ' ([×]ᵢ (subst-shape P' d pP pd p₁) (subst-shape Q' d pQ pd p₂))
      subst-shape (μ Q')    d pQ' pd {x} {y} p = subst-fib Q' d pQ' pd {x} {y} p

      subst-el : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPred r dr)
                 {x y : El r} (e : elEq r x y) →
                 fib-el-Gl r dr pr x =>ᵢ fib-el-Gl r dr pr y
      subst-el (inj₁ p) _ _ e = elem-iso (δ p) (δP p) e
      subst-el (inj₂ s) (mkDeco Q ρd) (pQ , pρ) {x} {y} e = subst-fib Q ρd pQ pρ {x} {y} e

private module GlCP = Gl.coproducts coproducts

-- The glued interpretation of a polynomial: the carrier interpretation with the matching glued
-- former at every node, the μ case supplying the closed join.
fobj-Gl : ∀ {j} (Q : Poly j) (pQ : PolyPred Q)
          (δ : Fin j → Obj) (δP : ∀ i → Predicate (G .fobj (δ i))) → Gl.Obj
fobj-Gl (const A) pA δ δP = glue A pA
fobj-Gl (var i)   _  δ δP = glue (δ i) (δP i)
fobj-Gl (P' + Q') (pP , pQ) δ δP =
  GlCP._[+]_ (Lf-Gl (fobj-Gl P' pP δ δP)) (Lf-Gl (fobj-Gl Q' pQ δ δP))
fobj-Gl (P' × Q') (pP , pQ) δ δP = Lf-Gl (fobj-Gl P' pP δ δP [×] fobj-Gl Q' pQ δ δP)
fobj-Gl (μ Q')    pQ' δ δP = MuPred.μ-Gl δ δP Q' pQ'
