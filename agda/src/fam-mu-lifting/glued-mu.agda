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
open import prop using (_,_; tt)
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
  module CME = CMonEnriched CM

  ℓpred : Level
  ℓpred = lsuc o₂ ⊔ lsuc m₂ ⊔ lsuc e₂ ⊔ o ⊔ m ⊔ e ⊔ lsuc 0ℓ

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
  Lf-Gl-map (f .mor) (assembleF-natural (f .mor .morph) (f .inv) (f .inv₁) (f .inv₂)) rt
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

-- The inclusion of a fibre absorbs the zero: the zero element of a fibre is the zero element of
-- the family it sits in.
zeroF-elem-in : ∀ {W : Obj} (X : Obj) (x : X .idx .Carrier)
                (u : simple[ PS.𝟙 , X .fam .fm x ] .idx .Carrier) →
                Fam𝒞._≈_ (Fam𝒞._∘_ (elem-in X x) (zeroF {W} u)) (zeroF x)
zeroF-elem-in X x u ._≃_.idxf-eq .PS._≃m_.func-eq _ = X .idx .isEquivalence .refl
zeroF-elem-in X x u ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans (∘-cong (X .fam .refl*) (≈-trans id-left (CME.comp-bilinear-ε₂ _))) id-left

-- A predicate at a const leaf, together with the fact that it holds of the zero element: the
-- fold's root branch reads the context against a zero payload.
record ConstPred (A : Obj) : Set ℓpred where
  field
    cpred : Predicate (G .fobj A)
    czero : Zeroed (glue A cpred)
open ConstPred public

-- A predicate assignment for a polynomial: a predicate on the image of each const leaf.
PolyPred : ∀ {j} → Poly j → Set ℓpred
PolyPred (const A) = ConstPred A
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
      glue simple[ PS.𝟙 , A .fam .fm x ] (pA .cpred [ G .fmor (elem-in A x) ])
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

  -- Every fibre glued object holds of the zero element, given that the leaf predicates do: the
  -- lifted and product formers carry the property, and the leaves reindex it along their own
  -- inclusion.
  module MuZero (δZ : ∀ i → Zeroed (glue (δ i) (δP i))) where

    mutual
      fib-Gl-zero : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
                    (d : ∀ i → DecoAssign (ρ̄ i))
                    (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
                    (t : W ∣ Q ∣ ρ̄) → Zeroed (fib-Gl Q d pQ pd t)
      fib-Gl-zero Q d pQ pd (sup x) =
        fib-shape-Gl-zero Q (deco-ext Q d) pQ (deco-ext-pred Q pQ pd) x

      fib-shape-Gl-zero : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
                          (d : ∀ i → DecoAssign (η̄ i))
                          (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (η̄ i) (d i))
                          (x : ⟦ ∣ Q ∣ ⟧shape η̄) → Zeroed (fib-shape-Gl Q d pQ pd x)
      fib-shape-Gl-zero (const A) d pA pd x u =
        ⊑-trans (pA .czero x)
        (⊑-trans ([]-cong (G .fmor-cong (Fam𝒞.≈-sym (zeroF-elem-in A x u))))
        (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _)))
      fib-shape-Gl-zero (var i)   d pQ pd x = fib-el-Gl-zero _ (d i) (pd i) x
      fib-shape-Gl-zero (P' + Q') d (pP , pQ) pd (inj₁ x) =
        Zeroed-Lf {fib-shape-Gl P' d pP pd x} (fib-shape-Gl-zero P' d pP pd x)
      fib-shape-Gl-zero (P' + Q') d (pP , pQ) pd (inj₂ y) =
        Zeroed-Lf {fib-shape-Gl Q' d pQ pd y} (fib-shape-Gl-zero Q' d pQ pd y)
      fib-shape-Gl-zero (P' × Q') d (pP , pQ) pd (x , y) =
        Zeroed-Lf {fib-shape-Gl P' d pP pd x [×] fib-shape-Gl Q' d pQ pd y}
          (Zeroed-[×] {fib-shape-Gl P' d pP pd x} {fib-shape-Gl Q' d pQ pd y}
            (fib-shape-Gl-zero P' d pP pd x) (fib-shape-Gl-zero Q' d pQ pd y))
      fib-shape-Gl-zero (μ Q')    d pQ' pd t = fib-Gl-zero Q' d pQ' pd t

      fib-el-Gl-zero : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPred r dr)
                       (x : El r) → Zeroed (fib-el-Gl r dr pr x)
      fib-el-Gl-zero (inj₁ p) _ _ x u =
        ⊑-trans (δZ p x)
        (⊑-trans ([]-cong (G .fmor-cong (Fam𝒞.≈-sym (zeroF-elem-in (δ p) x u))))
        (⊑-trans ([]-cong (G .fmor-comp _ _)) ([]-comp⁻¹ _ _)))
      fib-el-Gl-zero (inj₂ s) (mkDeco Q ρd) (pQ , pρ) x = fib-Gl-zero Q ρd pQ pρ x

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

  -- Every index of a fibre carrier is the canonical one: the index setoids are built from
  -- singletons at the leaves and pairs at the nodes.
  mutual
    fib-ix-uniq : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
                  (d : ∀ i → DecoAssign (ρ̄ i))
                  (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
                  (t : W ∣ Q ∣ ρ̄) (ι : fib-Gl Q d pQ pd t .carrier .idx .Carrier) →
                  _≈s_ (fib-Gl Q d pQ pd t .carrier .idx) ι (fib-ix Q d pQ pd t)
    fib-ix-uniq Q d pQ pd (sup x) ι =
      shape-ix-uniq Q (deco-ext Q d) pQ (deco-ext-pred Q pQ pd) x ι

    shape-ix-uniq : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
                    (d : ∀ i → DecoAssign (η̄ i))
                    (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (η̄ i) (d i))
                    (x : ⟦ ∣ Q ∣ ⟧shape η̄)
                    (ι : fib-shape-Gl Q d pQ pd x .carrier .idx .Carrier) →
                    _≈s_ (fib-shape-Gl Q d pQ pd x .carrier .idx) ι (shape-ix Q d pQ pd x)
    shape-ix-uniq (const A) d pA pd x ι = tt
    shape-ix-uniq (var i)   d pQ pd x ι = el-ix-uniq _ (d i) (pd i) x ι
    shape-ix-uniq (P' + Q') d (pP , pQ) pd (inj₁ x) ι = shape-ix-uniq P' d pP pd x ι
    shape-ix-uniq (P' + Q') d (pP , pQ) pd (inj₂ y) ι = shape-ix-uniq Q' d pQ pd y ι
    shape-ix-uniq (P' × Q') d (pP , pQ) pd (x , y) (ι₁ , ι₂) =
      shape-ix-uniq P' d pP pd x ι₁ , shape-ix-uniq Q' d pQ pd y ι₂
    shape-ix-uniq (μ Q')    d pQ' pd t ι = fib-ix-uniq Q' d pQ' pd t ι

    el-ix-uniq : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPred r dr)
                 (x : El r) (ι : fib-el-Gl r dr pr x .carrier .idx .Carrier) →
                 _≈s_ (fib-el-Gl r dr pr x .carrier .idx) ι (el-ix r dr pr x)
    el-ix-uniq (inj₁ p) _ _ x ι = tt
    el-ix-uniq (inj₂ s) (mkDeco Q ρd) (pQ , pρ) x ι = fib-ix-uniq Q ρd pQ pρ x ι

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

  -- Reverse-inclusion naturality, derived from the inverse laws.
  out-fib-natural : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
                    (d : ∀ i → DecoAssign (ρ̄ i))
                    (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
                    (t : W ∣ Q ∣ ρ̄) {ι₁ ι₂ : fib-Gl Q d pQ pd t .carrier .idx .Carrier}
                    (e : _≈s_ (fib-Gl Q d pQ pd t .carrier .idx) ι₁ ι₂) →
                    (fib-Gl Q d pQ pd t .carrier .fam .subst e ∘ out-fib Q d pQ pd t ι₁)
                      ≈ out-fib Q d pQ pd t ι₂
  out-fib-natural Q d pQ pd t {ι₁} {ι₂} e =
    ≈-sym (≈-trans (≈-sym id-right)
          (≈-trans (∘-cong ≈-refl (≈-sym (in-out-fib Q d pQ pd t ι₁)))
          (≈-trans (∘-cong ≈-refl (∘-cong (≈-sym (in-fib-natural Q d pQ pd t e)) ≈-refl))
          (≈-trans (∘-cong ≈-refl (assoc _ _ _))
          (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong (out-in-fib Q d pQ pd t ι₂) ≈-refl) id-left))))))

  out-shape-natural : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
                      (d : ∀ i → DecoAssign (η̄ i))
                      (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (η̄ i) (d i))
                      (x : ⟦ ∣ Q ∣ ⟧shape η̄)
                      {ι₁ ι₂ : fib-shape-Gl Q d pQ pd x .carrier .idx .Carrier}
                      (e : _≈s_ (fib-shape-Gl Q d pQ pd x .carrier .idx) ι₁ ι₂) →
                      (fib-shape-Gl Q d pQ pd x .carrier .fam .subst e
                        ∘ out-shape Q d pQ pd x ι₁)
                        ≈ out-shape Q d pQ pd x ι₂
  out-shape-natural Q d pQ pd x {ι₁} {ι₂} e =
    ≈-sym (≈-trans (≈-sym id-right)
          (≈-trans (∘-cong ≈-refl (≈-sym (in-out-shape Q d pQ pd x ι₁)))
          (≈-trans (∘-cong ≈-refl (∘-cong (≈-sym (in-shape-natural Q d pQ pd x e)) ≈-refl))
          (≈-trans (∘-cong ≈-refl (assoc _ _ _))
          (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong (out-in-shape Q d pQ pd x ι₂) ≈-refl) id-left))))))

  out-el-natural : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPred r dr)
                   (x : El r) {ι₁ ι₂ : fib-el-Gl r dr pr x .carrier .idx .Carrier}
                   (e : _≈s_ (fib-el-Gl r dr pr x .carrier .idx) ι₁ ι₂) →
                   (fib-el-Gl r dr pr x .carrier .fam .subst e ∘ out-el r dr pr x ι₁)
                     ≈ out-el r dr pr x ι₂
  out-el-natural r dr pr x {ι₁} {ι₂} e =
    ≈-sym (≈-trans (≈-sym id-right)
          (≈-trans (∘-cong ≈-refl (≈-sym (in-out-el r dr pr x ι₁)))
          (≈-trans (∘-cong ≈-refl (∘-cong (≈-sym (in-el-natural r dr pr x e)) ≈-refl))
          (≈-trans (∘-cong ≈-refl (assoc _ _ _))
          (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong (out-in-el r dr pr x ι₂) ≈-refl) id-left))))))

  -- The singleton at a fibre includes into the fibre's glued carrier at the canonical index.
  fib-out : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
            (d : ∀ i → DecoAssign (ρ̄ i))
            (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
            (t : W ∣ Q ∣ ρ̄) →
            Mor simple[ PS.𝟙 , fib Q d t ] (fib-Gl Q d pQ pd t .carrier)
  fib-out Q d pQ pd t .idxf .PS._⇒_.func _ = fib-ix Q d pQ pd t
  fib-out Q d pQ pd t .idxf .PS._⇒_.func-resp-≈ _ =
    fib-Gl Q d pQ pd t .carrier .idx .isEquivalence .refl
  fib-out Q d pQ pd t .famf ._⇒f_.transf _ = out-fib Q d pQ pd t (fib-ix Q d pQ pd t)
  fib-out Q d pQ pd t .famf ._⇒f_.natural _ =
    ≈-trans id-right (≈-sym (out-fib-natural Q d pQ pd t _))

  shape-out : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
              (d : ∀ i → DecoAssign (η̄ i))
              (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (η̄ i) (d i))
              (x : ⟦ ∣ Q ∣ ⟧shape η̄) →
              Mor simple[ PS.𝟙 , fib-shape Q d x ] (fib-shape-Gl Q d pQ pd x .carrier)
  shape-out Q d pQ pd x .idxf .PS._⇒_.func _ = shape-ix Q d pQ pd x
  shape-out Q d pQ pd x .idxf .PS._⇒_.func-resp-≈ _ =
    fib-shape-Gl Q d pQ pd x .carrier .idx .isEquivalence .refl
  shape-out Q d pQ pd x .famf ._⇒f_.transf _ = out-shape Q d pQ pd x (shape-ix Q d pQ pd x)
  shape-out Q d pQ pd x .famf ._⇒f_.natural _ =
    ≈-trans id-right (≈-sym (out-shape-natural Q d pQ pd x _))

  el-out : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPred r dr) (x : El r) →
           Mor simple[ PS.𝟙 , fib-el r dr x ] (fib-el-Gl r dr pr x .carrier)
  el-out r dr pr x .idxf .PS._⇒_.func _ = el-ix r dr pr x
  el-out r dr pr x .idxf .PS._⇒_.func-resp-≈ _ =
    fib-el-Gl r dr pr x .carrier .idx .isEquivalence .refl
  el-out r dr pr x .famf ._⇒f_.transf _ = out-el r dr pr x (el-ix r dr pr x)
  el-out r dr pr x .famf ._⇒f_.natural _ =
    ≈-trans id-right (≈-sym (out-el-natural r dr pr x _))

  -- The singleton inclusions agree across the levels of the recursion.
  fib-shape-out : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
                  (d : ∀ i → DecoAssign (ρ̄ i))
                  (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
                  (x : ⟦ ∣ Q ∣ ⟧shape (extend ρ̄ (inj₂ (mkSort ∣ Q ∣ ρ̄)))) →
                  Fam𝒞._≈_ (fib-out Q d pQ pd (sup x))
                           (shape-out Q (deco-ext Q d) pQ (deco-ext-pred Q pQ pd) x)
  fib-shape-out Q d pQ pd x ._≃_.idxf-eq .PS._≃m_.func-eq _ =
    fib-Gl Q d pQ pd (sup x) .carrier .idx .isEquivalence .refl
  fib-shape-out Q d pQ pd x ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
    ≈-trans (∘-cong (fib-Gl Q d pQ pd (sup x) .carrier .fam .refl*) ≈-refl) id-left

  shape-el-out : ∀ {j} {η̄ : Fin j → Fin n ⊎ Sort n} (i : Fin j)
                 (d : ∀ v → DecoAssign (η̄ v))
                 (pQ : PolyPred (var i)) (pd : ∀ v → DecoAssignPred (η̄ v) (d v))
                 (x : El (η̄ i)) →
                 Fam𝒞._≈_ (shape-out (var i) d pQ pd x) (el-out (η̄ i) (d i) (pd i) x)
  shape-el-out i d pQ pd x ._≃_.idxf-eq .PS._≃m_.func-eq _ =
    fib-el-Gl _ (d i) (pd i) x .carrier .idx .isEquivalence .refl
  shape-el-out i d pQ pd x ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
    ≈-trans (∘-cong (fib-el-Gl _ (d i) (pd i) x .carrier .fam .refl*) ≈-refl) id-left

  shape-fib-out : ∀ {j} (Q' : Poly (suc j)) {η̄ : Fin j → Fin n ⊎ Sort n}
                  (d : ∀ v → DecoAssign (η̄ v))
                  (pQ' : PolyPred (μ Q')) (pd : ∀ v → DecoAssignPred (η̄ v) (d v))
                  (t : W ∣ Q' ∣ η̄) →
                  Fam𝒞._≈_ (shape-out (μ Q') d pQ' pd t) (fib-out Q' d pQ' pd t)
  shape-fib-out Q' d pQ' pd t ._≃_.idxf-eq .PS._≃m_.func-eq _ =
    fib-Gl Q' d pQ' pd t .carrier .idx .isEquivalence .refl
  shape-fib-out Q' d pQ' pd t ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
    ≈-trans (∘-cong (fib-Gl Q' d pQ' pd t .carrier .fam .refl*) ≈-refl) id-left

  el-fib-out : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
               (ρd : ∀ i → DecoAssign (ρ̄ i))
               (pQ : PolyPred Q) (pρ : ∀ i → DecoAssignPred (ρ̄ i) (ρd i))
               (x : El (inj₂ (mkSort ∣ Q ∣ ρ̄))) →
               Fam𝒞._≈_ (el-out (inj₂ (mkSort ∣ Q ∣ ρ̄)) (mkDeco Q ρd) (pQ , pρ) x)
                        (fib-out Q ρd pQ pρ x)
  el-fib-out Q ρd pQ pρ x ._≃_.idxf-eq .PS._≃m_.func-eq _ =
    fib-Gl Q ρd pQ pρ x .carrier .idx .isEquivalence .refl
  el-fib-out Q ρd pQ pρ x ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
    ≈-trans (∘-cong (fib-Gl Q ρd pQ pρ x .carrier .fam .refl*) ≈-refl) id-left

  -- The inclusion of a fibre's carrier at its tree, over the constant index map.
  tree-in : (P' : Poly (suc n)) (pP : PolyPred P') (t : W ∣ P' ∣ (λ i → inj₁ i)) →
            Mor (fib-Gl P' (λ i → lift tt) pP (λ i → lift tt) t .carrier) (μObj P' δ)
  tree-in P' pP t .idxf .PS._⇒_.func _ = t
  tree-in P' pP t .idxf .PS._⇒_.func-resp-≈ _ = W-≈-refl t
  tree-in P' pP t .famf ._⇒f_.transf ι = in-fib P' (λ i → lift tt) pP (λ i → lift tt) t ι
  tree-in P' pP t .famf ._⇒f_.natural {ι₁} {ι₂} e =
    ≈-trans (in-fib-natural P' (λ i → lift tt) pP (λ i → lift tt) t e)
            (≈-sym (≈-trans (∘-cong (fib-refl* P' (λ i → lift tt) t) ≈-refl) id-left))

  -- The reverse of tree-in over the singleton at a tree, landing at the canonical index.
  tree-out : (P' : Poly (suc n)) (pP : PolyPred P') (t : W ∣ P' ∣ (λ i → inj₁ i)) →
             Mor simple[ PS.𝟙 , μObj P' δ .fam .fm t ]
                 (fib-Gl P' (λ i → lift tt) pP (λ i → lift tt) t .carrier)
  tree-out P' pP t .idxf .PS._⇒_.func _ = fib-ix P' (λ i → lift tt) pP (λ i → lift tt) t
  tree-out P' pP t .idxf .PS._⇒_.func-resp-≈ _ =
    fib-Gl P' (λ i → lift tt) pP (λ i → lift tt) t .carrier .idx .isEquivalence .refl
  tree-out P' pP t .famf ._⇒f_.transf _ =
    out-fib P' (λ i → lift tt) pP (λ i → lift tt) t
            (fib-ix P' (λ i → lift tt) pP (λ i → lift tt) t)
  tree-out P' pP t .famf ._⇒f_.natural _ =
    ≈-trans id-right (≈-sym (out-fib-natural P' (λ i → lift tt) pP (λ i → lift tt) t _))

  -- tree-in after tree-out is the singleton inclusion at the tree.
  tree-in-out : (P' : Poly (suc n)) (pP : PolyPred P') (t : W ∣ P' ∣ (λ i → inj₁ i)) →
                Fam𝒞._≈_ (Fam𝒞._∘_ (tree-in P' pP t) (tree-out P' pP t))
                         (elem-in (μObj P' δ) t)
  tree-in-out P' pP t ._≃_.idxf-eq .PS._≃m_.func-eq _ = W-≈-refl t
  tree-in-out P' pP t ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
    ≈-trans (∘-cong (fib-refl* P' (λ i → lift tt) t)
                    (≈-trans id-left
                             (in-out-fib P' (λ i → lift tt) pP (λ i → lift tt) t _)))
            id-left

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
      subst-shape (const A) d pA pd p = elem-iso A (pA .cpred) p
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

    -- The transports intertwine the carrier inclusions with the fibres' own transport.
    mutual
      subst-fib-in : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
                     (d : ∀ i → DecoAssign (ρ̄ i))
                     (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (ρ̄ i) (d i))
                     {t t' : W ∣ Q ∣ ρ̄} (p : W-≈ t t')
                     (ι : fib-Gl Q d pQ pd t .carrier .idx .Carrier) →
                     (in-fib Q d pQ pd t'
                        (subst-fib Q d pQ pd {t} {t'} p .mor .morph .idxf .PS._⇒_.func ι)
                       ∘ subst-fib Q d pQ pd {t} {t'} p .mor .morph .famf ._⇒f_.transf ι)
                       ≈ (fib-subst Q d {t} {t'} p ∘ in-fib Q d pQ pd t ι)
      subst-fib-in Q d pQ pd {sup x} {sup y} p ι =
        subst-shape-in Q (deco-ext Q d) pQ (deco-ext-pred Q pQ pd) {x} {y} p ι

      subst-shape-in : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
                       (d : ∀ i → DecoAssign (η̄ i))
                       (pQ : PolyPred Q) (pd : ∀ i → DecoAssignPred (η̄ i) (d i))
                       {x y : ⟦ ∣ Q ∣ ⟧shape η̄} (p : shape≈ ∣ Q ∣ η̄ x y)
                       (ι : fib-shape-Gl Q d pQ pd x .carrier .idx .Carrier) →
                       (in-shape Q d pQ pd y
                          (subst-shape Q d pQ pd {x} {y} p .mor .morph .idxf .PS._⇒_.func ι)
                         ∘ subst-shape Q d pQ pd {x} {y} p .mor .morph .famf ._⇒f_.transf ι)
                         ≈ (fib-shape-subst Q d {x} {y} p ∘ in-shape Q d pQ pd x ι)
      subst-shape-in (const A) d pA pd p ι = ≈-trans id-left (≈-sym id-right)
      subst-shape-in (var i)   d pQ pd p ι = subst-el-in _ (d i) (pd i) p ι
      subst-shape-in (P' + Q') d (pP , pQ) pd {inj₁ x} {inj₁ y} p ι =
        ≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (subst-shape-in P' d pP pd {x} {y} p ι)) (Lmap-comp _ _))
      subst-shape-in (P' + Q') d (pP , pQ) pd {inj₂ x} {inj₂ y} p ι =
        ≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (subst-shape-in Q' d pQ pd {x} {y} p ι)) (Lmap-comp _ _))
      subst-shape-in (P' × Q') d (pP , pQ) pd {x₁ , x₂} {y₁ , y₂} (p₁ , p₂) (ι₁ , ι₂) =
        ≈-trans (∘-cong ≈-refl (Lmap-cong (pair-cong id-left id-left)))
        (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong
                   (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                    (≈-trans (prod-m-cong (subst-shape-in P' d pP pd {x₁} {y₁} p₁ ι₁)
                                          (subst-shape-in Q' d pQ pd {x₂} {y₂} p₂ ι₂))
                             (prod-m-comp _ _ _ _))))
                 (Lmap-comp _ _)))
      subst-shape-in (μ Q')    d pQ' pd {x} {y} p ι = subst-fib-in Q' d pQ' pd {x} {y} p ι

      subst-el-in : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPred r dr)
                    {x y : El r} (e : elEq r x y)
                    (ι : fib-el-Gl r dr pr x .carrier .idx .Carrier) →
                    (in-el r dr pr y
                       (subst-el r dr pr {x} {y} e .mor .morph .idxf .PS._⇒_.func ι)
                      ∘ subst-el r dr pr {x} {y} e .mor .morph .famf ._⇒f_.transf ι)
                      ≈ (fib-el-subst r dr {x} {y} e ∘ in-el r dr pr x ι)
      subst-el-in (inj₁ p) _ _ e ι = ≈-trans id-left (≈-sym id-right)
      subst-el-in (inj₂ s) (mkDeco Q ρd) (pQ , pρ) {x} {y} e ι =
        subst-fib-in Q ρd pQ pρ {x} {y} e ι

private module GlCP = Gl.coproducts coproducts

-- The glued interpretation of a polynomial: the carrier interpretation with the matching glued
-- former's predicate at every node, the μ case supplying the closed join. The carrier is the
-- interpretation itself on the nose, so statements over an arbitrary polynomial elaborate; the
-- predicate is projected from the glued former applied to the recursive interpretations.
mutual
  fobj-Gl : ∀ {j} (Q : Poly j) (pQ : PolyPred Q)
            (δ : Fin j → Obj) (δP : ∀ i → Predicate (G .fobj (δ i))) → Gl.Obj
  fobj-Gl Q pQ δ δP .carrier = R.fobj μObj Q δ
  fobj-Gl Q pQ δ δP .pred = fobj-pred Q pQ δ δP

  fobj-pred : ∀ {j} (Q : Poly j) (pQ : PolyPred Q)
              (δ : Fin j → Obj) (δP : ∀ i → Predicate (G .fobj (δ i))) →
              Predicate (G .fobj (R.fobj μObj Q δ))
  fobj-pred (const A) pA δ δP = pA .cpred
  fobj-pred (var i)   _  δ δP = δP i
  fobj-pred (P' + Q') (pP , pQ) δ δP =
    GlCP._[+]_ (Lf-Gl (fobj-Gl P' pP δ δP)) (Lf-Gl (fobj-Gl Q' pQ δ δP)) .pred
  fobj-pred (P' × Q') (pP , pQ) δ δP =
    Lf-Gl (fobj-Gl P' pP δ δP [×] fobj-Gl Q' pQ δ δP) .pred
  fobj-pred (μ Q')    pQ' δ δP = MuPred.μ-Gl δ δP Q' pQ' .pred
