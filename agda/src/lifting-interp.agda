{-# OPTIONS --prop --postfix-projections --safe #-}

-- The rooted interpretation of polynomials in a category with a lifting: sums are coproducts of
-- lifted summands and products are lifted products, so an algebra is by freeness a constant with a
-- linear part at every former. The initial-algebra laws are stated against applying the algebra
-- once with candidates at the variables, the continuation splitting at each root; the strong
-- action of the μ-operations appears only at μ-variables, where re-reading a candidate's root is
-- the intended meaning, never at a rebuilt cell.
open import Level using (_⊔_)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import categories
  using (Category; HasTerminal; HasProducts; HasStrongCoproducts; HasCoproducts;
         strong-coproducts→coproducts)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import commutative-monoid using (CommutativeMonoid)
open import lifting using (Lifting)
open import polynomial-functor using (Poly; extend)
import lifting-fold

module lifting-interp
  {o m e} {𝒞 : Category o m e}
  (𝒞T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
  {𝟙c : Category.obj 𝒞} (Lft : Lifting CM 𝟙c)
  (𝒞SC : HasStrongCoproducts 𝒞 (biproducts→products CM BP))
  where

open Category 𝒞
open Lifting Lft using (L)
open HasProducts (biproducts→products CM BP)
open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SC) using (coprod; in₁; in₂)
open HasStrongCoproducts 𝒞SC using () renaming (copair to scopair)
open Poly

module LF = lifting-fold CM BP Lft

-- The rooted interpretation: a root above each sum branch and each product.
fobjL : (μ-obj : ∀ {k} → Poly 𝒞 (suc k) → (Fin k → obj) → obj) →
        ∀ {n} → Poly 𝒞 n → (Fin n → obj) → obj
fobjL μ-obj (const A) δ = A
fobjL μ-obj (var i)   δ = δ i
fobjL μ-obj (P + Q)   δ = coprod (L (fobjL μ-obj P δ)) (L (fobjL μ-obj Q δ))
fobjL μ-obj (P × Q)   δ = L (prod (fobjL μ-obj P δ) (fobjL μ-obj Q δ))
fobjL μ-obj (μ P)     δ = μ-obj P δ

-- The μ-operations against the rooted interpretation.
record HasMu : Set (o ⊔ m ⊔ e) where
  field
    μ-obj : ∀ {n} → Poly 𝒞 (suc n) → (Fin n → obj) → obj
    inMap : ∀ {n} (P : Poly 𝒞 (suc n)) (δ : Fin n → obj) →
            fobjL μ-obj P (extend δ (μ-obj P δ)) ⇒ μ-obj P δ
    ⦅_⦆   : ∀ {n Γ A} {P : Poly 𝒞 (suc n)} {δ : Fin n → obj} →
            (prod Γ (fobjL μ-obj P (extend δ A)) ⇒ A) → prod Γ (μ-obj P δ) ⇒ A

  strong-extend-mor : ∀ {n Γ} {δ δ' : Fin n → obj} {X Y} →
                      (∀ i → prod Γ (δ i) ⇒ δ' i) → (prod Γ X ⇒ Y) →
                      ∀ i → prod Γ (extend δ X i) ⇒ extend δ' Y i
  strong-extend-mor fs xy Fin.zero    = xy
  strong-extend-mor fs xy (Fin.suc i) = fs i

  -- Applying a continuation over the reindexed interpretation once, with candidates at the
  -- variables: the continuation splits at each root and never rebuilds a cell.
  mutual
    applyCo : ∀ {n Γ} (P : Poly 𝒞 n) {δ δ' : Fin n → obj} →
              (∀ i → prod Γ (δ i) ⇒ δ' i) →
              ∀ {Z} → (prod Γ (fobjL μ-obj P δ') ⇒ Z) → prod Γ (fobjL μ-obj P δ) ⇒ Z
    applyCo (const A) gs k = k
    applyCo (var i)   gs k = k ∘ LF.pairb LF.π₁ (gs i)
    applyCo {Γ = Γ} (P + Q) {δ} {δ'} gs {Z} k =
      scopair
        (LF.rootStep Γ Z (fobjL μ-obj P δ') (fobjL μ-obj P δ) (k ∘ prod-m (id Γ) in₁)
          (applyCo P gs (LF.rootCont Γ Z (fobjL μ-obj P δ') (k ∘ prod-m (id Γ) in₁))))
        (LF.rootStep Γ Z (fobjL μ-obj Q δ') (fobjL μ-obj Q δ) (k ∘ prod-m (id Γ) in₂)
          (applyCo Q gs (LF.rootCont Γ Z (fobjL μ-obj Q δ') (k ∘ prod-m (id Γ) in₂))))
    applyCo {Γ = Γ} (P × Q) {δ} {δ'} gs {Z} k =
      LF.rootStep Γ Z (prod (fobjL μ-obj P δ') (fobjL μ-obj Q δ'))
                      (prod (fobjL μ-obj P δ) (fobjL μ-obj Q δ)) k
        (LF.prodStep Γ Z (fobjL μ-obj P δ) (fobjL μ-obj Q δ)
          (applyCo P gs
            (LF.prodCont₁ Γ Z (fobjL μ-obj P δ') (fobjL μ-obj Q δ')
              (LF.rootCont Γ Z (prod (fobjL μ-obj P δ') (fobjL μ-obj Q δ')) k)))
          (applyCo Q gs
            (LF.prodCont₂ Γ Z (fobjL μ-obj P δ') (fobjL μ-obj Q δ')
              (LF.rootCont Γ Z (prod (fobjL μ-obj P δ') (fobjL μ-obj Q δ')) k))))
    applyCo (μ P') gs k = k ∘ LF.pairb LF.π₁ (strong-μ-fmor P' gs)

    strong-μ-fmor : ∀ {n Γ} (P : Poly 𝒞 (suc n)) {δ δ' : Fin n → obj} →
                    (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (μ-obj P δ) ⇒ μ-obj P δ'
    strong-μ-fmor P {δ} {δ'} gs =
      ⦅ applyCo P (strong-extend-mor gs p₂) (inMap P δ' ∘ p₂) ⦆

-- The fused initial-algebra laws: β computes the fold on one unfolding, η makes any solution the
-- fold. Both are one equation, the per-former content living in applyCo.
record HasMuLaws (Mu : HasMu) : Set (o ⊔ m ⊔ e) where
  open HasMu Mu
  field
    ⦅⦆-β : ∀ {n Γ A} {P : Poly 𝒞 (suc n)} {δ : Fin n → obj}
           (alg : prod Γ (fobjL μ-obj P (extend δ A)) ⇒ A) →
           (⦅ alg ⦆ ∘ LF.pairb LF.π₁ (inMap P δ ∘ p₂))
             ≈ applyCo P (strong-extend-mor (λ i → p₂) ⦅ alg ⦆) alg
    ⦅⦆-η : ∀ {n Γ A} {P : Poly 𝒞 (suc n)} {δ : Fin n → obj}
           (alg : prod Γ (fobjL μ-obj P (extend δ A)) ⇒ A) (h : prod Γ (μ-obj P δ) ⇒ A) →
           (h ∘ LF.pairb LF.π₁ (inMap P δ ∘ p₂))
             ≈ applyCo P (strong-extend-mor (λ i → p₂) h) alg →
           h ≈ ⦅ alg ⦆
