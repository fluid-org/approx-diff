{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_; suc; lift)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_; tt; substP)
open import Data.Unit using (tt) renaming (⊤ to 𝟙S)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; cong₂)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts; strong-coproducts→coproducts)
open import functor using (Functor; Id; StrongPointedFunctor; StrongPointedFunctor-Id)
open import prop-setoid as PS
  using (IsEquivalence; Setoid; module ≈-Reasoning)
open import indexed-family using (Fam; _⇒f_; changeCat)
import fam
import fam-functor

-- Rename Setoid._≈_ to _≈s_ to avoid clashing with Category._≈_ (morphism eq).
open Setoid using (Carrier; isEquivalence) renaming (_≈_ to _≈s_)

module polynomial-functor where

------------------------------------------------------------------------------
-- Syntactic polynomial expressions in one variable, with constants drawn from obj 𝒞; they form a category.
data Poly {o m e} (𝒞 : Category o m e) : Set o where
  one  : Poly 𝒞                              -- constant terminal
  const : Category.obj 𝒞 → Poly 𝒞            -- constant object
  var  : Poly 𝒞                              -- recursive slot
  _+_  : Poly 𝒞 → Poly 𝒞 → Poly 𝒞          -- sum
  _×_  : Poly 𝒞 → Poly 𝒞 → Poly 𝒞          -- product

_∘ₚ_ : ∀ {o m e} {𝒞 : Category o m e} → Poly 𝒞 → Poly 𝒞 → Poly 𝒞
one        ∘ₚ Q = one
const A    ∘ₚ Q = const A
var        ∘ₚ Q = Q
(P₁ + P₂)  ∘ₚ Q = (P₁ ∘ₚ Q) + (P₂ ∘ₚ Q)
(P₁ × P₂)  ∘ₚ Q = (P₁ ∘ₚ Q) × (P₂ ∘ₚ Q)

-- Map a polynomial through a functor by applying F to const slots.
Poly-map : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} →
           Functor 𝒞 𝒟 → Poly 𝒞 → Poly 𝒟
Poly-map F one         = one
Poly-map F (const A)   = const (Functor.fobj F A)
Poly-map F var         = var
Poly-map F (P₁ + P₂)   = Poly-map F P₁ + Poly-map F P₂
Poly-map F (P₁ × P₂)   = Poly-map F P₁ × Poly-map F P₂

-- Two polynomials are iso if they have the same tree shape, with isomorphic objects at const slots.
-- Restrictive (requires matching tree shapes); sufficient for our use (P₁ and P₂ both derived from the
-- same first-order-poly P-fo, differing only at const slots).
data Poly-iso {o m e} {𝒞 : Category o m e} : Poly 𝒞 → Poly 𝒞 → Set (o ⊔ m ⊔ e) where
  one   : Poly-iso one one
  const : ∀ {A B} → Category.Iso 𝒞 A B → Poly-iso (const A) (const B)
  var   : Poly-iso var var
  _+_   : ∀ {P₁ P₂ Q₁ Q₂} → Poly-iso P₁ Q₁ → Poly-iso P₂ Q₂ → Poly-iso (P₁ + P₂) (Q₁ + Q₂)
  _×_   : ∀ {P₁ P₂ Q₁ Q₂} → Poly-iso P₁ Q₁ → Poly-iso P₂ Q₂ → Poly-iso (P₁ × P₂) (Q₁ × Q₂)

{- ------------------------------------------------------------------------------
-- μPoly: polynomial signature extended with a Mon constructor (fibre-only decoration relative to whatever
-- LiftMon the interpretation supplies). Currently only consumed by language-interpretation-approx (broken);
-- commented out until that's revived.
data μPoly {o m e} (𝒞 : Category o m e) : Set o where
  one    : μPoly 𝒞
  const  : Category.obj 𝒞 → μPoly 𝒞
  var    : μPoly 𝒞
  _+_    : μPoly 𝒞 → μPoly 𝒞 → μPoly 𝒞
  _×_    : μPoly 𝒞 → μPoly 𝒞 → μPoly 𝒞
  Mon    : μPoly 𝒞 → μPoly 𝒞
-}

module Sem {o m e} {𝒞 : Category o m e}
           (T : HasTerminal 𝒞) (P : HasProducts 𝒞) (SCP : HasStrongCoproducts 𝒞 P) where
  open Category 𝒞
  open HasTerminal T renaming (witness to terminal)
  open HasProducts P
  CP : HasCoproducts 𝒞
  CP = strong-coproducts→coproducts T SCP
  open HasCoproducts CP
  open HasStrongCoproducts SCP using ()
    renaming (copair to scopair; copair-cong to scopair-cong;
              copair-in₁ to scopair-in₁; copair-in₂ to scopair-in₂;
              copair-ext to scopair-ext)

  poly-obj : Poly 𝒞 → obj → obj
  poly-obj one         _ = terminal
  poly-obj (const A)   _ = A
  poly-obj var         x = x
  poly-obj (P + Q)     x = coprod (poly-obj P x) (poly-obj Q x)
  poly-obj (P × Q)     x = prod   (poly-obj P x) (poly-obj Q x)

  -- Open-form functorial action of Poly Q: lifts (prod Γ X ⇒ Y) to
  -- (prod Γ (poly-obj Q X) ⇒ poly-obj Q Y). Uses strong copair for sums.
  poly-fmor : ∀ Q {Γ X Y} → (prod Γ X ⇒ Y) → (prod Γ (poly-obj Q X) ⇒ poly-obj Q Y)
  poly-fmor one         _ = to-terminal
  poly-fmor (const A)   _ = p₂
  poly-fmor var         h = h
  poly-fmor (Q₁ + Q₂)   h = scopair (in₁ ∘ poly-fmor Q₁ h) (in₂ ∘ poly-fmor Q₂ h)
  poly-fmor (Q₁ × Q₂)   h = pair (poly-fmor Q₁ h ∘ pair p₁ (p₁ ∘ p₂)) (poly-fmor Q₂ h ∘ pair p₁ (p₂ ∘ p₂))

  -- Identity preservation: poly-fmor applied to the (parameterised) identity is the (parameterised) identity.
  poly-fmor-id : ∀ Q {Γ X} → poly-fmor Q {Γ} {X} {X} p₂ ≈ p₂
  poly-fmor-id one         = to-terminal-unique _ _
  poly-fmor-id (const A)   = ≈-refl
  poly-fmor-id var         = ≈-refl
  poly-fmor-id (Q₁ + Q₂)   =
    ≈-trans (scopair-cong (∘-cong ≈-refl (poly-fmor-id Q₁)) (∘-cong ≈-refl (poly-fmor-id Q₂)))
            (≈-trans (scopair-cong (≈-sym (pair-p₂ _ _)) (≈-sym (pair-p₂ _ _)))
                     (scopair-ext p₂))
  poly-fmor-id (Q₁ × Q₂)   =
    ≈-trans (pair-cong (∘-cong (poly-fmor-id Q₁) ≈-refl) (∘-cong (poly-fmor-id Q₂) ≈-refl))
            (≈-trans (pair-cong (pair-p₂ _ _) (pair-p₂ _ _))
                     (pair-ext p₂))

  -- Polynomial composition agrees with composition of functor actions.
  poly-obj-comp : ∀ P Q X → poly-obj (P ∘ₚ Q) X ≡ poly-obj P (poly-obj Q X)
  poly-obj-comp one        Q X = ≡.refl
  poly-obj-comp (const A)  Q X = ≡.refl
  poly-obj-comp var        Q X = ≡.refl
  poly-obj-comp (P₁ + P₂)  Q X = cong₂ coprod (poly-obj-comp P₁ Q X) (poly-obj-comp P₂ Q X)
  poly-obj-comp (P₁ × P₂)  Q X = cong₂ prod   (poly-obj-comp P₁ Q X) (poly-obj-comp P₂ Q X)

  record HasMu : Set (o ⊔ m ⊔ e) where
    field
      μ    : Poly 𝒞 → obj
      inF  : ∀ Q → poly-obj Q (μ Q) ⇒ μ Q
      -- Open (parametric) form: algebra in extended context. Avoids the
      -- closure conversion that would otherwise need exponentials.
      ⦅_⦆  : ∀ {Γ Q y} → (prod Γ (poly-obj Q y) ⇒ y) → prod Γ (μ Q) ⇒ y

      -- β: ⦅alg⦆ on a rolled value (in extended context) equals alg applied
      -- to the recursively folded structure (γ threaded through).
      ⦅⦆-β : ∀ {Γ Q y} (alg : prod Γ (poly-obj Q y) ⇒ y) →
             (⦅ alg ⦆ ∘ pair p₁ (inF Q ∘ p₂)) ≈ (alg ∘ pair p₁ (poly-fmor Q ⦅ alg ⦆))
      -- η: ⦅alg⦆ is the unique morphism satisfying β.
      ⦅⦆-η : ∀ {Γ Q y} (alg : prod Γ (poly-obj Q y) ⇒ y) (h : prod Γ (μ Q) ⇒ y) →
             (h ∘ pair p₁ (inF Q ∘ p₂)) ≈ (alg ∘ pair p₁ (poly-fmor Q h)) →
             h ≈ ⦅ alg ⦆

  -- μ respects Poly-iso: structurally iso polynomials (matching shape, const slots iso) yield iso μ-types.
  -- Built directly from catamorphism universal property (β, η).
  module μ-respects-Poly-iso (Mu : HasMu) where
    open HasMu Mu
    open Iso

    iso-mor : ∀ {P P'} → Poly-iso P P' → ∀ {Γ X} → prod Γ (poly-obj P X) ⇒ poly-obj P' X
    iso-mor one             = to-terminal
    iso-mor (const A≅B)     = A≅B .fwd ∘ p₂
    iso-mor var             = p₂
    iso-mor (P₁≅Q₁ + P₂≅Q₂)     = scopair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂)
    iso-mor (P₁≅Q₁ × P₂≅Q₂)     = pair (iso-mor P₁≅Q₁ ∘ pair p₁ (p₁ ∘ p₂))
                                        (iso-mor P₂≅Q₂ ∘ pair p₁ (p₂ ∘ p₂))

    iso-sym : ∀ {P P'} → Poly-iso P P' → Poly-iso P' P
    iso-sym one         = one
    iso-sym (const A≅B) = const (Category.Iso-sym 𝒞 A≅B)
    iso-sym var         = var
    iso-sym (P₁≅Q₁ + P₂≅Q₂) = iso-sym P₁≅Q₁ + iso-sym P₂≅Q₂
    iso-sym (P₁≅Q₁ × P₂≅Q₂) = iso-sym P₁≅Q₁ × iso-sym P₂≅Q₂

    iso-sym-involutive : ∀ {P P'} (P≅P' : Poly-iso P P') → iso-sym (iso-sym P≅P') ≡ P≅P'
    iso-sym-involutive one         = ≡.refl
    iso-sym-involutive (const A≅B) = ≡.refl
    iso-sym-involutive var         = ≡.refl
    iso-sym-involutive (P₁≅Q₁ + P₂≅Q₂) = ≡.cong₂ _+_ (iso-sym-involutive P₁≅Q₁) (iso-sym-involutive P₂≅Q₂)
    iso-sym-involutive (P₁≅Q₁ × P₂≅Q₂) = ≡.cong₂ _×_ (iso-sym-involutive P₁≅Q₁) (iso-sym-involutive P₂≅Q₂)

    -- Round-trip law: forward then backward at the polynomial-functor level is (parameterised) identity.
    iso-mor-fwd∘bwd : ∀ {P P'} (P≅P' : Poly-iso P P') {Γ X} →
      iso-mor P≅P' {Γ} {X} ∘ pair p₁ (iso-mor (iso-sym P≅P')) ≈ p₂
    iso-mor-fwd∘bwd one = to-terminal-unique _ _
    iso-mor-fwd∘bwd (const A≅B) =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (pair-p₂ _ _))
      (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (A≅B .fwd∘bwd≈id) ≈-refl) id-left)))
    iso-mor-fwd∘bwd var = pair-p₂ _ _
    iso-mor-fwd∘bwd (_+_ {P₁} {P₂} {Q₁} {Q₂} P₁≅Q₁ P₂≅Q₂) {Γ} {X} =
      ≈-trans (≈-sym (scopair-ext _)) (≈-trans (scopair-cong in₁-branch in₂-branch) (scopair-ext _))
      where
        in₁-branch : (scopair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘
                      pair p₁ (scopair (in₁ ∘ iso-mor (iso-sym P₁≅Q₁)) (in₂ ∘ iso-mor (iso-sym P₂≅Q₂)))) ∘ pair p₁ (in₁ ∘ p₂)
                   ≈ p₂ ∘ pair p₁ (in₁ ∘ p₂)
        in₁-branch =
          begin
            (scopair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘
             pair p₁ (scopair (in₁ ∘ iso-mor (iso-sym P₁≅Q₁)) (in₂ ∘ iso-mor (iso-sym P₂≅Q₂)))) ∘ pair p₁ (in₁ ∘ p₂)
          ≈⟨ assoc _ _ _ ⟩
            scopair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘
            (pair p₁ (scopair (in₁ ∘ iso-mor (iso-sym P₁≅Q₁)) (in₂ ∘ iso-mor (iso-sym P₂≅Q₂))) ∘ pair p₁ (in₁ ∘ p₂))
          ≈⟨ ∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) (scopair-in₁ _ _))) ⟩
            scopair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘ pair p₁ (in₁ ∘ iso-mor (iso-sym P₁≅Q₁))
          ≈˘⟨ ∘-cong ≈-refl
                (≈-trans (pair-natural _ _ _)
                (pair-cong (pair-p₁ _ _) (≈-trans (assoc _ _ _) (∘-cong ≈-refl (pair-p₂ _ _))))) ⟩
            scopair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘ (pair p₁ (in₁ ∘ p₂) ∘ pair p₁ (iso-mor (iso-sym P₁≅Q₁)))
          ≈˘⟨ assoc _ _ _ ⟩
            (scopair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘ pair p₁ (in₁ ∘ p₂)) ∘ pair p₁ (iso-mor (iso-sym P₁≅Q₁))
          ≈⟨ ∘-cong (scopair-in₁ _ _) ≈-refl ⟩
            (in₁ ∘ iso-mor P₁≅Q₁) ∘ pair p₁ (iso-mor (iso-sym P₁≅Q₁))
          ≈⟨ assoc _ _ _ ⟩
            in₁ ∘ (iso-mor P₁≅Q₁ ∘ pair p₁ (iso-mor (iso-sym P₁≅Q₁)))
          ≈⟨ ∘-cong ≈-refl (iso-mor-fwd∘bwd P₁≅Q₁) ⟩
            in₁ ∘ p₂
          ≈˘⟨ pair-p₂ _ _ ⟩
            p₂ ∘ pair p₁ (in₁ ∘ p₂)
          ∎ where open ≈-Reasoning isEquiv

        in₂-branch : (scopair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘
                      pair p₁ (scopair (in₁ ∘ iso-mor (iso-sym P₁≅Q₁)) (in₂ ∘ iso-mor (iso-sym P₂≅Q₂)))) ∘ pair p₁ (in₂ ∘ p₂)
                   ≈ p₂ ∘ pair p₁ (in₂ ∘ p₂)
        in₂-branch = begin
            (scopair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘
             pair p₁ (scopair (in₁ ∘ iso-mor (iso-sym P₁≅Q₁)) (in₂ ∘ iso-mor (iso-sym P₂≅Q₂)))) ∘ pair p₁ (in₂ ∘ p₂)
          ≈⟨ assoc _ _ _ ⟩
            scopair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘
            (pair p₁ (scopair (in₁ ∘ iso-mor (iso-sym P₁≅Q₁)) (in₂ ∘ iso-mor (iso-sym P₂≅Q₂))) ∘ pair p₁ (in₂ ∘ p₂))
          ≈⟨ ∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) (scopair-in₂ _ _))) ⟩
            scopair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘ pair p₁ (in₂ ∘ iso-mor (iso-sym P₂≅Q₂))
          ≈˘⟨ ∘-cong ≈-refl
                (≈-trans (pair-natural _ _ _)
                (pair-cong (pair-p₁ _ _) (≈-trans (assoc _ _ _) (∘-cong ≈-refl (pair-p₂ _ _))))) ⟩
            scopair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘ (pair p₁ (in₂ ∘ p₂) ∘ pair p₁ (iso-mor (iso-sym P₂≅Q₂)))
          ≈˘⟨ assoc _ _ _ ⟩
            (scopair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘ pair p₁ (in₂ ∘ p₂)) ∘ pair p₁ (iso-mor (iso-sym P₂≅Q₂))
          ≈⟨ ∘-cong (scopair-in₂ _ _) ≈-refl ⟩
            (in₂ ∘ iso-mor P₂≅Q₂) ∘ pair p₁ (iso-mor (iso-sym P₂≅Q₂))
          ≈⟨ assoc _ _ _ ⟩
            in₂ ∘ (iso-mor P₂≅Q₂ ∘ pair p₁ (iso-mor (iso-sym P₂≅Q₂)))
          ≈⟨ ∘-cong ≈-refl (iso-mor-fwd∘bwd P₂≅Q₂) ⟩
            in₂ ∘ p₂
          ≈˘⟨ pair-p₂ _ _ ⟩
            p₂ ∘ pair p₁ (in₂ ∘ p₂)
          ∎ where open ≈-Reasoning isEquiv

    iso-mor-fwd∘bwd (_×_ {P₁} {P₂} {Q₁} {Q₂} P₁≅Q₁ P₂≅Q₂) {Γ} {X} =
      ≈-trans (≈-sym (pair-ext _)) (≈-trans (pair-cong p₁-branch p₂-branch) (pair-ext _))
      where
        pair-fwd = pair (iso-mor P₁≅Q₁ ∘ pair p₁ (p₁ ∘ p₂)) (iso-mor P₂≅Q₂ ∘ pair p₁ (p₂ ∘ p₂))
        pair-bwd = pair (iso-mor (iso-sym P₁≅Q₁) ∘ pair p₁ (p₁ ∘ p₂))
                        (iso-mor (iso-sym P₂≅Q₂) ∘ pair p₁ (p₂ ∘ p₂))

        p₁-branch : p₁ ∘ (pair-fwd ∘ pair p₁ pair-bwd) ≈ p₁ ∘ p₂
        p₁-branch = begin
            p₁ ∘ (pair-fwd ∘ pair p₁ pair-bwd)
          ≈˘⟨ assoc _ _ _ ⟩
            (p₁ ∘ pair-fwd) ∘ pair p₁ pair-bwd
          ≈⟨ ∘-cong (pair-p₁ _ _) ≈-refl ⟩
            (iso-mor P₁≅Q₁ ∘ pair p₁ (p₁ ∘ p₂)) ∘ pair p₁ pair-bwd
          ≈⟨ assoc _ _ _ ⟩
            iso-mor P₁≅Q₁ ∘ (pair p₁ (p₁ ∘ p₂) ∘ pair p₁ pair-bwd)
          ≈⟨ ∘-cong ≈-refl (≈-trans (pair-natural _ _ _)
                           (≈-trans (pair-cong (pair-p₁ _ _) (≈-trans (assoc _ _ _) (∘-cong ≈-refl (pair-p₂ _ _))))
                                    (pair-cong ≈-refl (pair-p₁ _ _)))) ⟩
            iso-mor P₁≅Q₁ ∘ pair p₁ (iso-mor (iso-sym P₁≅Q₁) ∘ pair p₁ (p₁ ∘ p₂))
          ≈˘⟨ ∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) ≈-refl)) ⟩
            iso-mor P₁≅Q₁ ∘ (pair p₁ (iso-mor (iso-sym P₁≅Q₁)) ∘ pair p₁ (p₁ ∘ p₂))
          ≈˘⟨ assoc _ _ _ ⟩
            (iso-mor P₁≅Q₁ ∘ pair p₁ (iso-mor (iso-sym P₁≅Q₁))) ∘ pair p₁ (p₁ ∘ p₂)
          ≈⟨ ∘-cong (iso-mor-fwd∘bwd P₁≅Q₁) ≈-refl ⟩
            p₂ ∘ pair p₁ (p₁ ∘ p₂)
          ≈⟨ pair-p₂ _ _ ⟩
            p₁ ∘ p₂
          ∎ where open ≈-Reasoning isEquiv

        p₂-branch : p₂ ∘ (pair-fwd ∘ pair p₁ pair-bwd) ≈ p₂ ∘ p₂
        p₂-branch = begin
            p₂ ∘ (pair-fwd ∘ pair p₁ pair-bwd)
          ≈˘⟨ assoc _ _ _ ⟩
            (p₂ ∘ pair-fwd) ∘ pair p₁ pair-bwd
          ≈⟨ ∘-cong (pair-p₂ _ _) ≈-refl ⟩
            (iso-mor P₂≅Q₂ ∘ pair p₁ (p₂ ∘ p₂)) ∘ pair p₁ pair-bwd
          ≈⟨ assoc _ _ _ ⟩
            iso-mor P₂≅Q₂ ∘ (pair p₁ (p₂ ∘ p₂) ∘ pair p₁ pair-bwd)
          ≈⟨ ∘-cong ≈-refl (≈-trans (pair-natural _ _ _)
                           (≈-trans (pair-cong (pair-p₁ _ _) (≈-trans (assoc _ _ _) (∘-cong ≈-refl (pair-p₂ _ _))))
                                    (pair-cong ≈-refl (pair-p₂ _ _)))) ⟩
            iso-mor P₂≅Q₂ ∘ pair p₁ (iso-mor (iso-sym P₂≅Q₂) ∘ pair p₁ (p₂ ∘ p₂))
          ≈˘⟨ ∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) ≈-refl)) ⟩
            iso-mor P₂≅Q₂ ∘ (pair p₁ (iso-mor (iso-sym P₂≅Q₂)) ∘ pair p₁ (p₂ ∘ p₂))
          ≈˘⟨ assoc _ _ _ ⟩
            (iso-mor P₂≅Q₂ ∘ pair p₁ (iso-mor (iso-sym P₂≅Q₂))) ∘ pair p₁ (p₂ ∘ p₂)
          ≈⟨ ∘-cong (iso-mor-fwd∘bwd P₂≅Q₂) ≈-refl ⟩
            p₂ ∘ pair p₁ (p₂ ∘ p₂)
          ≈⟨ pair-p₂ _ _ ⟩
            p₂ ∘ p₂
          ∎ where open ≈-Reasoning isEquiv

    iso-fwd∘bwd-β : ∀ {P P'} (P≅P' : Poly-iso P P') {Γ} →
      (((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P')))) ∘ p₂ {x = Γ}) ∘ pair p₁ (inF P' ∘ p₂)
      ≈ (inF P' ∘ p₂) ∘ pair p₁ (poly-fmor P'
          (((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
              ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P')))) ∘ p₂ {x = Γ}))
    iso-fwd∘bwd-β {P} {P'} P≅P' {Γ} =
      begin
        (((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
            ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P')))) ∘ p₂ {x = Γ}) ∘ pair p₁ (inF P' ∘ p₂)
      ≈⟨ assoc _ _ _ ⟩
        ((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P')))) ∘ (p₂ ∘ pair p₁ (inF P' ∘ p₂))
      ≈⟨ ∘-cong ≈-refl (pair-p₂ _ _) ⟩
        ((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P')))) ∘ (inF P' ∘ p₂)
      ≈˘⟨ assoc _ _ _ ⟩
        (((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
            ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P')))) ∘ inF P') ∘ p₂
      ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
        ((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ ((⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P'))) ∘ inF P')) ∘ p₂
      ≈⟨ ∘-cong (∘-cong ≈-refl (assoc _ _ _)) ≈-refl ⟩
        ((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ (pair to-terminal (id (μ P')) ∘ inF P'))) ∘ p₂
      ≈⟨ ∘-cong (∘-cong ≈-refl (∘-cong ≈-refl
           (≈-trans (pair-natural _ _ _) (pair-cong (to-terminal-unique _ _) id-left)))) ≈-refl ⟩
        ((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (inF P'))) ∘ p₂
      ≈˘⟨ ∘-cong (∘-cong ≈-refl (∘-cong ≈-refl
            (≈-trans (pair-natural _ _ _)
                     (pair-cong (pair-p₁ _ _)
                                (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) id-right)))))) ≈-refl ⟩
        ((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ (pair p₁ (inF P' ∘ p₂) ∘ pair to-terminal (id _))))
          ∘ p₂
      ≈˘⟨ ∘-cong (∘-cong ≈-refl (assoc _ _ _)) ≈-refl ⟩
        ((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ ((⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair p₁ (inF P' ∘ p₂)) ∘ pair to-terminal (id _)))
          ∘ p₂
      ≈⟨ ∘-cong (∘-cong ≈-refl (∘-cong (⦅⦆-β _) ≈-refl)) ≈-refl ⟩
        ((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ (((inF P ∘ iso-mor (iso-sym P≅P')) ∘ pair p₁ (poly-fmor P' ⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆))
              ∘ pair to-terminal (id _)))
          ∘ p₂
      ≈⟨ ∘-cong (∘-cong ≈-refl (≈-trans (∘-cong (assoc _ _ _) ≈-refl) (assoc _ _ _))) ≈-refl ⟩
        ((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ (inF P ∘ ((iso-mor (iso-sym P≅P') ∘ pair p₁ (poly-fmor P' ⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆))
                        ∘ pair to-terminal (id _))))
          ∘ p₂
      ≈⟨ {!!} ⟩
        (inF P' ∘ p₂) ∘ pair p₁ (poly-fmor P'
          (((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
              ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P')))) ∘ p₂ {x = Γ}))
      ∎ where open ≈-Reasoning isEquiv

    iso-fwd∘bwd : ∀ {P P'} (P≅P' : Poly-iso P P') →
      (⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
        ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P'))) ≈ id (μ P')
    iso-fwd∘bwd {P} {P'} P≅P' = begin
        (⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P')))
      ≈⟨ ≈-sym id-right ⟩
        ((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P')))) ∘ id (μ P')
      ≈⟨ ∘-cong ≈-refl (≈-sym (pair-p₂ to-terminal (id (μ P')))) ⟩
        ((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P'))))
          ∘ (p₂ ∘ pair to-terminal (id (μ P')))
      ≈⟨ ≈-sym (assoc _ _ _) ⟩
        (((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
            ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P'))))
          ∘ p₂)
          ∘ pair to-terminal (id (μ P'))
      ≈⟨ ∘-cong (⦅⦆-η (inF P' ∘ p₂)
                        (((⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
                            ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P'))))
                          ∘ p₂) (iso-fwd∘bwd-β P≅P')) ≈-refl ⟩
        ⦅ inF P' ∘ p₂ ⦆ ∘ pair to-terminal (id (μ P'))
      ≈⟨ ∘-cong (≈-sym (⦅⦆-η (inF P' ∘ p₂) p₂
                          (≈-trans (pair-p₂ _ _) (≈-sym
                          (≈-trans (assoc _ _ _)
                          (∘-cong ≈-refl (≈-trans (pair-p₂ _ _) (poly-fmor-id P')))))))) ≈-refl ⟩
        p₂ ∘ pair to-terminal (id (μ P'))
      ≈⟨ pair-p₂ _ _ ⟩
        id (μ P')
      ∎ where open ≈-Reasoning isEquiv

    iso : ∀ {P P'} → Poly-iso P P' → Category.Iso 𝒞 (μ P) (μ P')
    iso P≅P' .fwd        = ⦅ inF _ ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id _)
    iso P≅P' .bwd        = ⦅ inF _ ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id _)
    iso P≅P' .fwd∘bwd≈id = iso-fwd∘bwd P≅P'
    iso {P} {P'} P≅P' .bwd∘fwd≈id =
      substP (λ q → (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id _))
                       ∘ (⦅ inF P' ∘ iso-mor q ⦆ ∘ pair to-terminal (id _)) ≈ id (μ P))
             (iso-sym-involutive P≅P')
             (iso-fwd∘bwd (iso-sym P≅P'))

  {- μPoly-Sem: interpretation of μPoly with Mon (commented out alongside μPoly).
  module μPoly-Sem (F : Functor 𝒞 𝒞) where
    μPoly-obj : μPoly 𝒞 → obj → obj
    μPoly-obj one        _ = terminal
    μPoly-obj (const A)  _ = A
    μPoly-obj var        x = x
    μPoly-obj (P + Q)    x = coprod (μPoly-obj P x) (μPoly-obj Q x)
    μPoly-obj (P × Q)    x = prod   (μPoly-obj P x) (μPoly-obj Q x)
    μPoly-obj (Mon P)    x = Functor.fobj F (μPoly-obj P x)

    record HasMu-μPoly : Set (o ⊔ m ⊔ e) where
      field
        μ    : μPoly 𝒞 → obj
        inμ  : ∀ Q → μPoly-obj Q (μ Q) ⇒ μ Q
        ⦅_⦆  : ∀ {Γ Q y} → (prod Γ (μPoly-obj Q y) ⇒ y) → prod Γ (μ Q) ⇒ y
      -- FIXME: equations (β/η for inμ / ⦅_⦆). Mon case needs strength on F.
  -}

------------------------------------------------------------------------------
-- A functor F : 𝒞 → 𝒟 preserves μ if, for each polynomial signature P, the
-- F-image of 𝒞's μ P is isomorphic to 𝒟's μ of the F-mapped polynomial.
module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂}
         (T₁ : HasTerminal 𝒞) (P₁ : HasProducts 𝒞) (SCP₁ : HasStrongCoproducts 𝒞 P₁)
         (T₂ : HasTerminal 𝒟) (P₂ : HasProducts 𝒟) (SCP₂ : HasStrongCoproducts 𝒟 P₂)
         where
  private
    module S₁ = Sem T₁ P₁ SCP₁
    module S₂ = Sem T₂ P₂ SCP₂

  Preserves-μ : S₁.HasMu → S₂.HasMu → Functor 𝒞 𝒟 → Set _
  Preserves-μ 𝒞Mu 𝒟Mu F =
    ∀ (P : Poly 𝒞) →
      Category.Iso 𝒟 (Functor.fobj F (S₁.HasMu.μ 𝒞Mu P))
                      (S₂.HasMu.μ 𝒟Mu (Poly-map F P))

------------------------------------------------------------------------------
-- Like Poly above but constant slots hold a setoid rather than a category object. Used to build the W-type
-- carrier of HasMu in the Fam category. W P is the set of P-shaped trees; W-≈ is tree equality by structural
-- recursion on the polynomial.
module _ {o e} where
  open import Data.Sum using (_⊎_)
  open import Data.Product using () renaming (_×_ to _×T_)
  open import prop using (_∧_; ⊤; ⊥)

  data IdxPoly : Set (suc (o ⊔ e)) where
    one  : IdxPoly
    param : Setoid o e → IdxPoly
    var  : IdxPoly
    _+_  : IdxPoly → IdxPoly → IdxPoly
    _×_  : IdxPoly → IdxPoly → IdxPoly

  -- Well-founded tree carrier (Martin-Löf W-types).
  mutual
    data W (P : IdxPoly) : Set o where
      inF : WIdx P P → W P

    WIdx : IdxPoly → IdxPoly → Set o
    WIdx P one         = Level.Lift o 𝟙S
    WIdx P (param A)   = Carrier A
    WIdx P var         = W P
    WIdx P (Q₁ + Q₂)   = WIdx P Q₁ ⊎ WIdx P Q₂
    WIdx P (Q₁ × Q₂)   = WIdx P Q₁ ×T WIdx P Q₂

  mutual
    W-≈ : (P : IdxPoly) → W P → W P → Prop e
    W-≈ P (inF i₁) (inF i₂) = WIdx-≈ P P i₁ i₂

    WIdx-≈ : (P Q : IdxPoly) → WIdx P Q → WIdx P Q → Prop e
    WIdx-≈ P one         _          _          = ⊤
    WIdx-≈ P (param A)   x          y          = _≈s_ A x y
    WIdx-≈ P var         w₁         w₂         = W-≈ P w₁ w₂
    WIdx-≈ P (Q₁ + Q₂)   (inj₁ x₁)  (inj₁ x₂)  = WIdx-≈ P Q₁ x₁ x₂
    WIdx-≈ P (Q₁ + Q₂)   (inj₁ _)   (inj₂ _)   = ⊥
    WIdx-≈ P (Q₁ + Q₂)   (inj₂ _)   (inj₁ _)   = ⊥
    WIdx-≈ P (Q₁ + Q₂)   (inj₂ y₁)  (inj₂ y₂)  = WIdx-≈ P Q₂ y₁ y₂
    WIdx-≈ P (Q₁ × Q₂)   (x₁ , y₁)  (x₂ , y₂)  = WIdx-≈ P Q₁ x₁ x₂ ∧ WIdx-≈ P Q₂ y₁ y₂

  mutual
    W-≈-refl : ∀ P {w} → W-≈ P w w
    W-≈-refl P {inF i} = WIdx-≈-refl P P {i}

    WIdx-≈-refl : ∀ P Q {x} → WIdx-≈ P Q x x
    WIdx-≈-refl P one                   = tt
    WIdx-≈-refl P (param A) {x}         = IsEquivalence.refl (Setoid.isEquivalence A) {x}
    WIdx-≈-refl P var       {w}         = W-≈-refl P {w}
    WIdx-≈-refl P (Q₁ + Q₂) {inj₁ x}    = WIdx-≈-refl P Q₁ {x}
    WIdx-≈-refl P (Q₁ + Q₂) {inj₂ y}    = WIdx-≈-refl P Q₂ {y}
    WIdx-≈-refl P (Q₁ × Q₂) {x , y}     = WIdx-≈-refl P Q₁ {x} , WIdx-≈-refl P Q₂ {y}

  mutual
    W-≈-sym : ∀ P {w₁ w₂} → W-≈ P w₁ w₂ → W-≈ P w₂ w₁
    W-≈-sym P {inF i₁} {inF i₂} i₁≈i₂ = WIdx-≈-sym P P {i₁} {i₂} i₁≈i₂

    WIdx-≈-sym : ∀ P Q {x y} → WIdx-≈ P Q x y → WIdx-≈ P Q y x
    WIdx-≈-sym P one         _  = tt
    WIdx-≈-sym P (param A) {x} {y} x≈y = IsEquivalence.sym (Setoid.isEquivalence A) x≈y
    WIdx-≈-sym P var       {w₁} {w₂} w₁≈w₂ = W-≈-sym P {w₁} {w₂} w₁≈w₂
    WIdx-≈-sym P (Q₁ + Q₂) {inj₁ x₁} {inj₁ x₂} x₁≈x₂ = WIdx-≈-sym P Q₁ x₁≈x₂
    WIdx-≈-sym P (Q₁ + Q₂) {inj₂ y₁} {inj₂ y₂} y₁≈y₂ = WIdx-≈-sym P Q₂ y₁≈y₂
    WIdx-≈-sym P (Q₁ × Q₂) {x₁ , y₁} {x₂ , y₂} (x₁≈x₂ , y₁≈y₂) = WIdx-≈-sym P Q₁ x₁≈x₂ , WIdx-≈-sym P Q₂ y₁≈y₂

  mutual
    W-≈-trans : ∀ P {w₁ w₂ w₃} → W-≈ P w₁ w₂ → W-≈ P w₂ w₃ → W-≈ P w₁ w₃
    W-≈-trans P {inF _} {inF _} {inF _} w₁≈w₂ w₂≈w₃ = WIdx-≈-trans P P w₁≈w₂ w₂≈w₃

    WIdx-≈-trans : ∀ P Q {x y z} →
                      WIdx-≈ P Q x y → WIdx-≈ P Q y z → WIdx-≈ P Q x z
    WIdx-≈-trans P one        _  _  = tt
    WIdx-≈-trans P (param A) {x} {y} {z} x≈y y≈z = IsEquivalence.trans (Setoid.isEquivalence A) x≈y y≈z
    WIdx-≈-trans P var       {x} {y} {z} x≈y y≈z = W-≈-trans P {x} {y} {z} x≈y y≈z
    WIdx-≈-trans P (Q₁ + Q₂) {inj₁ _} {inj₁ _} {inj₁ _} x≈y y≈z = WIdx-≈-trans P Q₁ x≈y y≈z
    WIdx-≈-trans P (Q₁ + Q₂) {inj₂ _} {inj₂ _} {inj₂ _} x≈y y≈z = WIdx-≈-trans P Q₂ x≈y y≈z
    WIdx-≈-trans P (Q₁ × Q₂) {_ , _} {_ , _} {_ , _} (x₁≈y₁ , x₂≈y₂) (y₁≈z₁ , y₂≈z₂) =
      WIdx-≈-trans P Q₁ x₁≈y₁ y₁≈z₁ , WIdx-≈-trans P Q₂ x₂≈y₂ y₂≈z₂

  WSetoid : IdxPoly → Setoid o e
  WSetoid P .Carrier                            = W P
  WSetoid P ._≈s_                                = W-≈ P
  WSetoid P .Setoid.isEquivalence .IsEquivalence.refl  {w} = W-≈-refl P {w}
  WSetoid P .Setoid.isEquivalence .IsEquivalence.sym   {w₁} {w₂} = W-≈-sym P {w₁} {w₂}
  WSetoid P .Setoid.isEquivalence .IsEquivalence.trans {w₁} {w₂} {w₃} = W-≈-trans P {w₁} {w₂} {w₃}

{- ------------------------------------------------------------------------------
-- Mu: subset of Lucatelli Nunes & Vákár's μν Poly_L (Def 53). Commented out alongside μPoly.
module Mu {o m e os es} {𝒟 : Category o m e}
          (T : HasTerminal 𝒟) (PP : HasProducts 𝒟) (L : StrongPointedFunctor PP) where
  open fam.CategoryOfFamilies os es 𝒟
  open Obj
  open products PP
  open StrongPointedFunctor L using (F)   -- L's underlying Functor 𝒟 𝒟

  idx-of : μPoly cat → IdxPoly {os} {es}
  idx-of one          = IdxPoly.one
  idx-of (const A)    = IdxPoly.param (A .idx)
  idx-of var          = IdxPoly.var
  idx-of (F + G)      = idx-of F IdxPoly.+ idx-of G
  idx-of (F × G)      = idx-of F IdxPoly.× idx-of G
  idx-of (Mon F)      = idx-of F

  open HasTerminal (terminal T) using () renaming (witness to Fam-terminal)
  open HasCoproducts coproducts using () renaming (coprod to Fam-coprod)

  Mon-Fam : Obj → Obj
  Mon-Fam Y .idx = Y .idx
  Mon-Fam Y .fam = changeCat F (Y .fam)

  μPoly-obj : μPoly cat → Obj → Obj
  μPoly-obj one        X = Fam-terminal
  μPoly-obj (const A)  X = A
  μPoly-obj var        X = X
  μPoly-obj (F + G)    X = Fam-coprod (μPoly-obj F X) (μPoly-obj G X)
  μPoly-obj (F × G)    X = (μPoly-obj F X) ⊗ (μPoly-obj G X)
  μPoly-obj (Mon F)    X = Mon-Fam (μPoly-obj F X)
-}

------------------------------------------------------------------------------
-- HasMu instance for the Fam construction.
module WFam {o m e} (os es : _) {𝒞 : Category o m e} (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where
  open Category 𝒞
  open IsEquivalence
  open HasTerminal
  open HasProducts P
  open fam.CategoryOfFamilies os es 𝒞
  open Obj
  open Mor
  open Fam
  private module Fam𝒞 = Category cat
  open products P  -- Fam-level products
  private module Fam𝒞-P = HasProducts products
  open _⇒f_
  open Sem (terminal T) products strongCoproducts

  ----------------------------------------------------------------------
  -- Generic μ-types in Fam(𝒞), for polynomials Q : Poly cat. The idx side is WSetoid of Q (projecting param
  -- slots from Fam-objs to their idx setoids); the fibre side is built recursively over Q using 𝒞's products.
  module W-types (Q : Poly cat) where
    open Obj
    open Mor
    open Fam

    idx-of : Poly cat → IdxPoly
    idx-of Poly.one        = one
    idx-of (Poly.const A)  = param (A .idx)
    idx-of Poly.var        = var
    idx-of (P Poly.+ Q)  = idx-of P + idx-of Q
    idx-of (P Poly.× Q)  = idx-of P × idx-of Q

    poly : IdxPoly
    poly = idx-of Q

    WFam-fm : (P : Poly cat) → WIdx poly (idx-of P) → obj
    WFam-fm Poly.one          _        = T .witness
    WFam-fm (Poly.const A)    a        = A .fam .fm a
    WFam-fm Poly.var          (inF i)  = WFam-fm Q i
    WFam-fm (P Poly.+ Q)      (inj₁ x) = WFam-fm P x
    WFam-fm (P Poly.+ Q)      (inj₂ y) = WFam-fm Q y
    WFam-fm (P Poly.× Q)      (x , y)  = prod (WFam-fm P x) (WFam-fm Q y)

    WFam-subst : (P : Poly cat) → ∀ {x y} → WIdx-≈ poly (idx-of P) x y → WFam-fm P x ⇒ WFam-fm P y
    WFam-subst Poly.one _ = id _
    WFam-subst (Poly.const A) {x} {y} x≈y = A .fam .subst x≈y
    WFam-subst Poly.var {inF i₁} {inF i₂} i₁≈i₂ = WFam-subst Q i₁≈i₂
    WFam-subst (P Poly.+ Q) {inj₁ _} {inj₁ _} x≈y = WFam-subst P x≈y
    WFam-subst (P Poly.+ Q) {inj₂ _} {inj₂ _} x≈y = WFam-subst Q x≈y
    WFam-subst (P Poly.+ Q) {inj₁ _} {inj₂ _} ()
    WFam-subst (P Poly.+ Q) {inj₂ _} {inj₁ _} ()
    WFam-subst (P Poly.× Q) {_ , _} {_ , _} (x₁≈y₁ , x₂≈y₂) =
      prod-m (WFam-subst P x₁≈y₁) (WFam-subst Q x₂≈y₂)

    WFam-refl* : (P : Poly cat) → ∀ {x} →
                    WFam-subst P (WIdx-≈-refl poly (idx-of P) {x}) ≈ id _
    WFam-refl* Poly.one         = isEquiv .refl
    WFam-refl* (Poly.const A) {x} = A .fam .refl*
    WFam-refl* Poly.var {inF i} = WFam-refl* Q {i}
    WFam-refl* (P Poly.+ Q) {inj₁ x} = WFam-refl* P {x}
    WFam-refl* (P Poly.+ Q) {inj₂ y} = WFam-refl* Q {y}
    WFam-refl* (P Poly.× Q) {x , y}  =
      begin
        prod-m (WFam-subst P _) (WFam-subst Q _)
      ≈⟨ prod-m-cong (WFam-refl* P {x}) (WFam-refl* Q {y}) ⟩
        prod-m (id _) (id _)
      ≈⟨ prod-m-id ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv

    WFam-trans* : (P : Poly cat) → ∀ {x y z}
                     (y≈z : WIdx-≈ poly (idx-of P) y z) (x≈y : WIdx-≈ poly (idx-of P) x y) →
                     WFam-subst P (WIdx-≈-trans poly (idx-of P) x≈y y≈z) ≈
                     (WFam-subst P y≈z ∘ WFam-subst P x≈y)
    WFam-trans* Poly.one _ _ = isEquiv .sym id-left
    WFam-trans* (Poly.const A) y≈z x≈y = A .fam .trans* y≈z x≈y
    WFam-trans* Poly.var {inF _} {inF _} {inF _} y≈z x≈y =
      WFam-trans* Q y≈z x≈y
    WFam-trans* (P Poly.+ Q) {inj₁ _} {inj₁ _} {inj₁ _} y≈z x≈y = WFam-trans* P y≈z x≈y
    WFam-trans* (P Poly.+ Q) {inj₂ _} {inj₂ _} {inj₂ _} y≈z x≈y = WFam-trans* Q y≈z x≈y
    WFam-trans* (P Poly.× Q) {_ , _} {_ , _} {_ , _} (y₁≈z₁ , y₂≈z₂) (x₁≈y₁ , x₂≈y₂) =
      begin
        prod-m (WFam-subst P _) (WFam-subst Q _)
      ≈⟨ prod-m-cong (WFam-trans* P y₁≈z₁ x₁≈y₁) (WFam-trans* Q y₂≈z₂ x₂≈y₂) ⟩
        prod-m (WFam-subst P y₁≈z₁ ∘ WFam-subst P x₁≈y₁) (WFam-subst Q y₂≈z₂ ∘ WFam-subst Q x₂≈y₂)
      ≈⟨ pair-functorial _ _ _ _ ⟩
        prod-m (WFam-subst P y₁≈z₁) (WFam-subst Q y₂≈z₂) ∘ prod-m (WFam-subst P x₁≈y₁) (WFam-subst Q x₂≈y₂)
      ∎ where open ≈-Reasoning isEquiv

    WFam : Fam (WSetoid poly) 𝒞
    WFam .fm (inF i)                            = WFam-fm Q i
    WFam .subst {inF _} {inF _} i₁≈i₂           = WFam-subst Q i₁≈i₂
    WFam .refl* {inF _}                         = WFam-refl* Q
    WFam .trans* {inF _} {inF _} {inF _} y≈z x≈y = WFam-trans* Q y≈z x≈y

    WObj : Obj
    WObj .idx = WSetoid poly
    WObj .fam = WFam

    embed-idx : (P : Poly cat) → poly-obj P WObj .idx .Carrier → WIdx poly (idx-of P)
    embed-idx Poly.one         (lift tt)  = lift tt
    embed-idx (Poly.const A)   a          = a
    embed-idx Poly.var         w          = w
    embed-idx (P Poly.+ Q)     (inj₁ x)   = inj₁ (embed-idx P x)
    embed-idx (P Poly.+ Q)     (inj₂ y)   = inj₂ (embed-idx Q y)
    embed-idx (P Poly.× Q)     (x , y)    = (embed-idx P x , embed-idx Q y)

    unembed-idx : (P : Poly cat) → WIdx poly (idx-of P) → poly-obj P WObj .idx .Carrier
    unembed-idx Poly.one         (lift tt)  = lift tt
    unembed-idx (Poly.const A)   a          = a
    unembed-idx Poly.var         w          = w
    unembed-idx (P Poly.+ Q)     (inj₁ x)   = inj₁ (unembed-idx P x)
    unembed-idx (P Poly.+ Q)     (inj₂ y)   = inj₂ (unembed-idx Q y)
    unembed-idx (P Poly.× Q)     (x , y)    = (unembed-idx P x , unembed-idx Q y)

    embed-≈ : (P : Poly cat) → ∀ {x y} →
              poly-obj P WObj .idx ._≈s_ x y → WIdx-≈ poly (idx-of P) (embed-idx P x) (embed-idx P y)
    embed-≈ Poly.one         _    = tt
    embed-≈ (Poly.const A)   x≈y  = x≈y
    embed-≈ Poly.var         x≈y  = x≈y
    embed-≈ (P Poly.+ Q) {inj₁ _} {inj₁ _} x≈y         = embed-≈ P x≈y
    embed-≈ (P Poly.+ Q) {inj₂ _} {inj₂ _} x≈y         = embed-≈ Q x≈y
    embed-≈ (P Poly.× Q) {_ , _} {_ , _} (x₁≈y₁ , x₂≈y₂) = (embed-≈ P x₁≈y₁ , embed-≈ Q x₂≈y₂)

    unembed-≈ : (P : Poly cat) → ∀ {x y} →
                WIdx-≈ poly (idx-of P) x y → poly-obj P WObj .idx ._≈s_ (unembed-idx P x) (unembed-idx P y)
    unembed-≈ Poly.one         _    = tt
    unembed-≈ (Poly.const A)   x≈y  = x≈y
    unembed-≈ Poly.var         x≈y  = x≈y
    unembed-≈ (P Poly.+ Q) {inj₁ _} {inj₁ _} x≈y         = unembed-≈ P x≈y
    unembed-≈ (P Poly.+ Q) {inj₂ _} {inj₂ _} x≈y         = unembed-≈ Q x≈y
    unembed-≈ (P Poly.× Q) {_ , _} {_ , _} (x₁≈y₁ , x₂≈y₂) = (unembed-≈ P x₁≈y₁ , unembed-≈ Q x₂≈y₂)

    embed-unembed-id : (P : Poly cat) (i : WIdx poly (idx-of P)) →
                       WIdx-≈ poly (idx-of P) (embed-idx P (unembed-idx P i)) i
    embed-unembed-id Poly.one       (lift tt) = tt
    embed-unembed-id (Poly.const A) a         = A .idx .isEquivalence .refl
    embed-unembed-id Poly.var       w         = W-≈-refl poly {w}
    embed-unembed-id (P Poly.+ Q)   (inj₁ x)  = embed-unembed-id P x
    embed-unembed-id (P Poly.+ Q)   (inj₂ y)  = embed-unembed-id Q y
    embed-unembed-id (P Poly.× Q)   (x , y)   = (embed-unembed-id P x , embed-unembed-id Q y)

    unembed-embed-id : (P : Poly cat) (j : poly-obj P WObj .idx .Carrier) →
                       poly-obj P WObj .idx ._≈s_ (unembed-idx P (embed-idx P j)) j
    unembed-embed-id Poly.one       (lift tt) = tt
    unembed-embed-id (Poly.const A) a         = A .idx .isEquivalence .refl
    unembed-embed-id Poly.var       (inF _)   = poly-obj Poly.var WObj .idx .isEquivalence .refl
    unembed-embed-id (P Poly.+ Q)   (inj₁ x)  = unembed-embed-id P x
    unembed-embed-id (P Poly.+ Q)   (inj₂ y)  = unembed-embed-id Q y
    unembed-embed-id (P Poly.× Q)   (x , y)   = (unembed-embed-id P x , unembed-embed-id Q y)

    embed-fam : (P : Poly cat) (i : poly-obj P WObj .idx .Carrier) →
                poly-obj P WObj .fam .fm i ⇒ WFam-fm P (embed-idx P i)
    embed-fam Poly.one         (lift tt)  = id _
    embed-fam (Poly.const A)   a          = id _
    embed-fam Poly.var         (inF _)    = id _
    embed-fam (P Poly.+ Q)     (inj₁ x)   = embed-fam P x
    embed-fam (P Poly.+ Q)     (inj₂ y)   = embed-fam Q y
    embed-fam (P Poly.× Q)     (x , y)    = prod-m (embed-fam P x) (embed-fam Q y)

    embed-fam-natural : (P : Poly cat) → ∀ {x₁ x₂} (x₁≈x₂ : poly-obj P WObj .idx ._≈s_ x₁ x₂) →
                        (embed-fam P x₂ ∘ poly-obj P WObj .fam .subst x₁≈x₂) ≈
                        (WFam-subst P (embed-≈ P x₁≈x₂) ∘ embed-fam P x₁)
    embed-fam-natural Poly.one _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural (Poly.const A) _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural Poly.var {inF _} {inF _} _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural (P Poly.+ Q) {inj₁ _} {inj₁ _} x₁≈x₂ = embed-fam-natural P x₁≈x₂
    embed-fam-natural (P Poly.+ Q) {inj₂ _} {inj₂ _} x₁≈x₂ = embed-fam-natural Q x₁≈x₂
    embed-fam-natural (P Poly.× Q) {x₁ , y₁} {x₂ , y₂} (x₁≈x₂ , y₁≈y₂) =
      begin
        prod-m (embed-fam P x₂) (embed-fam Q y₂) ∘ prod-m _ _
      ≈⟨ ≈-sym (pair-functorial _ _ _ _) ⟩
        prod-m (embed-fam P x₂ ∘ _) (embed-fam Q y₂ ∘ _)
      ≈⟨ prod-m-cong (embed-fam-natural P x₁≈x₂) (embed-fam-natural Q y₁≈y₂) ⟩
        prod-m (WFam-subst P (embed-≈ P x₁≈x₂) ∘ embed-fam P x₁) (WFam-subst Q (embed-≈ Q y₁≈y₂) ∘ embed-fam Q y₁)
      ≈⟨ pair-functorial _ _ _ _ ⟩
        prod-m (WFam-subst P (embed-≈ P x₁≈x₂)) (WFam-subst Q (embed-≈ Q y₁≈y₂)) ∘ prod-m (embed-fam P x₁) (embed-fam Q y₁)
      ∎ where open ≈-Reasoning isEquiv

    unembed-fam : (P : Poly cat) (j : WIdx poly (idx-of P)) →
                  WFam-fm P j ⇒ poly-obj P WObj .fam .fm (unembed-idx P j)
    unembed-fam Poly.one       _        = id _
    unembed-fam (Poly.const A) _        = id _
    unembed-fam Poly.var       (inF _)  = id _
    unembed-fam (P Poly.+ Q)   (inj₁ x) = unembed-fam P x
    unembed-fam (P Poly.+ Q)   (inj₂ y) = unembed-fam Q y
    unembed-fam (P Poly.× Q)   (x , y)  = prod-m (unembed-fam P x) (unembed-fam Q y)

    embed-unembed-fam-id : (P : Poly cat) (j : WIdx poly (idx-of P)) →
                           (embed-fam P (unembed-idx P j) ∘ unembed-fam P j) ≈
                           WFam-subst P (WIdx-≈-sym poly (idx-of P) (embed-unembed-id P j))
    embed-unembed-fam-id Poly.one       _        = id-left
    embed-unembed-fam-id (Poly.const A) _        = isEquiv .trans id-left (≈-sym (A .fam .refl*))
    embed-unembed-fam-id Poly.var       (inF j)  = isEquiv .trans id-left (≈-sym (WFam-refl* Q {j}))
    embed-unembed-fam-id (P Poly.+ Q')  (inj₁ x) = embed-unembed-fam-id P x
    embed-unembed-fam-id (P Poly.+ Q')  (inj₂ y) = embed-unembed-fam-id Q' y
    embed-unembed-fam-id (P Poly.× Q')  (x , y)  =
      isEquiv .trans (≈-sym (pair-functorial _ _ _ _))
                     (prod-m-cong (embed-unembed-fam-id P x) (embed-unembed-fam-id Q' y))

    inF-mor : Mor (poly-obj Q WObj) WObj
    inF-mor .idxf .PS._⇒_.func i            = inF (embed-idx Q i)
    inF-mor .idxf .PS._⇒_.func-resp-≈ x≈y   = embed-≈ Q x≈y
    inF-mor .famf .transf i                 = embed-fam Q i
    inF-mor .famf .natural x₁≈x₂            = embed-fam-natural Q x₁≈x₂

    module _ {y : Obj} (alg : Mor (poly-obj Q y) y) where

      project-idx : (P : Poly cat) → WIdx poly (idx-of P) → poly-obj P y .idx .Carrier
      project-idx Poly.one       _         = lift tt
      project-idx (Poly.const A) a         = a
      project-idx Poly.var       (inF i)   = alg .idxf .PS._⇒_.func (project-idx Q i)
      project-idx (P Poly.+ Q)   (inj₁ x)  = inj₁ (project-idx P x)
      project-idx (P Poly.+ Q)   (inj₂ z)  = inj₂ (project-idx Q z)
      project-idx (P Poly.× Q)   (x , z)   = (project-idx P x , project-idx Q z)

      project-≈ : (P : Poly cat) → ∀ {x z} → WIdx-≈ poly (idx-of P) x z →
                  poly-obj P y .idx ._≈s_ (project-idx P x) (project-idx P z)
      project-≈ Poly.one _ = tt
      project-≈ (Poly.const A) x≈z = x≈z
      project-≈ Poly.var {inF _} {inF _} x≈z =
        alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q x≈z)
      project-≈ (P Poly.+ Q) {inj₁ _} {inj₁ _} x≈z = project-≈ P x≈z
      project-≈ (P Poly.+ Q) {inj₂ _} {inj₂ _} x≈z = project-≈ Q x≈z
      project-≈ (P Poly.× Q) {_ , _} {_ , _} (x₁≈z₁ , x₂≈z₂) = (project-≈ P x₁≈z₁ , project-≈ Q x₂≈z₂)

      project-fam : (P : Poly cat) (i : WIdx poly (idx-of P)) →
                    WFam-fm P i ⇒ poly-obj P y .fam .fm (project-idx P i)
      project-fam Poly.one _            = id _
      project-fam (Poly.const A) a      = id _
      project-fam Poly.var (inF i)      = alg .famf .transf (project-idx Q i) ∘ project-fam Q i
      project-fam (P Poly.+ Q) (inj₁ x) = project-fam P x
      project-fam (P Poly.+ Q) (inj₂ z) = project-fam Q z
      project-fam (P Poly.× Q) (x , z)  = prod-m (project-fam P x) (project-fam Q z)

      project-fam-natural : (P : Poly cat) → ∀ {x z} (x≈z : WIdx-≈ poly (idx-of P) x z) →
                            (project-fam P z ∘ WFam-subst P x≈z) ≈
                            (poly-obj P y .fam .subst (project-≈ P x≈z) ∘ project-fam P x)
      project-fam-natural Poly.one _ = isEquiv .trans id-left (≈-sym id-right)
      project-fam-natural (Poly.const A) _ = isEquiv .trans id-left (≈-sym id-right)
      project-fam-natural Poly.var {inF i₁} {inF i₂} i₁≈i₂ =
        begin
          (alg .famf .transf (project-idx Q i₂) ∘ project-fam Q i₂) ∘ WFam-subst Q i₁≈i₂
        ≈⟨ assoc _ _ _ ⟩
          alg .famf .transf (project-idx Q i₂) ∘ (project-fam Q i₂ ∘ WFam-subst Q i₁≈i₂)
        ≈⟨ ∘-cong (isEquiv .refl) (project-fam-natural Q i₁≈i₂) ⟩
          alg .famf .transf (project-idx Q i₂) ∘
            (poly-obj Q y .fam .subst (project-≈ Q i₁≈i₂) ∘ project-fam Q i₁)
        ≈⟨ ≈-sym (assoc _ _ _) ⟩
          (alg .famf .transf (project-idx Q i₂) ∘
            poly-obj Q y .fam .subst (project-≈ Q i₁≈i₂)) ∘ project-fam Q i₁
        ≈⟨ ∘-cong (alg .famf .natural (project-≈ Q i₁≈i₂)) (isEquiv .refl) ⟩
          (y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q i₁≈i₂)) ∘ alg .famf .transf (project-idx Q i₁)) ∘ project-fam Q i₁
        ≈⟨ assoc _ _ _ ⟩
          y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q i₁≈i₂)) ∘
            (alg .famf .transf (project-idx Q i₁) ∘ project-fam Q i₁)
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural (P Poly.+ Q) {inj₁ _} {inj₁ _} x≈z = project-fam-natural P x≈z
      project-fam-natural (P Poly.+ Q) {inj₂ _} {inj₂ _} x≈z = project-fam-natural Q x≈z
      project-fam-natural (P Poly.× Q) {x₁ , z₁} {x₂ , z₂} (x₁≈x₂ , z₁≈z₂) =
        begin
          prod-m (project-fam P x₂) (project-fam Q z₂) ∘ prod-m _ _
        ≈⟨ ≈-sym (pair-functorial _ _ _ _) ⟩
          prod-m (project-fam P x₂ ∘ _) (project-fam Q z₂ ∘ _)
        ≈⟨ prod-m-cong (project-fam-natural P x₁≈x₂) (project-fam-natural Q z₁≈z₂) ⟩
          prod-m (_ ∘ project-fam P x₁) (_ ∘ project-fam Q z₁)
        ≈⟨ pair-functorial _ _ _ _ ⟩
          prod-m _ _ ∘ prod-m (project-fam P x₁) (project-fam Q z₁)
        ∎ where open ≈-Reasoning isEquiv

      fold : Mor WObj y
      fold .idxf .PS._⇒_.func (inF i)                       = alg .idxf .PS._⇒_.func (project-idx Q i)
      fold .idxf .PS._⇒_.func-resp-≈ {inF _} {inF _} i₁≈i₂  = alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q i₁≈i₂)
      fold .famf .transf (inF i)                            = alg .famf .transf (project-idx Q i) ∘ project-fam Q i
      fold .famf .natural {inF _} {inF _} i₁≈i₂             = project-fam-natural Poly.var i₁≈i₂

    -- Open (parametric) fold: takes algebra in extended context Γ ⊗ poly-obj Q y ⇒ y
    -- and produces Γ ⊗ μ Q ⇒ y. Threads γ through the structural recursion.
    module Open {Γ y : Obj} (alg : Mor (Γ ⊗ poly-obj Q y) y) where
      open Obj
      open Mor

      project-idx-open : (P : Poly cat) → Γ .idx .Carrier → WIdx poly (idx-of P) →
                         poly-obj P y .idx .Carrier
      project-idx-open Poly.one       _ _         = lift tt
      project-idx-open (Poly.const A) _ a         = a
      project-idx-open Poly.var       γ (inF i)   =
        alg .idxf .PS._⇒_.func (γ , project-idx-open Q γ i)
      project-idx-open (P Poly.+ R)   γ (inj₁ x)  = inj₁ (project-idx-open P γ x)
      project-idx-open (P Poly.+ R)   γ (inj₂ z)  = inj₂ (project-idx-open R γ z)
      project-idx-open (P Poly.× R)   γ (x , z)   = (project-idx-open P γ x , project-idx-open R γ z)

      project-≈-open : (P : Poly cat) → ∀ {γ₁ γ₂ : Γ .idx .Carrier} {x z}
                       (γ₁≈γ₂ : Γ .idx ._≈s_ γ₁ γ₂) (i₁≈i₂ : WIdx-≈ poly (idx-of P) x z) →
                       poly-obj P y .idx ._≈s_
                         (project-idx-open P γ₁ x) (project-idx-open P γ₂ z)
      project-≈-open Poly.one _ _ = tt
      project-≈-open (Poly.const A) _ x≈z = x≈z
      project-≈-open Poly.var {γ₁} {γ₂} {inF _} {inF _} γ₁≈γ₂ x≈z =
        alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ x≈z)
      project-≈-open (P Poly.+ R) {x = inj₁ _} {inj₁ _} γ₁≈γ₂ x≈z = project-≈-open P γ₁≈γ₂ x≈z
      project-≈-open (P Poly.+ R) {x = inj₂ _} {inj₂ _} γ₁≈γ₂ x≈z = project-≈-open R γ₁≈γ₂ x≈z
      project-≈-open (P Poly.× R) {x = _ , _} {_ , _} γ₁≈γ₂ (x₁≈z₁ , x₂≈z₂) =
        project-≈-open P γ₁≈γ₂ x₁≈z₁ , project-≈-open R γ₁≈γ₂ x₂≈z₂

      project-fam-open : (P : Poly cat) (γ : Γ .idx .Carrier)
                         (i : WIdx poly (idx-of P)) →
                         prod (Γ .fam .fm γ) (WFam-fm P i) ⇒
                         poly-obj P y .fam .fm (project-idx-open P γ i)
      project-fam-open Poly.one         _ _         = HasTerminal.to-terminal T
      project-fam-open (Poly.const A)   _ _         = p₂
      project-fam-open Poly.var         γ (inF i)   =
        alg .famf .transf (γ , project-idx-open Q γ i) ∘ pair p₁ (project-fam-open Q γ i)
      project-fam-open (P Poly.+ R)     γ (inj₁ x)  = project-fam-open P γ x
      project-fam-open (P Poly.+ R)     γ (inj₂ z)  = project-fam-open R γ z
      project-fam-open (P Poly.× R)     γ (x , z)   =
        pair (project-fam-open P γ x ∘ pair p₁ (p₁ ∘ p₂))
             (project-fam-open R γ z ∘ pair p₁ (p₂ ∘ p₂))

      project-fam-natural-open :
        (P : Poly cat) → ∀ {γ₁ γ₂ : Γ .idx .Carrier} {x z}
        (γ₁≈γ₂ : Γ .idx ._≈s_ γ₁ γ₂)
        (i₁≈i₂ : WIdx-≈ poly (idx-of P) x z) →
        (project-fam-open P γ₂ z ∘
          prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P i₁≈i₂)) ≈
        (poly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ i₁≈i₂) ∘ project-fam-open P γ₁ x)
      project-fam-natural-open Poly.one _ _ =
        HasTerminal.to-terminal-unique T _ _
      project-fam-natural-open (Poly.const A) {x = a} {z = b} _ i₁≈i₂ =
        begin
          p₂ ∘ prod-m _ (A .fam .subst i₁≈i₂)
        ≈⟨ pair-p₂ _ _ ⟩
          A .fam .subst i₁≈i₂ ∘ p₂
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural-open Poly.var {γ₁} {γ₂} {inF i₁} {inF i₂} γ₁≈γ₂ i₁≈i₂ =
        begin
          (alg .famf .transf (γ₂ , _) ∘ pair p₁ (project-fam-open Q γ₂ i₂))
            ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst Q i₁≈i₂)
        ≈⟨ assoc _ _ _ ⟩
          alg .famf .transf (γ₂ , _) ∘
            (pair p₁ (project-fam-open Q γ₂ i₂) ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst Q i₁≈i₂))
        ≈⟨ ∘-cong (isEquiv .refl) (pair-natural _ _ _) ⟩
          alg .famf .transf (γ₂ , _) ∘
            pair (p₁ ∘ prod-m _ _) (project-fam-open Q γ₂ i₂ ∘ prod-m _ _)
        ≈⟨ ∘-cong (isEquiv .refl)
             (pair-cong (pair-p₁ _ _) (project-fam-natural-open Q γ₁≈γ₂ i₁≈i₂)) ⟩
          alg .famf .transf (γ₂ , _) ∘
            pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁)
                 (poly-obj Q y .fam .subst (project-≈-open Q γ₁≈γ₂ i₁≈i₂) ∘ project-fam-open Q γ₁ i₁)
        ≈⟨ ≈-sym (∘-cong (isEquiv .refl) (pair-compose _ _ _ _)) ⟩
          alg .famf .transf (γ₂ , _) ∘
            (prod-m (Γ .fam .subst γ₁≈γ₂) (poly-obj Q y .fam .subst (project-≈-open Q γ₁≈γ₂ i₁≈i₂))
              ∘ pair p₁ (project-fam-open Q γ₁ i₁))
        ≈⟨ ≈-sym (assoc _ _ _) ⟩
          (alg .famf .transf (γ₂ , _) ∘
            prod-m (Γ .fam .subst γ₁≈γ₂) (poly-obj Q y .fam .subst (project-≈-open Q γ₁≈γ₂ i₁≈i₂)))
            ∘ pair p₁ (project-fam-open Q γ₁ i₁)
        ≈⟨ ∘-cong (alg .famf .natural (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂)) (isEquiv .refl) ⟩
          (y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂))
            ∘ alg .famf .transf (γ₁ , _))
            ∘ pair p₁ (project-fam-open Q γ₁ i₁)
        ≈⟨ assoc _ _ _ ⟩
          y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂))
            ∘ (alg .famf .transf (γ₁ , _) ∘ pair p₁ (project-fam-open Q γ₁ i₁))
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural-open (P Poly.+ R) {x = inj₁ _} {inj₁ _} γ₁≈γ₂ i₁≈i₂ =
        project-fam-natural-open P γ₁≈γ₂ i₁≈i₂
      project-fam-natural-open (P Poly.+ R) {x = inj₂ _} {inj₂ _} γ₁≈γ₂ i₁≈i₂ =
        project-fam-natural-open R γ₁≈γ₂ i₁≈i₂
      project-fam-natural-open (P Poly.× R) {γ₁} {γ₂} {x₁ , z₁} {x₂ , z₂} γ₁≈γ₂ (x₁≈x₂ , z₁≈z₂) =
        begin
          pair (project-fam-open P γ₂ x₂ ∘ pair p₁ (p₁ ∘ p₂))
               (project-fam-open R γ₂ z₂ ∘ pair p₁ (p₂ ∘ p₂))
            ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (prod-m (WFam-subst P x₁≈x₂) (WFam-subst R z₁≈z₂))
        ≈⟨ pair-natural _ _ _ ⟩
          pair ((project-fam-open P γ₂ x₂ ∘ pair p₁ (p₁ ∘ p₂)) ∘ prod-m _ _)
               ((project-fam-open R γ₂ z₂ ∘ pair p₁ (p₂ ∘ p₂)) ∘ prod-m _ _)
        ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
          pair (project-fam-open P γ₂ x₂ ∘ (pair p₁ (p₁ ∘ p₂) ∘ prod-m _ _))
               (project-fam-open R γ₂ z₂ ∘ (pair p₁ (p₂ ∘ p₂) ∘ prod-m _ _))
        ≈⟨ pair-cong
             (∘-cong (isEquiv .refl)
               (≈-trans (pair-natural _ _ _)
                 (pair-cong (pair-p₁ _ _)
                   (≈-trans (assoc _ _ _)
                     (≈-trans (∘-cong (isEquiv .refl) (pair-p₂ _ _))
                       (≈-trans (≈-sym (assoc _ _ _))
                         (≈-trans (∘-cong (pair-p₁ _ _) (isEquiv .refl))
                                  (assoc _ _ _))))))))
             (∘-cong (isEquiv .refl)
               (≈-trans (pair-natural _ _ _)
                 (pair-cong (pair-p₁ _ _)
                   (≈-trans (assoc _ _ _)
                     (≈-trans (∘-cong (isEquiv .refl) (pair-p₂ _ _))
                       (≈-trans (≈-sym (assoc _ _ _))
                         (≈-trans (∘-cong (pair-p₂ _ _) (isEquiv .refl))
                                  (assoc _ _ _)))))))) ⟩
          pair (project-fam-open P γ₂ x₂ ∘ pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁) (WFam-subst P x₁≈x₂ ∘ (p₁ ∘ p₂)))
               (project-fam-open R γ₂ z₂ ∘ pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁) (WFam-subst R z₁≈z₂ ∘ (p₂ ∘ p₂)))
        ≈⟨ pair-cong (∘-cong (isEquiv .refl) (≈-sym (pair-compose _ _ _ _)))
                     (∘-cong (isEquiv .refl) (≈-sym (pair-compose _ _ _ _))) ⟩
          pair (project-fam-open P γ₂ x₂ ∘
                 (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P x₁≈x₂) ∘ pair p₁ (p₁ ∘ p₂)))
               (project-fam-open R γ₂ z₂ ∘
                 (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst R z₁≈z₂) ∘ pair p₁ (p₂ ∘ p₂)))
        ≈⟨ pair-cong (≈-sym (assoc _ _ _)) (≈-sym (assoc _ _ _)) ⟩
          pair ((project-fam-open P γ₂ x₂ ∘ prod-m _ _) ∘ pair p₁ (p₁ ∘ p₂))
               ((project-fam-open R γ₂ z₂ ∘ prod-m _ _) ∘ pair p₁ (p₂ ∘ p₂))
        ≈⟨ pair-cong (∘-cong (project-fam-natural-open P γ₁≈γ₂ x₁≈x₂) (isEquiv .refl))
                     (∘-cong (project-fam-natural-open R γ₁≈γ₂ z₁≈z₂) (isEquiv .refl)) ⟩
          pair ((poly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ x₁≈x₂) ∘ project-fam-open P γ₁ x₁)
                  ∘ pair p₁ (p₁ ∘ p₂))
               ((poly-obj R y .fam .subst (project-≈-open R γ₁≈γ₂ z₁≈z₂) ∘ project-fam-open R γ₁ z₁)
                  ∘ pair p₁ (p₂ ∘ p₂))
        ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
          pair (poly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ x₁≈x₂)
                 ∘ (project-fam-open P γ₁ x₁ ∘ pair p₁ (p₁ ∘ p₂)))
               (poly-obj R y .fam .subst (project-≈-open R γ₁≈γ₂ z₁≈z₂)
                 ∘ (project-fam-open R γ₁ z₁ ∘ pair p₁ (p₂ ∘ p₂)))
        ≈⟨ ≈-sym (pair-compose _ _ _ _) ⟩
          prod-m (poly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ x₁≈x₂))
                 (poly-obj R y .fam .subst (project-≈-open R γ₁≈γ₂ z₁≈z₂))
            ∘ pair (project-fam-open P γ₁ x₁ ∘ pair p₁ (p₁ ∘ p₂))
                   (project-fam-open R γ₁ z₁ ∘ pair p₁ (p₂ ∘ p₂))
        ∎ where open ≈-Reasoning isEquiv

      fold-open : Mor (Γ ⊗ WObj) y
      fold-open .idxf .PS._⇒_.func (γ , inF i) =
        alg .idxf .PS._⇒_.func (γ , project-idx-open Q γ i)
      fold-open .idxf .PS._⇒_.func-resp-≈ {γ₁ , inF _} {γ₂ , inF _} (γ₁≈γ₂ , i₁≈i₂) =
        alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂)
      fold-open .famf .transf (γ , inF i) =
        alg .famf .transf (γ , project-idx-open Q γ i) ∘
          pair p₁ (project-fam-open Q γ i)
      fold-open .famf .natural {γ₁ , inF _} {γ₂ , inF _} (γ₁≈γ₂ , i₁≈i₂) =
        project-fam-natural-open Poly.var γ₁≈γ₂ i₁≈i₂

      -- project-idx through embed-idx agrees with poly-fmor's idx action of fold.
      β-idx : (P : Poly cat)
              {γ₁ γ₂ : Γ .idx .Carrier} (γ₁≈γ₂ : Γ .idx ._≈s_ γ₁ γ₂)
              {i₁ i₂ : poly-obj P WObj .idx .Carrier} (i₁≈i₂ : poly-obj P WObj .idx ._≈s_ i₁ i₂) →
              poly-obj P y .idx ._≈s_
                (project-idx-open P γ₁ (embed-idx P i₁)) (poly-fmor P fold-open .idxf .PS._⇒_.func (γ₂ , i₂))
      β-idx Poly.one       _ _                            = tt
      β-idx (Poly.const A) _ i₁≈i₂                        = i₁≈i₂
      β-idx Poly.var       γ₁≈γ₂ {inF _} {inF _} i₁≈i₂    =
        alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂)
      β-idx (P Poly.+ R)   γ₁≈γ₂ {inj₁ _} {inj₁ _} i₁≈i₂  = β-idx P γ₁≈γ₂ i₁≈i₂
      β-idx (P Poly.+ R)   γ₁≈γ₂ {inj₂ _} {inj₂ _} i₁≈i₂  = β-idx R γ₁≈γ₂ i₁≈i₂
      β-idx (P Poly.× R)   γ₁≈γ₂ (x₁≈x₂ , z₁≈z₂)          = β-idx P γ₁≈γ₂ x₁≈x₂ , β-idx R γ₁≈γ₂ z₁≈z₂

      -- project-fam through embed agrees (modulo subst from β-idx) with poly-fmor's fam action of fold.
      β-fam : (P : Poly cat) (γ : Γ .idx .Carrier) (i : poly-obj P WObj .idx .Carrier) →
              (poly-obj P y .fam .subst
                (β-idx P (Γ .idx .Setoid.refl) (poly-obj P WObj .idx .Setoid.refl)) ∘
                project-fam-open P γ (embed-idx P i) ∘ pair p₁ (embed-fam P i ∘ p₂)) ≈
              poly-fmor P fold-open .famf .transf (γ , i)
      β-fam Poly.one _ _ = HasTerminal.to-terminal-unique T _ _
      β-fam (Poly.const A) γ i = begin
          (A .fam .subst _ ∘ p₂) ∘ pair p₁ (id _ ∘ p₂)
        ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl id-left) ⟩
          (A .fam .subst _ ∘ p₂) ∘ pair p₁ p₂
        ≈⟨ assoc _ _ _ ⟩
          A .fam .subst _ ∘ (p₂ ∘ pair p₁ p₂)
        ≈⟨ ∘-cong ≈-refl (pair-p₂ _ _) ⟩
          A .fam .subst _ ∘ p₂
        ≈⟨ ∘-cong (A .fam .refl*) ≈-refl ⟩
          id _ ∘ p₂
        ≈⟨ id-left ⟩
          p₂
        ∎ where open ≈-Reasoning isEquiv
      β-fam Poly.var γ (inF i) = begin
          (y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx-open Q γ i) ∘ pair p₁ (project-fam-open Q γ i))) ∘ pair p₁ (id _ ∘ p₂)
        ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl id-left) ⟩
          (y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx-open Q γ i) ∘ pair p₁ (project-fam-open Q γ i))) ∘ pair p₁ p₂
        ≈⟨ ∘-cong ≈-refl (≈-trans (pair-cong (≈-sym id-right) (≈-sym id-right)) (pair-ext (id _))) ⟩
          (y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx-open Q γ i) ∘ pair p₁ (project-fam-open Q γ i))) ∘ id _
        ≈⟨ id-right ⟩
          y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx-open Q γ i) ∘ pair p₁ (project-fam-open Q γ i))
        ≈⟨ ∘-cong (y .fam .refl*) ≈-refl ⟩
          id _ ∘ (alg .famf .transf (γ , project-idx-open Q γ i) ∘ pair p₁ (project-fam-open Q γ i))
        ≈⟨ id-left ⟩
          alg .famf .transf (γ , project-idx-open Q γ i) ∘ pair p₁ (project-fam-open Q γ i)
        ∎ where open ≈-Reasoning isEquiv
      β-fam (P Poly.+ R)   γ (inj₁ x)       =
        ≈-trans (β-fam P γ x) (≈-sym (≈-trans id-left id-left))
      β-fam (P Poly.+ R)   γ (inj₂ z)       =
        ≈-trans (β-fam R γ z) (≈-sym (≈-trans id-left id-left))
      β-fam (P Poly.× R)   γ (x , z)        =
        ≈-trans (∘-cong (pair-natural _ _ _) ≈-refl) (≈-trans (pair-natural _ _ _) (pair-cong eq-P eq-R))
        where
          -- Lift a WObj-fibre pair into the WFam-fibre form.
          pair-embed : prod (Γ .fam .fm γ) (prod (poly-obj P WObj .fam .fm x) (poly-obj R WObj .fam .fm z)) ⇒
                       prod (Γ .fam .fm γ) (prod (WFam-fm P (embed-idx P x)) (WFam-fm R (embed-idx R z)))
          pair-embed = pair p₁ (pair (embed-fam P x ∘ p₁) (embed-fam R z ∘ p₂) ∘ p₂)

          bridge-P : (pair p₁ (p₁ ∘ p₂) ∘ pair-embed) ≈ pair p₁ (embed-fam P x ∘ (p₁ ∘ p₂))
          bridge-P = begin
              pair p₁ (p₁ ∘ p₂) ∘ pair-embed
            ≈⟨ pair-natural _ _ _ ⟩
              pair (p₁ ∘ pair-embed) ((p₁ ∘ p₂) ∘ pair-embed)
            ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
              pair p₁ (p₁ ∘ (p₂ ∘ pair-embed))
            ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
              pair p₁ (p₁ ∘ (pair (embed-fam P x ∘ p₁) (embed-fam R z ∘ p₂) ∘ p₂))
            ≈⟨ pair-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
              pair p₁ ((p₁ ∘ pair (embed-fam P x ∘ p₁) (embed-fam R z ∘ p₂)) ∘ p₂)
            ≈⟨ pair-cong ≈-refl (∘-cong (pair-p₁ _ _) ≈-refl) ⟩
              pair p₁ ((embed-fam P x ∘ p₁) ∘ p₂)
            ≈⟨ pair-cong ≈-refl (assoc _ _ _) ⟩
              pair p₁ (embed-fam P x ∘ (p₁ ∘ p₂))
            ∎ where open ≈-Reasoning isEquiv

          bridge-R : (pair p₁ (p₂ ∘ p₂) ∘ pair-embed) ≈ pair p₁ (embed-fam R z ∘ (p₂ ∘ p₂))
          bridge-R = begin
              pair p₁ (p₂ ∘ p₂) ∘ pair-embed
            ≈⟨ pair-natural _ _ _ ⟩
              pair (p₁ ∘ pair-embed) ((p₂ ∘ p₂) ∘ pair-embed)
            ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
              pair p₁ (p₂ ∘ (p₂ ∘ pair-embed))
            ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
              pair p₁ (p₂ ∘ (pair (embed-fam P x ∘ p₁) (embed-fam R z ∘ p₂) ∘ p₂))
            ≈⟨ pair-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
              pair p₁ ((p₂ ∘ pair (embed-fam P x ∘ p₁) (embed-fam R z ∘ p₂)) ∘ p₂)
            ≈⟨ pair-cong ≈-refl (∘-cong (pair-p₂ _ _) ≈-refl) ⟩
              pair p₁ ((embed-fam R z ∘ p₂) ∘ p₂)
            ≈⟨ pair-cong ≈-refl (assoc _ _ _) ⟩
              pair p₁ (embed-fam R z ∘ (p₂ ∘ p₂))
            ∎ where open ≈-Reasoning isEquiv

          eq-P : ((poly-obj P y .fam .subst _ ∘ p₁) ∘
                    pair (project-fam-open P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                         (project-fam-open R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘ pair-embed
                 ≈ id _ ∘ (poly-fmor P fold-open .famf .transf (γ , x) ∘ pair p₁ (id _ ∘ (p₁ ∘ p₂)))
          eq-P = begin
              ((poly-obj P y .fam .subst _ ∘ p₁) ∘
                pair (project-fam-open P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                     (project-fam-open R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘ pair-embed
            ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
              (poly-obj P y .fam .subst _ ∘ (p₁ ∘
                pair (project-fam-open P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                     (project-fam-open R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂)))) ∘ pair-embed
            ≈⟨ ∘-cong (∘-cong ≈-refl (pair-p₁ _ _)) ≈-refl ⟩
              (poly-obj P y .fam .subst _ ∘ (project-fam-open P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))) ∘ pair-embed
            ≈⟨ ∘-cong (≈-sym (assoc _ _ _)) ≈-refl ⟩
              ((poly-obj P y .fam .subst _ ∘ project-fam-open P γ (embed-idx P x)) ∘ pair p₁ (p₁ ∘ p₂)) ∘ pair-embed
            ≈⟨ assoc _ _ _ ⟩
              (poly-obj P y .fam .subst _ ∘ project-fam-open P γ (embed-idx P x)) ∘ (pair p₁ (p₁ ∘ p₂) ∘ pair-embed)
            ≈⟨ ∘-cong ≈-refl bridge-P ⟩
              (poly-obj P y .fam .subst _ ∘ project-fam-open P γ (embed-idx P x)) ∘
                pair p₁ (embed-fam P x ∘ (p₁ ∘ p₂))
            ≈˘⟨ ∘-cong ≈-refl (pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _))) ⟩
              (poly-obj P y .fam .subst _ ∘ project-fam-open P γ (embed-idx P x)) ∘
                pair p₁ (embed-fam P x ∘ (p₂ ∘ pair p₁ (p₁ ∘ p₂)))
            ≈˘⟨ ∘-cong ≈-refl (pair-cong ≈-refl (assoc _ _ _)) ⟩
              (poly-obj P y .fam .subst _ ∘ project-fam-open P γ (embed-idx P x)) ∘
                pair p₁ ((embed-fam P x ∘ p₂) ∘ pair p₁ (p₁ ∘ p₂))
            ≈˘⟨ ∘-cong ≈-refl (pair-cong (pair-p₁ _ _) ≈-refl) ⟩
              (poly-obj P y .fam .subst _ ∘ project-fam-open P γ (embed-idx P x)) ∘
                pair (p₁ ∘ pair p₁ (p₁ ∘ p₂)) ((embed-fam P x ∘ p₂) ∘ pair p₁ (p₁ ∘ p₂))
            ≈˘⟨ ∘-cong ≈-refl (pair-natural _ _ _) ⟩
              (poly-obj P y .fam .subst _ ∘ project-fam-open P γ (embed-idx P x)) ∘
                (pair p₁ (embed-fam P x ∘ p₂) ∘ pair p₁ (p₁ ∘ p₂))
            ≈˘⟨ assoc _ _ _ ⟩
              ((poly-obj P y .fam .subst _ ∘ project-fam-open P γ (embed-idx P x)) ∘
                pair p₁ (embed-fam P x ∘ p₂)) ∘ pair p₁ (p₁ ∘ p₂)
            ≈⟨ ∘-cong (β-fam P γ x) ≈-refl ⟩
              poly-fmor P fold-open .famf .transf (γ , x) ∘ pair p₁ (p₁ ∘ p₂)
            ≈˘⟨ ∘-cong ≈-refl (pair-cong ≈-refl id-left) ⟩
              poly-fmor P fold-open .famf .transf (γ , x) ∘ pair p₁ (id _ ∘ (p₁ ∘ p₂))
            ≈˘⟨ id-left ⟩
              id _ ∘ (poly-fmor P fold-open .famf .transf (γ , x) ∘ pair p₁ (id _ ∘ (p₁ ∘ p₂)))
            ∎ where open ≈-Reasoning isEquiv

          eq-R : ((poly-obj R y .fam .subst _ ∘ p₂) ∘
                    pair (project-fam-open P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                         (project-fam-open R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘ pair-embed
                 ≈ id _ ∘ (poly-fmor R fold-open .famf .transf (γ , z) ∘ pair p₁ (id _ ∘ (p₂ ∘ p₂)))
          eq-R = begin
              ((poly-obj R y .fam .subst _ ∘ p₂) ∘
                pair (project-fam-open P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                     (project-fam-open R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘ pair-embed
            ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
              (poly-obj R y .fam .subst _ ∘ (p₂ ∘
                pair (project-fam-open P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                     (project-fam-open R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂)))) ∘ pair-embed
            ≈⟨ ∘-cong (∘-cong ≈-refl (pair-p₂ _ _)) ≈-refl ⟩
              (poly-obj R y .fam .subst _ ∘ (project-fam-open R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘ pair-embed
            ≈⟨ ∘-cong (≈-sym (assoc _ _ _)) ≈-refl ⟩
              ((poly-obj R y .fam .subst _ ∘ project-fam-open R γ (embed-idx R z)) ∘ pair p₁ (p₂ ∘ p₂)) ∘ pair-embed
            ≈⟨ assoc _ _ _ ⟩
              (poly-obj R y .fam .subst _ ∘ project-fam-open R γ (embed-idx R z)) ∘ (pair p₁ (p₂ ∘ p₂) ∘ pair-embed)
            ≈⟨ ∘-cong ≈-refl bridge-R ⟩
              (poly-obj R y .fam .subst _ ∘ project-fam-open R γ (embed-idx R z)) ∘
                pair p₁ (embed-fam R z ∘ (p₂ ∘ p₂))
            ≈˘⟨ ∘-cong ≈-refl (pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _))) ⟩
              (poly-obj R y .fam .subst _ ∘ project-fam-open R γ (embed-idx R z)) ∘
                pair p₁ (embed-fam R z ∘ (p₂ ∘ pair p₁ (p₂ ∘ p₂)))
            ≈˘⟨ ∘-cong ≈-refl (pair-cong ≈-refl (assoc _ _ _)) ⟩
              (poly-obj R y .fam .subst _ ∘ project-fam-open R γ (embed-idx R z)) ∘
                pair p₁ ((embed-fam R z ∘ p₂) ∘ pair p₁ (p₂ ∘ p₂))
            ≈˘⟨ ∘-cong ≈-refl (pair-cong (pair-p₁ _ _) ≈-refl) ⟩
              (poly-obj R y .fam .subst _ ∘ project-fam-open R γ (embed-idx R z)) ∘
                pair (p₁ ∘ pair p₁ (p₂ ∘ p₂)) ((embed-fam R z ∘ p₂) ∘ pair p₁ (p₂ ∘ p₂))
            ≈˘⟨ ∘-cong ≈-refl (pair-natural _ _ _) ⟩
              (poly-obj R y .fam .subst _ ∘ project-fam-open R γ (embed-idx R z)) ∘
                (pair p₁ (embed-fam R z ∘ p₂) ∘ pair p₁ (p₂ ∘ p₂))
            ≈˘⟨ assoc _ _ _ ⟩
              ((poly-obj R y .fam .subst _ ∘ project-fam-open R γ (embed-idx R z)) ∘
                pair p₁ (embed-fam R z ∘ p₂)) ∘ pair p₁ (p₂ ∘ p₂)
            ≈⟨ ∘-cong (β-fam R γ z) ≈-refl ⟩
              poly-fmor R fold-open .famf .transf (γ , z) ∘ pair p₁ (p₂ ∘ p₂)
            ≈˘⟨ ∘-cong ≈-refl (pair-cong ≈-refl id-left) ⟩
              poly-fmor R fold-open .famf .transf (γ , z) ∘ pair p₁ (id _ ∘ (p₂ ∘ p₂))
            ≈˘⟨ id-left ⟩
              id _ ∘ (poly-fmor R fold-open .famf .transf (γ , z) ∘ pair p₁ (id _ ∘ (p₂ ∘ p₂)))
            ∎ where open ≈-Reasoning isEquiv

      -- Cata helpers (η case): given h with h-step, build proof h ≃ fold-open.
      module _ (h : Mor (Γ ⊗ WObj) y)
               (h-step : (h Fam𝒞.∘ Fam𝒞-P.pair Fam𝒞-P.p₁ (inF-mor Fam𝒞.∘ Fam𝒞-P.p₂)) ≃
                         (alg Fam𝒞.∘ Fam𝒞-P.pair Fam𝒞-P.p₁ (poly-fmor Q h))) where
        η-idx : (P : Poly cat) {δ₁ δ₂ : Γ .idx .Carrier} (δ₁≈δ₂ : Γ .idx ._≈s_ δ₁ δ₂)
                {j₁ j₂ : WIdx poly (idx-of P)} (j₁≈j₂ : WIdx-≈ poly (idx-of P) j₁ j₂) →
                poly-obj P y .idx ._≈s_
                  (poly-fmor P h .idxf .PS._⇒_.func (δ₁ , unembed-idx P j₁)) (project-idx-open P δ₂ j₂)
        η-idx Poly.one _ _ = tt
        η-idx (Poly.const A) _ j₁≈j₂ = j₁≈j₂
        η-idx Poly.var δ₁≈δ₂ {inF j₁} {inF j₂} j₁≈j₂ =
          begin
            h .idxf .PS._⇒_.func (_ , inF j₁)
          ≈⟨ h .idxf .PS._⇒_.func-resp-≈
               (δ₁≈δ₂ ,
                WObj .idx .isEquivalence .trans j₁≈j₂
                  (WObj .idx .isEquivalence .sym (embed-unembed-id Q j₂))) ⟩
            h .idxf .PS._⇒_.func (_ , inF (embed-idx Q (unembed-idx Q j₂)))
          ≈⟨ h-step ._≃_.idxf-eq .PS._≃m_.func-eq
               (Γ .idx .isEquivalence .refl ,
                poly-obj Q WObj .idx .isEquivalence .refl) ⟩
            alg .idxf .PS._⇒_.func (_ , poly-fmor Q h .idxf .PS._⇒_.func (_ , unembed-idx Q j₂))
          ≈⟨ alg .idxf .PS._⇒_.func-resp-≈
               (Γ .idx .isEquivalence .refl ,
                η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q))) ⟩
            alg .idxf .PS._⇒_.func (_ , project-idx-open Q _ j₂)
          ∎ where open ≈-Reasoning (y .idx .isEquivalence)
        η-idx (P Poly.+ R)   δ₁≈δ₂ {inj₁ x₁} {inj₁ x₂} j₁≈j₂      = η-idx P δ₁≈δ₂ j₁≈j₂
        η-idx (P Poly.+ R)   δ₁≈δ₂ {inj₂ y₁} {inj₂ y₂} j₁≈j₂      = η-idx R δ₁≈δ₂ j₁≈j₂
        η-idx (P Poly.× R)   δ₁≈δ₂ {x₁ , z₁} {x₂ , z₂} (x₁≈x₂ , z₁≈z₂) =
          η-idx P δ₁≈δ₂ x₁≈x₂ , η-idx R δ₁≈δ₂ z₁≈z₂

        -- Fam-level analog at WIdx level: relates poly-fmor h's transf (bridged via unembed-fam) to
        -- project-fam-open (modulo subst from η-idx).
        η-fam : (P : Poly cat) (γ : Γ .idx .Carrier) (j : WIdx poly (idx-of P)) →
                (poly-obj P y .fam .subst
                   (η-idx P (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of P) {j})) ∘
                 poly-fmor P h .famf .transf (γ , unembed-idx P j) ∘ pair p₁ (unembed-fam P j ∘ p₂)) ≈
                project-fam-open P γ j
        η-fam Poly.one γ j = HasTerminal.to-terminal-unique T _ _
        η-fam (Poly.const A) γ j = begin
            (A .fam .subst _ ∘ p₂) ∘ pair p₁ (id _ ∘ p₂)
          ≈⟨ ∘-cong (∘-cong (A .fam .refl*) ≈-refl) ≈-refl ⟩
            (id _ ∘ p₂) ∘ pair p₁ (id _ ∘ p₂)
          ≈⟨ ∘-cong id-left ≈-refl ⟩
            p₂ ∘ pair p₁ (id _ ∘ p₂)
          ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl id-left) ⟩
            p₂ ∘ pair p₁ p₂
          ≈⟨ pair-p₂ _ _ ⟩
            p₂
          ∎ where open ≈-Reasoning isEquiv
        η-fam Poly.var γ (inF j) = begin
            (y .fam .subst _ ∘ h .famf .transf (γ , inF j) ∘ pair p₁ (id _ ∘ p₂))
          ≈⟨ isEquiv .trans (∘-cong ≈-refl (isEquiv .trans (pair-cong ≈-refl id-left) pair-ext0)) id-right ⟩
            y .fam .subst _ ∘ h .famf .transf (γ , inF j)
          ≈⟨ ∘-cong (y .fam .trans*
                       (y .idx .isEquivalence .trans
                         (h-step ._≃_.idxf-eq .PS._≃m_.func-eq
                           (Γ .idx .isEquivalence .refl , poly-obj Q WObj .idx .isEquivalence .refl))
                         (alg .idxf .PS._⇒_.func-resp-≈
                           (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q)))))
                       (h .idxf .PS._⇒_.func-resp-≈
                          (Γ .idx .isEquivalence .refl , WObj .idx .isEquivalence .sym (embed-unembed-id Q j)))) ≈-refl ⟩
            (y .fam .subst (y .idx .isEquivalence .trans
                             (h-step ._≃_.idxf-eq .PS._≃m_.func-eq
                               (Γ .idx .isEquivalence .refl , poly-obj Q WObj .idx .isEquivalence .refl))
                             (alg .idxf .PS._⇒_.func-resp-≈
                               (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q))))) ∘
               y .fam .subst (h .idxf .PS._⇒_.func-resp-≈
                                (Γ .idx .isEquivalence .refl , WObj .idx .isEquivalence .sym (embed-unembed-id Q j)))) ∘
            h .famf .transf (γ , inF j)
          ≈⟨ assoc _ _ _ ⟩
            y .fam .subst _ ∘
              (y .fam .subst (h .idxf .PS._⇒_.func-resp-≈
                                (Γ .idx .isEquivalence .refl , WObj .idx .isEquivalence .sym (embed-unembed-id Q j))) ∘
               h .famf .transf (γ , inF j))
          ≈˘⟨ ∘-cong ≈-refl (h .famf .natural {γ , inF j} {γ , inF (embed-idx Q (unembed-idx Q j))}
                              (Γ .idx .isEquivalence .refl ,
                               WObj .idx .isEquivalence .sym (embed-unembed-id Q j))) ⟩
            y .fam .subst _ ∘
              (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
               (Γ ⊗ WObj) .fam .subst
                 (Γ .idx .isEquivalence .refl , WObj .idx .isEquivalence .sym (embed-unembed-id Q j)))
          ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl
                (pair-cong (isEquiv .trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left) ≈-refl)) ⟩
            y .fam .subst _ ∘
              (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
               pair p₁ (WFam-subst Q (WObj .idx .isEquivalence .sym (embed-unembed-id Q j)) ∘ p₂))
          ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (pair-cong ≈-refl
                (∘-cong (embed-unembed-fam-id Q j) ≈-refl))) ⟩
            y .fam .subst _ ∘
              (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
               pair p₁ ((embed-fam Q (unembed-idx Q j) ∘ unembed-fam Q j) ∘ p₂))
          ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (pair-cong ≈-refl (assoc _ _ _))) ⟩
            y .fam .subst _ ∘
              (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
               pair p₁ (embed-fam Q (unembed-idx Q j) ∘ (unembed-fam Q j ∘ p₂)))
          ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl
                (isEquiv .trans (pair-cong (≈-sym id-left) ≈-refl) (≈-sym (pair-compose _ _ _ _)))) ⟩
            y .fam .subst _ ∘
              (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
               (prod-m (id _) (embed-fam Q (unembed-idx Q j)) ∘ pair p₁ (unembed-fam Q j ∘ p₂)))
          ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl
                (∘-cong (isEquiv .trans (pair-cong id-left ≈-refl) (pair-cong ≈-refl (≈-sym id-left))) ≈-refl)) ⟩
            y .fam .subst _ ∘
              (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
               (pair p₁ (id _ ∘ (embed-fam Q (unembed-idx Q j) ∘ p₂)) ∘
                pair p₁ (unembed-fam Q j ∘ p₂)))
          ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
            y .fam .subst _ ∘
              ((h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘ pair p₁ (id _ ∘ (embed-fam Q (unembed-idx Q j) ∘ p₂))) ∘
               pair p₁ (unembed-fam Q j ∘ p₂))
          ≈˘⟨ ∘-cong ≈-refl (∘-cong id-left ≈-refl) ⟩
            y .fam .subst _ ∘
              ((id _ ∘
                (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘ pair p₁ (id _ ∘ (embed-fam Q (unembed-idx Q j) ∘ p₂)))) ∘
               pair p₁ (unembed-fam Q j ∘ p₂))
          ≈⟨ ∘-cong (y .fam .trans*
                       (alg .idxf .PS._⇒_.func-resp-≈
                          (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q))))
                       (h-step ._≃_.idxf-eq .PS._≃m_.func-eq
                          (Γ .idx .isEquivalence .refl , poly-obj Q WObj .idx .isEquivalence .refl))) ≈-refl ⟩
            (y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈
                              (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q)))) ∘
             y .fam .subst (h-step ._≃_.idxf-eq .PS._≃m_.func-eq
                              (Γ .idx .isEquivalence .refl , poly-obj Q WObj .idx .isEquivalence .refl))) ∘
              ((id _ ∘
                (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘ pair p₁ (id _ ∘ (embed-fam Q (unembed-idx Q j) ∘ p₂)))) ∘
               pair p₁ (unembed-fam Q j ∘ p₂))
          ≈⟨ isEquiv .trans (assoc _ _ _) (∘-cong ≈-refl (≈-sym (assoc _ _ _))) ⟩
            y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈
                              (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q)))) ∘
              ((y .fam .subst (h-step ._≃_.idxf-eq .PS._≃m_.func-eq
                                 (Γ .idx .isEquivalence .refl , poly-obj Q WObj .idx .isEquivalence .refl)) ∘
                (id _ ∘
                 (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
                  pair p₁ (id _ ∘ (embed-fam Q (unembed-idx Q j) ∘ p₂))))) ∘
               pair p₁ (unembed-fam Q j ∘ p₂))
          ≈⟨ ∘-cong ≈-refl (∘-cong (h-step ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , unembed-idx Q j}) ≈-refl) ⟩
            y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈
                              (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q)))) ∘
              ((cat Category.∘ alg) (products .HasProducts.pair (products .HasProducts.p₁) (poly-fmor Q h))
                 .famf .transf (γ , unembed-idx Q j) ∘ pair p₁ (unembed-fam Q j ∘ p₂))
          ≈⟨ ∘-cong ≈-refl (∘-cong id-left ≈-refl) ⟩
            y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈
                              (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q)))) ∘
              ((alg .famf .transf (γ , poly-fmor Q h .idxf .PS._⇒_.func (γ , unembed-idx Q j)) ∘
                pair p₁ (poly-fmor Q h .famf .transf (γ , unembed-idx Q j))) ∘
               pair p₁ (unembed-fam Q j ∘ p₂))
          ≈⟨ isEquiv .trans (≈-sym (assoc _ _ _)) (∘-cong (≈-sym (assoc _ _ _)) ≈-refl) ⟩
            ((y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈
                                (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q)))) ∘
              alg .famf .transf (γ , poly-fmor Q h .idxf .PS._⇒_.func (γ , unembed-idx Q j))) ∘
             pair p₁ (poly-fmor Q h .famf .transf (γ , unembed-idx Q j))) ∘
            pair p₁ (unembed-fam Q j ∘ p₂)
          ≈˘⟨ ∘-cong (∘-cong (alg .famf .natural
                                (Γ .idx .isEquivalence .refl ,
                                 η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q)))) ≈-refl) ≈-refl ⟩
            ((alg .famf .transf (γ , project-idx-open Q γ j) ∘
              (Γ ⊗ poly-obj Q y) .fam .subst
                (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q)))) ∘
             pair p₁ (poly-fmor Q h .famf .transf (γ , unembed-idx Q j))) ∘
            pair p₁ (unembed-fam Q j ∘ p₂)
          ≈⟨ ∘-cong (∘-cong (∘-cong ≈-refl
                (pair-cong (isEquiv .trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left) ≈-refl)) ≈-refl) ≈-refl ⟩
            ((alg .famf .transf (γ , project-idx-open Q γ j) ∘
              pair p₁ (poly-obj Q y .fam .subst
                         (η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q))) ∘ p₂)) ∘
             pair p₁ (poly-fmor Q h .famf .transf (γ , unembed-idx Q j))) ∘
            pair p₁ (unembed-fam Q j ∘ p₂)
          ≈⟨ isEquiv .trans (assoc _ _ _) (assoc _ _ _) ⟩
            alg .famf .transf (γ , project-idx-open Q γ j) ∘
              (pair p₁ (poly-obj Q y .fam .subst
                          (η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q))) ∘ p₂) ∘
               (pair p₁ (poly-fmor Q h .famf .transf (γ , unembed-idx Q j)) ∘ pair p₁ (unembed-fam Q j ∘ p₂)))
          ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl
                (isEquiv .trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) ≈-refl))) ⟩
            alg .famf .transf (γ , project-idx-open Q γ j) ∘
              (pair p₁ (poly-obj Q y .fam .subst
                          (η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q))) ∘ p₂) ∘
               pair p₁ (poly-fmor Q h .famf .transf (γ , unembed-idx Q j) ∘ pair p₁ (unembed-fam Q j ∘ p₂)))
          ≈⟨ ∘-cong ≈-refl (isEquiv .trans (pair-natural _ _ _)
                              (isEquiv .trans (pair-cong (pair-p₁ _ _) (assoc _ _ _))
                                              (pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _))))) ⟩
            alg .famf .transf (γ , project-idx-open Q γ j) ∘
              pair p₁ (poly-obj Q y .fam .subst
                         (η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl poly (idx-of Q))) ∘
                       (poly-fmor Q h .famf .transf (γ , unembed-idx Q j) ∘ pair p₁ (unembed-fam Q j ∘ p₂)))
          ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl (isEquiv .trans (≈-sym (assoc _ _ _)) (η-fam Q γ j))) ⟩
            alg .famf .transf (γ , project-idx-open Q γ j) ∘ pair p₁ (project-fam-open Q γ j)
          ∎ where open ≈-Reasoning isEquiv
        η-fam (P Poly.+ R) γ (inj₁ x) =
          isEquiv .trans
            (∘-cong (∘-cong ≈-refl (isEquiv .trans id-left id-left)) ≈-refl) (η-fam P γ x)
        η-fam (P Poly.+ R) γ (inj₂ z) =
          isEquiv .trans
            (∘-cong (∘-cong ≈-refl (isEquiv .trans id-left id-left)) ≈-refl) (η-fam R γ z)
        η-fam (P Poly.× R) γ (x , z) = begin
            (prod-m (poly-obj P y .fam .subst _) (poly-obj R y .fam .subst _) ∘
             pair (id _ ∘ (poly-fmor P h .famf .transf (γ , unembed-idx P x) ∘ pair p₁ (id _ ∘ (p₁ ∘ p₂))))
                  (id _ ∘ (poly-fmor R h .famf .transf (γ , unembed-idx R z) ∘ pair p₁ (id _ ∘ (p₂ ∘ p₂))))) ∘
             pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
          ≈⟨ ∘-cong (∘-cong ≈-refl
                (pair-cong (isEquiv .trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left)))
                           (isEquiv .trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left))))) ≈-refl ⟩
            (prod-m (poly-obj P y .fam .subst _) (poly-obj R y .fam .subst _) ∘
             pair (poly-fmor P h .famf .transf (γ , unembed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                  (poly-fmor R h .famf .transf (γ , unembed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘
            pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
          ≈⟨ ∘-cong (pair-compose _ _ _ _) ≈-refl ⟩
            pair (poly-obj P y .fam .subst _ ∘
                    (poly-fmor P h .famf .transf (γ , unembed-idx P x) ∘ pair p₁ (p₁ ∘ p₂)))
                 (poly-obj R y .fam .subst _ ∘
                    (poly-fmor R h .famf .transf (γ , unembed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘
            pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
          ≈⟨ pair-natural _ _ _ ⟩
            pair ((poly-obj P y .fam .subst _ ∘
                     (poly-fmor P h .famf .transf (γ , unembed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))) ∘
                  pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂))
                 ((poly-obj R y .fam .subst _ ∘
                     (poly-fmor R h .famf .transf (γ , unembed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘
                  pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂))
          ≈⟨ pair-cong (bridge P x (p₁ ∘ p₂) (p₁ ∘ p₂) merge-pair-P fold-pair-P)
                       (bridge R z (p₂ ∘ p₂) (p₂ ∘ p₂) merge-pair-R fold-pair-R) ⟩
            pair (project-fam-open P γ x ∘ pair p₁ (p₁ ∘ p₂)) (project-fam-open R γ z ∘ pair p₁ (p₂ ∘ p₂))
          ∎ where
            merge-pair-P : pair {prod (Γ .fam .fm γ) _} p₁ (p₁ ∘ p₂)
                           ∘ pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
                         ≈ pair p₁ (unembed-fam P x ∘ (p₁ ∘ p₂))
            merge-pair-P =
              begin
                pair p₁ (p₁ ∘ p₂) ∘ pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
              ≈⟨ pair-natural _ _ _ ⟩
                pair (p₁ ∘ pair p₁ _) ((p₁ ∘ p₂) ∘ pair p₁ _)
              ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
                pair p₁ (p₁ ∘ (p₂ ∘ pair p₁ _))
              ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
                pair p₁ (p₁ ∘ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂))
              ≈⟨ pair-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
                pair p₁ ((p₁ ∘ prod-m (unembed-fam P x) (unembed-fam R z)) ∘ p₂)
              ≈⟨ pair-cong ≈-refl (∘-cong (pair-p₁ _ _) ≈-refl) ⟩
                pair p₁ ((unembed-fam P x ∘ p₁) ∘ p₂)
              ≈⟨ pair-cong ≈-refl (assoc _ _ _) ⟩
                pair p₁ (unembed-fam P x ∘ (p₁ ∘ p₂))
              ∎ where open ≈-Reasoning isEquiv

            fold-pair-P : pair {prod (Γ .fam .fm γ) (WFam-fm P x)} p₁ (unembed-fam P x ∘ p₂)
                          ∘ pair {prod (Γ .fam .fm γ) (prod (WFam-fm P x) (WFam-fm R z))} p₁ (p₁ ∘ p₂)
                        ≈ pair p₁ (unembed-fam P x ∘ (p₁ ∘ p₂))
            fold-pair-P = begin
                pair p₁ (unembed-fam P x ∘ p₂) ∘ pair p₁ (p₁ ∘ p₂)
              ≈⟨ pair-natural _ _ _ ⟩
                pair (p₁ ∘ pair p₁ _) ((unembed-fam P x ∘ p₂) ∘ pair p₁ _)
              ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
                pair p₁ (unembed-fam P x ∘ (p₂ ∘ pair p₁ _))
              ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
                pair p₁ (unembed-fam P x ∘ (p₁ ∘ p₂))
              ∎ where open ≈-Reasoning isEquiv

            merge-pair-R : pair {prod (Γ .fam .fm γ) _} p₁ (p₂ ∘ p₂) ∘
                           pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
                         ≈ pair p₁ (unembed-fam R z ∘ (p₂ ∘ p₂))
            merge-pair-R = begin
                pair p₁ (p₂ ∘ p₂) ∘ pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
              ≈⟨ pair-natural _ _ _ ⟩
                pair (p₁ ∘ pair p₁ _) ((p₂ ∘ p₂) ∘ pair p₁ _)
              ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
                pair p₁ (p₂ ∘ (p₂ ∘ pair p₁ _))
              ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
                pair p₁ (p₂ ∘ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂))
              ≈⟨ pair-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
                pair p₁ ((p₂ ∘ prod-m (unembed-fam P x) (unembed-fam R z)) ∘ p₂)
              ≈⟨ pair-cong ≈-refl (∘-cong (pair-p₂ _ _) ≈-refl) ⟩
                pair p₁ ((unembed-fam R z ∘ p₂) ∘ p₂)
              ≈⟨ pair-cong ≈-refl (assoc _ _ _) ⟩
                pair p₁ (unembed-fam R z ∘ (p₂ ∘ p₂))
              ∎ where open ≈-Reasoning isEquiv

            fold-pair-R : pair {prod (Γ .fam .fm γ) (WFam-fm R z)} p₁ (unembed-fam R z ∘ p₂)
                          ∘ pair {prod (Γ .fam .fm γ) (prod (WFam-fm P x) (WFam-fm R z))} p₁ (p₂ ∘ p₂)
                        ≈ pair p₁ (unembed-fam R z ∘ (p₂ ∘ p₂))
            fold-pair-R = begin
                pair p₁ (unembed-fam R z ∘ p₂) ∘ pair p₁ (p₂ ∘ p₂)
              ≈⟨ pair-natural _ _ _ ⟩
                pair (p₁ ∘ pair p₁ _) ((unembed-fam R z ∘ p₂) ∘ pair p₁ _)
              ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
                pair p₁ (unembed-fam R z ∘ (p₂ ∘ pair p₁ _))
              ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
                pair p₁ (unembed-fam R z ∘ (p₂ ∘ p₂))
              ∎ where open ≈-Reasoning isEquiv

            bridge : (W : Poly cat) (j : WIdx poly (idx-of W))
                     (π-poly : prod (Γ .fam .fm γ)
                                    (prod (poly-obj P WObj .fam .fm (unembed-idx P x))
                                          (poly-obj R WObj .fam .fm (unembed-idx R z)))
                               ⇒ poly-obj W WObj .fam .fm (unembed-idx W j))
                     (π-WFam : prod (Γ .fam .fm γ) (prod (WFam-fm P x) (WFam-fm R z)) ⇒ WFam-fm W j)
                     (merge : pair p₁ π-poly ∘ pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
                              ≈ pair p₁ (unembed-fam W j ∘ π-WFam))
                     (fold : pair p₁ (unembed-fam W j ∘ p₂) ∘ pair p₁ π-WFam
                             ≈ pair p₁ (unembed-fam W j ∘ π-WFam)) →
                     (poly-obj W y .fam .subst _ ∘
                       (poly-fmor W h .famf .transf (γ , unembed-idx W j) ∘ pair p₁ π-poly)) ∘
                     pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
                   ≈ project-fam-open W γ j ∘ pair p₁ π-WFam
            bridge W j π-poly π-WFam merge fold = begin
                (poly-obj W y .fam .subst _ ∘
                   (poly-fmor W h .famf .transf (γ , unembed-idx W j) ∘ pair p₁ π-poly)) ∘
                pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
              ≈⟨ assoc _ _ _ ⟩
                poly-obj W y .fam .subst _ ∘
                  ((poly-fmor W h .famf .transf (γ , unembed-idx W j) ∘ pair p₁ π-poly) ∘
                   pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂))
              ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
                poly-obj W y .fam .subst _ ∘
                  (poly-fmor W h .famf .transf (γ , unembed-idx W j) ∘
                   (pair p₁ π-poly ∘ pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)))
              ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl merge) ⟩
                poly-obj W y .fam .subst _ ∘
                  (poly-fmor W h .famf .transf (γ , unembed-idx W j) ∘ pair p₁ (unembed-fam W j ∘ π-WFam))
              ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl fold) ⟩
                poly-obj W y .fam .subst _ ∘
                  (poly-fmor W h .famf .transf (γ , unembed-idx W j) ∘
                   (pair p₁ (unembed-fam W j ∘ p₂) ∘ pair p₁ π-WFam))
              ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
                poly-obj W y .fam .subst _ ∘
                  ((poly-fmor W h .famf .transf (γ , unembed-idx W j) ∘ pair p₁ (unembed-fam W j ∘ p₂)) ∘
                   pair p₁ π-WFam)
              ≈˘⟨ assoc _ _ _ ⟩
                (poly-obj W y .fam .subst _ ∘
                   (poly-fmor W h .famf .transf (γ , unembed-idx W j) ∘ pair p₁ (unembed-fam W j ∘ p₂))) ∘
                pair p₁ π-WFam
              ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
                ((poly-obj W y .fam .subst _ ∘
                    poly-fmor W h .famf .transf (γ , unembed-idx W j)) ∘ pair p₁ (unembed-fam W j ∘ p₂)) ∘
                pair p₁ π-WFam
              ≈⟨ ∘-cong (η-fam W γ j) ≈-refl ⟩
                project-fam-open W γ j ∘ pair p₁ π-WFam
              ∎ where open ≈-Reasoning isEquiv

            open ≈-Reasoning isEquiv

  hasMu : HasMu
  hasMu .HasMu.μ Q          = W-types.WObj Q
  hasMu .HasMu.inF Q        = W-types.inF-mor Q
  hasMu .HasMu.⦅_⦆ {Γ} {Q}  = W-types.Open.fold-open Q
  hasMu .HasMu.⦅⦆-β {Γ} {Q} alg ._≃_.idxf-eq .PS._≃m_.func-eq {γ₁ , i₁} {γ₂ , i₂} (γ₁≈γ₂ , i₁≈i₂) =
    alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , β-idx Q γ₁≈γ₂ i₁≈i₂)
    where open W-types Q; open Open alg
  hasMu .HasMu.⦅⦆-β {Γ} {Q} {y} alg ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , i} = begin
      y .fam .subst _ ∘ (id _ ∘ (alg .famf .transf (γ , project-idx-open Q γ (embed-idx Q i)) ∘
          pair p₁ (project-fam-open Q γ (embed-idx Q i)) ∘ pair p₁ (id _ ∘ (embed-fam Q i ∘ p₂))))
    ≈⟨ ∘-cong ≈-refl id-left ⟩
      y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx-open Q γ (embed-idx Q i)) ∘
          pair p₁ (project-fam-open Q γ (embed-idx Q i)) ∘ pair p₁ (id _ ∘ (embed-fam Q i ∘ p₂)))
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx-open Q γ (embed-idx Q i)) ∘
          (pair p₁ (project-fam-open Q γ (embed-idx Q i)) ∘ pair p₁ (id _ ∘ (embed-fam Q i ∘ p₂))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl
        (≈-trans (pair-natural _ _ _)
                 (pair-cong (pair-p₁ _ _) (∘-cong ≈-refl (pair-cong ≈-refl id-left))))) ⟩
      y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx-open Q γ (embed-idx Q i)) ∘
          pair p₁ (project-fam-open Q γ (embed-idx Q i) ∘ pair p₁ (embed-fam Q i ∘ p₂)))
    ≈⟨ ≈-sym (assoc _ _ _) ⟩
      (y .fam .subst _ ∘ alg .famf .transf (γ , project-idx-open Q γ (embed-idx Q i))) ∘
          pair p₁ (project-fam-open Q γ (embed-idx Q i) ∘ pair p₁ (embed-fam Q i ∘ p₂))
    ≈⟨ ∘-cong
        (≈-sym (alg .famf .natural (
          Setoid.isEquivalence (Γ .idx) .IsEquivalence.refl ,
          β-idx Q (Setoid.isEquivalence (Γ .idx) .IsEquivalence.refl)
                  (Setoid.isEquivalence (poly-obj Q WObj .idx) .IsEquivalence.refl)
        )))
        ≈-refl ⟩
      (alg .famf .transf (γ , poly-fmor Q fold-open .idxf .PS._⇒_.func (γ , i)) ∘
          pair (Γ .fam .subst _ ∘ p₁) (poly-obj Q y .fam .subst _ ∘ p₂)) ∘
          pair p₁ (project-fam-open Q γ (embed-idx Q i) ∘ pair p₁ (embed-fam Q i ∘ p₂))
    ≈⟨ assoc _ _ _ ⟩
      alg .famf .transf (γ , poly-fmor Q fold-open .idxf .PS._⇒_.func (γ , i)) ∘
          (pair (Γ .fam .subst _ ∘ p₁) (poly-obj Q y .fam .subst _ ∘ p₂) ∘
          pair p₁ (project-fam-open Q γ (embed-idx Q i) ∘ pair p₁ (embed-fam Q i ∘ p₂)))
    ≈⟨ ∘-cong ≈-refl (pair-compose _ _ _ _) ⟩
      alg .famf .transf (γ , poly-fmor Q fold-open .idxf .PS._⇒_.func (γ , i)) ∘
          pair (Γ .fam .subst _ ∘ p₁)
               (poly-obj Q y .fam .subst _ ∘
                  (project-fam-open Q γ (embed-idx Q i) ∘ pair p₁ (embed-fam Q i ∘ p₂)))
    ≈⟨ ∘-cong ≈-refl (pair-cong
                (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left)
                (≈-trans (≈-sym (assoc _ _ _)) (β-fam Q γ i))) ⟩
      alg .famf .transf (γ , poly-fmor Q fold-open .idxf .PS._⇒_.func (γ , i)) ∘
          pair p₁ (poly-fmor Q fold-open .famf .transf (γ , i))
    ≈⟨ ≈-sym id-left ⟩
      id _ ∘ (alg .famf .transf (γ , poly-fmor Q fold-open .idxf .PS._⇒_.func (γ , i)) ∘
          pair p₁ (poly-fmor Q fold-open .famf .transf (γ , i)))
    ∎ where
      open W-types Q; open Open alg; open ≈-Reasoning isEquiv
  hasMu .HasMu.⦅⦆-η {Γ} {Q} {y} alg h h-step ._≃_.idxf-eq .PS._≃m_.func-eq
                                            {γ₁ , inF i₁} {γ₂ , inF i₂} (γ₁≈γ₂ , t₁≈t₂) =
    η-idx h h-step Poly.var γ₁≈γ₂ {inF i₁} {inF i₂} t₁≈t₂
    where open W-types Q; open Open alg
  hasMu .HasMu.⦅⦆-η {Γ} {Q} {y} alg h h-step ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , inF i} =
    isEquiv .trans
      (isEquiv .trans (≈-sym id-right)
                      (≈-sym (∘-cong ≈-refl (isEquiv .trans (pair-cong ≈-refl id-left) pair-ext0))))
      (η-fam h h-step Poly.var γ (inF i))
    where open W-types Q; open Open alg

{- ------------------------------------------------------------------------------
-- WFam-μ: HasMu-μPoly instance for the Fam construction. Commented out alongside μPoly.
module WFam-μ {o m e} (os es : _) {𝒟 : Category o m e}
              (T : HasTerminal 𝒟) (P : HasProducts 𝒟) (L : StrongPointedFunctor P) where
  open Category 𝒟
  open IsEquivalence
  open HasTerminal
  open HasProducts P
  open fam.CategoryOfFamilies os es 𝒟
  open products P  -- Fam-level products
  open _⇒f_
  open Sem (terminal T) products strongCoproducts
  open StrongPointedFunctor L
  open μPoly-Sem (fam-functor.FamF os es F)

  module W-types-μ (Q : μPoly cat) where
    open Obj
    open Mor
    open Fam

    idx-of-μ : μPoly cat → IdxPoly
    idx-of-μ μPoly.one        = one
    idx-of-μ (μPoly.const A)  = param (A .idx)
    idx-of-μ μPoly.var        = var
    idx-of-μ (P μPoly.+ Q)    = idx-of-μ P + idx-of-μ Q
    idx-of-μ (P μPoly.× Q)    = idx-of-μ P × idx-of-μ Q
    idx-of-μ (μPoly.Mon P)    = idx-of-μ P   -- Mon doesn't change idx

    poly : IdxPoly
    poly = idx-of-μ Q

    WFam-fm : (P : μPoly cat) → WIdx poly (idx-of-μ P) → obj
    WFam-fm μPoly.one          _        = T .witness
    WFam-fm (μPoly.const A)    a        = A .fam .fm a
    WFam-fm μPoly.var          (inF i)  = WFam-fm Q i
    WFam-fm (P μPoly.+ Q)      (inj₁ x) = WFam-fm P x
    WFam-fm (P μPoly.+ Q)      (inj₂ y) = WFam-fm Q y
    WFam-fm (P μPoly.× Q)      (x , y)  = prod (WFam-fm P x) (WFam-fm Q y)
    WFam-fm (μPoly.Mon P)      i        = fobj (WFam-fm P i)

    WFam-subst : (P : μPoly cat) → ∀ {x y} → WIdx-≈ poly (idx-of-μ P) x y → WFam-fm P x ⇒ WFam-fm P y
    WFam-subst μPoly.one _ = id _
    WFam-subst (μPoly.const A) {x} {y} x≈y = A .fam .subst x≈y
    WFam-subst μPoly.var {inF i₁} {inF i₂} i₁≈i₂ = WFam-subst Q i₁≈i₂
    WFam-subst (P μPoly.+ Q) {inj₁ _} {inj₁ _} x≈y = WFam-subst P x≈y
    WFam-subst (P μPoly.+ Q) {inj₂ _} {inj₂ _} x≈y = WFam-subst Q x≈y
    WFam-subst (P μPoly.+ Q) {inj₁ _} {inj₂ _} ()
    WFam-subst (P μPoly.+ Q) {inj₂ _} {inj₁ _} ()
    WFam-subst (P μPoly.× Q) {_ , _} {_ , _} (x₁≈y₁ , x₂≈y₂) =
      prod-m (WFam-subst P x₁≈y₁) (WFam-subst Q x₂≈y₂)
    WFam-subst (μPoly.Mon P) x≈y = fmor (WFam-subst P x≈y)

    WFam-refl* : (P : μPoly cat) → ∀ {x} →
                    WFam-subst P (WIdx-≈-refl poly (idx-of-μ P) {x}) ≈ id _
    WFam-refl* μPoly.one         = isEquiv .refl
    WFam-refl* (μPoly.const A) {x} = A .fam .refl*
    WFam-refl* μPoly.var {inF i} = WFam-refl* Q {i}
    WFam-refl* (P μPoly.+ Q) {inj₁ x} = WFam-refl* P {x}
    WFam-refl* (P μPoly.+ Q) {inj₂ y} = WFam-refl* Q {y}
    WFam-refl* (P μPoly.× Q) {x , y}  =
      begin
        prod-m (WFam-subst P _) (WFam-subst Q _)
      ≈⟨ prod-m-cong (WFam-refl* P {x}) (WFam-refl* Q {y}) ⟩
        prod-m (id _) (id _)
      ≈⟨ prod-m-id ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv
    WFam-refl* (μPoly.Mon P) {x} =
      begin
        fmor (WFam-subst P _)
      ≈⟨ fmor-cong (WFam-refl* P {x}) ⟩
        fmor (id _)
      ≈⟨ fmor-id ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv

    WFam-trans* : (P : μPoly cat) → ∀ {x y z}
                     (y≈z : WIdx-≈ poly (idx-of-μ P) y z) (x≈y : WIdx-≈ poly (idx-of-μ P) x y) →
                     WFam-subst P (WIdx-≈-trans poly (idx-of-μ P) x≈y y≈z) ≈
                     (WFam-subst P y≈z ∘ WFam-subst P x≈y)
    WFam-trans* μPoly.one _ _ = isEquiv .sym id-left
    WFam-trans* (μPoly.const A) y≈z x≈y = A .fam .trans* y≈z x≈y
    WFam-trans* μPoly.var {inF _} {inF _} {inF _} y≈z x≈y =
      WFam-trans* Q y≈z x≈y
    WFam-trans* (P μPoly.+ Q) {inj₁ _} {inj₁ _} {inj₁ _} y≈z x≈y = WFam-trans* P y≈z x≈y
    WFam-trans* (P μPoly.+ Q) {inj₂ _} {inj₂ _} {inj₂ _} y≈z x≈y = WFam-trans* Q y≈z x≈y
    WFam-trans* (P μPoly.× Q) {_ , _} {_ , _} {_ , _} (y₁≈z₁ , y₂≈z₂) (x₁≈y₁ , x₂≈y₂) =
      begin
        prod-m (WFam-subst P _) (WFam-subst Q _)
      ≈⟨ prod-m-cong (WFam-trans* P y₁≈z₁ x₁≈y₁) (WFam-trans* Q y₂≈z₂ x₂≈y₂) ⟩
        prod-m (WFam-subst P y₁≈z₁ ∘ WFam-subst P x₁≈y₁) (WFam-subst Q y₂≈z₂ ∘ WFam-subst Q x₂≈y₂)
      ≈⟨ pair-functorial _ _ _ _ ⟩
        prod-m (WFam-subst P y₁≈z₁) (WFam-subst Q y₂≈z₂) ∘ prod-m (WFam-subst P x₁≈y₁) (WFam-subst Q x₂≈y₂)
      ∎ where open ≈-Reasoning isEquiv
    WFam-trans* (μPoly.Mon P) y≈z x≈y =
      begin
        fmor (WFam-subst P _)
      ≈⟨ fmor-cong (WFam-trans* P y≈z x≈y) ⟩
        fmor (WFam-subst P y≈z ∘ WFam-subst P x≈y)
      ≈⟨ fmor-comp _ _ ⟩
        fmor (WFam-subst P y≈z) ∘ fmor (WFam-subst P x≈y)
      ∎ where open ≈-Reasoning isEquiv

    WFam : Fam (WSetoid poly) 𝒟
    WFam .fm (inF i)                              = WFam-fm Q i
    WFam .subst {inF _} {inF _} i₁≈i₂             = WFam-subst Q i₁≈i₂
    WFam .refl* {inF _}                           = WFam-refl* Q
    WFam .trans* {inF _} {inF _} {inF _} y≈z x≈y  = WFam-trans* Q y≈z x≈y

    WObj : Obj
    WObj .idx = WSetoid poly
    WObj .fam = WFam

    embed-idx : (P : μPoly cat) → μPoly-obj P WObj .idx .Carrier → WIdx poly (idx-of-μ P)
    embed-idx μPoly.one         (lift tt)  = lift tt
    embed-idx (μPoly.const A)   a          = a
    embed-idx μPoly.var         w          = w
    embed-idx (P μPoly.+ Q)     (inj₁ x)   = inj₁ (embed-idx P x)
    embed-idx (P μPoly.+ Q)     (inj₂ y)   = inj₂ (embed-idx Q y)
    embed-idx (P μPoly.× Q)     (x , y)    = (embed-idx P x , embed-idx Q y)
    embed-idx (μPoly.Mon P)     i          = embed-idx P i   -- Mon preserves idx

    embed-≈ : (P : μPoly cat) → ∀ {x y} →
              μPoly-obj P WObj .idx ._≈s_ x y → WIdx-≈ poly (idx-of-μ P) (embed-idx P x) (embed-idx P y)
    embed-≈ μPoly.one _                                 = tt
    embed-≈ (μPoly.const A) x≈y                         = x≈y
    embed-≈ μPoly.var x≈y                               = x≈y
    embed-≈ (P μPoly.+ Q) {inj₁ _} {inj₁ _} x≈y         = embed-≈ P x≈y
    embed-≈ (P μPoly.+ Q) {inj₂ _} {inj₂ _} x≈y         = embed-≈ Q x≈y
    embed-≈ (P μPoly.× Q) {_ , _} {_ , _} (x₁≈y₁ , x₂≈y₂) = (embed-≈ P x₁≈y₁ , embed-≈ Q x₂≈y₂)
    embed-≈ (μPoly.Mon P)  x≈y                          = embed-≈ P x≈y

    embed-fam : (P : μPoly cat) (i : μPoly-obj P WObj .idx .Carrier) →
                μPoly-obj P WObj .fam .fm i ⇒ WFam-fm P (embed-idx P i)
    embed-fam μPoly.one         (lift tt)  = id _
    embed-fam (μPoly.const A)   a          = id _
    embed-fam μPoly.var         (inF _)    = id _
    embed-fam (P μPoly.+ Q)     (inj₁ x)   = embed-fam P x
    embed-fam (P μPoly.+ Q)     (inj₂ y)   = embed-fam Q y
    embed-fam (P μPoly.× Q)     (x , y)    = prod-m (embed-fam P x) (embed-fam Q y)
    embed-fam (μPoly.Mon P)     i          = fmor (embed-fam P i)

    embed-fam-natural : (P : μPoly cat) → ∀ {x₁ x₂} (x₁≈x₂ : μPoly-obj P WObj .idx ._≈s_ x₁ x₂) →
                        (embed-fam P x₂ ∘ μPoly-obj P WObj .fam .subst x₁≈x₂) ≈
                        (WFam-subst P (embed-≈ P x₁≈x₂) ∘ embed-fam P x₁)
    embed-fam-natural μPoly.one _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural (μPoly.const A) _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural μPoly.var {inF _} {inF _} _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural (P μPoly.+ Q) {inj₁ _} {inj₁ _} x₁≈x₂ = embed-fam-natural P x₁≈x₂
    embed-fam-natural (P μPoly.+ Q) {inj₂ _} {inj₂ _} x₁≈x₂ = embed-fam-natural Q x₁≈x₂
    embed-fam-natural (P μPoly.× Q) {x₁ , y₁} {x₂ , y₂} (x₁≈x₂ , y₁≈y₂) =
      begin
        prod-m (embed-fam P x₂) (embed-fam Q y₂) ∘ prod-m _ _
      ≈⟨ ≈-sym (pair-functorial _ _ _ _) ⟩
        prod-m (embed-fam P x₂ ∘ _) (embed-fam Q y₂ ∘ _)
      ≈⟨ prod-m-cong (embed-fam-natural P x₁≈x₂) (embed-fam-natural Q y₁≈y₂) ⟩
        prod-m (WFam-subst P (embed-≈ P x₁≈x₂) ∘ embed-fam P x₁) (WFam-subst Q (embed-≈ Q y₁≈y₂) ∘ embed-fam Q y₁)
      ≈⟨ pair-functorial _ _ _ _ ⟩
        prod-m (WFam-subst P (embed-≈ P x₁≈x₂)) (WFam-subst Q (embed-≈ Q y₁≈y₂)) ∘ prod-m (embed-fam P x₁) (embed-fam Q y₁)
      ∎ where open ≈-Reasoning isEquiv
    embed-fam-natural (μPoly.Mon P) {x₁} {x₂} x₁≈x₂ =
      begin
        fmor (embed-fam P x₂) ∘ fmor _
      ≈⟨ ≈-sym (fmor-comp _ _) ⟩
        fmor (embed-fam P x₂ ∘ _)
      ≈⟨ fmor-cong (embed-fam-natural P x₁≈x₂) ⟩
        fmor (WFam-subst P (embed-≈ P x₁≈x₂) ∘ embed-fam P x₁)
      ≈⟨ fmor-comp _ _ ⟩
        fmor (WFam-subst P (embed-≈ P x₁≈x₂)) ∘ fmor (embed-fam P x₁)
      ∎ where open ≈-Reasoning isEquiv

    inF-mor : Mor (μPoly-obj Q WObj) WObj
    inF-mor .idxf .PS._⇒_.func i            = inF (embed-idx Q i)
    inF-mor .idxf .PS._⇒_.func-resp-≈ x≈y   = embed-≈ Q x≈y
    inF-mor .famf .transf i                 = embed-fam Q i
    inF-mor .famf .natural x₁≈x₂            = embed-fam-natural Q x₁≈x₂

    module _ {y : Obj} (alg : Mor (μPoly-obj Q y) y) where

      project-idx : (P : μPoly cat) → WIdx poly (idx-of-μ P) → μPoly-obj P y .idx .Carrier
      project-idx μPoly.one       _         = lift tt
      project-idx (μPoly.const A) a         = a
      project-idx μPoly.var       (inF i)   = alg .idxf .PS._⇒_.func (project-idx Q i)
      project-idx (P μPoly.+ Q)   (inj₁ x)  = inj₁ (project-idx P x)
      project-idx (P μPoly.+ Q)   (inj₂ z)  = inj₂ (project-idx Q z)
      project-idx (P μPoly.× Q)   (x , z)   = (project-idx P x , project-idx Q z)
      project-idx (μPoly.Mon P)   i         = project-idx P i

      project-≈ : (P : μPoly cat) → ∀ {x z} → WIdx-≈ poly (idx-of-μ P) x z →
                  μPoly-obj P y .idx ._≈s_ (project-idx P x) (project-idx P z)
      project-≈ μPoly.one _ = tt
      project-≈ (μPoly.const A) x≈z = x≈z
      project-≈ μPoly.var {inF _} {inF _} x≈z =
        alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q x≈z)
      project-≈ (P μPoly.+ Q) {inj₁ _} {inj₁ _} x≈z = project-≈ P x≈z
      project-≈ (P μPoly.+ Q) {inj₂ _} {inj₂ _} x≈z = project-≈ Q x≈z
      project-≈ (P μPoly.× Q) {_ , _} {_ , _} (x₁≈z₁ , x₂≈z₂) = (project-≈ P x₁≈z₁ , project-≈ Q x₂≈z₂)
      project-≈ (μPoly.Mon P)   x≈z = project-≈ P x≈z

      project-fam : (P : μPoly cat) (i : WIdx poly (idx-of-μ P)) →
                    WFam-fm P i ⇒ μPoly-obj P y .fam .fm (project-idx P i)
      project-fam μPoly.one _            = id _
      project-fam (μPoly.const A) a      = id _
      project-fam μPoly.var (inF i)      = alg .famf .transf (project-idx Q i) ∘ project-fam Q i
      project-fam (P μPoly.+ Q) (inj₁ x) = project-fam P x
      project-fam (P μPoly.+ Q) (inj₂ z) = project-fam Q z
      project-fam (P μPoly.× Q) (x , z)  = prod-m (project-fam P x) (project-fam Q z)
      project-fam (μPoly.Mon P) i        = fmor (project-fam P i)

      project-fam-natural : (P : μPoly cat) → ∀ {x z} (x≈z : WIdx-≈ poly (idx-of-μ P) x z) →
                            (project-fam P z ∘ WFam-subst P x≈z) ≈
                            (μPoly-obj P y .fam .subst (project-≈ P x≈z) ∘ project-fam P x)
      project-fam-natural μPoly.one _ = isEquiv .trans id-left (≈-sym id-right)
      project-fam-natural (μPoly.const A) _ = isEquiv .trans id-left (≈-sym id-right)
      project-fam-natural μPoly.var {inF i₁} {inF i₂} i₁≈i₂ =
        begin
          (alg .famf .transf (project-idx Q i₂) ∘ project-fam Q i₂) ∘ WFam-subst Q i₁≈i₂
        ≈⟨ assoc _ _ _ ⟩
          alg .famf .transf (project-idx Q i₂) ∘ (project-fam Q i₂ ∘ WFam-subst Q i₁≈i₂)
        ≈⟨ ∘-cong (isEquiv .refl) (project-fam-natural Q i₁≈i₂) ⟩
          alg .famf .transf (project-idx Q i₂) ∘
            (μPoly-obj Q y .fam .subst (project-≈ Q i₁≈i₂) ∘ project-fam Q i₁)
        ≈⟨ ≈-sym (assoc _ _ _) ⟩
          (alg .famf .transf (project-idx Q i₂) ∘
            μPoly-obj Q y .fam .subst (project-≈ Q i₁≈i₂)) ∘ project-fam Q i₁
        ≈⟨ ∘-cong (alg .famf .natural (project-≈ Q i₁≈i₂)) (isEquiv .refl) ⟩
          (y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q i₁≈i₂)) ∘ alg .famf .transf (project-idx Q i₁)) ∘ project-fam Q i₁
        ≈⟨ assoc _ _ _ ⟩
          y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q i₁≈i₂)) ∘
            (alg .famf .transf (project-idx Q i₁) ∘ project-fam Q i₁)
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural (P μPoly.+ Q) {inj₁ _} {inj₁ _} x≈z = project-fam-natural P x≈z
      project-fam-natural (P μPoly.+ Q) {inj₂ _} {inj₂ _} x≈z = project-fam-natural Q x≈z
      project-fam-natural (P μPoly.× Q) {x₁ , z₁} {x₂ , z₂} (x₁≈x₂ , z₁≈z₂) =
        begin
          prod-m (project-fam P x₂) (project-fam Q z₂) ∘ prod-m _ _
        ≈⟨ ≈-sym (pair-functorial _ _ _ _) ⟩
          prod-m (project-fam P x₂ ∘ _) (project-fam Q z₂ ∘ _)
        ≈⟨ prod-m-cong (project-fam-natural P x₁≈x₂) (project-fam-natural Q z₁≈z₂) ⟩
          prod-m (_ ∘ project-fam P x₁) (_ ∘ project-fam Q z₁)
        ≈⟨ pair-functorial _ _ _ _ ⟩
          prod-m _ _ ∘ prod-m (project-fam P x₁) (project-fam Q z₁)
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural (μPoly.Mon P) {x₁} {x₂} x₁≈x₂ =
        begin
          fmor (project-fam P x₂) ∘ fmor _
        ≈⟨ ≈-sym (fmor-comp _ _) ⟩
          fmor (project-fam P x₂ ∘ _)
        ≈⟨ fmor-cong (project-fam-natural P x₁≈x₂) ⟩
          fmor (_ ∘ project-fam P x₁)
        ≈⟨ fmor-comp _ _ ⟩
          fmor _ ∘ fmor (project-fam P x₁)
        ∎ where open ≈-Reasoning isEquiv

      fold : Mor WObj y
      fold .idxf .PS._⇒_.func (inF i)                       = alg .idxf .PS._⇒_.func (project-idx Q i)
      fold .idxf .PS._⇒_.func-resp-≈ {inF _} {inF _} i₁≈i₂  = alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q i₁≈i₂)
      fold .famf .transf (inF i)                            = alg .famf .transf (project-idx Q i) ∘ project-fam Q i
      fold .famf .natural {inF _} {inF _} i₁≈i₂             = project-fam-natural μPoly.var i₁≈i₂

    -- Open (parametric) fold: takes algebra in extended context Γ ⊗ μPoly-obj Q y ⇒ y
    -- and produces Γ ⊗ μ Q ⇒ y. Threads γ through the structural recursion;
    -- right-strength of L handles the Mon case.
    module Open {Γ y : Obj} (alg : Mor (Γ ⊗ μPoly-obj Q y) y) where
      open Obj
      open Mor

      -- idx-level: descend the W-tree, applying alg at var positions with γ fixed.
      project-idx-open : (P : μPoly cat) → Γ .idx .Carrier → WIdx poly (idx-of-μ P) →
                         μPoly-obj P y .idx .Carrier
      project-idx-open μPoly.one       _ _         = lift tt
      project-idx-open (μPoly.const A) _ a         = a
      project-idx-open μPoly.var       γ (inF i)   =
        alg .idxf .PS._⇒_.func (γ , project-idx-open Q γ i)
      project-idx-open (P μPoly.+ R)   γ (inj₁ x)  = inj₁ (project-idx-open P γ x)
      project-idx-open (P μPoly.+ R)   γ (inj₂ z)  = inj₂ (project-idx-open R γ z)
      project-idx-open (P μPoly.× R)   γ (x , z)   = (project-idx-open P γ x , project-idx-open R γ z)
      project-idx-open (μPoly.Mon P)   γ i         = project-idx-open P γ i

      project-≈-open : (P : μPoly cat) → ∀ {γ₁ γ₂ : Γ .idx .Carrier} {x z}
                       (γ₁≈γ₂ : Γ .idx ._≈s_ γ₁ γ₂) (i₁≈i₂ : WIdx-≈ poly (idx-of-μ P) x z) →
                       μPoly-obj P y .idx ._≈s_
                         (project-idx-open P γ₁ x) (project-idx-open P γ₂ z)
      project-≈-open μPoly.one _ _ = tt
      project-≈-open (μPoly.const A) _ x≈z = x≈z
      project-≈-open μPoly.var {γ₁} {γ₂} {inF _} {inF _} γ₁≈γ₂ x≈z =
        alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ x≈z)
      project-≈-open (P μPoly.+ R) {x = inj₁ _} {inj₁ _} γ₁≈γ₂ x≈z = project-≈-open P γ₁≈γ₂ x≈z
      project-≈-open (P μPoly.+ R) {x = inj₂ _} {inj₂ _} γ₁≈γ₂ x≈z = project-≈-open R γ₁≈γ₂ x≈z
      project-≈-open (P μPoly.× R) {x = _ , _} {_ , _} γ₁≈γ₂ (x₁≈z₁ , x₂≈z₂) =
        project-≈-open P γ₁≈γ₂ x₁≈z₁ , project-≈-open R γ₁≈γ₂ x₂≈z₂
      project-≈-open (μPoly.Mon P) γ₁≈γ₂ x≈z = project-≈-open P γ₁≈γ₂ x≈z

      -- fam-level: input is Γ-fibre ⊗ W-fibre; output is the corresponding μPoly-obj y-fibre.
      project-fam-open : (P : μPoly cat) (γ : Γ .idx .Carrier)
                         (i : WIdx poly (idx-of-μ P)) →
                         prod (Γ .fam .fm γ) (WFam-fm P i) ⇒
                         μPoly-obj P y .fam .fm (project-idx-open P γ i)
      project-fam-open μPoly.one         _ _         = HasTerminal.to-terminal T
      project-fam-open (μPoly.const A)   _ _         = p₂
      project-fam-open μPoly.var         γ (inF i)   =
        alg .famf .transf (γ , project-idx-open Q γ i) ∘ pair p₁ (project-fam-open Q γ i)
      project-fam-open (P μPoly.+ R)     γ (inj₁ x)  = project-fam-open P γ x
      project-fam-open (P μPoly.+ R)     γ (inj₂ z)  = project-fam-open R γ z
      project-fam-open (P μPoly.× R)     γ (x , z)   =
        pair (project-fam-open P γ x ∘ pair p₁ (p₁ ∘ p₂))
             (project-fam-open R γ z ∘ pair p₁ (p₂ ∘ p₂))
      project-fam-open (μPoly.Mon P)     γ i         =
        fmor (project-fam-open P γ i) ∘ right-strength

      -- Naturality of project-fam-open w.r.t. γ and W-tree equivalences.
      project-fam-natural-open :
        (P : μPoly cat) → ∀ {γ₁ γ₂ : Γ .idx .Carrier} {x z}
        (γ₁≈γ₂ : Γ .idx ._≈s_ γ₁ γ₂)
        (i₁≈i₂ : WIdx-≈ poly (idx-of-μ P) x z) →
        (project-fam-open P γ₂ z ∘
          prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P i₁≈i₂)) ≈
        (μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ i₁≈i₂) ∘ project-fam-open P γ₁ x)
      project-fam-natural-open μPoly.one _ _ =
        HasTerminal.to-terminal-unique T _ _
      project-fam-natural-open (μPoly.const A) {x = a} {z = b} _ i₁≈i₂ =
        begin
          p₂ ∘ prod-m _ (A .fam .subst i₁≈i₂)
        ≈⟨ pair-p₂ _ _ ⟩
          A .fam .subst i₁≈i₂ ∘ p₂
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural-open μPoly.var {γ₁} {γ₂} {inF i₁} {inF i₂} γ₁≈γ₂ i₁≈i₂ =
        begin
          (alg .famf .transf (γ₂ , _) ∘ pair p₁ (project-fam-open Q γ₂ i₂))
            ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst Q i₁≈i₂)
        ≈⟨ assoc _ _ _ ⟩
          alg .famf .transf (γ₂ , _) ∘
            (pair p₁ (project-fam-open Q γ₂ i₂) ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst Q i₁≈i₂))
        ≈⟨ ∘-cong (isEquiv .refl) (pair-natural _ _ _) ⟩
          alg .famf .transf (γ₂ , _) ∘
            pair (p₁ ∘ prod-m _ _) (project-fam-open Q γ₂ i₂ ∘ prod-m _ _)
        ≈⟨ ∘-cong (isEquiv .refl)
             (pair-cong (pair-p₁ _ _) (project-fam-natural-open Q γ₁≈γ₂ i₁≈i₂)) ⟩
          alg .famf .transf (γ₂ , _) ∘
            pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁)
                 (μPoly-obj Q y .fam .subst (project-≈-open Q γ₁≈γ₂ i₁≈i₂) ∘ project-fam-open Q γ₁ i₁)
        ≈⟨ ≈-sym (∘-cong (isEquiv .refl) (pair-compose _ _ _ _)) ⟩
          alg .famf .transf (γ₂ , _) ∘
            (prod-m (Γ .fam .subst γ₁≈γ₂) (μPoly-obj Q y .fam .subst (project-≈-open Q γ₁≈γ₂ i₁≈i₂))
              ∘ pair p₁ (project-fam-open Q γ₁ i₁))
        ≈⟨ ≈-sym (assoc _ _ _) ⟩
          (alg .famf .transf (γ₂ , _) ∘
            prod-m (Γ .fam .subst γ₁≈γ₂) (μPoly-obj Q y .fam .subst (project-≈-open Q γ₁≈γ₂ i₁≈i₂)))
            ∘ pair p₁ (project-fam-open Q γ₁ i₁)
        ≈⟨ ∘-cong (alg .famf .natural (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂)) (isEquiv .refl) ⟩
          (y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂))
            ∘ alg .famf .transf (γ₁ , _))
            ∘ pair p₁ (project-fam-open Q γ₁ i₁)
        ≈⟨ assoc _ _ _ ⟩
          y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂))
            ∘ (alg .famf .transf (γ₁ , _) ∘ pair p₁ (project-fam-open Q γ₁ i₁))
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural-open (P μPoly.+ R) {x = inj₁ _} {inj₁ _} γ₁≈γ₂ i₁≈i₂ =
        project-fam-natural-open P γ₁≈γ₂ i₁≈i₂
      project-fam-natural-open (P μPoly.+ R) {x = inj₂ _} {inj₂ _} γ₁≈γ₂ i₁≈i₂ =
        project-fam-natural-open R γ₁≈γ₂ i₁≈i₂
      project-fam-natural-open (P μPoly.× R) {γ₁} {γ₂} {x₁ , z₁} {x₂ , z₂} γ₁≈γ₂ (x₁≈x₂ , z₁≈z₂) =
        begin
          pair (project-fam-open P γ₂ x₂ ∘ pair p₁ (p₁ ∘ p₂))
               (project-fam-open R γ₂ z₂ ∘ pair p₁ (p₂ ∘ p₂))
            ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (prod-m (WFam-subst P x₁≈x₂) (WFam-subst R z₁≈z₂))
        ≈⟨ pair-natural _ _ _ ⟩
          pair ((project-fam-open P γ₂ x₂ ∘ pair p₁ (p₁ ∘ p₂)) ∘ prod-m _ _)
               ((project-fam-open R γ₂ z₂ ∘ pair p₁ (p₂ ∘ p₂)) ∘ prod-m _ _)
        ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
          pair (project-fam-open P γ₂ x₂ ∘ (pair p₁ (p₁ ∘ p₂) ∘ prod-m _ _))
               (project-fam-open R γ₂ z₂ ∘ (pair p₁ (p₂ ∘ p₂) ∘ prod-m _ _))
        ≈⟨ pair-cong
             (∘-cong (isEquiv .refl)
               (≈-trans (pair-natural _ _ _)
                 (pair-cong (pair-p₁ _ _)
                   (≈-trans (assoc _ _ _)
                     (≈-trans (∘-cong (isEquiv .refl) (pair-p₂ _ _))
                       (≈-trans (≈-sym (assoc _ _ _))
                         (≈-trans (∘-cong (pair-p₁ _ _) (isEquiv .refl)) (assoc _ _ _))))))))
             (∘-cong (isEquiv .refl)
               (≈-trans (pair-natural _ _ _)
                 (pair-cong (pair-p₁ _ _)
                   (≈-trans (assoc _ _ _)
                     (≈-trans (∘-cong (isEquiv .refl) (pair-p₂ _ _))
                       (≈-trans (≈-sym (assoc _ _ _))
                         (≈-trans (∘-cong (pair-p₂ _ _) (isEquiv .refl)) (assoc _ _ _)))))))) ⟩
          pair (project-fam-open P γ₂ x₂ ∘ pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁) (WFam-subst P x₁≈x₂ ∘ (p₁ ∘ p₂)))
               (project-fam-open R γ₂ z₂ ∘ pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁) (WFam-subst R z₁≈z₂ ∘ (p₂ ∘ p₂)))
        ≈⟨ pair-cong (∘-cong (isEquiv .refl) (≈-sym (pair-compose _ _ _ _)))
                     (∘-cong (isEquiv .refl) (≈-sym (pair-compose _ _ _ _))) ⟩
          pair (project-fam-open P γ₂ x₂ ∘
                 (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P x₁≈x₂) ∘ pair p₁ (p₁ ∘ p₂)))
               (project-fam-open R γ₂ z₂ ∘
                 (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst R z₁≈z₂) ∘ pair p₁ (p₂ ∘ p₂)))
        ≈⟨ pair-cong (≈-sym (assoc _ _ _)) (≈-sym (assoc _ _ _)) ⟩
          pair ((project-fam-open P γ₂ x₂ ∘ prod-m _ _) ∘ pair p₁ (p₁ ∘ p₂))
               ((project-fam-open R γ₂ z₂ ∘ prod-m _ _) ∘ pair p₁ (p₂ ∘ p₂))
        ≈⟨ pair-cong (∘-cong (project-fam-natural-open P γ₁≈γ₂ x₁≈x₂) (isEquiv .refl))
                     (∘-cong (project-fam-natural-open R γ₁≈γ₂ z₁≈z₂) (isEquiv .refl)) ⟩
          pair ((μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ x₁≈x₂) ∘ project-fam-open P γ₁ x₁)
                  ∘ pair p₁ (p₁ ∘ p₂))
               ((μPoly-obj R y .fam .subst (project-≈-open R γ₁≈γ₂ z₁≈z₂) ∘ project-fam-open R γ₁ z₁)
                  ∘ pair p₁ (p₂ ∘ p₂))
        ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
          pair (μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ x₁≈x₂)
                 ∘ (project-fam-open P γ₁ x₁ ∘ pair p₁ (p₁ ∘ p₂)))
               (μPoly-obj R y .fam .subst (project-≈-open R γ₁≈γ₂ z₁≈z₂)
                 ∘ (project-fam-open R γ₁ z₁ ∘ pair p₁ (p₂ ∘ p₂)))
        ≈⟨ ≈-sym (pair-compose _ _ _ _) ⟩
          prod-m (μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ x₁≈x₂))
                 (μPoly-obj R y .fam .subst (project-≈-open R γ₁≈γ₂ z₁≈z₂))
            ∘ pair (project-fam-open P γ₁ x₁ ∘ pair p₁ (p₁ ∘ p₂))
                   (project-fam-open R γ₁ z₁ ∘ pair p₁ (p₂ ∘ p₂))
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural-open (μPoly.Mon P) {γ₁} {γ₂} {x} {z} γ₁≈γ₂ i₁≈i₂ =
        begin
          (fmor (project-fam-open P γ₂ z) ∘ right-strength) ∘
            prod-m (Γ .fam .subst γ₁≈γ₂) (fmor (WFam-subst P i₁≈i₂))
        ≈⟨ assoc _ _ _ ⟩
          fmor (project-fam-open P γ₂ z) ∘
            (right-strength ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (fmor (WFam-subst P i₁≈i₂)))
        ≈⟨ ∘-cong (isEquiv .refl)
             (isEquiv .sym (right-strength-natural _ _)) ⟩
          fmor (project-fam-open P γ₂ z) ∘
            (fmor (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P i₁≈i₂)) ∘ right-strength)
        ≈⟨ isEquiv .sym (assoc _ _ _) ⟩
          (fmor (project-fam-open P γ₂ z) ∘
            fmor (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P i₁≈i₂))) ∘ right-strength
        ≈⟨ ∘-cong (isEquiv .sym (fmor-comp _ _)) (isEquiv .refl) ⟩
          fmor (project-fam-open P γ₂ z ∘
            prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P i₁≈i₂)) ∘ right-strength
        ≈⟨ ∘-cong (fmor-cong (project-fam-natural-open P γ₁≈γ₂ i₁≈i₂)) (isEquiv .refl) ⟩
          fmor (μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ i₁≈i₂) ∘
                project-fam-open P γ₁ x) ∘ right-strength
        ≈⟨ ∘-cong (fmor-comp _ _) (isEquiv .refl) ⟩
          (fmor (μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ i₁≈i₂)) ∘
            fmor (project-fam-open P γ₁ x)) ∘ right-strength
        ≈⟨ assoc _ _ _ ⟩
          fmor (μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ i₁≈i₂)) ∘
            (fmor (project-fam-open P γ₁ x) ∘ right-strength)
        ∎ where open ≈-Reasoning isEquiv

      fold-open : Mor (Γ ⊗ WObj) y
      fold-open .idxf .PS._⇒_.func (γ , inF i) =
        alg .idxf .PS._⇒_.func (γ , project-idx-open Q γ i)
      fold-open .idxf .PS._⇒_.func-resp-≈ {γ₁ , inF _} {γ₂ , inF _} (γ₁≈γ₂ , i₁≈i₂) =
        alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂)
      fold-open .famf .transf (γ , inF i) =
        alg .famf .transf (γ , project-idx-open Q γ i) ∘
          pair p₁ (project-fam-open Q γ i)
      fold-open .famf .natural {γ₁ , inF _} {γ₂ , inF _} (γ₁≈γ₂ , i₁≈i₂) =
        project-fam-natural-open μPoly.var γ₁≈γ₂ i₁≈i₂

  hasMu-μPoly : HasMu-μPoly
  hasMu-μPoly .HasMu-μPoly.μ Q          = W-types-μ.WObj Q
  hasMu-μPoly .HasMu-μPoly.inμ Q        = W-types-μ.inF-mor Q
  hasMu-μPoly .HasMu-μPoly.⦅_⦆ {Γ} {Q}  = W-types-μ.Open.fold-open Q
-}
