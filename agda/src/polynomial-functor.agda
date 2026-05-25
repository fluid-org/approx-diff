{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_; suc; lift)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_; tt; substP)
open import Data.Unit using (tt) renaming (⊤ to 𝟙S)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; cong₂)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts; strong-coproducts→coproducts;
         coKleisli-prod)
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
-- Syntactic polynomial expressions in one variable, with constants drawn from obj 𝒞; they form a category, but
-- but we don't make use of that fact.
data Poly {o m e} (𝒞 : Category o m e) : Set o where
  const : Category.obj 𝒞 → Poly 𝒞
  var  : Poly 𝒞
  _+_  : Poly 𝒞 → Poly 𝒞 → Poly 𝒞
  _×_  : Poly 𝒞 → Poly 𝒞 → Poly 𝒞

Poly-map : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} →
           Functor 𝒞 𝒟 → Poly 𝒞 → Poly 𝒟
Poly-map F (const A)   = const (Functor.fobj F A)
Poly-map F var         = var
Poly-map F (P₁ + P₂)   = Poly-map F P₁ + Poly-map F P₂
Poly-map F (P₁ × P₂)   = Poly-map F P₁ × Poly-map F P₂

-- Two polynomials are iso if they have the same tree shape, with isomorphic objects at const slots.
-- Restrictive (requires matching tree shapes); sufficient for our use (P₁ and P₂ both derived from the
-- same first-order-idx-of Q P-fo, differing only at const slots).
data Poly-iso {o m e} {𝒞 : Category o m e} : Poly 𝒞 → Poly 𝒞 → Set (o ⊔ m ⊔ e) where
  const : ∀ {A B} → Category.Iso 𝒞 A B → Poly-iso (const A) (const B)
  var   : Poly-iso var var
  _+_   : ∀ {P₁ P₂ Q₁ Q₂} → Poly-iso P₁ Q₁ → Poly-iso P₂ Q₂ → Poly-iso (P₁ + P₂) (Q₁ + Q₂)
  _×_   : ∀ {P₁ P₂ Q₁ Q₂} → Poly-iso P₁ Q₁ → Poly-iso P₂ Q₂ → Poly-iso (P₁ × P₂) (Q₁ × Q₂)

module Sem {o m e} {𝒞 : Category o m e}
           (T : HasTerminal 𝒞) (P : HasProducts 𝒞) (SCP : HasStrongCoproducts 𝒞 P) where
  open Category 𝒞
  open HasTerminal T renaming (witness to terminal)
  open HasProducts P
  CP : HasCoproducts 𝒞
  CP = strong-coproducts→coproducts T SCP
  open HasCoproducts CP
  open HasStrongCoproducts SCP using ()
    renaming (copair to s-copair; copair-cong to s-copair-cong;
              copair-in₁ to s-copair-in₁; copair-in₂ to s-copair-in₂;
              copair-ext to s-copair-ext)

  cat-ext : obj → Category o m e
  cat-ext = coKleisli-prod P

  infixl 21 _∘co_
  _∘co_ : ∀ {Γ X Y Z} → (prod Γ Y ⇒ Z) → (prod Γ X ⇒ Y) → (prod Γ X ⇒ Z)
  _∘co_ {Γ} = Category._∘_ (cat-ext Γ)

  module _ {Γ : obj} where
    open Category (cat-ext Γ) public using ()
      renaming (assoc to assoc-co; ∘-cong to ∘-cong-co; ∘-cong₁ to ∘-cong-co₁; ∘-cong₂ to ∘-cong-co₂;
                id-left to id-left-co; id-right to id-right-co)

  module Poly-fun where
    fobj : Poly 𝒞 → obj → obj
    fobj (const A)   _ = A
    fobj var         x = x
    fobj (P + Q)     x = coprod (fobj P x) (fobj Q x)
    fobj (P × Q)     x = prod   (fobj P x) (fobj Q x)

    fmor : ∀ Q {Γ X Y} → (prod Γ X ⇒ Y) → (prod Γ (fobj Q X) ⇒ fobj Q Y)
    fmor (const A)   _ = p₂
    fmor var         h = h
    fmor (Q₁ + Q₂)   h = s-copair (in₁ ∘ fmor Q₁ h) (in₂ ∘ fmor Q₂ h)
    fmor (Q₁ × Q₂)   h = pair (fmor Q₁ h ∘co (p₁ ∘ p₂)) (fmor Q₂ h ∘co (p₂ ∘ p₂))

    fmor-id : ∀ Q {Γ X} → fmor Q {Γ} {X} {X} p₂ ≈ p₂
    fmor-id (const A)   = ≈-refl
    fmor-id var         = ≈-refl
    fmor-id (Q₁ + Q₂)   =
      ≈-trans (s-copair-cong (∘-cong₂ (fmor-id Q₁)) (∘-cong₂ (fmor-id Q₂)))
              (≈-trans (s-copair-cong (≈-sym (pair-p₂ _ _)) (≈-sym (pair-p₂ _ _))) (s-copair-ext p₂))
    fmor-id (Q₁ × Q₂)   =
      ≈-trans (pair-cong (∘-cong₁ (fmor-id Q₁)) (∘-cong₁ (fmor-id Q₂)))
              (≈-trans (pair-cong (pair-p₂ _ _) (pair-p₂ _ _)) (pair-ext p₂))

    fmor-cong : ∀ Q {Γ X Y} {f₁ f₂ : prod Γ X ⇒ Y} → f₁ ≈ f₂ → fmor Q f₁ ≈ fmor Q f₂
    fmor-cong (const A)   _    = ≈-refl
    fmor-cong var         f≈g  = f≈g
    fmor-cong (Q₁ + Q₂)   f≈g  = s-copair-cong (∘-cong₂ (fmor-cong Q₁ f≈g)) (∘-cong₂ (fmor-cong Q₂ f≈g))
    fmor-cong (Q₁ × Q₂)   f≈g  = pair-cong (∘-cong₁ (fmor-cong Q₁ f≈g)) (∘-cong₁ (fmor-cong Q₂ f≈g))

    fmor-comp : ∀ Q {Γ X Y Z} (f : prod Γ Y ⇒ Z) (g : prod Γ X ⇒ Y) →
                fmor Q (f ∘co g) ≈ fmor Q f ∘co (fmor Q g)
    fmor-comp (const A)   f g = ≈-sym id-left-co
    fmor-comp var         f g = ≈-refl
    fmor-comp (Q₁ + Q₂)   f g = begin
        fmor (Q₁ + Q₂) (f ∘co g)
      ≈⟨ s-copair-cong (∘-cong₂ (fmor-comp Q₁ f g)) (∘-cong₂ (fmor-comp Q₂ f g)) ⟩
        s-copair (in₁ ∘ (fmor Q₁ f ∘co fmor Q₁ g)) (in₂ ∘ (fmor Q₂ f ∘co fmor Q₂ g))
      ≈˘⟨ s-copair-cong eq-in₁ eq-in₂ ⟩
        s-copair ((fmor (Q₁ + Q₂) f ∘co fmor (Q₁ + Q₂) g) ∘co (in₁ ∘ p₂))
                 ((fmor (Q₁ + Q₂) f ∘co fmor (Q₁ + Q₂) g) ∘co (in₂ ∘ p₂))
      ≈⟨ s-copair-ext _ ⟩
        fmor (Q₁ + Q₂) f ∘co fmor (Q₁ + Q₂) g
      ∎ where
        eq-in₁ : (fmor (Q₁ + Q₂) f ∘co fmor (Q₁ + Q₂) g) ∘co (in₁ ∘ p₂) ≈ in₁ ∘ (fmor Q₁ f ∘co fmor Q₁ g)
        eq-in₁ = begin
            (fmor (Q₁ + Q₂) f ∘co fmor (Q₁ + Q₂) g) ∘co (in₁ ∘ p₂)
          ≈⟨ assoc-co _ _ _ ⟩
            fmor (Q₁ + Q₂) f ∘co (fmor (Q₁ + Q₂) g ∘co (in₁ ∘ p₂))
          ≈⟨ ∘-cong-co ≈-refl (s-copair-in₁ _ _) ⟩
            fmor (Q₁ + Q₂) f ∘co (in₁ ∘ fmor Q₁ g)
          ≈˘⟨ ∘-cong-co ≈-refl (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))) ⟩
            fmor (Q₁ + Q₂) f ∘co ((in₁ ∘ p₂) ∘co fmor Q₁ g)
          ≈˘⟨ assoc-co _ _ _ ⟩
            (fmor (Q₁ + Q₂) f ∘co (in₁ ∘ p₂)) ∘co fmor Q₁ g
          ≈⟨ ∘-cong-co (s-copair-in₁ _ _) ≈-refl ⟩
            (in₁ ∘ fmor Q₁ f) ∘co fmor Q₁ g
          ≈⟨ assoc _ _ _ ⟩
            in₁ ∘ (fmor Q₁ f ∘co fmor Q₁ g)
          ∎ where open ≈-Reasoning isEquiv
        eq-in₂ : (fmor (Q₁ + Q₂) f ∘co fmor (Q₁ + Q₂) g) ∘co (in₂ ∘ p₂) ≈ in₂ ∘ (fmor Q₂ f ∘co fmor Q₂ g)
        eq-in₂ = begin
            (fmor (Q₁ + Q₂) f ∘co fmor (Q₁ + Q₂) g) ∘co (in₂ ∘ p₂)
          ≈⟨ assoc-co _ _ _ ⟩
            fmor (Q₁ + Q₂) f ∘co (fmor (Q₁ + Q₂) g ∘co (in₂ ∘ p₂))
          ≈⟨ ∘-cong-co ≈-refl (s-copair-in₂ _ _) ⟩
            fmor (Q₁ + Q₂) f ∘co (in₂ ∘ fmor Q₂ g)
          ≈˘⟨ ∘-cong-co ≈-refl (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))) ⟩
            fmor (Q₁ + Q₂) f ∘co ((in₂ ∘ p₂) ∘co fmor Q₂ g)
          ≈˘⟨ assoc-co _ _ _ ⟩
            (fmor (Q₁ + Q₂) f ∘co (in₂ ∘ p₂)) ∘co fmor Q₂ g
          ≈⟨ ∘-cong-co (s-copair-in₂ _ _) ≈-refl ⟩
            (in₂ ∘ fmor Q₂ f) ∘co fmor Q₂ g
          ≈⟨ assoc _ _ _ ⟩
            in₂ ∘ (fmor Q₂ f ∘co fmor Q₂ g)
          ∎ where open ≈-Reasoning isEquiv
        open ≈-Reasoning isEquiv
    fmor-comp (Q₁ × Q₂)   f g = begin
        fmor (Q₁ × Q₂) (f ∘co g)
      ≈⟨ pair-cong (∘-cong₁ (fmor-comp Q₁ f g)) (∘-cong₁ (fmor-comp Q₂ f g)) ⟩
        pair ((fmor Q₁ f ∘co fmor Q₁ g) ∘ pair p₁ (p₁ ∘ p₂))
             ((fmor Q₂ f ∘co fmor Q₂ g) ∘ pair p₁ (p₂ ∘ p₂))
      ≈˘⟨ pair-cong eq-p₁ eq-p₂ ⟩
        pair (p₁ ∘ (fmor (Q₁ × Q₂) f ∘co fmor (Q₁ × Q₂) g))
             (p₂ ∘ (fmor (Q₁ × Q₂) f ∘co fmor (Q₁ × Q₂) g))
      ≈⟨ pair-ext _ ⟩
        fmor (Q₁ × Q₂) f ∘co fmor (Q₁ × Q₂) g
      ∎ where
        eq-p₁ : p₁ ∘ (fmor (Q₁ × Q₂) f ∘co fmor (Q₁ × Q₂) g)
                ≈ (fmor Q₁ f ∘co fmor Q₁ g) ∘ pair p₁ (p₁ ∘ p₂)
        eq-p₁ = begin
            p₁ ∘ (fmor (Q₁ × Q₂) f ∘co fmor (Q₁ × Q₂) g)
          ≈˘⟨ assoc _ _ _ ⟩
            (p₁ ∘ fmor (Q₁ × Q₂) f) ∘ pair p₁ (fmor (Q₁ × Q₂) g)
          ≈⟨ ∘-cong₁ (pair-p₁ _ _) ⟩
            (fmor Q₁ f ∘ pair p₁ (p₁ ∘ p₂)) ∘ pair p₁ (fmor (Q₁ × Q₂) g)
          ≈⟨ assoc _ _ _ ⟩
            fmor Q₁ f ∘ (pair p₁ (p₁ ∘ p₂) ∘ pair p₁ (fmor (Q₁ × Q₂) g))
          ≈⟨ ∘-cong₂ (≈-trans (pair-natural _ _ _)
                              (pair-cong (pair-p₁ _ _)
                                         (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))))) ⟩
            fmor Q₁ f ∘ pair p₁ (p₁ ∘ fmor (Q₁ × Q₂) g)
          ≈⟨ ∘-cong₂ (pair-cong₂ (pair-p₁ _ _)) ⟩
            fmor Q₁ f ∘ pair p₁ (fmor Q₁ g ∘ pair p₁ (p₁ ∘ p₂))
          ≈˘⟨ ∘-cong₂ (≈-trans (pair-natural _ _ _) (pair-cong₁ (pair-p₁ _ _))) ⟩
            fmor Q₁ f ∘ (pair p₁ (fmor Q₁ g) ∘ pair p₁ (p₁ ∘ p₂))
          ≈˘⟨ assoc _ _ _ ⟩
            (fmor Q₁ f ∘co fmor Q₁ g) ∘ pair p₁ (p₁ ∘ p₂)
          ∎ where open ≈-Reasoning isEquiv
        eq-p₂ : p₂ ∘ (fmor (Q₁ × Q₂) f ∘co fmor (Q₁ × Q₂) g)
                ≈ (fmor Q₂ f ∘co fmor Q₂ g) ∘ pair p₁ (p₂ ∘ p₂)
        eq-p₂ = begin
            p₂ ∘ (fmor (Q₁ × Q₂) f ∘co fmor (Q₁ × Q₂) g)
          ≈˘⟨ assoc _ _ _ ⟩
            (p₂ ∘ fmor (Q₁ × Q₂) f) ∘ pair p₁ (fmor (Q₁ × Q₂) g)
          ≈⟨ ∘-cong₁ (pair-p₂ _ _) ⟩
            (fmor Q₂ f ∘ pair p₁ (p₂ ∘ p₂)) ∘ pair p₁ (fmor (Q₁ × Q₂) g)
          ≈⟨ assoc _ _ _ ⟩
            fmor Q₂ f ∘ (pair p₁ (p₂ ∘ p₂) ∘ pair p₁ (fmor (Q₁ × Q₂) g))
          ≈⟨ ∘-cong₂ (≈-trans (pair-natural _ _ _)
                              (pair-cong (pair-p₁ _ _)
                                         (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))))) ⟩
            fmor Q₂ f ∘ pair p₁ (p₂ ∘ fmor (Q₁ × Q₂) g)
          ≈⟨ ∘-cong₂ (pair-cong₂ (pair-p₂ _ _)) ⟩
            fmor Q₂ f ∘ pair p₁ (fmor Q₂ g ∘ pair p₁ (p₂ ∘ p₂))
          ≈˘⟨ ∘-cong₂ (≈-trans (pair-natural _ _ _) (pair-cong₁ (pair-p₁ _ _))) ⟩
            fmor Q₂ f ∘ (pair p₁ (fmor Q₂ g) ∘ pair p₁ (p₂ ∘ p₂))
          ≈˘⟨ assoc _ _ _ ⟩
            (fmor Q₂ f ∘co fmor Q₂ g) ∘ pair p₁ (p₂ ∘ p₂)
          ∎ where open ≈-Reasoning isEquiv
        open ≈-Reasoning isEquiv

    functor : ∀ Q Γ → Functor (cat-ext Γ) (cat-ext Γ)
    functor Q Γ .Functor.fobj      = fobj Q
    functor Q Γ .Functor.fmor      = fmor Q
    functor Q Γ .Functor.fmor-cong = fmor-cong Q
    functor Q Γ .Functor.fmor-id   = fmor-id Q
    functor Q Γ .Functor.fmor-comp = fmor-comp Q

  open Poly-fun public

  record HasMu : Set (o ⊔ m ⊔ e) where
    field
      μ    : Poly 𝒞 → obj
      inF  : ∀ Q → fobj Q (μ Q) ⇒ μ Q
      -- Open (parametric) form: algebra in extended context. Avoids the closure conversion that would
      -- otherwise need exponentials.
      ⦅_⦆  : ∀ {Γ Q y} → (prod Γ (fobj Q y) ⇒ y) → prod Γ (μ Q) ⇒ y

      ⦅⦆-β : ∀ {Γ Q y} (alg : prod Γ (fobj Q y) ⇒ y) → (⦅ alg ⦆ ∘co (inF Q ∘ p₂)) ≈ (alg ∘co fmor Q ⦅ alg ⦆)
      ⦅⦆-η : ∀ {Γ Q y} (alg : prod Γ (fobj Q y) ⇒ y) (h : prod Γ (μ Q) ⇒ y) →
             (h ∘co (inF Q ∘ p₂)) ≈ (alg ∘co fmor Q h) → h ≈ ⦅ alg ⦆

  -- Derived consequences of HasMu's β/η.
  module HasMu-derived (Mu : HasMu) where
    open HasMu Mu

    cata-fusion : ∀ {Γ Q y y'} (alg : prod Γ (fobj Q y) ⇒ y) (alg' : prod Γ (fobj Q y') ⇒ y')
                  (f : prod Γ y ⇒ y') → (f ∘co alg) ≈ (alg' ∘co fmor Q f) → (f ∘co ⦅ alg ⦆) ≈ ⦅ alg' ⦆
    cata-fusion {Q = Q} alg alg' f f-is-alg-mor = ⦅⦆-η _ _ (begin
        (f ∘co ⦅ alg ⦆) ∘co (inF Q ∘ p₂)
      ≈⟨ assoc-co _ _ _ ⟩
        f ∘co (⦅ alg ⦆ ∘co (inF Q ∘ p₂))
      ≈⟨ ∘-cong-co ≈-refl (⦅⦆-β _) ⟩
        f ∘co (alg ∘co fmor Q ⦅ alg ⦆)
      ≈˘⟨ assoc-co _ _ _ ⟩
        (f ∘co alg) ∘co fmor Q ⦅ alg ⦆
      ≈⟨ ∘-cong-co f-is-alg-mor ≈-refl ⟩
        (alg' ∘co fmor Q f) ∘co fmor Q ⦅ alg ⦆
      ≈⟨ assoc-co _ _ _ ⟩
        alg' ∘co (fmor Q f ∘co fmor Q ⦅ alg ⦆)
      ≈˘⟨ ∘-cong-co ≈-refl (fmor-comp Q _ _) ⟩
        alg' ∘co fmor Q (f ∘co ⦅ alg ⦆)
      ∎) where open ≈-Reasoning isEquiv

    -- Cata of inF is the coKleisli identity p₂.
    cata-inF : ∀ {Γ Q} → p₂ {x = Γ} {y = μ Q} ≈ ⦅ inF Q ∘ p₂ ⦆
    cata-inF {Γ} {Q} = ⦅⦆-η _ _ (begin
        p₂ ∘co (inF Q ∘ p₂)
      ≈⟨ pair-p₂ _ _ ⟩
        inF Q ∘ p₂
      ≈˘⟨ id-right ⟩
        (inF Q ∘ p₂) ∘ id _
      ≈˘⟨ ∘-cong₂ pair-ext0 ⟩
        (inF Q ∘ p₂) ∘ pair p₁ p₂
      ≈˘⟨ ∘-cong₂ (pair-cong₂ (fmor-id Q)) ⟩
        (inF Q ∘ p₂) ∘co fmor Q p₂
      ∎) where open ≈-Reasoning isEquiv

  -- μ respects Poly-iso: structurally iso polynomials (matching shape, const slots iso) yield iso μ-types.
  -- Built directly from catamorphism universal property (β, η).
  module μ-respects-Poly-iso (Mu : HasMu) where
    open HasMu Mu
    open HasMu-derived Mu
    open Iso

    iso-mor : ∀ {P P'} → Poly-iso P P' → ∀ {Γ X} → prod Γ (fobj P X) ⇒ fobj P' X
    iso-mor (const A≅B)     = A≅B .fwd ∘ p₂
    iso-mor var             = p₂
    iso-mor (P₁≅Q₁ + P₂≅Q₂) = s-copair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂)
    iso-mor (P₁≅Q₁ × P₂≅Q₂) = pair (iso-mor P₁≅Q₁ ∘co (p₁ ∘ p₂)) (iso-mor P₂≅Q₂ ∘co (p₂ ∘ p₂))

    iso-sym : ∀ {P P'} → Poly-iso P P' → Poly-iso P' P
    iso-sym (const A≅B) = const (Category.Iso-sym 𝒞 A≅B)
    iso-sym var         = var
    iso-sym (P₁≅Q₁ + P₂≅Q₂) = iso-sym P₁≅Q₁ + iso-sym P₂≅Q₂
    iso-sym (P₁≅Q₁ × P₂≅Q₂) = iso-sym P₁≅Q₁ × iso-sym P₂≅Q₂

    iso-sym-involutive : ∀ {P P'} (P≅P' : Poly-iso P P') → iso-sym (iso-sym P≅P') ≡ P≅P'
    iso-sym-involutive (const A≅B) = ≡.refl
    iso-sym-involutive var         = ≡.refl
    iso-sym-involutive (P₁≅Q₁ + P₂≅Q₂) = ≡.cong₂ _+_ (iso-sym-involutive P₁≅Q₁) (iso-sym-involutive P₂≅Q₂)
    iso-sym-involutive (P₁≅Q₁ × P₂≅Q₂) = ≡.cong₂ _×_ (iso-sym-involutive P₁≅Q₁) (iso-sym-involutive P₂≅Q₂)

    -- Round-trip law: forward then backward at the polynomial-functor level is (parameterised) identity.
    iso-mor-fwd∘bwd : ∀ {P P'} (P≅P' : Poly-iso P P') {Γ X} → iso-mor P≅P' {Γ} {X} ∘co iso-mor (iso-sym P≅P') ≈ p₂
    iso-mor-fwd∘bwd (const A≅B) =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong₂ (pair-p₂ _ _))
      (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ (A≅B .fwd∘bwd≈id)) id-left)))
    iso-mor-fwd∘bwd var = pair-p₂ _ _
    iso-mor-fwd∘bwd (_+_ {P₁} {P₂} {Q₁} {Q₂} P₁≅Q₁ P₂≅Q₂) {Γ} {X} =
      ≈-trans (≈-sym (s-copair-ext _)) (≈-trans (s-copair-cong in₁-branch in₂-branch) (s-copair-ext _))
      where
        in₁-branch : (s-copair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂)
                       ∘co s-copair (in₁ ∘ iso-mor (iso-sym P₁≅Q₁)) (in₂ ∘ iso-mor (iso-sym P₂≅Q₂)))
                       ∘co (in₁ ∘ p₂)
                   ≈ p₂ ∘co (in₁ ∘ p₂)
        in₁-branch =
          begin
            (s-copair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘co
             (s-copair (in₁ ∘ iso-mor (iso-sym P₁≅Q₁)) (in₂ ∘ iso-mor (iso-sym P₂≅Q₂)))) ∘co (in₁ ∘ p₂)
          ≈⟨ assoc-co _ _ _ ⟩
            s-copair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘co
            (s-copair (in₁ ∘ iso-mor (iso-sym P₁≅Q₁)) (in₂ ∘ iso-mor (iso-sym P₂≅Q₂)) ∘co (in₁ ∘ p₂))
          ≈⟨ ∘-cong-co ≈-refl (s-copair-in₁ _ _) ⟩
            s-copair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘co (in₁ ∘ iso-mor (iso-sym P₁≅Q₁))
          ≈˘⟨ ∘-cong₂ (≈-trans (pair-natural _ _ _)
                (pair-cong (pair-p₁ _ _) (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))))) ⟩
            s-copair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘ (pair p₁ (in₁ ∘ p₂) ∘co (iso-mor (iso-sym P₁≅Q₁)))
          ≈˘⟨ assoc _ _ _ ⟩
            (s-copair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘co (in₁ ∘ p₂)) ∘co (iso-mor (iso-sym P₁≅Q₁))
          ≈⟨ ∘-cong₁ (s-copair-in₁ _ _) ⟩
            (in₁ ∘ iso-mor P₁≅Q₁) ∘co (iso-mor (iso-sym P₁≅Q₁))
          ≈⟨ assoc _ _ _ ⟩
            in₁ ∘ (iso-mor P₁≅Q₁ ∘co (iso-mor (iso-sym P₁≅Q₁)))
          ≈⟨ ∘-cong₂ (iso-mor-fwd∘bwd P₁≅Q₁) ⟩
            in₁ ∘ p₂
          ≈˘⟨ pair-p₂ _ _ ⟩
            p₂ ∘co (in₁ ∘ p₂)
          ∎ where open ≈-Reasoning isEquiv

        in₂-branch : (s-copair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘co
                      (s-copair (in₁ ∘ iso-mor (iso-sym P₁≅Q₁)) (in₂ ∘ iso-mor (iso-sym P₂≅Q₂)))) ∘co (in₂ ∘ p₂)
                   ≈ p₂ ∘co (in₂ ∘ p₂)
        in₂-branch = begin
            (s-copair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘co
             (s-copair (in₁ ∘ iso-mor (iso-sym P₁≅Q₁)) (in₂ ∘ iso-mor (iso-sym P₂≅Q₂)))) ∘co (in₂ ∘ p₂)
          ≈⟨ assoc-co _ _ _ ⟩
            s-copair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘co
            (s-copair (in₁ ∘ iso-mor (iso-sym P₁≅Q₁)) (in₂ ∘ iso-mor (iso-sym P₂≅Q₂)) ∘co (in₂ ∘ p₂))
          ≈⟨ ∘-cong-co ≈-refl (s-copair-in₂ _ _) ⟩
            s-copair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘co (in₂ ∘ iso-mor (iso-sym P₂≅Q₂))
          ≈˘⟨ ∘-cong₂ (≈-trans (pair-natural _ _ _)
                (pair-cong (pair-p₁ _ _) (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))))) ⟩
            s-copair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘ (pair p₁ (in₂ ∘ p₂) ∘co (iso-mor (iso-sym P₂≅Q₂)))
          ≈˘⟨ assoc _ _ _ ⟩
            (s-copair (in₁ ∘ iso-mor P₁≅Q₁) (in₂ ∘ iso-mor P₂≅Q₂) ∘co (in₂ ∘ p₂)) ∘co (iso-mor (iso-sym P₂≅Q₂))
          ≈⟨ ∘-cong₁ (s-copair-in₂ _ _) ⟩
            (in₂ ∘ iso-mor P₂≅Q₂) ∘co (iso-mor (iso-sym P₂≅Q₂))
          ≈⟨ assoc _ _ _ ⟩
            in₂ ∘ (iso-mor P₂≅Q₂ ∘co (iso-mor (iso-sym P₂≅Q₂)))
          ≈⟨ ∘-cong₂ (iso-mor-fwd∘bwd P₂≅Q₂) ⟩
            in₂ ∘ p₂
          ≈˘⟨ pair-p₂ _ _ ⟩
            p₂ ∘co (in₂ ∘ p₂)
          ∎ where open ≈-Reasoning isEquiv

    iso-mor-fwd∘bwd (_×_ {P₁} {P₂} {Q₁} {Q₂} P₁≅Q₁ P₂≅Q₂) {Γ} {X} =
      ≈-trans (≈-sym (pair-ext _)) (≈-trans (pair-cong p₁-branch p₂-branch) (pair-ext _))
      where
        pair-fwd = pair (iso-mor P₁≅Q₁ ∘co (p₁ ∘ p₂)) (iso-mor P₂≅Q₂ ∘co (p₂ ∘ p₂))
        pair-bwd = pair (iso-mor (iso-sym P₁≅Q₁) ∘co (p₁ ∘ p₂)) (iso-mor (iso-sym P₂≅Q₂) ∘co (p₂ ∘ p₂))

        p₁-branch : p₁ ∘ (pair-fwd ∘co pair-bwd) ≈ p₁ ∘ p₂
        p₁-branch = begin
            p₁ ∘ (pair-fwd ∘co pair-bwd)
          ≈˘⟨ assoc _ _ _ ⟩
            (p₁ ∘ pair-fwd) ∘co pair-bwd
          ≈⟨ ∘-cong₁ (pair-p₁ _ _) ⟩
            (iso-mor P₁≅Q₁ ∘co (p₁ ∘ p₂)) ∘co pair-bwd
          ≈⟨ assoc _ _ _ ⟩
            iso-mor P₁≅Q₁ ∘ (pair p₁ (p₁ ∘ p₂) ∘co pair-bwd)
          ≈⟨ ∘-cong₂ (≈-trans (pair-natural _ _ _)
                           (≈-trans (pair-cong (pair-p₁ _ _) (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))))
                                    (pair-cong₂ (pair-p₁ _ _)))) ⟩
            iso-mor P₁≅Q₁ ∘co (iso-mor (iso-sym P₁≅Q₁) ∘co (p₁ ∘ p₂))
          ≈˘⟨ ∘-cong₂ (≈-trans (pair-natural _ _ _) (pair-cong₁ (pair-p₁ _ _))) ⟩
            iso-mor P₁≅Q₁ ∘ (pair p₁ (iso-mor (iso-sym P₁≅Q₁)) ∘co (p₁ ∘ p₂))
          ≈˘⟨ assoc _ _ _ ⟩
            (iso-mor P₁≅Q₁ ∘co (iso-mor (iso-sym P₁≅Q₁))) ∘co (p₁ ∘ p₂)
          ≈⟨ ∘-cong₁ (iso-mor-fwd∘bwd P₁≅Q₁) ⟩
            p₂ ∘co (p₁ ∘ p₂)
          ≈⟨ pair-p₂ _ _ ⟩
            p₁ ∘ p₂
          ∎ where open ≈-Reasoning isEquiv

        p₂-branch : p₂ ∘ (pair-fwd ∘co pair-bwd) ≈ p₂ ∘ p₂
        p₂-branch = begin
            p₂ ∘ (pair-fwd ∘co pair-bwd)
          ≈˘⟨ assoc _ _ _ ⟩
            (p₂ ∘ pair-fwd) ∘co pair-bwd
          ≈⟨ ∘-cong₁ (pair-p₂ _ _) ⟩
            (iso-mor P₂≅Q₂ ∘co (p₂ ∘ p₂)) ∘co pair-bwd
          ≈⟨ assoc _ _ _ ⟩
            iso-mor P₂≅Q₂ ∘ (pair p₁ (p₂ ∘ p₂) ∘co pair-bwd)
          ≈⟨ ∘-cong₂ (≈-trans (pair-natural _ _ _)
                           (≈-trans (pair-cong (pair-p₁ _ _) (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))))
                                    (pair-cong₂ (pair-p₂ _ _)))) ⟩
            iso-mor P₂≅Q₂ ∘co (iso-mor (iso-sym P₂≅Q₂) ∘co (p₂ ∘ p₂))
          ≈˘⟨ ∘-cong₂ (≈-trans (pair-natural _ _ _) (pair-cong₁ (pair-p₁ _ _))) ⟩
            iso-mor P₂≅Q₂ ∘ (pair p₁ (iso-mor (iso-sym P₂≅Q₂)) ∘co (p₂ ∘ p₂))
          ≈˘⟨ assoc _ _ _ ⟩
            (iso-mor P₂≅Q₂ ∘co (iso-mor (iso-sym P₂≅Q₂))) ∘co (p₂ ∘ p₂)
          ≈⟨ ∘-cong₁ (iso-mor-fwd∘bwd P₂≅Q₂) ⟩
            p₂ ∘co (p₂ ∘ p₂)
          ≈⟨ pair-p₂ _ _ ⟩
            p₂ ∘ p₂
          ∎ where open ≈-Reasoning isEquiv

    iso-mor-natural : ∀ {P P'} (P≅P' : Poly-iso P P') {Γ X Y} (f : prod Γ X ⇒ Y) →
                      iso-mor P≅P' ∘co fmor P f ≈ fmor P' f ∘co iso-mor P≅P'
    iso-mor-natural (const A≅B) f = ≈-trans id-right-co (≈-sym id-left-co)
    iso-mor-natural var         f = ≈-trans id-left-co (≈-sym id-right-co)
    iso-mor-natural (_+_ {P₁} {P₂} {Q₁} {Q₂} P₁≅Q₁ P₂≅Q₂) f =
      begin
        iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co fmor (P₁ + P₂) f
      ≈˘⟨ s-copair-ext _ ⟩
        s-copair ((iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co fmor (P₁ + P₂) f) ∘co (in₁ ∘ p₂))
                 ((iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co fmor (P₁ + P₂) f) ∘co (in₂ ∘ p₂))
      ≈⟨ s-copair-cong eq-in₁ eq-in₂ ⟩
        s-copair ((fmor (Q₁ + Q₂) f ∘co iso-mor (P₁≅Q₁ + P₂≅Q₂)) ∘co (in₁ ∘ p₂))
                 ((fmor (Q₁ + Q₂) f ∘co iso-mor (P₁≅Q₁ + P₂≅Q₂)) ∘co (in₂ ∘ p₂))
      ≈⟨ s-copair-ext _ ⟩
        fmor (Q₁ + Q₂) f ∘co iso-mor (P₁≅Q₁ + P₂≅Q₂)
      ∎ where
        eq-in₁ : (iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co fmor (P₁ + P₂) f) ∘co (in₁ ∘ p₂)
                 ≈ (fmor (Q₁ + Q₂) f ∘co iso-mor (P₁≅Q₁ + P₂≅Q₂)) ∘co (in₁ ∘ p₂)
        eq-in₁ = begin
            (iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co fmor (P₁ + P₂) f) ∘co (in₁ ∘ p₂)
          ≈⟨ assoc-co _ _ _ ⟩
            iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co (fmor (P₁ + P₂) f ∘co (in₁ ∘ p₂))
          ≈⟨ ∘-cong-co ≈-refl (s-copair-in₁ _ _) ⟩
            iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co (in₁ ∘ fmor P₁ f)
          ≈˘⟨ ∘-cong-co ≈-refl (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))) ⟩
            iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co ((in₁ ∘ p₂) ∘co fmor P₁ f)
          ≈˘⟨ assoc-co _ _ _ ⟩
            (iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co (in₁ ∘ p₂)) ∘co fmor P₁ f
          ≈⟨ ∘-cong-co (s-copair-in₁ _ _) ≈-refl ⟩
            (in₁ ∘ iso-mor P₁≅Q₁) ∘co fmor P₁ f
          ≈⟨ assoc _ _ _ ⟩
            in₁ ∘ (iso-mor P₁≅Q₁ ∘co fmor P₁ f)
          ≈⟨ ∘-cong₂ (iso-mor-natural P₁≅Q₁ f) ⟩
            in₁ ∘ (fmor Q₁ f ∘co iso-mor P₁≅Q₁)
          ≈˘⟨ assoc _ _ _ ⟩
            (in₁ ∘ fmor Q₁ f) ∘co iso-mor P₁≅Q₁
          ≈˘⟨ ∘-cong-co (s-copair-in₁ _ _) ≈-refl ⟩
            (fmor (Q₁ + Q₂) f ∘co (in₁ ∘ p₂)) ∘co iso-mor P₁≅Q₁
          ≈⟨ assoc-co _ _ _ ⟩
            fmor (Q₁ + Q₂) f ∘co ((in₁ ∘ p₂) ∘co iso-mor P₁≅Q₁)
          ≈⟨ ∘-cong-co ≈-refl (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))) ⟩
            fmor (Q₁ + Q₂) f ∘co (in₁ ∘ iso-mor P₁≅Q₁)
          ≈˘⟨ ∘-cong-co ≈-refl (s-copair-in₁ _ _) ⟩
            fmor (Q₁ + Q₂) f ∘co (iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co (in₁ ∘ p₂))
          ≈˘⟨ assoc-co _ _ _ ⟩
            (fmor (Q₁ + Q₂) f ∘co iso-mor (P₁≅Q₁ + P₂≅Q₂)) ∘co (in₁ ∘ p₂)
          ∎ where open ≈-Reasoning isEquiv
        eq-in₂ : (iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co fmor (P₁ + P₂) f) ∘co (in₂ ∘ p₂)
                 ≈ (fmor (Q₁ + Q₂) f ∘co iso-mor (P₁≅Q₁ + P₂≅Q₂)) ∘co (in₂ ∘ p₂)
        eq-in₂ = begin
            (iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co fmor (P₁ + P₂) f) ∘co (in₂ ∘ p₂)
          ≈⟨ assoc-co _ _ _ ⟩
            iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co (fmor (P₁ + P₂) f ∘co (in₂ ∘ p₂))
          ≈⟨ ∘-cong-co ≈-refl (s-copair-in₂ _ _) ⟩
            iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co (in₂ ∘ fmor P₂ f)
          ≈˘⟨ ∘-cong-co ≈-refl (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))) ⟩
            iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co ((in₂ ∘ p₂) ∘co fmor P₂ f)
          ≈˘⟨ assoc-co _ _ _ ⟩
            (iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co (in₂ ∘ p₂)) ∘co fmor P₂ f
          ≈⟨ ∘-cong-co (s-copair-in₂ _ _) ≈-refl ⟩
            (in₂ ∘ iso-mor P₂≅Q₂) ∘co fmor P₂ f
          ≈⟨ assoc _ _ _ ⟩
            in₂ ∘ (iso-mor P₂≅Q₂ ∘co fmor P₂ f)
          ≈⟨ ∘-cong₂ (iso-mor-natural P₂≅Q₂ f) ⟩
            in₂ ∘ (fmor Q₂ f ∘co iso-mor P₂≅Q₂)
          ≈˘⟨ assoc _ _ _ ⟩
            (in₂ ∘ fmor Q₂ f) ∘co iso-mor P₂≅Q₂
          ≈˘⟨ ∘-cong-co (s-copair-in₂ _ _) ≈-refl ⟩
            (fmor (Q₁ + Q₂) f ∘co (in₂ ∘ p₂)) ∘co iso-mor P₂≅Q₂
          ≈⟨ assoc-co _ _ _ ⟩
            fmor (Q₁ + Q₂) f ∘co ((in₂ ∘ p₂) ∘co iso-mor P₂≅Q₂)
          ≈⟨ ∘-cong-co ≈-refl (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))) ⟩
            fmor (Q₁ + Q₂) f ∘co (in₂ ∘ iso-mor P₂≅Q₂)
          ≈˘⟨ ∘-cong-co ≈-refl (s-copair-in₂ _ _) ⟩
            fmor (Q₁ + Q₂) f ∘co (iso-mor (P₁≅Q₁ + P₂≅Q₂) ∘co (in₂ ∘ p₂))
          ≈˘⟨ assoc-co _ _ _ ⟩
            (fmor (Q₁ + Q₂) f ∘co iso-mor (P₁≅Q₁ + P₂≅Q₂)) ∘co (in₂ ∘ p₂)
          ∎ where open ≈-Reasoning isEquiv
        open ≈-Reasoning isEquiv
    iso-mor-natural (_×_ {P₁} {P₂} {Q₁} {Q₂} P₁≅Q₁ P₂≅Q₂) f = begin
        iso-mor (P₁≅Q₁ × P₂≅Q₂) ∘co fmor (P₁ × P₂) f
      ≈˘⟨ pair-ext _ ⟩
        pair (p₁ ∘ (iso-mor (P₁≅Q₁ × P₂≅Q₂) ∘co fmor (P₁ × P₂) f))
             (p₂ ∘ (iso-mor (P₁≅Q₁ × P₂≅Q₂) ∘co fmor (P₁ × P₂) f))
      ≈⟨ pair-cong eq-p₁ eq-p₂ ⟩
        pair (p₁ ∘ (fmor (Q₁ × Q₂) f ∘co iso-mor (P₁≅Q₁ × P₂≅Q₂)))
             (p₂ ∘ (fmor (Q₁ × Q₂) f ∘co iso-mor (P₁≅Q₁ × P₂≅Q₂)))
      ≈⟨ pair-ext _ ⟩
        fmor (Q₁ × Q₂) f ∘co iso-mor (P₁≅Q₁ × P₂≅Q₂)
      ∎ where
        eq-p₁ : p₁ ∘ (iso-mor (P₁≅Q₁ × P₂≅Q₂) ∘co fmor (P₁ × P₂) f)
                ≈ p₁ ∘ (fmor (Q₁ × Q₂) f ∘co iso-mor (P₁≅Q₁ × P₂≅Q₂))
        eq-p₁ = begin
            p₁ ∘ (iso-mor (P₁≅Q₁ × P₂≅Q₂) ∘co fmor (P₁ × P₂) f)
          ≈˘⟨ assoc _ _ _ ⟩
            (p₁ ∘ iso-mor (P₁≅Q₁ × P₂≅Q₂)) ∘co fmor (P₁ × P₂) f
          ≈⟨ ∘-cong-co (pair-p₁ _ _) ≈-refl ⟩
            (iso-mor P₁≅Q₁ ∘co (p₁ ∘ p₂)) ∘co fmor (P₁ × P₂) f
          ≈⟨ assoc-co _ _ _ ⟩
            iso-mor P₁≅Q₁ ∘co ((p₁ ∘ p₂) ∘co fmor (P₁ × P₂) f)
          ≈⟨ ∘-cong-co ≈-refl (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (pair-p₂ _ _)) (pair-p₁ _ _))) ⟩
            iso-mor P₁≅Q₁ ∘co (fmor P₁ f ∘co (p₁ ∘ p₂))
          ≈˘⟨ assoc-co _ _ _ ⟩
            (iso-mor P₁≅Q₁ ∘co fmor P₁ f) ∘co (p₁ ∘ p₂)
          ≈⟨ ∘-cong-co (iso-mor-natural P₁≅Q₁ f) ≈-refl ⟩
            (fmor Q₁ f ∘co iso-mor P₁≅Q₁) ∘co (p₁ ∘ p₂)
          ≈⟨ assoc-co _ _ _ ⟩
            fmor Q₁ f ∘co (iso-mor P₁≅Q₁ ∘co (p₁ ∘ p₂))
          ≈˘⟨ ∘-cong-co ≈-refl (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (pair-p₂ _ _)) (pair-p₁ _ _))) ⟩
            fmor Q₁ f ∘co ((p₁ ∘ p₂) ∘co iso-mor (P₁≅Q₁ × P₂≅Q₂))
          ≈˘⟨ assoc-co _ _ _ ⟩
            (fmor Q₁ f ∘co (p₁ ∘ p₂)) ∘co iso-mor (P₁≅Q₁ × P₂≅Q₂)
          ≈˘⟨ ∘-cong-co (pair-p₁ _ _) ≈-refl ⟩
            (p₁ ∘ fmor (Q₁ × Q₂) f) ∘co iso-mor (P₁≅Q₁ × P₂≅Q₂)
          ≈⟨ assoc _ _ _ ⟩
            p₁ ∘ (fmor (Q₁ × Q₂) f ∘co iso-mor (P₁≅Q₁ × P₂≅Q₂))
          ∎ where open ≈-Reasoning isEquiv
        eq-p₂ : p₂ ∘ (iso-mor (P₁≅Q₁ × P₂≅Q₂) ∘co fmor (P₁ × P₂) f)
                ≈ p₂ ∘ (fmor (Q₁ × Q₂) f ∘co iso-mor (P₁≅Q₁ × P₂≅Q₂))
        eq-p₂ = begin
            p₂ ∘ (iso-mor (P₁≅Q₁ × P₂≅Q₂) ∘co fmor (P₁ × P₂) f)
          ≈˘⟨ assoc _ _ _ ⟩
            (p₂ ∘ iso-mor (P₁≅Q₁ × P₂≅Q₂)) ∘co fmor (P₁ × P₂) f
          ≈⟨ ∘-cong-co (pair-p₂ _ _) ≈-refl ⟩
            (iso-mor P₂≅Q₂ ∘co (p₂ ∘ p₂)) ∘co fmor (P₁ × P₂) f
          ≈⟨ assoc-co _ _ _ ⟩
            iso-mor P₂≅Q₂ ∘co ((p₂ ∘ p₂) ∘co fmor (P₁ × P₂) f)
          ≈⟨ ∘-cong-co ≈-refl (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (pair-p₂ _ _)) (pair-p₂ _ _))) ⟩
            iso-mor P₂≅Q₂ ∘co (fmor P₂ f ∘co (p₂ ∘ p₂))
          ≈˘⟨ assoc-co _ _ _ ⟩
            (iso-mor P₂≅Q₂ ∘co fmor P₂ f) ∘co (p₂ ∘ p₂)
          ≈⟨ ∘-cong-co (iso-mor-natural P₂≅Q₂ f) ≈-refl ⟩
            (fmor Q₂ f ∘co iso-mor P₂≅Q₂) ∘co (p₂ ∘ p₂)
          ≈⟨ assoc-co _ _ _ ⟩
            fmor Q₂ f ∘co (iso-mor P₂≅Q₂ ∘co (p₂ ∘ p₂))
          ≈˘⟨ ∘-cong-co ≈-refl (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (pair-p₂ _ _)) (pair-p₂ _ _))) ⟩
            fmor Q₂ f ∘co ((p₂ ∘ p₂) ∘co iso-mor (P₁≅Q₁ × P₂≅Q₂))
          ≈˘⟨ assoc-co _ _ _ ⟩
            (fmor Q₂ f ∘co (p₂ ∘ p₂)) ∘co iso-mor (P₁≅Q₁ × P₂≅Q₂)
          ≈˘⟨ ∘-cong-co (pair-p₂ _ _) ≈-refl ⟩
            (p₂ ∘ fmor (Q₁ × Q₂) f) ∘co iso-mor (P₁≅Q₁ × P₂≅Q₂)
          ≈⟨ assoc _ _ _ ⟩
            p₂ ∘ (fmor (Q₁ × Q₂) f ∘co iso-mor (P₁≅Q₁ × P₂≅Q₂))
          ∎ where open ≈-Reasoning isEquiv
        open ≈-Reasoning isEquiv

    -- Algebra-morphism condition: fwd-cata ⦅ alg-fwd ⦆ commutes with alg-bwd and inF P', after
    -- using iso-mor-natural to move iso-mor through fmor and iso-mor-fwd∘bwd to cancel iso-mor pairs.
    fwd-cata-alg-mor : ∀ {P P'} (P≅P' : Poly-iso P P') {Γ} →
      ⦅ inF P' ∘ iso-mor P≅P' {Γ} ⦆ ∘co (inF P ∘ iso-mor (iso-sym P≅P'))
      ≈ (inF P' ∘ p₂) ∘co fmor P' ⦅ inF P' ∘ iso-mor P≅P' ⦆
    fwd-cata-alg-mor {P} {P'} P≅P' = begin
        ⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘co (inF P ∘ iso-mor (iso-sym P≅P'))
      ≈˘⟨ ∘-cong-co₂ (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))) ⟩
        ⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘co ((inF P ∘ p₂) ∘co iso-mor (iso-sym P≅P'))
      ≈˘⟨ assoc-co _ _ _ ⟩
        (⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘co (inF P ∘ p₂)) ∘co iso-mor (iso-sym P≅P')
      ≈⟨ ∘-cong-co₁ (⦅⦆-β _) ⟩
        ((inF P' ∘ iso-mor P≅P') ∘co fmor P ⦅ inF P' ∘ iso-mor P≅P' ⦆) ∘co iso-mor (iso-sym P≅P')
      ≈⟨ ∘-cong-co₁ (≈-trans (assoc _ _ _) (≈-sym (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _))))) ⟩
        ((inF P' ∘ p₂) ∘co (iso-mor P≅P' ∘co fmor P ⦅ inF P' ∘ iso-mor P≅P' ⦆)) ∘co iso-mor (iso-sym P≅P')
      ≈⟨ ∘-cong-co₁ (∘-cong-co₂ (iso-mor-natural P≅P' _)) ⟩
        ((inF P' ∘ p₂) ∘co (fmor P' ⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘co iso-mor P≅P')) ∘co iso-mor (iso-sym P≅P')
      ≈˘⟨ ∘-cong-co₁ (assoc-co _ _ _) ⟩
        (((inF P' ∘ p₂) ∘co fmor P' ⦅ inF P' ∘ iso-mor P≅P' ⦆) ∘co iso-mor P≅P') ∘co iso-mor (iso-sym P≅P')
      ≈⟨ assoc-co _ _ _ ⟩
        ((inF P' ∘ p₂) ∘co fmor P' ⦅ inF P' ∘ iso-mor P≅P' ⦆) ∘co (iso-mor P≅P' ∘co iso-mor (iso-sym P≅P'))
      ≈⟨ ∘-cong-co₂ (iso-mor-fwd∘bwd P≅P') ⟩
        ((inF P' ∘ p₂) ∘co fmor P' ⦅ inF P' ∘ iso-mor P≅P' ⦆) ∘co p₂
      ≈⟨ ≈-trans (∘-cong₂ pair-ext0) id-right ⟩
        (inF P' ∘ p₂) ∘co fmor P' ⦅ inF P' ∘ iso-mor P≅P' ⦆
      ∎ where open ≈-Reasoning isEquiv

    iso-fwd∘bwd : ∀ {P P'} (P≅P' : Poly-iso P P') →
      (⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
        ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P'))) ≈ id (μ P')
    iso-fwd∘bwd {P} {P'} P≅P' = begin
        (⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair to-terminal (id (μ P)))
          ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P')))
      ≈⟨ assoc _ _ _ ⟩
        ⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ (pair to-terminal (id (μ P))
          ∘ (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P'))))
      ≈˘⟨ ∘-cong₂ (assoc _ _ _) ⟩
        ⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ ((pair to-terminal (id (μ P)) ∘ ⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆)
          ∘ pair to-terminal (id (μ P')))
      ≈⟨ ∘-cong₂ (∘-cong₁
           (≈-trans (pair-natural _ _ _) (pair-cong (to-terminal-unique _ _) id-left))) ⟩
        ⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ (pair to-terminal ⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆
          ∘ pair to-terminal (id (μ P')))
      ≈⟨ ∘-cong₂ (pair-natural _ _ _) ⟩
        ⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair (to-terminal ∘ pair to-terminal (id (μ P')))
                                          (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P')))
      ≈⟨ ∘-cong₂ (pair-cong₁ (≈-trans (to-terminal-unique _ _) (≈-sym (pair-p₁ _ _)))) ⟩
        ⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ pair (p₁ ∘ pair to-terminal (id (μ P')))
                                          (⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P')))
      ≈˘⟨ ∘-cong₂ (pair-natural _ _ _) ⟩
        ⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘ (pair p₁ ⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆ ∘ pair to-terminal (id (μ P')))
      ≈˘⟨ assoc _ _ _ ⟩
        (⦅ inF P' ∘ iso-mor P≅P' ⦆ ∘co ⦅ inF P ∘ iso-mor (iso-sym P≅P') ⦆) ∘ pair to-terminal (id (μ P'))
      ≈⟨ ∘-cong₁ (≈-trans (cata-fusion _ _ _ (fwd-cata-alg-mor P≅P')) (≈-sym cata-inF)) ⟩
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
    ∀ (P : Poly 𝒞) → Category.Iso 𝒟 (Functor.fobj F (S₁.HasMu.μ 𝒞Mu P)) (S₂.HasMu.μ 𝒟Mu (Poly-map F P))

