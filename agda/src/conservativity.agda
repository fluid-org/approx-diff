{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (Level; Lift; lift; lower; _⊔_; 0ℓ) renaming (suc to lsuc)
open import Data.Product using (_,_)
open import prop using (_,_; ∃; ∃ₛ; Prf; ⟪_⟫; LiftP; lift; lower; liftS; inj₁; inj₂)
open import basics using (module ≤-Reasoning; IsClosureOp; IsJoin; IsMeet; IsBigJoin; IsPreorder)
open import categories
  using (Category; HasBooleans; HasProducts; HasCoproducts; HasExponentials;
         HasTerminal; IsTerminal; IsProduct; coproducts+exp→booleans;
         setoid→category; HasStrongCoproducts; ccc→strong-coproducts;
         strong-coproducts→coproducts)
import Data.Nat
import Data.Fin
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
import polynomial-functor
open import functor
  using (Functor; _∘F_; opF; _∘H_; ∘H-cong; id; _∘_; NatTrans; ≃-NatTrans; ≃-isEquivalence;
         interchange; H-id; NT-id-left;
         HasColimits; Colimit; colambda-unique; constF; NatIso; functor-preserve-iso)
open import prop-setoid using (module ≈-Reasoning; IsEquivalence; Setoid)
open import predicate-system using (PredicateSystem; ClosureOp; FunctorPred; MonadPred)
open import stable-coproducts using (StableBits)
import fam-mu-realisation
import glueing-simple
import setoid-predicate
import stable-coproducts-indexed
import finite-coproducts-from-indexed
open import finite-product-functor
  using ( preserve-chosen-products
        ; preserve-chosen-terminal
        ; module preserve-chosen-products-consequences)
open import finite-coproduct-functor
  using (preserve-chosen-coproducts; module preserve-chosen-coproducts-consequences)
open import monad using (Monad; preserve-monad; MonadFunctor)

open import signature

open Functor
open NatTrans
open ≃-NatTrans

-- The Grothendieck Logical Relations construction of Fiore and Simpson (1999): for a functor
-- F : 𝒞 → 𝒟 preserving finite products and coproducts, with 𝒞 bicartesian with stable
-- coproducts and 𝒟 bicartesian closed, there is a bicartesian closed category of glued
-- predicates through which F factors, with the factor out of 𝒞 full: every glued morphism
-- between objects from 𝒞 is the image of a morphism of 𝒞 (the `definability` declaration
-- below).

module conservativity
  {o₁ o₂ m e}
  -- Category for interpreting first-order things, with stable set-indexed
  -- coproducts (the finite coproducts used below are their two-element instance)
  (𝒞 : Category o₁ m e) (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞M : Monad 𝒞)
  (𝒞DC : ∀ (S : Setoid 0ℓ 0ℓ) → HasColimits (setoid→category S) 𝒞)
  (𝒞istable : stable-coproducts-indexed.IdxStable 𝒞DC)
  -- A higher order model
  (𝒟 : Category o₂ m e) (𝒟T : HasTerminal 𝒟) (𝒟P : HasProducts 𝒟) (𝒟E : HasExponentials 𝒟 𝒟P) (𝒟M : Monad 𝒟)
  (𝒟DC : ∀ (A : Setoid 0ℓ 0ℓ) → HasColimits (setoid→category A) 𝒟)
  -- A functor which preserves terminal and products
  (F  : Functor 𝒞 𝒟)
  (FT : preserve-chosen-terminal F 𝒞T 𝒟T)
  (FP : preserve-chosen-products F 𝒞P 𝒟P)
  (FM : preserve-monad F 𝒞M 𝒟M)
  -- The monad functor preserves set-indexed coproducts (an iso commuting with
  -- the injections)
  (FM-DC : ∀ (S : Setoid 0ℓ 0ℓ) (D : Functor (setoid→category S) 𝒞) →
           ∃ₛ (Category.Iso 𝒞 (Colimit.apex (𝒞DC S (Monad.funct 𝒞M ∘F D)))
                              (Monad.funct 𝒞M .fobj (Colimit.apex (𝒞DC S D))))
              (λ i → ∀ s → Category._≈_ 𝒞
                            (Category._∘_ 𝒞 (Category.Iso.fwd i)
                               (Colimit.cocone (𝒞DC S (Monad.funct 𝒞M ∘F D)) .transf s))
                            (Monad.funct 𝒞M .fmor (Colimit.cocone (𝒞DC S D) .transf s))))
  -- F preserves set-indexed coproducts (an iso commuting with the injections)
  (F-DC : ∀ (S : Setoid 0ℓ 0ℓ) (D : Functor (setoid→category S) 𝒞) →
          ∃ₛ (Category.Iso 𝒟 (Colimit.apex (𝒟DC S (F ∘F D)))
                             (F .fobj (Colimit.apex (𝒞DC S D))))
             (λ i → ∀ s → Category._≈_ 𝒟
                           (Category._∘_ 𝒟 (Category.Iso.fwd i)
                              (Colimit.cocone (𝒟DC S (F ∘F D)) .transf s))
                           (F .fmor (Colimit.cocone (𝒞DC S D) .transf s))))
  -- F reflects equality, and picks a definability witness uniformly
  (F-faithful : ∀ {a b} {g₁ g₂ : Category._⇒_ 𝒞 a b} → Category._≈_ 𝒟 (F .fmor g₁) (F .fmor g₂) → Category._≈_ 𝒞 g₁ g₂)
  (Fdef : ∀ {a b} (h : Category._⇒_ 𝒟 (F .fobj a) (F .fobj b)) →
          Prf (∃ (Category._⇒_ 𝒞 a b) λ g → Category._≈_ 𝒟 (F .fmor g) h) →
          ∃ₛ (Category._⇒_ 𝒞 a b) λ g → Category._≈_ 𝒟 (F .fmor g) h)
  where

open import conservativity-base 𝒞 𝒞DC 𝒞istable 𝒟 F public

-- The finite coproducts and their preservation are the two-element instance of
-- the set-indexed structure.
private
  module 𝒟d = finite-coproducts-from-indexed.derive 𝒟DC

  𝒟CP = 𝒟d.coproducts-from-indexed
  FC = finite-coproducts-from-indexed.preserve.preserve-from-indexed 𝒞DC 𝒟DC F F-DC
  FM-C = finite-coproducts-from-indexed.preserve.preserve-from-indexed 𝒞DC 𝒞DC (Monad.funct 𝒞M) FM-DC

private
  module 𝒞 = Category 𝒞
  module 𝒞T = HasTerminal 𝒞T
  module 𝒞P = HasProducts 𝒞P
  module 𝒞CP = HasCoproducts 𝒞CP
  module 𝒟 = Category 𝒟
  module 𝒟T = HasTerminal 𝒟T
  module 𝒟P = HasProducts 𝒟P
  module 𝒟CP = HasCoproducts 𝒟CP
  module 𝒞M = Monad 𝒞M
  module 𝒟M = Monad 𝒟M
  module FM = preserve-monad FM

open DayMonad 𝒞M using (monad-hat)

private
  module PSh⟨𝒞⟩ = Category PSh⟨𝒞⟩
  module PSh⟨𝒞⟩P = HasProducts PSh⟨𝒞⟩-products
  module PSh⟨𝒞⟩M = Monad monad-hat

-- Product preservation of G. Presumably there is some more abstract
-- reason for this because the Yoneda embedding preserves products,
-- but this'll do for now.
module _ where
  open prop-setoid._⇒_
  open prop-setoid._≃m_
  open prop-setoid renaming (mk-≃m to mk-≈s) using (_∘S_; 𝟙; pair; to-𝟙; idS)

  G-prod : ∀ {x y} → PSh⟨𝒞⟩P.prod (G .fobj x) (G .fobj y) PSh⟨𝒞⟩.⇒ G .fobj (𝒟P.prod x y)
  G-prod {X} {Y} .transf x .func (lift f , lift g) = lift (𝒟P.pair f g)
  G-prod {X} {Y} .transf x .func-resp-≈ (lift f₁≈f₂ , lift g₁≈g₂) = lift (𝒟P.pair-cong f₁≈f₂ g₁≈g₂)
  G-prod {X} {Y} .natural f .func-eq {lift x₁ , lift y₁} {lift x₂ , lift y₂} (lift x₁≈x₂ , lift y₁≈y₂) =
    lift (begin
      𝒟P.pair x₁ y₁ 𝒟.∘ F .fmor f
    ≈⟨ 𝒟.∘-cong (𝒟P.pair-cong x₁≈x₂ y₁≈y₂) 𝒟.≈-refl ⟩
      𝒟P.pair x₂ y₂ 𝒟.∘ F .fmor f
    ≈⟨ 𝒟P.pair-natural _ _ _ ⟩
      𝒟P.pair (x₂ 𝒟.∘ F .fmor f) (y₂ 𝒟.∘ F .fmor f)
    ∎)
    where open ≈-Reasoning 𝒟.isEquiv

  G-preserve-products : preserve-chosen-products G 𝒟P PSh⟨𝒞⟩-products
  G-preserve-products .Category.IsIso.inverse = G-prod
  G-preserve-products .Category.IsIso.f∘inverse≈id .transf-eq m .func-eq {lift f₁ , lift g₁} {lift f₂ , lift g₂} (lift f₁≈f₂ , lift g₁≈g₂) =
    (lift (𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right) (𝒟.≈-trans (𝒟P.pair-p₁ _ _) f₁≈f₂))) ,
    (lift (𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right) (𝒟.≈-trans (𝒟P.pair-p₂ _ _) g₁≈g₂)))
  G-preserve-products .Category.IsIso.inverse∘f≈id .transf-eq x .func-eq {lift f₁} {lift f₂} (lift f₁≈f₂) =
    lift (𝒟.≈-trans (𝒟P.pair-cong (𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right)
                                   (𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right))
         (𝒟.≈-trans (𝒟P.pair-ext _)
                    f₁≈f₂))

  -- This is also a consequence of the yoneda embedding preserving the
  -- monad lifting, and F being a monad functor
  open UnaryDay 𝒞M.funct
  open Coend
  open Cowedge

  G-monad-cw : ∀ x y → Cowedge 𝟙 (M-hat-F (𝒟よ .fobj x ∘F opF F) y) (𝒟.hom-setoid-l (o₁ ⊔ o₂ ⊔ m ⊔ e ⊔ lsuc 0ℓ) (o₁ ⊔ o₂ ⊔ m ⊔ e ⊔ lsuc 0ℓ) (F .fobj y) (𝒟M.funct .fobj x))
  G-monad-cw x y .dtransf z .func (_ , lift g , lift h) =
    lift (𝒟M.funct .fmor h 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor g))
  G-monad-cw x y .dtransf z .func-resp-≈ (_ , lift g₁≈g₂ , lift h₁≈h₂) =
    lift (𝒟.∘-cong (𝒟M.funct .fmor-cong h₁≈h₂) (𝒟.∘-cong 𝒟.≈-refl (F .fmor-cong g₁≈g₂)))
  G-monad-cw x y .dinatural {z₁} {z₂} f = mk-≈s λ (_ , lift g , lift h) →
    lift (begin
      𝒟M.funct .fmor (h 𝒟.∘ F .fmor f) 𝒟.∘ (FM.transform .transf z₁ 𝒟.∘ F .fmor (𝒞M.funct .fmor (𝒞.id z₁) 𝒞.∘ g))
    ≈⟨ 𝒟.∘-cong (𝒟M.funct .fmor-comp _ _) (𝒟.∘-cong 𝒟.≈-refl (F .fmor-cong (𝒞.∘-cong (𝒞M.funct .fmor-id) 𝒞.≈-refl))) ⟩
      (𝒟M.funct .fmor h 𝒟.∘ 𝒟M.funct .fmor (F .fmor f)) 𝒟.∘ (FM.transform .transf z₁ 𝒟.∘ F .fmor (𝒞.id _ 𝒞.∘ g))
    ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl (F .fmor-cong 𝒞.id-left)) ⟩
      (𝒟M.funct .fmor h 𝒟.∘ 𝒟M.funct .fmor (F .fmor f)) 𝒟.∘ (FM.transform .transf z₁ 𝒟.∘ F .fmor g)
    ≈⟨ 𝒟.assoc _ _ _ ⟩
      𝒟M.funct .fmor h 𝒟.∘ (𝒟M.funct .fmor (F .fmor f) 𝒟.∘ (FM.transform .transf z₁ 𝒟.∘ F .fmor g))
    ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
      𝒟M.funct .fmor h 𝒟.∘ (𝒟M.funct .fmor (F .fmor f) 𝒟.∘ FM.transform .transf z₁ 𝒟.∘ F .fmor g)
    ≈⟨ 𝒟.∘-cong (𝒟M.funct .fmor-cong (𝒟.≈-sym 𝒟.id-right)) (𝒟.∘-cong (FM.transform .natural f) 𝒟.≈-refl) ⟩
      𝒟M.funct .fmor (h 𝒟.∘ 𝒟.id _) 𝒟.∘ (FM.transform .transf _ 𝒟.∘ F .fmor (𝒞M.funct .fmor f) 𝒟.∘ F .fmor g)
    ≈⟨ 𝒟.∘-cong (𝒟M.funct .fmor-cong (𝒟.∘-cong 𝒟.≈-refl (𝒟.≈-sym (F .fmor-id)))) (𝒟.assoc _ _ _) ⟩
      𝒟M.funct .fmor (h 𝒟.∘ F .fmor (𝒞.id _)) 𝒟.∘ (FM.transform .transf _ 𝒟.∘ (F .fmor (𝒞M.funct .fmor f) 𝒟.∘ F .fmor g))
    ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _ )) ⟩
      𝒟M.funct .fmor (h 𝒟.∘ F .fmor (𝒞.id z₂)) 𝒟.∘ (FM.transform .transf z₂ 𝒟.∘ F .fmor (𝒞M.funct .fmor f 𝒞.∘ g))
    ∎)
    where open ≈-Reasoning 𝒟.isEquiv

  G-monad : NatTrans (PSh⟨𝒞⟩M.funct ∘F G) (G ∘F 𝒟M.funct)
  G-monad .transf x .transf y = M-hat-coend _ _ .coend-ext (G-monad-cw x y) ∘S pair to-𝟙 (idS _)
  G-monad .transf x .natural {y₁}{y₂} f = mk-≈s λ (z , g , lift h) →
    lift (begin
      𝒟M.funct .fmor h 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor g) 𝒟.∘ F .fmor f
    ≈⟨ 𝒟.assoc _ _ _ ⟩
      𝒟M.funct .fmor h 𝒟.∘ ((FM.transform .transf z 𝒟.∘ F .fmor g) 𝒟.∘ F .fmor f)
    ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
      𝒟M.funct .fmor h 𝒟.∘ (FM.transform .transf z 𝒟.∘ (F .fmor g 𝒟.∘ F .fmor f))
    ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _)) ⟩
      𝒟M.funct .fmor h 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor (g 𝒞.∘ f))
    ∎)
    where open ≈-Reasoning 𝒟.isEquiv
  G-monad .natural {x₁} {x₂} f .transf-eq y = mk-≈s λ (z , g , lift h) →
    lift (begin
      𝒟M.funct .fmor f 𝒟.∘ (𝒟M.funct .fmor h 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor g) 𝒟.∘ 𝒟.id (F .fobj y))
    ≈⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right ⟩
      𝒟M.funct .fmor f 𝒟.∘ (𝒟M.funct .fmor h 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor g))
    ≈˘⟨ 𝒟.assoc _ _ _ ⟩
      (𝒟M.funct .fmor f 𝒟.∘ 𝒟M.funct .fmor h) 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor g)
    ≈˘⟨ 𝒟.∘-cong (𝒟M.funct .fmor-comp _ _) 𝒟.≈-refl ⟩
      𝒟M.funct .fmor (f 𝒟.∘ h) 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor g)
    ≈˘⟨ 𝒟.∘-cong (𝒟M.funct .fmor-cong (𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right)) 𝒟.≈-refl ⟩
      𝒟M.funct .fmor (f 𝒟.∘ (h 𝒟.∘ 𝒟.id (F .fobj z))) 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor g)
    ∎)
    where open ≈-Reasoning 𝒟.isEquiv

  open MonadFunctor

  G-MonadFunctor : MonadFunctor G 𝒟M (DayMonad.monad-hat 𝒞M)
  G-MonadFunctor .transform = G-monad
  G-MonadFunctor .preserve-unit .transf-eq x = mk-≈s λ (lift f) →
    lift (begin
      𝒟M.funct .fmor f 𝒟.∘ (FM.transform .transf _ 𝒟.∘ F .fmor (𝒞M.unit .transf _))
    ≈⟨ 𝒟.∘-cong 𝒟.≈-refl FM.preserve-unit ⟩
      𝒟M.funct .fmor f 𝒟.∘ 𝒟M.unit .transf _
    ≈⟨ 𝒟M.unit .natural f ⟩
      𝒟M.unit .transf _ 𝒟.∘ f
    ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right ⟩
      𝒟M.unit .transf _ 𝒟.∘ (f 𝒟.∘ 𝒟.id _)
    ∎)
    where open ≈-Reasoning 𝒟.isEquiv
  G-MonadFunctor .preserve-join .transf-eq x = mk-≈s λ (y , f , z , g , lift h) →
    lift (begin
      𝒟M.funct .fmor h 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor (𝒞M.join .transf z 𝒞.∘ (𝒞M.funct .fmor g 𝒞.∘ f)))
    ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _)) ⟩
      𝒟M.funct .fmor h 𝒟.∘ (FM.transform .transf z 𝒟.∘ (F .fmor (𝒞M.join .transf z) 𝒟.∘ F .fmor (𝒞M.funct .fmor g 𝒞.∘ f)))
    ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
      𝒟M.funct .fmor h 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor (𝒞M.join .transf z) 𝒟.∘ F .fmor (𝒞M.funct .fmor g 𝒞.∘ f))
    ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong FM.preserve-join (F .fmor-comp _ _)) ⟩
      𝒟M.funct .fmor h 𝒟.∘ (𝒟M.join .transf _ 𝒟.∘ (𝒟M.funct .fmor (FM.transform .transf _) 𝒟.∘ FM.transform .transf _) 𝒟.∘ (F .fmor (𝒞M.funct .fmor g) 𝒟.∘ F .fmor f))
    ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
      𝒟M.funct .fmor h 𝒟.∘ (𝒟M.join .transf _ 𝒟.∘ (𝒟M.funct .fmor (FM.transform .transf _) 𝒟.∘ FM.transform .transf _ 𝒟.∘ (F .fmor (𝒞M.funct .fmor g) 𝒟.∘ F .fmor f)))
    ≈˘⟨ 𝒟.assoc _ _ _ ⟩
      (𝒟M.funct .fmor h 𝒟.∘ 𝒟M.join .transf _) 𝒟.∘ (𝒟M.funct .fmor (FM.transform .transf _) 𝒟.∘ FM.transform .transf _ 𝒟.∘ (F .fmor (𝒞M.funct .fmor g) 𝒟.∘ F .fmor f))
    ≈⟨ 𝒟.∘-cong (𝒟M.join .natural h) (𝒟.assoc _ _ _) ⟩
      (𝒟M.join .transf _ 𝒟.∘ 𝒟M.funct .fmor (𝒟M.funct .fmor h)) 𝒟.∘ (𝒟M.funct .fmor (FM.transform .transf _) 𝒟.∘ (FM.transform .transf _ 𝒟.∘ (F .fmor (𝒞M.funct .fmor g) 𝒟.∘ F .fmor f)))
    ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _)) ⟩
      (𝒟M.join .transf _ 𝒟.∘ 𝒟M.funct .fmor (𝒟M.funct .fmor h)) 𝒟.∘ (𝒟M.funct .fmor (FM.transform .transf _) 𝒟.∘ (FM.transform .transf _ 𝒟.∘ F .fmor (𝒞M.funct .fmor g) 𝒟.∘ F .fmor f))
    ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong (FM.transform .natural g) 𝒟.≈-refl)) ⟩
      (𝒟M.join .transf _ 𝒟.∘ 𝒟M.funct .fmor (𝒟M.funct .fmor h)) 𝒟.∘ (𝒟M.funct .fmor (FM.transform .transf _) 𝒟.∘ (𝒟M.funct .fmor (F .fmor g) 𝒟.∘ FM.transform .transf _ 𝒟.∘ F .fmor f))
    ≈⟨ 𝒟.assoc _ _ _ ⟩
      𝒟M.join .transf _ 𝒟.∘ (𝒟M.funct .fmor (𝒟M.funct .fmor h) 𝒟.∘ (𝒟M.funct .fmor (FM.transform .transf _) 𝒟.∘ (𝒟M.funct .fmor (F .fmor g) 𝒟.∘ FM.transform .transf _ 𝒟.∘ F .fmor f)))
    ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _))) ⟩
      𝒟M.join .transf _ 𝒟.∘ (𝒟M.funct .fmor (𝒟M.funct .fmor h) 𝒟.∘ (𝒟M.funct .fmor (FM.transform .transf _) 𝒟.∘ (𝒟M.funct .fmor (F .fmor g) 𝒟.∘ (FM.transform .transf _ 𝒟.∘ F .fmor f))))
    ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
      𝒟M.join .transf _ 𝒟.∘ (𝒟M.funct .fmor (𝒟M.funct .fmor h) 𝒟.∘ 𝒟M.funct .fmor (FM.transform .transf _) 𝒟.∘ (𝒟M.funct .fmor (F .fmor g) 𝒟.∘ (FM.transform .transf _ 𝒟.∘ F .fmor f)))
    ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong (𝒟M.funct .fmor-comp _ _) 𝒟.≈-refl) ⟩
      𝒟M.join .transf _ 𝒟.∘ (𝒟M.funct .fmor (𝒟M.funct .fmor h 𝒟.∘ FM.transform .transf _) 𝒟.∘ (𝒟M.funct .fmor (F .fmor g) 𝒟.∘ (FM.transform .transf _ 𝒟.∘ F .fmor f)))
    ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
      𝒟M.join .transf _ 𝒟.∘ (𝒟M.funct .fmor (𝒟M.funct .fmor h 𝒟.∘ FM.transform .transf _) 𝒟.∘ 𝒟M.funct .fmor (F .fmor g) 𝒟.∘ (FM.transform .transf _ 𝒟.∘ F .fmor f))
    ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong (𝒟M.funct .fmor-comp _ _) 𝒟.≈-refl) ⟩
      𝒟M.join .transf _ 𝒟.∘ (𝒟M.funct .fmor (𝒟M.funct .fmor h 𝒟.∘ FM.transform .transf _ 𝒟.∘ F .fmor g) 𝒟.∘ (FM.transform .transf _ 𝒟.∘ F .fmor f))
    ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong (𝒟M.funct .fmor-cong (𝒟.assoc _ _ _)) 𝒟.≈-refl) ⟩
      𝒟M.join .transf _ 𝒟.∘ (𝒟M.funct .fmor (𝒟M.funct .fmor h 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor g)) 𝒟.∘ (FM.transform .transf y 𝒟.∘ F .fmor f))
    ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right ⟩
      𝒟M.join .transf _ 𝒟.∘ (𝒟M.funct .fmor (𝒟M.funct .fmor h 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor g)) 𝒟.∘ (FM.transform .transf y 𝒟.∘ F .fmor f) 𝒟.∘ 𝒟.id _)
    ∎)
    where open ≈-Reasoning 𝒟.isEquiv

open Monad-hat-pred 𝒞M using (MP)

open PShPredicate
open setoid-predicate.Predicate
open setoid-predicate._⊑_
open _⊑_

-- The “𝒞 definability” predicate.
Definable : ∀ x → PShPredicate (G .fobj (F .fobj x))
Definable x .pred y .pred (lift f) = LiftP (o₁ ⊔ o₂ ⊔ lsuc 0ℓ) (∃ (y 𝒞.⇒ x) λ g → F .fmor g 𝒟.≈ f)
Definable x .pred y .pred-≃ {lift f₁} {lift f₂} (lift f₁≈f₂) (lift (g , eq)) = lift (g , 𝒟.≈-trans eq f₁≈f₂)
Definable x .pred-mor h .*⊑* (lift f) (lift (g , eq)) =
   lift (g 𝒞.∘ h , 𝒟.≈-trans (F .fmor-comp g h) (𝒟.∘-cong eq 𝒟.≈-refl))

Definable-reindex : ∀ {x y} (f : x 𝒞.⇒ y) → Definable x ⊑ (Definable y [ G .fmor (F .fmor f) ])
Definable-reindex {x} {y} f .*⊑* a .*⊑* (lift g) (lift (h , eq)) =
  lift (f 𝒞.∘ h , (begin
    F .fmor (f 𝒞.∘ h)
  ≈⟨ F .fmor-comp _ _ ⟩
    F .fmor f 𝒟.∘ F .fmor h
  ≈⟨ 𝒟.∘-cong 𝒟.≈-refl eq ⟩
    F .fmor f 𝒟.∘ g
  ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right ⟩
    F .fmor f 𝒟.∘ (g 𝒟.∘ 𝒟.id _)
  ∎))
  where open ≈-Reasoning 𝒟.isEquiv

Definable-terminal : TT ⊑ (Definable 𝒞T.witness [ G .fmor (Category.IsIso.inverse FT) ])
Definable-terminal .*⊑* a .*⊑* (lift f) _ =
  lift (𝒞T.is-terminal .IsTerminal.to-terminal , (begin
    F .fmor (𝒞T.is-terminal .IsTerminal.to-terminal)
  ≈˘⟨ 𝒟.id-left ⟩
    𝒟.id _ 𝒟.∘ F .fmor (𝒞T.is-terminal .IsTerminal.to-terminal)
  ≈˘⟨ 𝒟.∘-cong (Category.IsIso.inverse∘f≈id FT) 𝒟.≈-refl ⟩
    (Category.IsIso.inverse FT 𝒟.∘ 𝒟T.to-terminal) 𝒟.∘ F .fmor (𝒞T.is-terminal .IsTerminal.to-terminal)
  ≈⟨ 𝒟.assoc _ _ _ ⟩
    Category.IsIso.inverse FT 𝒟.∘ (𝒟T.to-terminal 𝒟.∘ F .fmor (𝒞T.is-terminal .IsTerminal.to-terminal))
  ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟T.to-terminal-unique _ _) ⟩
    Category.IsIso.inverse FT 𝒟.∘ (f 𝒟.∘ 𝒟.id _)
  ∎))
  where open ≈-Reasoning 𝒟.isEquiv

Definable-products : ∀ {x y} →
              ((Definable x [ G .fmor 𝒟P.p₁ ]) && (Definable y [ G .fmor 𝒟P.p₂ ])) ⊑ Definable (𝒞P.prod x y) [ G .fmor (Category.IsIso.inverse FP) ]
Definable-products {x} {y} .*⊑* a .*⊑* (lift f) (lift (g₁ , eq₁) , lift (g₂ , eq₂)) =
  lift (𝒞P.pair g₁ g₂ , (begin
          F .fmor (𝒞P.pair g₁ g₂)
        ≈˘⟨ F-pair ⟩
          mul 𝒟.∘ 𝒟P.pair (F .fmor g₁) (F .fmor g₂)
        ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟P.pair-cong eq₁ eq₂) ⟩
          mul 𝒟.∘ 𝒟P.pair (𝒟P.p₁ 𝒟.∘ (f 𝒟.∘ 𝒟.id _)) (𝒟P.p₂ 𝒟.∘ (f 𝒟.∘ 𝒟.id _))
        ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟P.pair-ext _) ⟩
          mul 𝒟.∘ (f 𝒟.∘ 𝒟.id _)
        ∎))
  where open ≈-Reasoning 𝒟.isEquiv
        open preserve-chosen-products-consequences F 𝒞P 𝒟P FP

module MDistrib = Distrib 𝒞M.funct

-- Covers pull back along morphisms into the monad functor's images, using its
-- preservation of finite and set-indexed coproducts: pull back the functor
-- image of the cover, and correct the injections.
FMpull : ∀ {x y} (c : Cover x) (g : y 𝒞.⇒ 𝒞M.funct .fobj x) → MDistrib.FCoverPullback c g
FMpull (bin c) g = fp
  where
    open MDistrib.FCoverPullback
    open preserve-chosen-coproducts-consequences 𝒞M.funct 𝒞CP 𝒞CP FM-C using (iso)

    Mc : BinCover (𝒞M.funct .fobj _)
    Mc .BinCover.y₁ = 𝒞M.funct .fobj (c .BinCover.y₁)
    Mc .BinCover.y₂ = 𝒞M.funct .fobj (c .BinCover.y₂)
    Mc .BinCover.iso = 𝒞.Iso-trans iso (functor-preserve-iso 𝒞M.funct (c .BinCover.iso))

    pb = covPull (bin Mc) g

    bridge₁ : 𝒞M.funct .fmor (cInj (bin c) inl) 𝒞.≈ cInj (bin Mc) inl
    bridge₁ =
      𝒞.≈-trans (𝒞M.funct .fmor-comp _ _)
        (𝒞.≈-trans (𝒞.∘-cong 𝒞.≈-refl (𝒞.≈-sym (𝒞CP.copair-in₁ _ _))) (𝒞.≈-sym (𝒞.assoc _ _ _)))
    bridge₂ : 𝒞M.funct .fmor (cInj (bin c) inr) 𝒞.≈ cInj (bin Mc) inr
    bridge₂ =
      𝒞.≈-trans (𝒞M.funct .fmor-comp _ _)
        (𝒞.≈-trans (𝒞.∘-cong 𝒞.≈-refl (𝒞.≈-sym (𝒞CP.copair-in₂ _ _))) (𝒞.≈-sym (𝒞.assoc _ _ _)))

    fp : MDistrib.FCoverPullback (bin c) g
    fp .cover = pb .CoverPullback.cover
    fp .reix s = s
    fp .leg inl = pb .CoverPullback.leg inl
    fp .leg inr = pb .CoverPullback.leg inr
    fp .eq inl = 𝒞.≈-trans (𝒞.∘-cong bridge₁ 𝒞.≈-refl) (pb .CoverPullback.eq inl)
    fp .eq inr = 𝒞.≈-trans (𝒞.∘-cong bridge₂ 𝒞.≈-refl) (pb .CoverPullback.eq inr)
FMpull (idx c) g with FM-DC (c .IdxCover.S) (c .IdxCover.D)
... | Miso , Mcompat = fp
  where
    open MDistrib.FCoverPullback

    Mc : IdxCover (𝒞M.funct .fobj _)
    Mc .IdxCover.S = c .IdxCover.S
    Mc .IdxCover.D = 𝒞M.funct ∘F (c .IdxCover.D)
    Mc .IdxCover.iso = 𝒞.Iso-trans Miso (functor-preserve-iso 𝒞M.funct (c .IdxCover.iso))

    pb = covPull (idx Mc) g

    bridge : ∀ s → 𝒞M.funct .fmor (cInj (idx c) (lift s)) 𝒞.≈ cInj (idx Mc) (lift s)
    bridge s =
      𝒞.≈-trans (𝒞M.funct .fmor-comp _ _)
        (𝒞.≈-trans (𝒞.∘-cong 𝒞.≈-refl (𝒞.≈-sym (Mcompat s))) (𝒞.≈-sym (𝒞.assoc _ _ _)))

    fp : MDistrib.FCoverPullback (idx c) g
    fp .cover = pb .CoverPullback.cover
    fp .reix (lift s) = lift s
    fp .leg (lift s) = pb .CoverPullback.leg (lift s)
    fp .eq (lift s) = 𝒞.≈-trans (𝒞.∘-cong (bridge s) 𝒞.≈-refl) (pb .CoverPullback.eq (lift s))

Definable-coproducts : ∀ {x y} →
                Definable (𝒞CP.coprod x y) ⊑
                𝐂 ((Definable x ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩) ++ (Definable y ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩))
Definable-coproducts {x} {y} .*⊑* z .*⊑* (lift g) (lift (f , eq)) =
  node (pb .CoverPullback.cover) xs ts eqs
  where
    c₀ : BinCover (𝒞CP.coprod x y)
    c₀ .BinCover.y₁ = x
    c₀ .BinCover.y₂ = y
    c₀ .BinCover.iso = 𝒞.Iso-refl

    pb = covPull (bin c₀) f

    h₁ = pb .CoverPullback.leg inl
    h₂ = pb .CoverPullback.leg inr

    xs : ∀ s → Setoid.Carrier (G .fobj (F .fobj (𝒞CP.coprod x y)) .fobj (cDom (pb .CoverPullback.cover) s))
    xs inl = lift (F .fmor (𝒞CP.in₁ 𝒞.∘ h₁))
    xs inr = lift (F .fmor (𝒞CP.in₂ 𝒞.∘ h₂))

    step : ∀ s → (cInj (bin c₀) s 𝒞.∘ pb .CoverPullback.leg s) 𝒞.≈ (f 𝒞.∘ cInj (pb .CoverPullback.cover) s)
    step = pb .CoverPullback.eq

    -- The summand restriction agrees with the reindexed witness.
    eq' : ∀ s → F .fmor (cInj (bin c₀) s 𝒞.∘ pb .CoverPullback.leg s) 𝒟.≈ (g 𝒟.∘ F .fmor (cInj (pb .CoverPullback.cover) s))
    eq' s = begin
        F .fmor (cInj (bin c₀) s 𝒞.∘ pb .CoverPullback.leg s)
      ≈⟨ F .fmor-cong (step s) ⟩
        F .fmor (f 𝒞.∘ cInj (pb .CoverPullback.cover) s)
      ≈⟨ F .fmor-comp _ _ ⟩
        F .fmor f 𝒟.∘ F .fmor (cInj (pb .CoverPullback.cover) s)
      ≈⟨ 𝒟.∘-cong eq 𝒟.≈-refl ⟩
        g 𝒟.∘ F .fmor (cInj (pb .CoverPullback.cover) s)
      ∎
      where open ≈-Reasoning 𝒟.isEquiv

    -- inl/inr injections differ from cInj (bin c₀) only by the identity iso.
    inj₁≈ : F .fmor (𝒞CP.in₁ 𝒞.∘ h₁) 𝒟.≈ F .fmor (cInj (bin c₀) inl 𝒞.∘ h₁)
    inj₁≈ = F .fmor-cong (𝒞.∘-cong (𝒞.≈-sym 𝒞.id-left) 𝒞.≈-refl)

    inj₂≈ : F .fmor (𝒞CP.in₂ 𝒞.∘ h₂) 𝒟.≈ F .fmor (cInj (bin c₀) inr 𝒞.∘ h₂)
    inj₂≈ = F .fmor-cong (𝒞.∘-cong (𝒞.≈-sym 𝒞.id-left) 𝒞.≈-refl)

    ts : ∀ s → Context (G .fobj (F .fobj (𝒞CP.coprod x y)))
                 ((Definable x ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩) ++ (Definable y ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩))
                 (cDom (pb .CoverPullback.cover) s) (xs s)
    ts inl = leaf (inj₁ (lift (F .fmor h₁) , lift (h₁ , 𝒟.≈-refl) ,
                         lift (𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right) (𝒟.≈-sym (F .fmor-comp _ _)))))
    ts inr = leaf (inj₂ (lift (F .fmor h₂) , lift (h₂ , 𝒟.≈-refl) ,
                         lift (𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right) (𝒟.≈-sym (F .fmor-comp _ _)))))

    eqs : ∀ s → Setoid._≈_ (G .fobj (F .fobj (𝒞CP.coprod x y)) .fobj (cDom (pb .CoverPullback.cover) s))
                  (xs s)
                  (G .fobj (F .fobj (𝒞CP.coprod x y)) .fmor (cInj (pb .CoverPullback.cover) s) .prop-setoid._⇒_.func (lift g))
    eqs inl = lift (𝒟.≈-trans inj₁≈ (eq' inl))
    eqs inr = lift (𝒟.≈-trans inj₂≈ (eq' inr))

-- Set-indexed form.
Definable-coproducts-indexed : ∀ {S : Setoid 0ℓ 0ℓ} {D : Functor (setoid→category S) 𝒞} →
                               Definable (SI.∐ S D) ⊑
                               𝐂 (⋁ (S .Setoid.Carrier) (λ s → Definable (D .fobj s) ⟨ G .fmor (F .fmor (SI.inj D s)) ⟩))
Definable-coproducts-indexed {S} {D} .*⊑* z .*⊑* (lift g) (lift (f , eq)) =
  node (pb .CoverPullback.cover) xs ts eqs
  where
    c₀ : IdxCover (SI.∐ S D)
    c₀ .IdxCover.S = S
    c₀ .IdxCover.D = D
    c₀ .IdxCover.iso = 𝒞.Iso-refl

    pb = covPull (idx c₀) f

    xs : ∀ s → Setoid.Carrier (G .fobj (F .fobj (SI.∐ S D)) .fobj (cDom (pb .CoverPullback.cover) s))
    xs (lift s) = lift (F .fmor (SI.inj D s 𝒞.∘ pb .CoverPullback.leg (lift s)))

    -- The summand restriction agrees with the reindexed witness.
    eq' : ∀ s → F .fmor (cInj (idx c₀) s 𝒞.∘ pb .CoverPullback.leg s) 𝒟.≈ (g 𝒟.∘ F .fmor (cInj (pb .CoverPullback.cover) s))
    eq' s = begin
        F .fmor (cInj (idx c₀) s 𝒞.∘ pb .CoverPullback.leg s)
      ≈⟨ F .fmor-cong (pb .CoverPullback.eq s) ⟩
        F .fmor (f 𝒞.∘ cInj (pb .CoverPullback.cover) s)
      ≈⟨ F .fmor-comp _ _ ⟩
        F .fmor f 𝒟.∘ F .fmor (cInj (pb .CoverPullback.cover) s)
      ≈⟨ 𝒟.∘-cong eq 𝒟.≈-refl ⟩
        g 𝒟.∘ F .fmor (cInj (pb .CoverPullback.cover) s)
      ∎
      where open ≈-Reasoning 𝒟.isEquiv

    ts : ∀ s → Context (G .fobj (F .fobj (SI.∐ S D)))
                 (⋁ (S .Setoid.Carrier) (λ s → Definable (D .fobj s) ⟨ G .fmor (F .fmor (SI.inj D s)) ⟩))
                 (cDom (pb .CoverPullback.cover) s) (xs s)
    ts (lift s) = leaf (s , (lift (F .fmor (pb .CoverPullback.leg (lift s))) , lift (pb .CoverPullback.leg (lift s) , 𝒟.≈-refl) ,
                        lift (𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right) (𝒟.≈-sym (F .fmor-comp _ _)))))

    eqs : ∀ s → Setoid._≈_ (G .fobj (F .fobj (SI.∐ S D)) .fobj (cDom (pb .CoverPullback.cover) s))
                  (xs s)
                  (G .fobj (F .fobj (SI.∐ S D)) .fmor (cInj (pb .CoverPullback.cover) s) .prop-setoid._⇒_.func (lift g))
    eqs (lift s) = lift (𝒟.≈-trans (F .fmor-cong (𝒞.∘-cong (𝒞.≈-sym 𝒞.id-left) 𝒞.≈-refl)) (eq' (lift s)))

open FunctorPred
open MonadPred

Definable-monad : ∀ {x} → Definable (𝒞M.funct .fobj x)
                          ⊑ MP .liftF (Definable x) ⟨ (𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F)) PSh⟨𝒞⟩.∘ G-monad .transf (F .fobj x) ⟩
Definable-monad {x} .*⊑* a .*⊑* (lift f) (lift (g , Fg≈f)) =
  (x , g , lift (𝒟.id _)) ,
  ((x , g , lift (𝒟.id _)) , (liftS (eq-stop _)) , lift (𝒞.id _ , F .fmor-id)) ,
  lift (begin
    FM.transform⁻¹ .transf x 𝒟.∘ (𝒟M.funct .fmor (𝒟.id _) 𝒟.∘ (FM.transform .transf x 𝒟.∘ F .fmor g) 𝒟.∘ 𝒟.id _)
  ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong (𝒟.∘-cong (𝒟M.funct .fmor-id) (𝒟.∘-cong 𝒟.≈-refl Fg≈f)) 𝒟.≈-refl) ⟩
    FM.transform⁻¹ .transf x 𝒟.∘ (𝒟.id _ 𝒟.∘ (FM.transform .transf x 𝒟.∘ f) 𝒟.∘ 𝒟.id _)
  ≈⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right ⟩
    FM.transform⁻¹ .transf x 𝒟.∘ (𝒟.id _ 𝒟.∘ (FM.transform .transf x 𝒟.∘ f))
  ≈⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-left ⟩
    FM.transform⁻¹ .transf x 𝒟.∘ (FM.transform .transf x 𝒟.∘ f)
  ≈˘⟨ 𝒟.assoc _ _ _ ⟩
    (FM.transform⁻¹ .transf x 𝒟.∘ FM.transform .transf x) 𝒟.∘ f
  ≈⟨ 𝒟.∘-cong (Category.IsIso.inverse∘f≈id (FM.transf-iso x)) 𝒟.≈-refl ⟩
    𝒟.id _ 𝒟.∘ f
  ≈⟨ 𝒟.id-left ⟩
    f
  ∎)
  where open ≈-Reasoning 𝒟.isEquiv
        open UnaryDay 𝒞M.funct

Definable-monad⁻¹ : ∀ {x} → MP .liftF (Definable x)
                            ⊑ Definable (𝒞M.funct .fobj x) [ (𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F)) PSh⟨𝒞⟩.∘ G-monad .transf (F .fobj x) ]
Definable-monad⁻¹ {x} .*⊑* a .*⊑* (z , g , lift h) ((z' , g' , lift h') , liftS eq , lift (f , Ff≈h')) =
  lift (𝒞M.funct .fmor f 𝒞.∘ g' , (begin
          F .fmor (𝒞M.funct .fmor f 𝒞.∘ g')
        ≈⟨ F .fmor-comp _ _ ⟩
          F .fmor (𝒞M.funct .fmor f) 𝒟.∘ F .fmor g'
        ≈˘⟨ 𝒟.id-left ⟩
          𝒟.id _ 𝒟.∘ (F .fmor (𝒞M.funct .fmor f) 𝒟.∘ F .fmor g')
        ≈˘⟨ 𝒟.∘-cong (Category.IsIso.inverse∘f≈id (FM.transf-iso x)) 𝒟.≈-refl ⟩
          (FM.transform⁻¹ .transf x 𝒟.∘ FM.transform .transf x) 𝒟.∘ (F .fmor (𝒞M.funct .fmor f) 𝒟.∘ F .fmor g')
        ≈⟨ 𝒟.assoc _ _ _ ⟩
          FM.transform⁻¹ .transf x 𝒟.∘ (FM.transform .transf x 𝒟.∘ (F .fmor (𝒞M.funct .fmor f) 𝒟.∘ F .fmor g'))
        ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
          FM.transform⁻¹ .transf x 𝒟.∘ ((FM.transform .transf x 𝒟.∘ F .fmor (𝒞M.funct .fmor f)) 𝒟.∘ F .fmor g')
        ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong (FM.transform .natural f) 𝒟.≈-refl) ⟩
          FM.transform⁻¹ .transf x 𝒟.∘ ((𝒟M.funct .fmor (F .fmor f) 𝒟.∘ FM.transform .transf _) 𝒟.∘ F .fmor g')
        ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong (𝒟.∘-cong (𝒟M.funct .fmor-cong Ff≈h') 𝒟.≈-refl) 𝒟.≈-refl) ⟩
          FM.transform⁻¹ .transf x 𝒟.∘ ((𝒟M.funct .fmor h' 𝒟.∘ FM.transform .transf _) 𝒟.∘ F .fmor g')
        ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (helper _ _ _ _ _ _ eq) ⟩
          FM.transform⁻¹ .transf x 𝒟.∘ ((𝒟M.funct .fmor h 𝒟.∘ FM.transform .transf z) 𝒟.∘ F .fmor g)
        ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
          FM.transform⁻¹ .transf x 𝒟.∘ (𝒟M.funct .fmor h 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor g))
        ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right ⟩
          FM.transform⁻¹ .transf x 𝒟.∘ (𝒟M.funct .fmor h 𝒟.∘ (FM.transform .transf z 𝒟.∘ F .fmor g) 𝒟.∘ 𝒟.id _)
        ∎))
  where open UnaryDay 𝒞M.funct

        helper : ∀ z g h z' g' h' → M-hat-eq (z , g , lift h) (z' , g' , lift h') →
                 (𝒟M.funct .fmor h' 𝒟.∘ FM.transform .transf _) 𝒟.∘ F .fmor g' 𝒟.≈ (𝒟M.funct .fmor h 𝒟.∘ FM.transform .transf _) 𝒟.∘ F .fmor g
        helper z g h z' g' h' (eq-stop a) = 𝒟.≈-refl
        helper z g h z' g' h' (eq-step {y₂ = z''} {f₂ = g''} {Fy₂ = lift h''} {Fy = lift h₃} h₁ h₂ ϕ (lift ψ₁) (lift ψ₂) eq) = begin
            𝒟M.funct .fmor h' 𝒟.∘ FM.transform .transf z' 𝒟.∘ F .fmor g'
          ≈⟨ helper _ _ _ _ _ _ eq ⟩
            𝒟M.funct .fmor h'' 𝒟.∘ FM.transform .transf z'' 𝒟.∘ F .fmor g''
          ≈˘⟨ 𝒟.∘-cong (𝒟.∘-cong (𝒟M.funct .fmor-cong ψ₂) 𝒟.≈-refl) 𝒟.≈-refl ⟩
            𝒟M.funct .fmor (h₃ 𝒟.∘ F .fmor h₂) 𝒟.∘ FM.transform .transf z'' 𝒟.∘ F .fmor g''
          ≈⟨ 𝒟.∘-cong (𝒟.∘-cong (𝒟M.funct .fmor-comp _ _) 𝒟.≈-refl) 𝒟.≈-refl ⟩
            (𝒟M.funct .fmor h₃ 𝒟.∘ 𝒟M.funct .fmor (F .fmor h₂)) 𝒟.∘ FM.transform .transf z'' 𝒟.∘ F .fmor g''
          ≈⟨ 𝒟.∘-cong (𝒟.assoc _ _ _) 𝒟.≈-refl ⟩
            𝒟M.funct .fmor h₃ 𝒟.∘ (𝒟M.funct .fmor (F .fmor h₂) 𝒟.∘ FM.transform .transf z'') 𝒟.∘ F .fmor g''
          ≈⟨ 𝒟.∘-cong (𝒟.∘-cong 𝒟.≈-refl (FM.transform .natural h₂)) 𝒟.≈-refl ⟩
            𝒟M.funct .fmor h₃ 𝒟.∘ (FM.transform .transf _ 𝒟.∘ F .fmor (𝒞M.funct .fmor h₂)) 𝒟.∘ F .fmor g''
          ≈⟨ 𝒟.assoc _ _ _ ⟩
            𝒟M.funct .fmor h₃ 𝒟.∘ ((FM.transform .transf _ 𝒟.∘ F .fmor (𝒞M.funct .fmor h₂)) 𝒟.∘ F .fmor g'')
          ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
            𝒟M.funct .fmor h₃ 𝒟.∘ (FM.transform .transf _ 𝒟.∘ (F .fmor (𝒞M.funct .fmor h₂) 𝒟.∘ F .fmor g''))
          ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _)) ⟩
            𝒟M.funct .fmor h₃ 𝒟.∘ (FM.transform .transf _ 𝒟.∘ (F .fmor (𝒞M.funct .fmor h₂ 𝒞.∘ g'')))
          ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl (F .fmor-cong (𝒞.≈-sym ϕ))) ⟩
            𝒟M.funct .fmor h₃ 𝒟.∘ (FM.transform .transf _ 𝒟.∘ (F .fmor (𝒞M.funct .fmor h₁ 𝒞.∘ g)))
          ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _)) ⟩
            𝒟M.funct .fmor h₃ 𝒟.∘ (FM.transform .transf _ 𝒟.∘ (F .fmor (𝒞M.funct .fmor h₁) 𝒟.∘ F .fmor g))
          ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
            𝒟M.funct .fmor h₃ 𝒟.∘ (FM.transform .transf _ 𝒟.∘ F .fmor (𝒞M.funct .fmor h₁) 𝒟.∘ F .fmor g)
          ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong (FM.transform .natural h₁) 𝒟.≈-refl) ⟩
            𝒟M.funct .fmor h₃ 𝒟.∘ (𝒟M.funct .fmor (F .fmor h₁) 𝒟.∘ FM.transform .transf _ 𝒟.∘ F .fmor g)
          ≈˘⟨ 𝒟.assoc _ _ _ ⟩
            𝒟M.funct .fmor h₃ 𝒟.∘ (𝒟M.funct .fmor (F .fmor h₁) 𝒟.∘ FM.transform .transf _) 𝒟.∘ F .fmor g
          ≈˘⟨ 𝒟.∘-cong (𝒟.assoc _ _ _) 𝒟.≈-refl ⟩
            (𝒟M.funct .fmor h₃ 𝒟.∘ 𝒟M.funct .fmor (F .fmor h₁)) 𝒟.∘ FM.transform .transf _ 𝒟.∘ F .fmor g
          ≈˘⟨ 𝒟.∘-cong (𝒟.∘-cong (𝒟M.funct .fmor-comp _ _) 𝒟.≈-refl) 𝒟.≈-refl ⟩
            𝒟M.funct .fmor (h₃ 𝒟.∘ F .fmor h₁) 𝒟.∘ FM.transform .transf _ 𝒟.∘ F .fmor g
          ≈⟨ 𝒟.∘-cong (𝒟.∘-cong (𝒟M.funct .fmor-cong ψ₁) 𝒟.≈-refl) 𝒟.≈-refl ⟩
            𝒟M.funct .fmor h 𝒟.∘ FM.transform .transf z 𝒟.∘ F .fmor g
          ∎
          where open ≈-Reasoning 𝒟.isEquiv

        open ≈-Reasoning 𝒟.isEquiv

-- FIXME: this ought to be true for any predicate that is closed under
-- glueing of sums.
Definable-closed : ∀ {X Y} (f : F .fobj X 𝒟.⇒ F .fobj Y) →
       Context (G .fobj (F .fobj Y)) (Definable Y) X (lift f) →
       ∃ (X 𝒞.⇒ Y) (λ g → F .fmor g 𝒟.≈ f)
Definable-closed f (leaf (lift p)) = p
Definable-closed f (node (bin c) xs ts eqs) with xs inl | xs inr | eqs inl | eqs inr | ts inl | ts inr
... | lift f₁ | lift f₂ | lift eq₁ | lift eq₂ | t₁ | t₂ with Definable-closed f₁ t₁
... | (g₁ , eq₃) with Definable-closed f₂ t₂
... | (g₂ , eq₄) = 𝒞CP.copair g₁ g₂ 𝒞.∘ i₀ .bwd ,
      (begin
        F .fmor (𝒞CP.copair g₁ g₂ 𝒞.∘ i₀ .bwd)
      ≈⟨ F .fmor-comp _ _ ⟩
        F .fmor (𝒞CP.copair g₁ g₂) 𝒟.∘ F .fmor (i₀ .bwd)
      ≈˘⟨ 𝒟.∘-cong F-copair 𝒟.≈-refl ⟩
        (𝒟CP.copair (F .fmor g₁) (F .fmor g₂) 𝒟.∘ mul) 𝒟.∘ F .fmor (i₀ .bwd)
      ≈⟨ 𝒟.assoc _ _ _ ⟩
        𝒟CP.copair (F .fmor g₁) (F .fmor g₂) 𝒟.∘ (mul 𝒟.∘ F .fmor (i₀ .bwd))
      ≈⟨ 𝒟.∘-cong (𝒟CP.copair-cong eq₃ eq₄) 𝒟.≈-refl ⟩
        𝒟CP.copair f₁ f₂ 𝒟.∘ (mul 𝒟.∘ F .fmor (i₀ .bwd))
      ≈⟨ 𝒟.∘-cong (𝒟CP.copair-cong eq₁ eq₂ ) 𝒟.≈-refl ⟩
        𝒟CP.copair (f 𝒟.∘ F .fmor (i₀ .fwd 𝒞.∘ 𝒞CP.in₁)) (f 𝒟.∘ F .fmor (i₀ .fwd 𝒞.∘ 𝒞CP.in₂)) 𝒟.∘ (mul 𝒟.∘ F .fmor (i₀ .bwd))
      ≈⟨ 𝒟.∘-cong (𝒟CP.copair-cong (𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _)) (𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _))) 𝒟.≈-refl ⟩
        𝒟CP.copair (f 𝒟.∘ (F .fmor (i₀ .fwd) 𝒟.∘ F .fmor 𝒞CP.in₁)) (f 𝒟.∘ (F .fmor (i₀ .fwd) 𝒟.∘ F .fmor 𝒞CP.in₂)) 𝒟.∘ (mul 𝒟.∘ F .fmor (i₀ .bwd))
      ≈˘⟨ 𝒟.∘-cong (𝒟CP.copair-cong (𝒟.assoc _ _ _) (𝒟.assoc _ _ _)) 𝒟.≈-refl ⟩
        𝒟CP.copair ((f 𝒟.∘ F .fmor (i₀ .fwd)) 𝒟.∘ F .fmor 𝒞CP.in₁) ((f 𝒟.∘ F .fmor (i₀ .fwd)) 𝒟.∘ F .fmor 𝒞CP.in₂) 𝒟.∘ (mul 𝒟.∘ F .fmor (i₀ .bwd))
      ≈˘⟨ 𝒟.∘-cong (𝒟CP.copair-natural _ _ _) 𝒟.≈-refl ⟩
        ((f 𝒟.∘ F .fmor (i₀ .fwd)) 𝒟.∘ 𝒟CP.copair (F .fmor 𝒞CP.in₁) (F .fmor 𝒞CP.in₂)) 𝒟.∘ (mul 𝒟.∘ F .fmor (i₀ .bwd))
      ≈⟨ 𝒟.assoc _ _ _ ⟩
        (f 𝒟.∘ F .fmor (i₀ .fwd)) 𝒟.∘ (𝒟CP.copair (F .fmor 𝒞CP.in₁) (F .fmor 𝒞CP.in₂) 𝒟.∘ (mul 𝒟.∘ F .fmor (i₀ .bwd)))
      ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
        (f 𝒟.∘ F .fmor (i₀ .fwd)) 𝒟.∘ ((𝒟CP.copair (F .fmor 𝒞CP.in₁) (F .fmor 𝒞CP.in₂) 𝒟.∘ mul) 𝒟.∘ F .fmor (i₀ .bwd))
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong (Category.IsIso.f∘inverse≈id FC) 𝒟.≈-refl) ⟩
        (f 𝒟.∘ F .fmor (i₀ .fwd)) 𝒟.∘ (𝒟.id _ 𝒟.∘ F .fmor (i₀ .bwd))
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-left ⟩
        (f 𝒟.∘ F .fmor (i₀ .fwd)) 𝒟.∘ F .fmor (i₀ .bwd)
      ≈⟨ 𝒟.assoc _ _ _ ⟩
        f 𝒟.∘ (F .fmor (i₀ .fwd) 𝒟.∘ F .fmor (i₀ .bwd))
      ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _) ⟩
        f 𝒟.∘ F .fmor (i₀ .fwd 𝒞.∘ i₀ .bwd)
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-cong (i₀ .fwd∘bwd≈id)) ⟩
        f 𝒟.∘ F .fmor (𝒞.id _)
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-id) ⟩
        f 𝒟.∘ 𝒟.id _
      ≈⟨ 𝒟.id-right ⟩
        f
      ∎)
  where open ≈-Reasoning 𝒟.isEquiv
        i₀ = c .BinCover.iso
        open preserve-chosen-coproducts-consequences F 𝒞CP 𝒟CP FC
        open 𝒞.Iso
Definable-closed {X} {Y} f (node (idx c) xs ts eqs) = g , Fg≈f
  where
    open NatTrans
    open ≃-NatTrans
    S = c .IdxCover.S
    D = c .IdxCover.D
    iso = c .IdxCover.iso
    module DC = Colimit (𝒞DC S D)

    inj : (s : S .Setoid.Carrier) → D .fobj s 𝒞.⇒ DC.apex
    inj s = DC.cocone .transf s

    fs : (s : S .Setoid.Carrier) → F .fobj (D .fobj s) 𝒟.⇒ F .fobj Y
    fs s = lower (xs (lift s))

    fs-eq : (s : S .Setoid.Carrier) → fs s 𝒟.≈ (f 𝒟.∘ F .fmor (iso .𝒞.Iso.fwd 𝒞.∘ inj s))
    fs-eq s = lower (eqs (lift s))

    -- The summand restrictions are definable; pick their witnesses uniformly.
    gs : (s : S .Setoid.Carrier) → D .fobj s 𝒞.⇒ Y
    gs s = ∃ₛ.fst (Fdef (fs s) ⟪ Definable-closed (fs s) (ts (lift s)) ⟫)

    Fgs : (s : S .Setoid.Carrier) → F .fmor (gs s) 𝒟.≈ fs s
    Fgs s = ∃ₛ.snd (Fdef (fs s) ⟪ Definable-closed (fs s) (ts (lift s)) ⟫)

    -- The witnesses form a cocone, faithfulness reflecting the naturality
    -- squares that hold after applying F.
    gs-cocone : NatTrans D (constF (setoid→category S) Y)
    gs-cocone .transf = gs
    gs-cocone .natural {s} {s'} ⟪ e ⟫ = 𝒞.≈-trans 𝒞.id-left (𝒞.≈-sym (F-faithful faith))
      where
        faith : F .fmor (gs s' 𝒞.∘ D .fmor ⟪ e ⟫) 𝒟.≈ F .fmor (gs s)
        faith = begin
            F .fmor (gs s' 𝒞.∘ D .fmor ⟪ e ⟫)
          ≈⟨ F .fmor-comp _ _ ⟩
            F .fmor (gs s') 𝒟.∘ F .fmor (D .fmor ⟪ e ⟫)
          ≈⟨ 𝒟.∘-cong (Fgs s') 𝒟.≈-refl ⟩
            fs s' 𝒟.∘ F .fmor (D .fmor ⟪ e ⟫)
          ≈⟨ 𝒟.∘-cong (fs-eq s') 𝒟.≈-refl ⟩
            (f 𝒟.∘ F .fmor (iso .𝒞.Iso.fwd 𝒞.∘ inj s')) 𝒟.∘ F .fmor (D .fmor ⟪ e ⟫)
          ≈⟨ 𝒟.assoc _ _ _ ⟩
            f 𝒟.∘ (F .fmor (iso .𝒞.Iso.fwd 𝒞.∘ inj s') 𝒟.∘ F .fmor (D .fmor ⟪ e ⟫))
          ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _) ⟩
            f 𝒟.∘ F .fmor ((iso .𝒞.Iso.fwd 𝒞.∘ inj s') 𝒞.∘ D .fmor ⟪ e ⟫)
          ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-cong (𝒞.assoc _ _ _)) ⟩
            f 𝒟.∘ F .fmor (iso .𝒞.Iso.fwd 𝒞.∘ (inj s' 𝒞.∘ D .fmor ⟪ e ⟫))
          ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-cong (𝒞.∘-cong 𝒞.≈-refl (𝒞.≈-trans (𝒞.≈-sym (DC.cocone .natural ⟪ e ⟫)) 𝒞.id-left))) ⟩
            f 𝒟.∘ F .fmor (iso .𝒞.Iso.fwd 𝒞.∘ inj s)
          ≈˘⟨ fs-eq s ⟩
            fs s
          ≈˘⟨ Fgs s ⟩
            F .fmor (gs s)
          ∎
          where open ≈-Reasoning 𝒟.isEquiv

    g₀ : DC.apex 𝒞.⇒ Y
    g₀ = DC.colambda Y gs-cocone

    g : X 𝒞.⇒ Y
    g = g₀ 𝒞.∘ iso .𝒞.Iso.bwd

    -- F takes the injections to a jointly-epic family (F preserves the
    -- coproduct), so agreement on injections gives equality.
    module DCF = Colimit (𝒟DC S (F ∘F D))
    Fiso    = ∃ₛ.fst (F-DC S D)
    Fcompat = ∃ₛ.snd (F-DC S D)

    F-epi : ∀ {Z} {h₁ h₂ : F .fobj DC.apex 𝒟.⇒ Z} →
            (∀ s → (h₁ 𝒟.∘ F .fmor (inj s)) 𝒟.≈ (h₂ 𝒟.∘ F .fmor (inj s))) → h₁ 𝒟.≈ h₂
    F-epi {Z} {h₁} {h₂} hyp = outer
      where
        uni : ∀ s → ((h₁ 𝒟.∘ Fiso .𝒟.Iso.fwd) 𝒟.∘ DCF.cocone .transf s)
                    𝒟.≈ ((h₂ 𝒟.∘ Fiso .𝒟.Iso.fwd) 𝒟.∘ DCF.cocone .transf s)
        uni s = begin
            (h₁ 𝒟.∘ Fiso .𝒟.Iso.fwd) 𝒟.∘ DCF.cocone .transf s
          ≈⟨ 𝒟.assoc _ _ _ ⟩
            h₁ 𝒟.∘ (Fiso .𝒟.Iso.fwd 𝒟.∘ DCF.cocone .transf s)
          ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (Fcompat s) ⟩
            h₁ 𝒟.∘ F .fmor (inj s)
          ≈⟨ hyp s ⟩
            h₂ 𝒟.∘ F .fmor (inj s)
          ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (Fcompat s) ⟩
            h₂ 𝒟.∘ (Fiso .𝒟.Iso.fwd 𝒟.∘ DCF.cocone .transf s)
          ≈˘⟨ 𝒟.assoc _ _ _ ⟩
            (h₂ 𝒟.∘ Fiso .𝒟.Iso.fwd) 𝒟.∘ DCF.cocone .transf s
          ∎
          where open ≈-Reasoning 𝒟.isEquiv

        outer : h₁ 𝒟.≈ h₂
        outer = begin
            h₁
          ≈˘⟨ 𝒟.id-right ⟩
            h₁ 𝒟.∘ 𝒟.id _
          ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (Fiso .𝒟.Iso.fwd∘bwd≈id) ⟩
            h₁ 𝒟.∘ (Fiso .𝒟.Iso.fwd 𝒟.∘ Fiso .𝒟.Iso.bwd)
          ≈˘⟨ 𝒟.assoc _ _ _ ⟩
            (h₁ 𝒟.∘ Fiso .𝒟.Iso.fwd) 𝒟.∘ Fiso .𝒟.Iso.bwd
          ≈⟨ 𝒟.∘-cong (colambda-unique (DCF.isColimit) uni) 𝒟.≈-refl ⟩
            (h₂ 𝒟.∘ Fiso .𝒟.Iso.fwd) 𝒟.∘ Fiso .𝒟.Iso.bwd
          ≈⟨ 𝒟.assoc _ _ _ ⟩
            h₂ 𝒟.∘ (Fiso .𝒟.Iso.fwd 𝒟.∘ Fiso .𝒟.Iso.bwd)
          ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (Fiso .𝒟.Iso.fwd∘bwd≈id) ⟩
            h₂ 𝒟.∘ 𝒟.id _
          ≈⟨ 𝒟.id-right ⟩
            h₂
          ∎
          where open ≈-Reasoning 𝒟.isEquiv

    Fg₀ : F .fmor g₀ 𝒟.≈ (f 𝒟.∘ F .fmor (iso .𝒞.Iso.fwd))
    Fg₀ = F-epi coeval-step
      where
        coeval-step : ∀ s → (F .fmor g₀ 𝒟.∘ F .fmor (inj s))
                            𝒟.≈ ((f 𝒟.∘ F .fmor (iso .𝒞.Iso.fwd)) 𝒟.∘ F .fmor (inj s))
        coeval-step s =
          𝒟.≈-trans (𝒟.≈-sym (F .fmor-comp g₀ (inj s)))
          (𝒟.≈-trans (F .fmor-cong (DC.colambda-coeval Y gs-cocone .transf-eq s))
          (𝒟.≈-trans (Fgs s)
          (𝒟.≈-trans (fs-eq s)
          (𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp (iso .𝒞.Iso.fwd) (inj s)))
                     (𝒟.≈-sym (𝒟.assoc _ _ _))))))

    Fg≈f : F .fmor g 𝒟.≈ f
    Fg≈f = begin
        F .fmor (g₀ 𝒞.∘ iso .𝒞.Iso.bwd)
      ≈⟨ F .fmor-comp _ _ ⟩
        F .fmor g₀ 𝒟.∘ F .fmor (iso .𝒞.Iso.bwd)
      ≈⟨ 𝒟.∘-cong Fg₀ 𝒟.≈-refl ⟩
        (f 𝒟.∘ F .fmor (iso .𝒞.Iso.fwd)) 𝒟.∘ F .fmor (iso .𝒞.Iso.bwd)
      ≈⟨ 𝒟.assoc _ _ _ ⟩
        f 𝒟.∘ (F .fmor (iso .𝒞.Iso.fwd) 𝒟.∘ F .fmor (iso .𝒞.Iso.bwd))
      ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _) ⟩
        f 𝒟.∘ F .fmor (iso .𝒞.Iso.fwd 𝒞.∘ iso .𝒞.Iso.bwd)
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-cong (iso .𝒞.Iso.fwd∘bwd≈id)) ⟩
        f 𝒟.∘ F .fmor (𝒞.id _)
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-id) ⟩
        f 𝒟.∘ 𝒟.id _
      ≈⟨ 𝒟.id-right ⟩
        f
      ∎
      where open ≈-Reasoning 𝒟.isEquiv

------------------------------------------------------------------------------
-- Now construct the category of Grothendieck Logical Relations

open 𝐂Monad _ MP (MDistrib.distrib FMpull)

module Gl = glueing-simple 𝒟 PSh⟨𝒞⟩ _ system G

-- This category has all the structure we need:
module GlCP = Gl.coproducts 𝒟CP
module GlCPM = HasCoproducts GlCP.coproducts
module GlPE = Gl.products-and-exponentials 𝒟T 𝒟P 𝒟E G-preserve-products
module GlPM = HasProducts GlPE.products
module GlT = HasTerminal GlPE.terminal
module GlM = Gl.monad-glueing 𝒟M _ G-MonadFunctor 𝐂MP

GDC : ∀ (A : Setoid 0ℓ 0ℓ) → HasColimits (setoid→category A) Gl.cat
GDC A = colimits where open Gl.colimits (setoid→category A) (𝒟DC A)

module Glued = Category Gl.cat
open Gl.Obj
open Gl._=>_
open Gl._≃m_

------------------------------------------------------------------------------
-- The category of first-order things embeds into the logical
-- relations category, and all first-order type formers are preserved.

GF : Functor 𝒞 Gl.cat
GF .fobj x .carrier = F .fobj x
GF .fobj x .pred = embed (Definable x)
GF .fmor f .morph = F .fmor f
GF .fmor {x} {y} f .presv = begin
    𝐂 (Definable x)
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (Definable-reindex f) ⟩
    𝐂 (Definable y [ G .fmor (F .fmor f) ])
  ≤⟨ 𝐂-[] ⟩
    𝐂 (Definable y) [ G .fmor (F .fmor f) ]
  ∎
  where open ≤-Reasoning ⊑-isPreorder
GF .fmor-cong f₁≈f₂ .f≃f = F .fmor-cong f₁≈f₂
GF .fmor-id .f≃f = F .fmor-id
GF .fmor-comp f g .f≃f = F .fmor-comp f g

-- GF is a finite product and coproduct preserving functor

presv-terminal : GlT.witness Glued.⇒ GF .fobj 𝒞T.witness
presv-terminal .morph = Category.IsIso.inverse FT
presv-terminal .presv = begin
    TT
  ≤⟨ 𝐂-isClosure .IsClosureOp.unit ⟩
    𝐂 TT
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono Definable-terminal ⟩
    𝐂 (Definable 𝒞T.witness [ G .fmor (Category.IsIso.inverse FT) ])
  ≤⟨ 𝐂-[] ⟩
    𝐂 (Definable 𝒞T.witness) [ G .fmor (Category.IsIso.inverse FT) ]
  ∎
  where open ≤-Reasoning ⊑-isPreorder

GF-preserve-terminal : Glued.IsIso (GlT.to-terminal {GF .fobj 𝒞T.witness})
GF-preserve-terminal .Category.IsIso.inverse = presv-terminal
GF-preserve-terminal .Category.IsIso.f∘inverse≈id .f≃f = Category.IsIso.f∘inverse≈id FT
GF-preserve-terminal .Category.IsIso.inverse∘f≈id .f≃f = Category.IsIso.inverse∘f≈id FT

presv-prod : ∀ {x y} → GlPM.prod (GF .fobj x) (GF .fobj y) Glued.⇒ GF .fobj (𝒞P.prod x y)
presv-prod {x} {y} .morph = FP {x} {y} .𝒟.IsIso.inverse
presv-prod {x} {y} .presv = begin
    (𝐂 (Definable x) [ G .fmor 𝒟P.p₁ ]) && (𝐂 (Definable y) [ G .fmor 𝒟P.p₂ ])
  ≤⟨ IsMeet.mono &&-isMeet 𝐂-[]⁻¹ 𝐂-[]⁻¹ ⟩
    (𝐂 (Definable x [ G .fmor 𝒟P.p₁ ])) && (𝐂 (Definable y [ G .fmor 𝒟P.p₂ ]))
  ≤⟨ ClosureOp.𝐂-monoidal closureOp ⟩
    𝐂 ((Definable x [ G .fmor 𝒟P.p₁ ]) && (Definable y [ G .fmor 𝒟P.p₂ ]))
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono Definable-products ⟩
    𝐂 (Definable (𝒞P.prod x y) [ G .fmor (Category.IsIso.inverse FP) ])
  ≤⟨ 𝐂-[] ⟩
    𝐂 (Definable (𝒞P.prod x y)) [ G .fmor (Category.IsIso.inverse FP) ]
  ∎
  where open ≤-Reasoning ⊑-isPreorder

GF-preserve-products : preserve-chosen-products GF 𝒞P GlPE.products
GF-preserve-products .Category.IsIso.inverse = presv-prod
GF-preserve-products .Category.IsIso.f∘inverse≈id .f≃f = Category.IsIso.f∘inverse≈id FP
GF-preserve-products .Category.IsIso.inverse∘f≈id .f≃f = Category.IsIso.inverse∘f≈id FP

presv-cp : ∀ {x y} → GF .fobj (𝒞CP.coprod x y) Glued.⇒ GlCPM.coprod (GF .fobj x) (GF .fobj y)
presv-cp {x} {y} .morph = FC .𝒟.IsIso.inverse
presv-cp {x} {y} .presv = begin
    𝐂 (Definable (𝒞CP.coprod x y))
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono Definable-coproducts ⟩
    𝐂 (𝐂 ((Definable x ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩) ++ (Definable y ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩)))
  ≤⟨ 𝐂-isClosure .IsClosureOp.closed ⟩
    𝐂 ((Definable x ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩) ++ (Definable y ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩))
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsJoin.mono ++-isJoin ((𝐂-isClosure .IsClosureOp.unit) PSh⟨𝒞⟩-system.⟨ _ ⟩m) ((𝐂-isClosure .IsClosureOp.unit) PSh⟨𝒞⟩-system.⟨ _ ⟩m)) ⟩
    𝐂 ((𝐂 (Definable x) ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩) ++ (𝐂 (Definable y) ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩))
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsJoin.mono ++-isJoin (𝐂-isClosure .IsClosureOp.unit) (𝐂-isClosure .IsClosureOp.unit)) ⟩
    𝐂 ((𝐂 (𝐂 (Definable x) ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩)) ++ (𝐂 (𝐂 (Definable y) ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩)))
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsJoin.mono ++-isJoin (𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.unit _)) (𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.unit _))) ⟩
    𝐂 ((𝐂 (𝐂 (Definable x) ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩ ⟨ G .fmor mul ⟩ [ G .fmor mul ])) ++ (𝐂 (𝐂 (Definable y) ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩ ⟨ G .fmor mul ⟩ [ G .fmor mul ])))
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono
        (IsJoin.mono ++-isJoin (𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.⟨⟩-comp _ _ PSh⟨𝒞⟩-system.[ _ ]m))
                               (𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.⟨⟩-comp _ _ PSh⟨𝒞⟩-system.[ _ ]m))) ⟩
    𝐂 ((𝐂 (𝐂 (Definable x) ⟨ G .fmor mul PSh⟨𝒞⟩.∘ G .fmor (F .fmor 𝒞CP.in₁) ⟩ [ G .fmor mul ])) ++ (𝐂 (𝐂 (Definable y) ⟨ G .fmor mul PSh⟨𝒞⟩.∘ G .fmor (F .fmor 𝒞CP.in₂) ⟩ [ G .fmor mul ])))
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono
        (IsJoin.mono ++-isJoin (𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.⟨⟩-cong (PSh⟨𝒞⟩.≈-sym (G .fmor-comp _ _)) PSh⟨𝒞⟩-system.[ _ ]m))
                               (𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.⟨⟩-cong (PSh⟨𝒞⟩.≈-sym (G .fmor-comp _ _)) PSh⟨𝒞⟩-system.[ _ ]m))) ⟩
    𝐂 ((𝐂 (𝐂 (Definable x) ⟨ G .fmor (mul 𝒟.∘ F .fmor 𝒞CP.in₁) ⟩ [ G .fmor mul ])) ++ (𝐂 (𝐂 (Definable y) ⟨ G .fmor (mul 𝒟.∘ F .fmor 𝒞CP.in₂) ⟩ [ G .fmor mul ])))
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono
        (IsJoin.mono ++-isJoin (𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.⟨⟩-cong (G .fmor-cong F-in₁) PSh⟨𝒞⟩-system.[ _ ]m))
                               (𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.⟨⟩-cong (G .fmor-cong F-in₂) PSh⟨𝒞⟩-system.[ _ ]m))) ⟩
    𝐂 ((𝐂 (𝐂 (Definable x) ⟨ G .fmor 𝒟CP.in₁ ⟩ [ G .fmor mul ])) ++ (𝐂 (𝐂 (Definable y) ⟨ G .fmor 𝒟CP.in₂ ⟩ [ G .fmor mul ])))
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsJoin.mono ++-isJoin 𝐂-[] 𝐂-[]) ⟩
    𝐂 ((𝐂 (𝐂 (Definable x) ⟨ G .fmor 𝒟CP.in₁ ⟩) [ G .fmor mul ]) ++ (𝐂 (𝐂 (Definable y) ⟨ G .fmor 𝒟CP.in₂ ⟩) [ G .fmor mul ]))
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono PSh⟨𝒞⟩-system.[]-++⁻¹ ⟩
    𝐂 ((𝐂 (𝐂 (Definable x) ⟨ G .fmor 𝒟CP.in₁ ⟩) ++ 𝐂 (𝐂 (Definable y) ⟨ G .fmor 𝒟CP.in₂ ⟩)) [ G .fmor mul ])
  ≤⟨ 𝐂-[] ⟩
    𝐂 (𝐂 (𝐂 (Definable x) ⟨ G .fmor 𝒟CP.in₁ ⟩) ++ 𝐂 (𝐂 (Definable y) ⟨ G .fmor 𝒟CP.in₂ ⟩)) [ G .fmor mul ]
  ∎
  where open ≤-Reasoning ⊑-isPreorder
        open preserve-chosen-coproducts-consequences F 𝒞CP 𝒟CP FC

GF-preserve-coproducts : preserve-chosen-coproducts GF 𝒞CP GlCP.coproducts
GF-preserve-coproducts .Category.IsIso.inverse = presv-cp
GF-preserve-coproducts .Category.IsIso.f∘inverse≈id .f≃f = Category.IsIso.f∘inverse≈id FC
GF-preserve-coproducts .Category.IsIso.inverse∘f≈id .f≃f = Category.IsIso.inverse∘f≈id FC

-- GF preserves set-indexed coproducts: carrier by F-DC, predicate by
-- Definable-coproducts-indexed. The set-indexed twin of GF-preserve-coproducts.
GF-preserve-coproducts-indexed : ∀ (S : Setoid 0ℓ 0ℓ) (D : Functor (setoid→category S) 𝒞) →
  Glued.Iso (GDC S (GF ∘F D) .Colimit.apex) (GF .fobj (SI.∐ S D))
GF-preserve-coproducts-indexed S D = iso
  where
    module FI = ∃ₛ (F-DC S D)

    -- project ∘F GF and F agree on objects and morphisms, but not as no-eta
    -- functor records, so the Gl coproduct's carrier 𝒟DC S (project ∘F GF ∘F D)
    -- is bridged to F-DC's 𝒟DC S (F ∘F D) by the identity natural iso.
    D-eq : NatIso (Gl.project ∘F (GF ∘F D)) (F ∘F D)
    D-eq .NatIso.transform .transf s = 𝒟.id _
    D-eq .NatIso.transform .natural {s} {s'} _ = 𝒟.≈-trans 𝒟.id-right (𝒟.≈-sym 𝒟.id-left)
    D-eq .NatIso.transf-iso s .Category.IsIso.inverse = 𝒟.id _
    D-eq .NatIso.transf-iso s .Category.IsIso.f∘inverse≈id = 𝒟.id-left
    D-eq .NatIso.transf-iso s .Category.IsIso.inverse∘f≈id = 𝒟.id-left

    carrierIso = 𝒟.Iso-trans (𝒟d.∐-iso D-eq) FI.fst

    -- Under the coproduct comparison each 𝒞-injection maps to the Gl carrier's
    -- colimit injection: F-DC's compat, then the D-eq bridge.
    F-inⱼ : ∀ s → (carrierIso .Category.Iso.bwd 𝒟.∘ F .fmor (SI.inj D s)) 𝒟.≈
                  (GDC S (GF ∘F D) .Colimit.cocone .transf s .morph)
    F-inⱼ s =
      𝒟.≈-trans (𝒟.assoc _ _ _)
        (𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl bwd-inj)
          (𝒟.≈-trans (𝒟d.∐-map-coeval (NatIso.transform⁻¹ D-eq) s) 𝒟.id-right))
      where
        bwd-inj : (FI.fst .Category.Iso.bwd 𝒟.∘ F .fmor (SI.inj D s)) 𝒟.≈
                  (𝒟DC S (F ∘F D) .Colimit.cocone .transf s)
        bwd-inj =
          𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl (𝒟.≈-sym (FI.snd s)))
            (𝒟.≈-trans (𝒟.≈-sym (𝒟.assoc _ _ _))
              (𝒟.≈-trans (𝒟.∘-cong (FI.fst .Category.Iso.bwd∘fwd≈id) 𝒟.≈-refl) 𝒟.id-left))

    iso : Glued.Iso (GDC S (GF ∘F D) .Colimit.apex) (GF .fobj (SI.∐ S D))
    iso .Glued.Iso.fwd .morph = carrierIso .Category.Iso.fwd
    iso .Glued.Iso.fwd .presv =
      IsPreorder.trans ⊑-isPreorder
        (𝐂-isClosure .IsClosureOp.mono (IsBigJoin.least PSh⟨𝒞⟩-system.⋁-isJoin _ _ _ per-s))
        target-closed
      where
        ι : ∀ s → _
        ι s = GDC S (GF ∘F D) .Colimit.cocone .transf s .morph

        fwd-inⱼ : ∀ s → (carrierIso .Category.Iso.fwd 𝒟.∘ ι s) 𝒟.≈ F .fmor (SI.inj D s)
        fwd-inⱼ s =
          𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl (𝒟.≈-sym (F-inⱼ s)))
            (𝒟.≈-trans (𝒟.≈-sym (𝒟.assoc _ _ _))
              (𝒟.≈-trans (𝒟.∘-cong (carrierIso .Category.Iso.fwd∘bwd≈id) 𝒟.≈-refl) 𝒟.id-left))

        target-closed :
          𝐂 (𝐂 (Definable (SI.∐ S D)) [ G .fmor (carrierIso .Category.Iso.fwd) ]) ⊑
          (𝐂 (Definable (SI.∐ S D)) [ G .fmor (carrierIso .Category.Iso.fwd) ])
        target-closed =
          IsPreorder.trans ⊑-isPreorder 𝐂-[]
            (𝐂-isClosure .IsClosureOp.closed PSh⟨𝒞⟩-system.[ _ ]m)

        inner-s : ∀ s →
          𝐂 (Definable (D .fobj s)) ⟨ G .fmor (ι s) ⟩ ⊑
          (𝐂 (Definable (SI.∐ S D)) [ G .fmor (carrierIso .Category.Iso.fwd) ])
        inner-s s =
          PSh⟨𝒞⟩-system.adjoint₂
            (IsPreorder.trans ⊑-isPreorder (GF .fmor (SI.inj D s) .presv)
              (IsPreorder.trans ⊑-isPreorder
                (PSh⟨𝒞⟩-system.[]-cong (G .fmor-cong (𝒟.≈-sym (fwd-inⱼ s))))
                (IsPreorder.trans ⊑-isPreorder
                  (PSh⟨𝒞⟩-system.[]-cong (G .fmor-comp _ _))
                  (PSh⟨𝒞⟩-system.[]-comp⁻¹ _ _))))

        per-s : ∀ s →
          𝐂 (𝐂 (Definable (D .fobj s)) ⟨ G .fmor (ι s) ⟩) ⊑
          (𝐂 (Definable (SI.∐ S D)) [ G .fmor (carrierIso .Category.Iso.fwd) ])
        per-s s =
          IsPreorder.trans ⊑-isPreorder
            (𝐂-isClosure .IsClosureOp.mono (inner-s s))
            target-closed
    iso .Glued.Iso.bwd .morph = carrierIso .Category.Iso.bwd
    iso .Glued.Iso.bwd .presv = begin
        𝐂 (Definable (SI.∐ S D))
      ≤⟨ 𝐂-isClosure .IsClosureOp.mono Definable-coproducts-indexed ⟩
        𝐂 (𝐂 (⋁ (S .Setoid.Carrier) (λ s → Definable (D .fobj s) ⟨ G .fmor (F .fmor (SI.inj D s)) ⟩)))
      ≤⟨ 𝐂-isClosure .IsClosureOp.closed ⟩
        𝐂 (⋁ (S .Setoid.Carrier) (λ s → Definable (D .fobj s) ⟨ G .fmor (F .fmor (SI.inj D s)) ⟩))
      ≤⟨ 𝐂-isClosure .IsClosureOp.mono
           (IsBigJoin.mono PSh⟨𝒞⟩-system.⋁-isJoin (λ s → (𝐂-isClosure .IsClosureOp.unit) PSh⟨𝒞⟩-system.⟨ _ ⟩m)) ⟩
        𝐂 (⋁ (S .Setoid.Carrier) (λ s → 𝐂 (Definable (D .fobj s)) ⟨ G .fmor (F .fmor (SI.inj D s)) ⟩))
      ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsBigJoin.mono PSh⟨𝒞⟩-system.⋁-isJoin (λ s → 𝐂-isClosure .IsClosureOp.unit)) ⟩
        _
      ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsBigJoin.mono PSh⟨𝒞⟩-system.⋁-isJoin (λ s → 𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.unit _))) ⟩
        _
      ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsBigJoin.mono PSh⟨𝒞⟩-system.⋁-isJoin (λ s → 𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.⟨⟩-comp _ _ PSh⟨𝒞⟩-system.[ _ ]m))) ⟩
        _
      ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsBigJoin.mono PSh⟨𝒞⟩-system.⋁-isJoin (λ s → 𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.⟨⟩-cong (PSh⟨𝒞⟩.≈-sym (G .fmor-comp _ _)) PSh⟨𝒞⟩-system.[ _ ]m))) ⟩
        _
      ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsBigJoin.mono PSh⟨𝒞⟩-system.⋁-isJoin (λ s → 𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.⟨⟩-cong (G .fmor-cong (F-inⱼ s)) PSh⟨𝒞⟩-system.[ _ ]m))) ⟩
        _
      ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsBigJoin.mono PSh⟨𝒞⟩-system.⋁-isJoin (λ s → 𝐂-[])) ⟩
        _
      ≤⟨ 𝐂-isClosure .IsClosureOp.mono (IsBigJoin.least PSh⟨𝒞⟩-system.⋁-isJoin _ _ _ (λ s → (IsBigJoin.upper PSh⟨𝒞⟩-system.⋁-isJoin _ _ s) PSh⟨𝒞⟩-system.[ _ ]m)) ⟩
        _
      ≤⟨ 𝐂-[] ⟩
        𝐂 (⋁ (S .Setoid.Carrier) (λ s → 𝐂 (𝐂 (Definable (D .fobj s)) ⟨ G .fmor (GDC S (GF ∘F D) .Colimit.cocone .transf s .morph) ⟩)))
          [ G .fmor (carrierIso .Category.Iso.bwd) ]
      ∎
      where open ≤-Reasoning ⊑-isPreorder
    iso .Glued.Iso.fwd∘bwd≈id .f≃f = carrierIso .Category.Iso.fwd∘bwd≈id
    iso .Glued.Iso.bwd∘fwd≈id .f≃f = carrierIso .Category.Iso.bwd∘fwd≈id

-- FIXME: If 𝒞 has exponentials, then GF preserves them as well.

open preserve-monad

GF-preserve-monad : preserve-monad GF 𝒞M GlM.GM
GF-preserve-monad .iso .NatIso.transform .transf x .morph = FM.transform .transf x
GF-preserve-monad .iso .NatIso.transform .transf x .presv = begin
    𝐂 (Definable (𝒞M.funct .fobj x))
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono Definable-monad ⟩
    𝐂 (MP .liftF (Definable x) ⟨ (𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F)) PSh⟨𝒞⟩.∘ G-monad .transf (F .fobj x) ⟩)
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (𝐂-isClosure .IsClosureOp.unit PSh⟨𝒞⟩-system.⟨ _ ⟩m) ⟩
    𝐂 (𝐂 (MP .liftF (Definable x)) ⟨ (𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F)) PSh⟨𝒞⟩.∘ G-monad .transf (F .fobj x) ⟩)
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.⟨⟩-comp⁻¹ _ _) ⟩
    𝐂 (𝐂 (MP .liftF (Definable x)) ⟨ G-monad .transf (F .fobj x) ⟩ ⟨ (𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F)) ⟩)
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.unit _) ⟩
    𝐂 (𝐂 (MP .liftF (Definable x)) ⟨ G-monad .transf (F .fobj x) ⟩ ⟨ (𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F)) ⟩ ⟨ 𝒟よ .fmor (FM.transform .transf x) ∘H id (opF F) ⟩ [ 𝒟よ .fmor (FM.transform .transf x) ∘H id (opF F) ])
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono ((PSh⟨𝒞⟩-system.⟨⟩-comp _ _) PSh⟨𝒞⟩-system.[ _ ]m) ⟩
    𝐂 (𝐂 (MP .liftF (Definable x)) ⟨ G-monad .transf (F .fobj x) ⟩ ⟨ (𝒟よ .fmor (FM.transform .transf x) ∘H id (opF F)) PSh⟨𝒞⟩.∘ (𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F)) ⟩ [ 𝒟よ .fmor (FM.transform .transf x) ∘H id (opF F) ])
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.⟨⟩-cong help PSh⟨𝒞⟩-system.[ _ ]m) ⟩
    𝐂 (𝐂 (MP .liftF (Definable x)) ⟨ G-monad .transf (F .fobj x) ⟩ ⟨ PSh⟨𝒞⟩.id _ ⟩ [ 𝒟よ .fmor (FM.transform .transf x) ∘H id (opF F) ])
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.⟨⟩-id⁻¹ PSh⟨𝒞⟩-system.[ _ ]m) ⟩
    𝐂 (𝐂 (MP .liftF (Definable x)) ⟨ G-monad .transf (F .fobj x) ⟩ [ 𝒟よ .fmor (FM.transform .transf x) ∘H id (opF F) ])
  ≤⟨ 𝐂-[] ⟩
    𝐂 (𝐂 (MP .liftF (Definable x)) ⟨ G-monad .transf (F .fobj x) ⟩) [ 𝒟よ .fmor (FM.transform .transf x) ∘H id (opF F) ]
  ≤⟨ (𝐂-isClosure .IsClosureOp.mono ((𝐂-isClosure .IsClosureOp.mono (MP .liftF-⊑ (𝐂-isClosure .IsClosureOp.unit))) PSh⟨𝒞⟩-system.⟨ _ ⟩m)) PSh⟨𝒞⟩-system.[ _ ]m ⟩
    𝐂 (𝐂 (MP .liftF (𝐂 (Definable x))) ⟨ G-monad .transf (F .fobj x) ⟩) [ 𝒟よ .fmor (FM.transform .transf x) ∘H id (opF F) ]
  ∎
  where open prop-setoid renaming (mk-≃m to mk-≈s)

        help : (𝒟よ .fmor (FM.transform .transf x) ∘H id (opF F)) PSh⟨𝒞⟩.∘ (𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F)) PSh⟨𝒞⟩.≈ PSh⟨𝒞⟩.id _
        help .transf-eq x = mk-≈s λ (lift f) → lift (begin
            FM.transform .transf _ 𝒟.∘ (FM.transform⁻¹ .transf _ 𝒟.∘ (f 𝒟.∘ 𝒟.id _) 𝒟.∘ 𝒟.id _)
          ≈⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right ⟩
            FM.transform .transf _ 𝒟.∘ (FM.transform⁻¹ .transf _ 𝒟.∘ (f 𝒟.∘ 𝒟.id _))
          ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right) ⟩
            FM.transform .transf _ 𝒟.∘ (FM.transform⁻¹ .transf _ 𝒟.∘ f)
          ≈˘⟨ 𝒟.assoc _ _ _ ⟩
            (FM.transform .transf _ 𝒟.∘ FM.transform⁻¹ .transf _) 𝒟.∘ f
          ≈⟨ 𝒟.∘-cong (FM.transf-iso _ .Category.IsIso.f∘inverse≈id) 𝒟.≈-refl ⟩
            𝒟.id _ 𝒟.∘ f
          ≈⟨ 𝒟.id-left ⟩
            f
          ∎)
          where open ≈-Reasoning 𝒟.isEquiv

        open ≤-Reasoning ⊑-isPreorder
GF-preserve-monad .iso .NatIso.transform .natural f .f≃f = FM.transform .natural f
GF-preserve-monad .iso .NatIso.transf-iso x .Category.IsIso.inverse .morph = FM.transform⁻¹ .transf x
GF-preserve-monad .iso .NatIso.transf-iso x .Category.IsIso.inverse .presv = begin
    𝐂 (𝐂 (MP .liftF (𝐂 (Definable x))) ⟨ G-monad .transf (F .fobj x) ⟩)
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (𝐂-isClosure .IsClosureOp.mono (MDistrib.distrib FMpull) PSh⟨𝒞⟩-system.⟨ _ ⟩m) ⟩
    𝐂 (𝐂 (𝐂 (MP .liftF (Definable x))) ⟨ G-monad .transf (F .fobj x) ⟩)
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (𝐂-isClosure .IsClosureOp.closed PSh⟨𝒞⟩-system.⟨ _ ⟩m) ⟩
    𝐂 (𝐂 (MP .liftF (Definable x)) ⟨ G-monad .transf (F .fobj x) ⟩)
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (𝐂-isClosure .IsClosureOp.mono Definable-monad⁻¹ PSh⟨𝒞⟩-system.⟨ _ ⟩m) ⟩
    𝐂 (𝐂 (Definable (𝒞M.funct .fobj x) [ (𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F)) PSh⟨𝒞⟩.∘ G-monad .transf (F .fobj x) ]) ⟨ G-monad .transf (F .fobj x) ⟩)
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (𝐂-[] PSh⟨𝒞⟩-system.⟨ _ ⟩m) ⟩
    𝐂 (𝐂 (Definable (𝒞M.funct .fobj x)) [ (𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F)) PSh⟨𝒞⟩.∘ G-monad .transf (F .fobj x) ] ⟨ G-monad .transf (F .fobj x) ⟩)
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.[]-comp⁻¹ _ _ PSh⟨𝒞⟩-system.⟨ _ ⟩m) ⟩
    𝐂 (𝐂 (Definable (𝒞M.funct .fobj x)) [ (𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F)) ] [ G-monad .transf (F .fobj x) ] ⟨ G-monad .transf (F .fobj x) ⟩)
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (PSh⟨𝒞⟩-system.counit _) ⟩
    𝐂 (𝐂 (Definable (𝒞M.funct .fobj x)) [ (𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F)) ])
  ≤⟨ 𝐂-[] ⟩
    𝐂 (𝐂 (Definable (𝒞M.funct .fobj x))) [ (𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F)) ]
  ≤⟨ 𝐂-isClosure .IsClosureOp.closed PSh⟨𝒞⟩-system.[ _ ]m ⟩
    𝐂 (Definable (𝒞M.funct .fobj x)) [ 𝒟よ .fmor (FM.transform⁻¹ .transf x) ∘H id (opF F) ]
  ∎
  where open ≤-Reasoning ⊑-isPreorder
GF-preserve-monad .iso .NatIso.transf-iso x .Category.IsIso.f∘inverse≈id .f≃f = Category.IsIso.f∘inverse≈id (FM.transf-iso x)
GF-preserve-monad .iso .NatIso.transf-iso x .Category.IsIso.inverse∘f≈id .f≃f = Category.IsIso.inverse∘f≈id (FM.transf-iso x)
GF-preserve-monad .preserve-unit .f≃f = FM.preserve-unit
GF-preserve-monad .preserve-join .f≃f = FM.preserve-join

------------------------------------------------------------------------------
-- Semantic version of first-order definability: if we have a
-- morphism in the GLR category whose domain and codomain are from
-- 𝒞, then it is really a 𝒞 morphism.
definability : ∀ {X Y} → (f : GF .fobj X Glued.⇒ GF .fobj Y) → ∃ (X 𝒞.⇒ Y) (λ g → F .fmor g 𝒟.≈ f .morph)
definability {X} {Y} f with Definable-closed _ (f .presv .*⊑* X .*⊑* (lift (F .fmor (𝒞.id _))) (leaf (lift (𝒞.id _ , 𝒟.≈-refl))))
... | g , eq = g , (begin
                      F .fmor g
                    ≈⟨ eq ⟩
                      f .morph 𝒟.∘ (F .fmor (𝒞.id _) 𝒟.∘ 𝒟.id _)
                    ≈⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right ⟩
                      f .morph 𝒟.∘ F .fmor (𝒞.id _)
                    ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-id) ⟩
                      f .morph 𝒟.∘ 𝒟.id _
                    ≈⟨ 𝒟.id-right ⟩
                      f .morph
                    ∎)
    where open ≈-Reasoning 𝒟.isEquiv

module strong-exponentials where

  Gl-exponentials : HasExponentials Gl.cat GlPE.products
  Gl-exponentials = GlPE.exponentials

  GlSC : HasStrongCoproducts Gl.cat GlPE.products
  GlSC = ccc→strong-coproducts GlCP.coproducts Gl-exponentials

  abstract
    Gl-Mu : polynomial-functor.Interp.HasMu GlPE.terminal GlPE.products GlSC
    Gl-Mu = fam-mu-realisation.Muℰ 0ℓ 0ℓ GDC GlPE.terminal GlPE.products Gl-exponentials GlSC

    Gl-MuLaws : polynomial-functor.Interp.HasMuLaws GlPE.terminal GlPE.products GlSC Gl-Mu
    Gl-MuLaws = fam-mu-realisation.MuLawsℰ 0ℓ 0ℓ GDC GlPE.terminal GlPE.products Gl-exponentials GlSC

    -- Expose the μ-objects behind the abstraction: they are the realised
    -- μ-objects of the construction above.
    Gl-Mu-obj : ∀ {n} (Q : polynomial-functor.Poly Gl.cat (Data.Nat.suc n))
                (δ : Data.Fin.Fin n → Category.obj Gl.cat) →
                polynomial-functor.Interp.HasMu.μ-obj Gl-Mu Q δ ≡
                fam-mu-realisation.μ-objℰ 0ℓ 0ℓ GDC GlPE.terminal GlPE.products Gl-exponentials GlSC Q δ
    Gl-Mu-obj Q δ = ≡-refl

  -- The morphisms in the logical relations category that we are
  -- interested are the ones that come from interpretations of the
  -- language.
  module syntactic {ℓ}
     (Sig : Signature ℓ)
     (𝒞SC : HasStrongCoproducts 𝒞 𝒞P)
     (𝒞Mu : polynomial-functor.Interp.HasMu 𝒞T 𝒞P 𝒞SC)
     (GFC : preserve-chosen-coproducts GF (strong-coproducts→coproducts 𝒞T 𝒞SC)
                                          (strong-coproducts→coproducts GlPE.terminal GlSC))
     (GFμ : polynomial-functor.Preserves-μ 𝒞T 𝒞P 𝒞SC GlPE.terminal GlPE.products GlSC 𝒞Mu Gl-Mu GF)
     (𝒞-Sig-Model : Model PFPC[ 𝒞 , 𝒞T , 𝒞P ,
                     HasCoproducts.coprod (strong-coproducts→coproducts 𝒞T 𝒞SC)
                       (𝒞T .HasTerminal.witness) (𝒞T .HasTerminal.witness) ] Sig)
     where

    open import language-syntax Sig using (_⊢_; first-order; first-order-ctxt)

    open import language-fo-interpretation Sig
           𝒞 𝒞T 𝒞P 𝒞SC 𝒞Mu (𝒞T .HasTerminal.witness)
           Gl.cat GlPE.terminal GlPE.products GlSC Gl-exponentials Gl-Mu Gl-MuLaws
           (GlPE.terminal .HasTerminal.witness) (Glued.id _)
           GF GF-preserve-terminal GF-preserve-products GFC GFμ
           (Glued.IsIso→Iso GF-preserve-terminal)
           𝒞-Sig-Model
      renaming (𝒟⟦_⟧ty to G⟦_⟧ty; 𝒟⟦_⟧ctxt to G⟦_⟧ctxt; 𝒟⟦_⟧tm to G⟦_⟧tm)

    open Glued.Iso

    syntactic-definability :
      ∀ {Γ τ} (Γ-fo : first-order-ctxt Γ) (τ-fo : first-order τ) (M : Γ ⊢ τ) →
      ∃ (𝒞⟦ Γ-fo ⟧ctxt 𝒞.⇒ 𝒞⟦ τ-fo ⟧ty (λ ())) λ g →
        F .fmor g 𝒟.≈ (⟦ τ-fo ⟧-iso (λ ()) .bwd .morph 𝒟.∘ (G⟦ M ⟧tm .morph 𝒟.∘ ⟦ Γ-fo ⟧ctxt-iso .fwd .morph))
    syntactic-definability Γ-fo τ-fo M =
      definability (⟦ τ-fo ⟧-iso (λ ()) .bwd Glued.∘ (G⟦ M ⟧tm Glued.∘ ⟦ Γ-fo ⟧ctxt-iso .fwd))
