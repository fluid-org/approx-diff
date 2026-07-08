{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (Lift; lift; lower; _⊔_; 0ℓ)
open import Data.Product using (_,_)
open import prop using (_,_; proj₁; proj₂; ∃; LiftP; lift; lower; liftS; LiftS; inj₁; inj₂)
open import basics using (module ≤-Reasoning; IsClosureOp; IsJoin; IsMeet)
open import categories
  using (Category; HasBooleans; HasProducts; HasCoproducts; HasExponentials;
         HasTerminal; IsTerminal; IsProduct; coproducts+exp→booleans; setoid→category;
         HasStrongCoproducts; ccc→strong-coproducts; strong-coproducts→coproducts)
import polynomial-functor-2
open import functor
  using (Functor; _∘F_; opF; _∘H_; ∘H-cong; id; _∘_; NatTrans; ≃-NatTrans; ≃-isEquivalence;
         interchange; H-id; NT-id-left;
         HasColimits; NatIso)
open import prop-setoid using (module ≈-Reasoning; IsEquivalence; Setoid)
open import setoid-cat using (SetoidCat)
open import predicate-system using (PredicateSystem; ClosureOp; FunctorPred; MonadPred)
open import stable-coproducts using (StableBits; Stable)
import fam-mu-realisation
import glueing-simple
import setoid-predicate
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

-- Let Sig be a signature
-- Let M be a model of Sig in 𝒞, and F be a finite product and infinite coproduct preserving functor
-- Then:
--   1. Can interpret the whole language in Glued
--   2. Every first order type is isomorphic to its interpretation in 𝒞
--   3. So every judgement x : A ⊢ M : B, with A, B first-order, has a morphism g : A 𝒞.⇒ B such that F(g) = ⟦ M ⟧

-- For the actual language:
--  1. 𝒞 = Fam⟨LatGal⟩ which has finite products and infinite coproducts
--  2. 𝒟 = Fam⟨M×J^op⟩ which is a BiCCC
--  3. F  = Fam⟨𝓖⟩ which preserves products and infinite coproducts
-- Could also replay the whole thing with `Stable` instead of Fam⟨LatGal⟩ ??

-- TODO:
--   7. Stability: prove it for Fam⟨𝒞⟩ (!!!)

module conservativity
  {o₁ o₂ m e}
  -- Category for interpreting first-order things
  (𝒞 : Category o₁ m e) (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞CP : HasCoproducts 𝒞) (stable : Stable 𝒞CP) (𝒞M : Monad 𝒞)
  -- A higher order model
  (𝒟 : Category o₂ m e) (𝒟T : HasTerminal 𝒟) (𝒟P : HasProducts 𝒟) (𝒟CP : HasCoproducts 𝒟) (𝒟E : HasExponentials 𝒟 𝒟P) (𝒟M : Monad 𝒟)
  (𝒟DC : ∀ (A : Setoid 0ℓ 0ℓ) → HasColimits (setoid→category A) 𝒟)
  -- A functor which preserves terminal, products, and coproducts
  (F  : Functor 𝒞 𝒟)
  (FT : preserve-chosen-terminal F 𝒞T 𝒟T)
  (FP : preserve-chosen-products F 𝒞P 𝒟P)
  (FC : preserve-chosen-coproducts F 𝒞CP 𝒟CP)
  (FM : preserve-monad F 𝒞M 𝒟M)
  (FM-C : preserve-chosen-coproducts (Monad.funct 𝒞M) 𝒞CP 𝒞CP)
  where

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

------------------------------------------------------------------------------
-- Kripke Predicates “of varying arity”
open import yoneda (o₁ ⊔ o₂ ⊔ m ⊔ e) 𝒞 renaming (PSh to PSh⟨𝒞⟩; products to PSh⟨𝒞⟩-products) using (module DayMonad; module UnaryDay; Coend; Cowedge)
open import yoneda (o₁ ⊔ o₂ ⊔ m ⊔ e) 𝒟 renaming (よ to 𝒟よ) using ()

open DayMonad 𝒞M using (monad-hat)

private
  module PSh⟨𝒞⟩ = Category PSh⟨𝒞⟩
  module PSh⟨𝒞⟩P = HasProducts PSh⟨𝒞⟩-products
  module PSh⟨𝒞⟩M = Monad monad-hat

-- FIXME: define PSh(F) : PSh⟨𝒟⟩ ⇒ PSh⟨𝒞⟩, then G is composition of this and yoneda

G : Functor 𝒟 PSh⟨𝒞⟩
G .fobj x = 𝒟よ .fobj x ∘F opF F
G .fmor f = 𝒟よ .fmor f ∘H id _
G .fmor-cong f₁≈f₂ = ∘H-cong (𝒟よ .fmor-cong f₁≈f₂) (≃-isEquivalence .IsEquivalence.refl)
G .fmor-id = begin
    𝒟よ .fmor (𝒟.id _) ∘H id _
  ≈⟨ ∘H-cong (𝒟よ .fmor-id) (≃-isEquivalence .IsEquivalence.refl) ⟩
    id (𝒟よ .fobj _) ∘H id (opF F)
  ≈⟨ H-id ⟩
    PSh⟨𝒞⟩.id _
  ∎ where open ≈-Reasoning PSh⟨𝒞⟩.isEquiv
G .fmor-comp f g = begin
    𝒟よ .fmor (f 𝒟.∘ g) ∘H id _
  ≈⟨ ∘H-cong (𝒟よ .fmor-comp f g) (≃-isEquivalence .IsEquivalence.sym NT-id-left) ⟩
    (𝒟よ .fmor f ∘ 𝒟よ .fmor g) ∘H (id _ ∘ id _)
  ≈⟨ interchange _ _ _ _ ⟩
    (𝒟よ .fmor f ∘H id _) PSh⟨𝒞⟩.∘ (𝒟よ .fmor g ∘H id _)
  ∎ where open ≈-Reasoning PSh⟨𝒞⟩.isEquiv

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

  G-monad-cw : ∀ x y → Cowedge 𝟙 (M-hat-F (𝒟よ .fobj x ∘F opF F) y) (𝒟.hom-setoid-l (o₁ ⊔ o₂ ⊔ m ⊔ e) (o₁ ⊔ o₂ ⊔ m ⊔ e) (F .fobj y) (𝒟M.funct .fobj x))
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

------------------------------------------------------------------------------
-- Presheaf predicates
open import presheaf-predicate (o₁ ⊔ o₂ ⊔ m ⊔ e) 𝒞
  renaming (system to PSh⟨𝒞⟩-system; Predicate to PShPredicate)
  using (_⊑_; module CoproductMonad;
         _++_; _⟨_⟩; ⊑-isPreorder; _[_]; []-++; ++-isJoin; _&&_; &&-isMeet; TT; TT-isTop;
         module Monad-hat-pred)

module PSh⟨𝒞⟩-system = PredicateSystem PSh⟨𝒞⟩-system

open Monad-hat-pred 𝒞M using (MP)

open PShPredicate
open setoid-predicate.Predicate
open setoid-predicate._⊑_
open _⊑_

-- The “𝒞 definability” predicate.
Definable : ∀ x → PShPredicate (G .fobj (F .fobj x))
Definable x .pred y .pred (lift f) = LiftP (o₁ ⊔ o₂) (∃ (y 𝒞.⇒ x) λ g → F .fmor g 𝒟.≈ f)
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

open CoproductMonad 𝒞CP stable

Definable-coproducts : ∀ {x y} →
                Definable (𝒞CP.coprod x y) ⊑
                𝐂 ((Definable x ⟨ G .fmor (F .fmor 𝒞CP.in₁) ⟩) ++ (Definable y ⟨ G .fmor (F .fmor 𝒞CP.in₂) ⟩))
Definable-coproducts .*⊑* z .*⊑* (lift g) (lift (f , eq)) =
  liftS (node (stb .StableBits.y₁) (stb .StableBits.y₂)
              (lift (F .fmor (𝒞CP.in₁ 𝒞.∘ stb .StableBits.h₁)))
              (lift (F .fmor (𝒞CP.in₂ 𝒞.∘ stb .StableBits.h₂)))
              (stb .StableBits.h)
              (leaf (inj₁ (lift (F .fmor (stb .StableBits.h₁)) , lift (stb .StableBits.h₁ , 𝒟.≈-refl) , lift (𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right) (𝒟.≈-sym (F .fmor-comp _ _))))))
              (leaf (inj₂ (lift (F .fmor (stb .StableBits.h₂)) , lift (stb .StableBits.h₂ , 𝒟.≈-refl) , lift (𝒟.≈-trans (𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right) (𝒟.≈-sym (F .fmor-comp _ _))))))
              (lift eq₁)
              (lift eq₂))
  where stb = stable 𝒞.Iso-refl f
        open 𝒞.Iso

        eq₁ : F .fmor (𝒞CP.in₁ 𝒞.∘ stb .StableBits.h₁) 𝒟.≈ (g 𝒟.∘ F .fmor (stb .StableBits.h .fwd 𝒞.∘ 𝒞CP.in₁))
        eq₁ = begin
            F .fmor (𝒞CP.in₁ 𝒞.∘ stb .StableBits.h₁)
          ≈˘⟨ F .fmor-cong 𝒞.id-left ⟩
            F .fmor (𝒞.id _ 𝒞.∘ (𝒞CP.in₁ 𝒞.∘ stb .StableBits.h₁))
          ≈⟨ F .fmor-cong (stb .StableBits.eq₁) ⟩
            F .fmor (f 𝒞.∘ (stb .StableBits.h .fwd 𝒞.∘ 𝒞CP.in₁))
          ≈⟨ F .fmor-comp _ _ ⟩
            F .fmor f 𝒟.∘ F .fmor (stb .StableBits.h .fwd 𝒞.∘ 𝒞CP.in₁)
          ≈⟨ 𝒟.∘-cong eq 𝒟.≈-refl ⟩
            g 𝒟.∘ F .fmor (stb .StableBits.h .fwd 𝒞.∘ 𝒞CP.in₁)
          ∎
          where open ≈-Reasoning 𝒟.isEquiv

        eq₂ : F .fmor (𝒞CP.in₂ 𝒞.∘ stb .StableBits.h₂) 𝒟.≈ (g 𝒟.∘ F .fmor (stb .StableBits.h .fwd 𝒞.∘ 𝒞CP.in₂))
        eq₂ = begin
            F .fmor (𝒞CP.in₂ 𝒞.∘ stb .StableBits.h₂)
          ≈˘⟨ F .fmor-cong 𝒞.id-left ⟩
            F .fmor (𝒞.id _ 𝒞.∘ (𝒞CP.in₂ 𝒞.∘ stb .StableBits.h₂))
          ≈⟨ F .fmor-cong (stb .StableBits.eq₂) ⟩
            F .fmor (f 𝒞.∘ (stb .StableBits.h .fwd 𝒞.∘ 𝒞CP.in₂))
          ≈⟨ F .fmor-comp _ _ ⟩
            F .fmor f 𝒟.∘ F .fmor (stb .StableBits.h .fwd 𝒞.∘ 𝒞CP.in₂)
          ≈⟨ 𝒟.∘-cong eq 𝒟.≈-refl ⟩
            g 𝒟.∘ F .fmor (stb .StableBits.h .fwd 𝒞.∘ 𝒞CP.in₂)
          ∎
          where open ≈-Reasoning 𝒟.isEquiv

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
Definable-closed f (node X₁ X₂ (lift f₁) (lift f₂) g t₁ t₂ (lift eq₁) (lift eq₂)) with Definable-closed f₁ t₁
... | (g₁ , eq₃) with Definable-closed f₂ t₂
... | (g₂ , eq₄) = 𝒞CP.copair g₁ g₂ 𝒞.∘ g .bwd ,
      (begin
        F .fmor (𝒞CP.copair g₁ g₂ 𝒞.∘ g .bwd)
      ≈⟨ F .fmor-comp _ _ ⟩
        F .fmor (𝒞CP.copair g₁ g₂) 𝒟.∘ F .fmor (g .bwd)
      ≈˘⟨ 𝒟.∘-cong F-copair 𝒟.≈-refl ⟩
        (𝒟CP.copair (F .fmor g₁) (F .fmor g₂) 𝒟.∘ mul) 𝒟.∘ F .fmor (g .bwd)
      ≈⟨ 𝒟.assoc _ _ _ ⟩
        𝒟CP.copair (F .fmor g₁) (F .fmor g₂) 𝒟.∘ (mul 𝒟.∘ F .fmor (g .bwd))
      ≈⟨ 𝒟.∘-cong (𝒟CP.copair-cong eq₃ eq₄) 𝒟.≈-refl ⟩
        𝒟CP.copair f₁ f₂ 𝒟.∘ (mul 𝒟.∘ F .fmor (g .bwd))
      ≈⟨ 𝒟.∘-cong (𝒟CP.copair-cong eq₁ eq₂ ) 𝒟.≈-refl ⟩
        𝒟CP.copair (f 𝒟.∘ F .fmor (g .fwd 𝒞.∘ 𝒞CP.in₁)) (f 𝒟.∘ F .fmor (g .fwd 𝒞.∘ 𝒞CP.in₂)) 𝒟.∘ (mul 𝒟.∘ F .fmor (g .bwd))
      ≈⟨ 𝒟.∘-cong (𝒟CP.copair-cong (𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _)) (𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _))) 𝒟.≈-refl ⟩
        𝒟CP.copair (f 𝒟.∘ (F .fmor (g .fwd) 𝒟.∘ F .fmor 𝒞CP.in₁)) (f 𝒟.∘ (F .fmor (g .fwd) 𝒟.∘ F .fmor 𝒞CP.in₂)) 𝒟.∘ (mul 𝒟.∘ F .fmor (g .bwd))
      ≈˘⟨ 𝒟.∘-cong (𝒟CP.copair-cong (𝒟.assoc _ _ _) (𝒟.assoc _ _ _)) 𝒟.≈-refl ⟩
        𝒟CP.copair ((f 𝒟.∘ F .fmor (g .fwd)) 𝒟.∘ F .fmor 𝒞CP.in₁) ((f 𝒟.∘ F .fmor (g .fwd)) 𝒟.∘ F .fmor 𝒞CP.in₂) 𝒟.∘ (mul 𝒟.∘ F .fmor (g .bwd))
      ≈˘⟨ 𝒟.∘-cong (𝒟CP.copair-natural _ _ _) 𝒟.≈-refl ⟩
        ((f 𝒟.∘ F .fmor (g .fwd)) 𝒟.∘ 𝒟CP.copair (F .fmor 𝒞CP.in₁) (F .fmor 𝒞CP.in₂)) 𝒟.∘ (mul 𝒟.∘ F .fmor (g .bwd))
      ≈⟨ 𝒟.assoc _ _ _ ⟩
        (f 𝒟.∘ F .fmor (g .fwd)) 𝒟.∘ (𝒟CP.copair (F .fmor 𝒞CP.in₁) (F .fmor 𝒞CP.in₂) 𝒟.∘ (mul 𝒟.∘ F .fmor (g .bwd)))
      ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
        (f 𝒟.∘ F .fmor (g .fwd)) 𝒟.∘ ((𝒟CP.copair (F .fmor 𝒞CP.in₁) (F .fmor 𝒞CP.in₂) 𝒟.∘ mul) 𝒟.∘ F .fmor (g .bwd))
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong (Category.IsIso.f∘inverse≈id FC) 𝒟.≈-refl) ⟩
        (f 𝒟.∘ F .fmor (g .fwd)) 𝒟.∘ (𝒟.id _ 𝒟.∘ F .fmor (g .bwd))
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-left ⟩
        (f 𝒟.∘ F .fmor (g .fwd)) 𝒟.∘ F .fmor (g .bwd)
      ≈⟨ 𝒟.assoc _ _ _ ⟩
        f 𝒟.∘ (F .fmor (g .fwd) 𝒟.∘ F .fmor (g .bwd))
      ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-comp _ _) ⟩
        f 𝒟.∘ F .fmor (g .fwd 𝒞.∘ g .bwd)
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-cong (g .fwd∘bwd≈id)) ⟩
        f 𝒟.∘ F .fmor (𝒞.id _)
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (F .fmor-id) ⟩
        f 𝒟.∘ 𝒟.id _
      ≈⟨ 𝒟.id-right ⟩
        f
      ∎)
  where open ≈-Reasoning 𝒟.isEquiv
        open preserve-chosen-coproducts-consequences F 𝒞CP 𝒟CP FC
        open 𝒞.Iso

------------------------------------------------------------------------------
-- Now construct the category of Grothendieck Logical Relations

open import closure-predicate PSh⟨𝒞⟩-system closureOp
  using (system; embed; module 𝐂Monad)

open 𝐂Monad _ MP (distrib _ FM-C)

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

open import lists Gl.cat GlPE.terminal GlPE.products GlPE.exponentials GDC
  using ()
  renaming (lists to Gl-lists)

-- Poly-types for the glued category, realised from the μ-types of Fam(Gl).
GlSC : HasStrongCoproducts Gl.cat GlPE.products
GlSC = ccc→strong-coproducts GlCP.coproducts GlPE.exponentials

abstract
  Gl-Mu : polynomial-functor-2.Interp.HasMu GlPE.terminal GlPE.products GlSC
  Gl-Mu = fam-mu-realisation.Muℰ 0ℓ 0ℓ GDC GlPE.terminal GlPE.products GlPE.exponentials GlSC

  Gl-MuLaws : polynomial-functor-2.Interp.HasMuLaws GlPE.terminal GlPE.products GlSC Gl-Mu
  Gl-MuLaws = fam-mu-realisation.MuLawsℰ 0ℓ 0ℓ GDC GlPE.terminal GlPE.products GlPE.exponentials GlSC

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
  ≤⟨ 𝐂-isClosure .IsClosureOp.mono (𝐂-isClosure .IsClosureOp.mono (distrib _ FM-C) PSh⟨𝒞⟩-system.⟨ _ ⟩m) ⟩
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
definability {X} {Y} f with f .presv .*⊑* X .*⊑* (lift (F .fmor (𝒞.id _))) (liftS (leaf (lift (𝒞.id _ , 𝒟.≈-refl))))
... | liftS t with Definable-closed _ t
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

------------------------------------------------------------------------------
-- The morphisms in the logical relations category that we are
-- interested are the ones that come from interpretations of the
-- language.

module syntactic {ℓ}
   (Sig : Signature ℓ)
   (𝒞-Sig-Model : Model PFPC[ 𝒞 , 𝒞T , 𝒞P , 𝒞CP .HasCoproducts.coprod (𝒞T .HasTerminal.witness) (𝒞T .HasTerminal.witness) ] Sig) where

  open import language-syntax Sig

  open import language-fo-interpretation Sig
         𝒞 𝒞T 𝒞P 𝒞CP
         Gl.cat GlPE.terminal GlPE.products GlCP.coproducts GlPE.exponentials Gl-lists
         GF GF-preserve-terminal GF-preserve-products GF-preserve-coproducts
         𝒞-Sig-Model
    renaming (𝒟⟦_⟧ty to G⟦_⟧ty; 𝒟⟦_⟧ctxt to G⟦_⟧ctxt; 𝒟⟦_⟧tm to G⟦_⟧tm)

  open Glued.Iso

  syntactic-definability :
    ∀ {Γ τ} (Γ-fo : first-order-ctxt Γ) (τ-fo : first-order τ) (M : Γ ⊢ τ) →
    ∃ (𝒞⟦ Γ-fo ⟧ctxt 𝒞.⇒ 𝒞⟦ τ-fo ⟧ty) λ g →
      F .fmor g 𝒟.≈ (⟦ τ-fo ⟧-iso .bwd .morph 𝒟.∘ (G⟦ M ⟧tm .morph 𝒟.∘ ⟦ Γ-fo ⟧ctxt-iso .fwd .morph))
  syntactic-definability {Γ} {τ} Γ-fo τ-fo M =
    definability (⟦ τ-fo ⟧-iso .bwd Glued.∘ (G⟦ M ⟧tm Glued.∘ ⟦ Γ-fo ⟧ctxt-iso .fwd))

module syntactic-2 {ℓ}
   (Sig : Signature ℓ)
   (𝒞SC : HasStrongCoproducts 𝒞 𝒞P)
   (𝒞Mu : polynomial-functor-2.Interp.HasMu 𝒞T 𝒞P 𝒞SC)
   (GFC : preserve-chosen-coproducts GF (strong-coproducts→coproducts 𝒞T 𝒞SC)
                                        (strong-coproducts→coproducts GlPE.terminal GlSC))
   (GFμ : polynomial-functor-2.Preserves-μ 𝒞T 𝒞P 𝒞SC GlPE.terminal GlPE.products GlSC 𝒞Mu Gl-Mu GF)
   (𝒞-Sig-Model : Model PFPC[ 𝒞 , 𝒞T , 𝒞P ,
                   HasCoproducts.coprod (strong-coproducts→coproducts 𝒞T 𝒞SC)
                     (𝒞T .HasTerminal.witness) (𝒞T .HasTerminal.witness) ] Sig)
   where

  open import language-syntax-2 Sig using (_⊢_; first-order; first-order-ctxt)

  open import language-fo-interpretation-2 Sig
         𝒞 𝒞T 𝒞P 𝒞SC 𝒞Mu
         Gl.cat GlPE.terminal GlPE.products GlSC GlPE.exponentials Gl-Mu Gl-MuLaws
         GF GF-preserve-terminal GF-preserve-products GFC GFμ
         𝒞-Sig-Model
    renaming (𝒟⟦_⟧ty to G⟦_⟧ty; 𝒟⟦_⟧ctxt to G⟦_⟧ctxt; 𝒟⟦_⟧tm to G⟦_⟧tm)

  open Glued.Iso

  syntactic-definability :
    ∀ {Γ τ} (Γ-fo : first-order-ctxt Γ) (τ-fo : first-order τ) (M : Γ ⊢ τ) →
    ∃ (𝒞⟦ Γ-fo ⟧ctxt 𝒞.⇒ 𝒞⟦ τ-fo ⟧ty (λ ())) λ g →
      F .fmor g 𝒟.≈ (⟦ τ-fo ⟧-iso (λ ()) .bwd .morph 𝒟.∘ (G⟦ M ⟧tm .morph 𝒟.∘ ⟦ Γ-fo ⟧ctxt-iso .fwd .morph))
  syntactic-definability Γ-fo τ-fo M =
    definability (⟦ τ-fo ⟧-iso (λ ()) .bwd Glued.∘ (G⟦ M ⟧tm Glued.∘ ⟦ Γ-fo ⟧ctxt-iso .fwd))
