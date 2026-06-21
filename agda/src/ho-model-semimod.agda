{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model interpreted directly in Fam(SemiMod S), with no
-- intermediate Mat(S): the source base category is SemiMod itself and the
-- transporting functor F is the identity.  Parameterised by the scalar semiring
-- S (instantiated at semiring-bool for the boolean model, semiring-Q-tropical for
-- the interval model, etc.).
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category; HasTerminal; HasProducts)
open import functor using (Functor; Id)
open import finite-product-functor using (preserve-chosen-terminal; preserve-chosen-products)
open import cmon-enriched using (biproducts→products)
import semimodule
import ho-model

module ho-model-semimod {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

module SM = semimodule S

private
  module SMc = Category SM.cat

products : HasProducts SM.cat
products = biproducts→products SM.cmon-enriched SM.biproduct

private
  module P = HasProducts products
  open SMc using (id; _∘_; _≈_; id-left; id-right; ≈-trans)
  open Category.IsIso

F-preserve-terminal : preserve-chosen-terminal (Id {𝒞 = SM.cat}) SM.terminal SM.terminal
F-preserve-terminal .inverse = id _
F-preserve-terminal .f∘inverse≈id = HasTerminal.to-terminal-unique SM.terminal _ _
F-preserve-terminal .inverse∘f≈id = HasTerminal.to-terminal-unique SM.terminal _ _

F-preserve-products : preserve-chosen-products (Id {𝒞 = SM.cat}) products products
F-preserve-products .inverse = id _
F-preserve-products .f∘inverse≈id = ≈-trans id-right P.pair-ext0
F-preserve-products .inverse∘f≈id = ≈-trans id-left P.pair-ext0

open ho-model.Interpretation
  SM.cat SM.terminal products
  SM.cat SM.cmon-enriched SM.limits SM.terminal SM.biproduct
  (Id {𝒞 = SM.cat}) F-preserve-terminal
  (λ {X} {Y} → F-preserve-products {X} {Y})
  public
