{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The Grothendieck logical relations at the level of families: the
-- construction applied to the categories of families over a first-order
-- category and a model, along the change of base. Taking the stages to be
-- families is what lets a stage's coproduct decomposition split a family into
-- its fibres, which the rooted μ-types need. The computation types play no
-- part here, so the monads are the identity ones.
------------------------------------------------------------------------------

open import Level using (0ℓ)
open import prop using (Prf; ∃; ∃ₛ; _,_)
open import categories using (Category; HasTerminal; HasProducts; HasWeakExponentials)
open import functor using (Functor)
open import monad using (IdentityMonad; preserve-identity-monad)
open import finite-product-functor
  using (preserve-chosen-terminal; preserve-chosen-products)
import fam
import fam-functor
import fam-stable-indexed
import fam-conservativity
import conservativity

module conservativity-fam {o₁ o₂ m e}
  {𝒞₀ : Category o₁ m e} (𝒞₀T : HasTerminal 𝒞₀) (𝒞₀P : HasProducts 𝒞₀)
  {𝒟₀ : Category o₂ m e} (𝒟₀T : HasTerminal 𝒟₀) (𝒟₀P : HasProducts 𝒟₀)
  (F₀ : Functor 𝒞₀ 𝒟₀)
  (F₀T : preserve-chosen-terminal F₀ 𝒞₀T 𝒟₀T)
  (F₀P : preserve-chosen-products F₀ 𝒞₀P 𝒟₀P)
  (let module Fam𝒞 = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒞₀)
  (let module Fam𝒟 = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒟₀)
  (let module Fam𝒟P = Fam𝒟.products 𝒟₀P)
  (𝒟E : HasWeakExponentials Fam𝒟.cat Fam𝒟P.products)
  (F₀-faithful : ∀ {a b} {g₁ g₂ : Category._⇒_ 𝒞₀ a b} →
                 Category._≈_ 𝒟₀ (F₀ .Functor.fmor g₁) (F₀ .Functor.fmor g₂) →
                 Category._≈_ 𝒞₀ g₁ g₂)
  (F₀def : ∀ {a b} (k : Category._⇒_ 𝒟₀ (F₀ .Functor.fobj a) (F₀ .Functor.fobj b)) →
           Prf (∃ (Category._⇒_ 𝒞₀ a b) λ g → Category._≈_ 𝒟₀ (F₀ .Functor.fmor g) k) →
           ∃ₛ (Category._⇒_ 𝒞₀ a b) λ g → Category._≈_ 𝒟₀ (F₀ .Functor.fmor g) k)
  where

private
  module Fam𝒞P = Fam𝒞.products 𝒞₀P
  module FC = fam-conservativity 0ℓ 0ℓ F₀

-- The change of base between the categories of families.
FamF : Functor Fam𝒞.cat Fam𝒟.cat
FamF = fam-functor.FamF 0ℓ 0ℓ F₀

-- The logical relations construction at the family level.
module Rel = conservativity
  Fam𝒞.cat (Fam𝒞.terminal 𝒞₀T) Fam𝒞P.products (IdentityMonad Fam𝒞.cat)
  Fam𝒞.bigCoproducts (fam-stable-indexed.fam-stable-indexed 𝒞₀)
  Fam𝒟.cat (Fam𝒟.terminal 𝒟₀T) Fam𝒟P.products 𝒟E (IdentityMonad Fam𝒟.cat)
  Fam𝒟.bigCoproducts
  FamF
  (fam-functor.preserve-terminal 0ℓ 0ℓ F₀ 𝒞₀T 𝒟₀T F₀T)
  (fam-functor.preserve-products 0ℓ 0ℓ F₀ 𝒞₀P 𝒟₀P F₀P)
  (preserve-identity-monad FamF)
  (FC.Id-preserves-colimits Fam𝒞.bigCoproducts)
  (λ S D → FC.FamF-∐-iso S D , FC.FamF-∐-leg S D)
  (FC.FamF-faithful F₀-faithful)
  (FC.FamF-def F₀-faithful F₀def)
