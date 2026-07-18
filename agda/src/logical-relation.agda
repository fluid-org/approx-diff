{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import Data.Nat using (ℕ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import signature-algebra using (Algebra)

import ho-model-sd-semimod

-- Logical relation between the operational semantics and the interpretation in
-- Fam(SemiMod(S)), in existential (computability) form.
module logical-relation
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (Sig : Signature 0ℓ) (𝒜 : Algebra Sig 0ℓ)
  (open ho-model-sd-semimod S)
  (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
  (sort-width : Signature.sort Sig → ℕ)
  (sort-embed : ∀ s → Algebra.sort-val 𝒜 s →
                Setoid.Carrier (Fam⟨𝒞⟩.Obj.idx (Model.⟦sort⟧ Impl s)))
  where

-- TODO: Rel, MuRel, EnvRel; fundamental property.
