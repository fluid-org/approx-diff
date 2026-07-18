{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import Data.Nat using (ℕ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import signature-algebra using (Algebra)

import ho-model-sd-semimod

-- Logical relation between the operational semantics (language-evaluation-mat)
-- and the denotational interpretation in Fam(SemiMod(S)) (interp-sd), following
-- Definition [logical-relation] of the graph-semantics paper, in existential
-- (computability) form.
--
-- Design (agreed 2026-07-18):
--
--  * Rel τ v a r : Set, by recursion on τ, relating a value v : Val τ, a point a
--    of ⟦ τ ⟧ty .idx, and a realisation r : SemiMod morphism from the free
--    semimodule on `width v` scalar positions (X^ (width v), via
--    matrix-embedding-semimod) to the fibre ⟦ τ ⟧ty .fam at a.
--  * Base and unit clauses: a agrees with the value via sort-embed, r the
--    canonical map; products/sums structural; arrow clause EXISTENTIAL: for
--    every related argument there exist u, R, a derivation γ·v ,, t ⇓ u [ R ],
--    and a related realisation with q ∘ R = [ π_a ∘ r , ∂f(a) ∘ s ].
--  * μ clause via an inductive family MuRel indexed by syntactic subexpressions
--    of the body (the same device as Map in language-evaluation and the
--    termination argument discussed for Definition 2.4): value-structural
--    constructors, leaf constructors invoking Rel at proper subtypes.
--  * Fundamental property (next step): ∀ t γ g r → EnvRel γ g r → ∃ v R q,
--    derivation + Rel; projecting gives eval (totality), then soundness at
--    first-order types via the collapse of Rel to the canonical isomorphism.
--
-- Parameters: the semiring, the signature with its value-level algebra, the
-- categorical model, and the agreement between algebra and model at base sorts
-- (sort-embed plus a fibre identification with the free semimodule on
-- sort-width s generators; op/rel agreement is deferred to the fundamental
-- property, which is where it is used).
module logical-relation
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (Sig : Signature 0ℓ) (𝒜 : Algebra Sig 0ℓ)
  (open ho-model-sd-semimod S)
  (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
  (sort-width : Signature.sort Sig → ℕ)
  (sort-embed : ∀ s → Algebra.sort-val 𝒜 s →
                Setoid.Carrier (Fam⟨𝒞⟩.Obj.idx (Model.⟦sort⟧ Impl s)))
  where

-- TODO: Rel, MuRel, EnvRel per the design above.
