{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The parameterised map between μ-carriers. It is the only part of the μ machinery that
-- needs a terminal object, to enter a fold from the empty context, so it sits above the chain
-- rather than forcing the parameter through every module below.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (suc)
import Data.Fin as Fin
open Fin using (Fin)
open import categories using (Category; HasTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct)
import fam-mu-lifting.in-map

module fam-mu-lifting.mu-map {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    (𝟙c : Category.obj 𝒞) where

open fam-mu-lifting.in-map os es CM BP 𝟙c public

private
  module M = HasMu hasMu

-- Fold the source against the target's algebra map after the given unfolding step. P and δ are
-- explicit because fobj and μ-obj are not injective.
μ-map : ∀ {j k} (P : Poly (suc j)) (δ : Fin j → Obj) (Q : Poly (suc k)) (δ' : Fin k → Obj) →
        Mor (fobj M.μ-obj P (extend δ (M.μ-obj Q δ')))
            (fobj M.μ-obj Q (extend δ' (M.μ-obj Q δ'))) →
        Mor (M.μ-obj P δ) (M.μ-obj Q δ')
μ-map P δ Q δ' unfold =
  Fam𝒞._∘_ (M.⦅_⦆ {P = P} {δ = δ} (Fam𝒞._∘_ (Fam𝒞._∘_ (M.inMap Q δ') unfold) Fam𝒞-P.p₂))
           (Fam𝒞-P.pair (HasTerminal.to-terminal (terminal T)) (Fam𝒞.id _))
