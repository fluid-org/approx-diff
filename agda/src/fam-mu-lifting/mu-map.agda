{-# OPTIONS --prop --postfix-projections --safe #-}

-- The map between μ-carriers needs a terminal object, to enter a fold from the empty context, so
-- it is instantiated here, above the chain, rather than forcing the parameter through every module
-- below.

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

-- The map between μ-carriers, at the terminal object of the families.
μ-map : ∀ {j k} (P : Poly (suc j)) (δ : Fin j → Obj) (Q : Poly (suc k)) (δ' : Fin k → Obj) →
        Mor (fobj (HasMu.μ-obj hasMu) P (extend δ (HasMu.μ-obj hasMu Q δ')))
            (fobj (HasMu.μ-obj hasMu) Q (extend δ' (HasMu.μ-obj hasMu Q δ'))) →
        Mor (HasMu.μ-obj hasMu P δ) (HasMu.μ-obj hasMu Q δ')
μ-map = HasMu.μ-map hasMu (terminal T)
