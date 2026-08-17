{-# OPTIONS --prop --postfix-projections --safe #-}

-- The functorial action and the map between μ-carriers need a terminal object, to enter a fold from
-- the empty context, so they are instantiated here, above the chain, rather than forcing the parameter
-- through every module below.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import categories using (Category; HasTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct)
import fam-mu-lifting.laws

module fam-mu-lifting.mu-map {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    (𝟙c : Category.obj 𝒞) where

open fam-mu-lifting.laws os es CM BP 𝟙c public

open HasMu.WithTerminal hasMu (terminal T) public using (fmor; μ-map)
open HasMuLaws.WithTerminal hasMuLaws (terminal T) public
  using (fmor-cong; fmor-id; fmor-comp; fmor-const; fmor-var; fmor-+; fmor-×; fmor-μ;
         μ-map-cong; μ-map-id; μ-map-in; μ-map-comp)
