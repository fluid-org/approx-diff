{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model over the matrix-embedding representation MatRep(D, X),
-- for a biproduct base D with chosen object X whose endomorphisms commute.
open import Level using (0ℓ; suc)
open import categories
  using (Category; HasTerminal; IsInitial; IsTerminal)
open import functor using (HasLimits)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
import matrix-embedding
import ho-model

module ho-model-matrix
  (𝒟 : Category (suc 0ℓ) 0ℓ 0ℓ)
  (𝒟-cmon : CMonEnriched 𝒟)
  (𝒟-biproducts : ∀ x y → Biproduct 𝒟-cmon x y)
  (𝒟-limits : ∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → HasLimits 𝒮 𝒟)
  (𝟘 : Category.obj 𝒟)
  (𝟘-initial : IsInitial 𝒟 𝟘)
  (𝟘-terminal : IsTerminal 𝒟 𝟘)
  (X : Category.obj 𝒟)
  (let open Category 𝒟)
  (let open CMonEnriched 𝒟-cmon)
  (∘-comm : ∀ {f g : X ⇒ X} → (f ∘ g) ≈ (g ∘ f))
  where

module ME = matrix-embedding 𝒟-cmon 𝒟-biproducts 𝟘 𝟘-initial 𝟘-terminal X ∘-comm

𝒟-terminal : HasTerminal 𝒟
𝒟-terminal = record { witness = 𝟘 ; is-terminal = 𝟘-terminal }

open ho-model.Interpretation
  ME.cat ME.terminal (biproducts→products ME.cmon ME.biproduct)
  𝒟 𝒟-cmon 𝒟-limits 𝒟-terminal 𝒟-biproducts
  ME.𝓕 ME.𝓕-preserve-terminal (λ {x} {y} → ME.𝓕-preserve-products {x} {y})
  public
