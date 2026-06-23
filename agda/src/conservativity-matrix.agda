{-# OPTIONS --postfix-projections --prop --safe #-}

-- Conservativity for the matrix model over an arbitrary biproduct base D (with a
-- chosen object X whose endomorphisms commute):
--   𝒞 = Fam(MatRep(D, X)),  𝒟 = Fam(D),  F = Fam⟨𝓕⟩
-- where 𝓕 : MatRep(D, X) ↪ D is the inclusion (matrix-embedding).
--
-- The Fam⟨_⟩ structure and the lifted functor are reused wholesale from
-- ho-model.Interpretation — its (𝒞, 𝒟, F)-context is exactly conservativity's,
-- so we only add fam-stable and bigCoproducts (both generic to Fam).
-- SemiMod(S) is one instantiation (D = SemiMod S, X = 𝕀).

open import Level using (0ℓ; suc)
open import categories
  using (Category; HasTerminal; IsInitial; IsTerminal)
open import functor using (HasLimits)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
import matrix-embedding
import ho-model

module conservativity-matrix
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

-- In a biproduct category the terminal is the zero object; use the one 𝓕 preserves.
𝒟-terminal : HasTerminal 𝒟
𝒟-terminal = record { witness = 𝟘 ; is-terminal = 𝟘-terminal }

open ho-model.Interpretation
  ME.cat ME.terminal (biproducts→products ME.cmon ME.biproduct)
  𝒟 𝒟-cmon 𝒟-limits 𝒟-terminal 𝒟-biproducts
  ME.𝓕 ME.𝓕-preserve-terminal (λ {x} {y} → ME.𝓕-preserve-products {x} {y})

open import conservativity
  Fam⟨𝒞⟩.cat Fam⟨𝒞⟩-terminal Fam⟨𝒞⟩-products Fam⟨𝒞⟩-coproducts Fam⟨𝒞⟩.fam-stable
  Fam⟨𝒟⟩.cat Fam⟨𝒟⟩-terminal Fam⟨𝒟⟩-products Fam⟨𝒟⟩-coproducts Fam⟨𝒟⟩-exponentials Fam⟨𝒟⟩.bigCoproducts
  Fam⟨F⟩ Fam⟨F⟩-preserves-terminal Fam⟨F⟩-preserves-products Fam⟨F⟩-preserves-coproducts
  public
