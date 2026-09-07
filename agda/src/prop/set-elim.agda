{-# OPTIONS --postfix-projections --safe --prop #-}

open import Data.Empty using () renaming (⊥ to ⊥ₛ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Nullary.Decidable using () renaming (Dec to Decₛ; yes to yesₛ; no to noₛ)

-- Eliminations of Set-level data into Prop.
module prop.set-elim where

⊥-elim : ∀ {p} {P : Prop p} → ⊥ₛ → P
⊥-elim ()

dec-case : ∀ {a p} {A : Set a} {P : Prop p} → Decₛ A → (A → P) → ((A → ⊥ₛ) → P) → P
dec-case (yesₛ k)  t f = t k
dec-case (noₛ ¬k) t f = f ¬k

⊎-case : ∀ {a b p} {A : Set a} {B : Set b} {P : Prop p} → (A → P) → (B → P) → A ⊎ B → P
⊎-case f g (inj₁ x) = f x
⊎-case f g (inj₂ y) = g y
