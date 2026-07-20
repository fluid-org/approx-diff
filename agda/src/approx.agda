{-# OPTIONS --postfix-projections --prop --safe #-}

-- Syntactic descriptions of the approximation attached to a first-order sort: no
-- approximation, the generator, or two approximations side by side. The width and
-- the 𝒞-object are computed from the description, so a single choice fixes both.

open import categories using (Category; HasTerminal; HasProducts)
import Data.Nat

module approx {o m e}
  (𝒞 : Category o m e) (𝒞-terminal : HasTerminal 𝒞) (𝒞-products : HasProducts 𝒞)
  (𝕀ᶜ : Category.obj 𝒞)
  where

private
  module C = Category 𝒞
  module CT = HasTerminal 𝒞-terminal
  module CP = HasProducts 𝒞-products

data Approx : Set where
  gen  : Approx
  unit : Approx
  _×_  : Approx → Approx → Approx

⟦_⟧ : Approx → C.obj
⟦ gen ⟧     = 𝕀ᶜ
⟦ unit ⟧    = CT.witness
⟦ a₁ × a₂ ⟧ = CP.prod ⟦ a₁ ⟧ ⟦ a₂ ⟧

width : Approx → Data.Nat.ℕ
width gen         = 1
width unit        = 0
width (a₁ × a₂)   = width a₁ Data.Nat.+ width a₂
