{-# OPTIONS --postfix-projections --prop --safe #-}

-- Syntactic descriptions of the fibre objects at first-order sorts: a fibre is
-- built from the generator, the terminal object, and products. The width and the
-- 𝒞-object are computed from the description, so a single choice fixes both.

open import categories using (Category; HasTerminal; HasProducts)
import Data.Nat

module free-object {o m e}
  (𝒞 : Category o m e) (𝒞-terminal : HasTerminal 𝒞) (𝒞-products : HasProducts 𝒞)
  (𝕀ᶜ : Category.obj 𝒞)
  where

private
  module C = Category 𝒞
  module CT = HasTerminal 𝒞-terminal
  module CP = HasProducts 𝒞-products

data FreeObj : Set where
  gen  : FreeObj
  unit : FreeObj
  _×f_ : FreeObj → FreeObj → FreeObj

⟦_⟧f : FreeObj → C.obj
⟦ gen ⟧f      = 𝕀ᶜ
⟦ unit ⟧f     = CT.witness
⟦ e₁ ×f e₂ ⟧f = CP.prod ⟦ e₁ ⟧f ⟦ e₂ ⟧f

fwidth : FreeObj → Data.Nat.ℕ
fwidth gen        = 1
fwidth unit       = 0
fwidth (e₁ ×f e₂) = fwidth e₁ Data.Nat.+ fwidth e₂
