{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts)

module polynomial-functor where

------------------------------------------------------------------------------
-- Syntactic polynomial expressions in one variable, with constants drawn from obj 𝒞,
-- and corresponding functors.
data Poly {o m e} (𝒞 : Category o m e) : Set o where
  one  : Poly 𝒞                              -- constant terminal
  const : Category.obj 𝒞 → Poly 𝒞            -- constant object
  var  : Poly 𝒞                              -- recursive slot
  _[+]_  : Poly 𝒞 → Poly 𝒞 → Poly 𝒞          -- sum
  _[×]_  : Poly 𝒞 → Poly 𝒞 → Poly 𝒞          -- product

module Sem {o m e} {𝒞 : Category o m e}
           (T : HasTerminal 𝒞) (P : HasProducts 𝒞) (CP : HasCoproducts 𝒞) where
  open Category 𝒞
  open HasTerminal T renaming (witness to terminal)
  open HasProducts P
  open HasCoproducts CP

  poly-obj : Poly 𝒞 → obj → obj
  poly-obj one         _ = terminal
  poly-obj (const A)   _ = A
  poly-obj var         x = x
  poly-obj (P [+] Q)   x = coprod (poly-obj P x) (poly-obj Q x)
  poly-obj (P [×] Q)   x = prod   (poly-obj P x) (poly-obj Q x)

  record HasMu (Q : Poly 𝒞) : Set (o ⊔ m ⊔ e) where
    field
      μ    : obj
      inF  : poly-obj Q μ ⇒ μ
      ⦅_⦆  : ∀ {y} → (poly-obj Q y ⇒ y) → μ ⇒ y
    -- FIXME: equations (β/η for inF / ⦅_⦆)
