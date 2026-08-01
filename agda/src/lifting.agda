{-# OPTIONS --prop --postfix-projections --safe #-}

-- What the interpretation needs of a lifting: an object with a root, an injection of the payload
-- under it, and the assembly of a map out of it from a constant and a linear part, with the constant
-- recovered by the root and every map its own assembly. Functoriality is not among the requirements,
-- since the recursion only ever splits a map out of a lifted object and rebuilds it.
--
-- Constants are maps out of a chosen object. Taking that object to be a zero object makes every
-- constant vanish, and the lifting can then be the identity, which is the reading without roots.
open import Level using (_⊔_)
open import categories using (Category; HasTerminal; IsTerminal)
open import cmon-enriched using (CMonEnriched)

module lifting where

record Lifting {o m e} (𝒞 : Category o m e) (𝟙 : Category.obj 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    L      : obj → obj
    root   : ∀ {P} → 𝟙 ⇒ L P
    inj    : ∀ {P} → P ⇒ L P
    affine : ∀ {P C} → 𝟙 ⇒ C → P ⇒ C → L P ⇒ C

    affine-cong : ∀ {P C} {c c' : 𝟙 ⇒ C} {M M' : P ⇒ C} →
                  c ≈ c' → M ≈ M' → affine c M ≈ affine c' M'
    -- The root recovers the constant.
    affine-root : ∀ {P C} (c : 𝟙 ⇒ C) (M : P ⇒ C) → (affine c M ∘ root) ≈ c
    -- Every map out of a lifted object is assembled from its own two restrictions.
    affine-η    : ∀ {P C} (h : L P ⇒ C) → affine (h ∘ root) (h ∘ inj) ≈ h

  -- Two maps out of a lifted object agreeing on the root and on the payload are equal, which is the
  -- uniqueness principle the initial-algebra laws use.
  lifting-ext : ∀ {P C} (h k : L P ⇒ C) →
                (h ∘ root) ≈ (k ∘ root) → (h ∘ inj) ≈ (k ∘ inj) → h ≈ k
  lifting-ext h k er ei =
    ≈-trans (≈-sym (affine-η h)) (≈-trans (affine-cong er ei) (affine-η k))

-- The reading without roots: constants live over a zero object, so there are none, and the lifting
-- leaves objects alone.
module _ {o m e} {𝒞 : Category o m e} (CM : CMonEnriched 𝒞) (T : HasTerminal 𝒞)
  (let open Category 𝒞; open CMonEnriched CM; open HasTerminal T)
  (zero-out : ∀ {C} (c : witness ⇒ C) → c ≈ εm)
  where

  trivial : Lifting 𝒞 witness
  trivial .Lifting.L P = P
  trivial .Lifting.root = εm
  trivial .Lifting.inj = id _
  trivial .Lifting.affine c M = M
  trivial .Lifting.affine-cong c≈c' M≈M' = M≈M'
  trivial .Lifting.affine-root c M =
    ≈-trans (comp-bilinear-ε₂ M) (≈-sym (zero-out c))
  trivial .Lifting.affine-η h = id-right
