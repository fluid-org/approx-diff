{-# OPTIONS --prop --postfix-projections --safe #-}

-- The biproduct lifting: the root is an isolated position, so lifting an object is forming its
-- biproduct with the unit object. The root and the injection are the two injections, the assembly
-- is the copairing, and the support is zero, so restricting an assembly along the injection is the
-- linear part alone: eliminating a value the program itself constructed charges nothing at the
-- root. Every law of the lifting is biproduct reasoning, and the action on morphisms is natural
-- outright, not only at isomorphisms.
open import Level using (_⊔_)
open import categories using (Category)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)
open import lifting using (Lifting)

module lifting-biproduct {o m e} {𝒞 : Category o m e} (CM : CMonEnriched 𝒞)
  (𝟙c : Category.obj 𝒞) (BP : ∀ x → Biproduct CM 𝟙c x) where

open Category 𝒞
open CMonEnriched CM
open CommutativeMonoid

private
  module B (x : obj) = Biproduct (BP x)

Lb : obj → obj
Lb x = B.prod x

-- Postcomposition distributes over the copairing, since composition is bilinear.
copair-post : ∀ {x y z} (h : y ⇒ z) (f : 𝟙c ⇒ y) (g : x ⇒ y) →
              (h ∘ B.copair x f g) ≈ B.copair x (h ∘ f) (h ∘ g)
copair-post {x} h f g =
  ≈-trans (comp-bilinear₂ h (f ∘ B.p₁ x) (g ∘ B.p₂ x))
    (homCM _ _ .+-cong (≈-sym (assoc h f (B.p₁ x))) (≈-sym (assoc h g (B.p₂ x))))

Lmap-b : ∀ {P Q} → P ⇒ Q → Lb P ⇒ Lb Q
Lmap-b {P} {Q} f = B.copair P (B.in₁ Q) (B.in₂ Q ∘ f)

biproduct-lifting : Lifting CM 𝟙c
biproduct-lifting .Lifting.L = Lb
biproduct-lifting .Lifting.root {P} = B.in₁ P
biproduct-lifting .Lifting.inj {P} = B.in₂ P
biproduct-lifting .Lifting.affine {P} {C} = B.copair P
biproduct-lifting .Lifting.affine-cong {P} = B.copair-cong P
biproduct-lifting .Lifting.affine-root {P} = B.copair-in₁ P
biproduct-lifting .Lifting.affine-η {P} = B.copair-ext P
biproduct-lifting .Lifting.Lmap = Lmap-b
biproduct-lifting .Lifting.Lmap-cong {P} {Q} e = B.copair-cong P ≈-refl (∘-cong ≈-refl e)
biproduct-lifting .Lifting.Lmap-id {P} =
  ≈-trans (B.copair-cong P ≈-refl id-right)
  (≈-trans (B.copair-cong P (≈-sym id-left) (≈-sym id-left)) (B.copair-ext P (id _)))
biproduct-lifting .Lifting.Lmap-comp {P} {Q} {R} g f =
  ≈-sym (≈-trans (copair-post (Lmap-b g) (B.in₁ Q) (B.in₂ Q ∘ f))
    (B.copair-cong P
      (B.copair-in₁ Q (B.in₁ R) (B.in₂ R ∘ g))
      (≈-trans (≈-sym (assoc (Lmap-b g) (B.in₂ Q) f))
      (≈-trans (∘-cong (B.copair-in₂ Q (B.in₁ R) (B.in₂ R ∘ g)) ≈-refl)
               (assoc (B.in₂ R) g f)))))
biproduct-lifting .Lifting.Lmap-root {P} {Q} f = B.copair-in₁ P (B.in₁ Q) (B.in₂ Q ∘ f)
biproduct-lifting .Lifting.spt {P} = εm
biproduct-lifting .Lifting.affine-inj {P} {C} c M =
  ≈-trans (B.copair-in₂ P c M)
    (≈-sym (≈-trans (homCM _ _ .+-cong (comp-bilinear-ε₂ c) ≈-refl) (homCM _ _ .+-lunit)))
biproduct-lifting .Lifting.Lmap-inj {P} {Q} {f} _ _ =
  B.copair-in₂ P (B.in₁ Q) (B.in₂ Q ∘ f)
biproduct-lifting .Lifting.spt-natural {P} {Q} {f} _ _ = comp-bilinear-ε₁ f
