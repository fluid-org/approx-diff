{-# OPTIONS --prop --postfix-projections --safe #-}

-- Objects paired with a support, and morphisms that do not increase it. The support of an object is
-- a morphism into a chosen object, and the order on hom-sets is the one the additive structure
-- gives. This is what the lifting needs on the target side: joining a constant into every column of
-- a map out of a lifted object means composing the constant with the support, so a bare object will
-- not do.
open import Level using (_⊔_)
open import prop-setoid using (IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import categories using (Category; HasTerminal; IsTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct)

module supported {o m e} {𝒞 : Category o m e} (CM : CMonEnriched 𝒞)
  (let open Category 𝒞; open CMonEnriched CM)
  (+m-idem : ∀ {x y} {f : x ⇒ y} → (f +m f) ≈ f)
  (𝟙 : Category.obj 𝒞)
  where

open CommutativeMonoid

infix 4 _≤m_

_≤m_ : ∀ {x y} → x ⇒ y → x ⇒ y → Prop e
f ≤m g = (f +m g) ≈ g

≤m-refl : ∀ {x y} {f : x ⇒ y} → f ≤m f
≤m-refl = +m-idem

≤m-trans : ∀ {x y} {f g h : x ⇒ y} → f ≤m g → g ≤m h → f ≤m h
≤m-trans {f = f} {g} {h} f≤g g≤h =
  ≈-trans (homCM _ _ .+-cong ≈-refl (≈-sym g≤h))
  (≈-trans (≈-sym (homCM _ _ .+-assoc))
  (≈-trans (homCM _ _ .+-cong f≤g ≈-refl) g≤h))

≤m-∘₁ : ∀ {x y z} {f g : y ⇒ z} (h : x ⇒ y) → f ≤m g → (f ∘ h) ≤m (g ∘ h)
≤m-∘₁ {f = f} {g} h f≤g =
  ≈-trans (≈-sym (comp-bilinear₁ f g h)) (∘-cong f≤g ≈-refl)

≤m-∘₂ : ∀ {x y z} (k : y ⇒ z) {f g : x ⇒ y} → f ≤m g → (k ∘ f) ≤m (k ∘ g)
≤m-∘₂ k {f} {g} f≤g =
  ≈-trans (≈-sym (comp-bilinear₂ k f g)) (∘-cong ≈-refl f≤g)

≤m-ε : ∀ {x y} {f : x ⇒ y} → εm ≤m f
≤m-ε = homCM _ _ .+-lunit

record Obj : Set (o ⊔ m) where
  field
    carrier : obj
    supp    : carrier ⇒ 𝟙

open Obj public

record Mor (X Y : Obj) : Set (m ⊔ e) where
  field
    mor   : X .carrier ⇒ Y .carrier
    bound : (Y .supp ∘ mor) ≤m X .supp

open Mor public

infix 4 _≈s_

_≈s_ : ∀ {X Y} → Mor X Y → Mor X Y → Prop e
f ≈s g = f .mor ≈ g .mor

id-s : ∀ X → Mor X X
id-s X .mor = id (X .carrier)
id-s X .bound = ≈-trans (homCM _ _ .+-cong id-right ≈-refl) +m-idem

∘-s : ∀ {X Y Z} → Mor Y Z → Mor X Y → Mor X Z
∘-s g f .mor = g .mor ∘ f .mor
∘-s {X} {Y} {Z} g f .bound =
  ≤m-trans (≤m-trans (≈→≤ (≈-sym (assoc _ _ _))) (≤m-∘₁ (f .mor) (g .bound))) (f .bound)
  where
  ≈→≤ : ∀ {x y} {p q : x ⇒ y} → p ≈ q → p ≤m q
  ≈→≤ p≈q = ≈-trans (homCM _ _ .+-cong p≈q ≈-refl) +m-idem

cat : Category (o ⊔ m) (m ⊔ e) e
cat .Category.obj = Obj
cat .Category._⇒_ = Mor
cat .Category._≈_ = _≈s_
cat .Category.isEquiv .IsEquivalence.refl = ≈-refl
cat .Category.isEquiv .IsEquivalence.sym = ≈-sym
cat .Category.isEquiv .IsEquivalence.trans = ≈-trans
cat .Category.id = id-s
cat .Category._∘_ = ∘-s
cat .Category.∘-cong = ∘-cong
cat .Category.id-left = id-left
cat .Category.id-right = id-right
cat .Category.assoc f g h = assoc (f .mor) (g .mor) (h .mor)

-- The additive structure is inherited, since a sum of morphisms that do not increase the support
-- does not increase it either, by idempotence.
+s : ∀ {X Y} → Mor X Y → Mor X Y → Mor X Y
+s f g .mor = f .mor +m g .mor
+s {X} {Y} f g .bound =
  ≈-trans (homCM _ _ .+-cong (comp-bilinear₂ (Y .supp) (f .mor) (g .mor)) ≈-refl)
  (≈-trans (homCM _ _ .+-assoc)
  (≈-trans (homCM _ _ .+-cong ≈-refl (g .bound)) (f .bound)))

εs : ∀ {X Y} → Mor X Y
εs {X} {Y} .mor = εm
εs {X} {Y} .bound =
  ≈-trans (homCM _ _ .+-cong (comp-bilinear-ε₂ (Y .supp)) ≈-refl) (homCM _ _ .+-lunit)

cmon : CMonEnriched cat
cmon .CMonEnriched.homCM X Y .ε = εs
cmon .CMonEnriched.homCM X Y ._+_ = +s
cmon .CMonEnriched.homCM X Y .+-cong = homCM _ _ .+-cong
cmon .CMonEnriched.homCM X Y .+-lunit = homCM _ _ .+-lunit
cmon .CMonEnriched.homCM X Y .+-assoc = homCM _ _ .+-assoc
cmon .CMonEnriched.homCM X Y .+-comm = homCM _ _ .+-comm
cmon .CMonEnriched.comp-bilinear₁ f₁ f₂ g = comp-bilinear₁ (f₁ .mor) (f₂ .mor) (g .mor)
cmon .CMonEnriched.comp-bilinear₂ f g₁ g₂ = comp-bilinear₂ (f .mor) (g₁ .mor) (g₂ .mor)
cmon .CMonEnriched.comp-bilinear-ε₁ f = comp-bilinear-ε₁ (f .mor)
cmon .CMonEnriched.comp-bilinear-ε₂ f = comp-bilinear-ε₂ (f .mor)

-- The terminal object supports nothing.
terminal-s : HasTerminal 𝒞 → HasTerminal cat
terminal-s T .HasTerminal.witness .carrier = T .HasTerminal.witness
terminal-s T .HasTerminal.witness .supp = εm
terminal-s T .HasTerminal.is-terminal .IsTerminal.to-terminal .mor =
  T .HasTerminal.is-terminal .IsTerminal.to-terminal
terminal-s T .HasTerminal.is-terminal .IsTerminal.to-terminal .bound =
  ≈-trans (homCM _ _ .+-cong (comp-bilinear-ε₁ _) ≈-refl) (homCM _ _ .+-lunit)
terminal-s T .HasTerminal.is-terminal .IsTerminal.to-terminal-ext f =
  T .HasTerminal.is-terminal .IsTerminal.to-terminal-ext (f .mor)

-- A biproduct supports by the join of its components' supports, so the projections and injections
-- respect the bound and the laws are those of the underlying biproduct.
module _ (BP : ∀ x y → Biproduct CM x y) where

  private
    module B (X Y : Obj) = Biproduct (BP (X .carrier) (Y .carrier))

  biproduct-s : ∀ X Y → Biproduct cmon X Y
  biproduct-s X Y .Biproduct.prod .carrier = B.prod X Y
  biproduct-s X Y .Biproduct.prod .supp =
    (X .supp ∘ B.p₁ X Y) +m (Y .supp ∘ B.p₂ X Y)
  biproduct-s X Y .Biproduct.p₁ .mor = B.p₁ X Y
  biproduct-s X Y .Biproduct.p₁ .bound =
    ≈-trans (≈-sym (homCM _ _ .+-assoc)) (homCM _ _ .+-cong +m-idem ≈-refl)
  biproduct-s X Y .Biproduct.p₂ .mor = B.p₂ X Y
  biproduct-s X Y .Biproduct.p₂ .bound =
    ≈-trans (≈-sym (homCM _ _ .+-assoc))
    (≈-trans (homCM _ _ .+-cong (homCM _ _ .+-comm) ≈-refl)
    (≈-trans (homCM _ _ .+-assoc) (homCM _ _ .+-cong ≈-refl +m-idem)))
  biproduct-s X Y .Biproduct.in₁ .mor = B.in₁ X Y
  biproduct-s X Y .Biproduct.in₁ .bound =
    ≈-trans (homCM _ _ .+-cong split ≈-refl) +m-idem
    where
    split : (((X .supp ∘ B.p₁ X Y) +m (Y .supp ∘ B.p₂ X Y)) ∘ B.in₁ X Y) ≈ X .supp
    split =
      ≈-trans (comp-bilinear₁ _ _ _)
      (≈-trans (homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _))
      (≈-trans (homCM _ _ .+-cong (∘-cong ≈-refl (B.id-1 X Y))
                                  (∘-cong ≈-refl (B.zero-2 X Y)))
      (≈-trans (homCM _ _ .+-cong id-right (comp-bilinear-ε₂ _))
               (≈-trans (homCM _ _ .+-comm) (homCM _ _ .+-lunit)))))
  biproduct-s X Y .Biproduct.in₂ .mor = B.in₂ X Y
  biproduct-s X Y .Biproduct.in₂ .bound =
    ≈-trans (homCM _ _ .+-cong split ≈-refl) +m-idem
    where
    split : (((X .supp ∘ B.p₁ X Y) +m (Y .supp ∘ B.p₂ X Y)) ∘ B.in₂ X Y) ≈ Y .supp
    split =
      ≈-trans (comp-bilinear₁ _ _ _)
      (≈-trans (homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _))
      (≈-trans (homCM _ _ .+-cong (∘-cong ≈-refl (B.zero-1 X Y))
                                  (∘-cong ≈-refl (B.id-2 X Y)))
      (≈-trans (homCM _ _ .+-cong (comp-bilinear-ε₂ _) id-right)
               (homCM _ _ .+-lunit))))
  biproduct-s X Y .Biproduct.id-1 = B.id-1 X Y
  biproduct-s X Y .Biproduct.id-2 = B.id-2 X Y
  biproduct-s X Y .Biproduct.zero-1 = B.zero-1 X Y
  biproduct-s X Y .Biproduct.zero-2 = B.zero-2 X Y
  biproduct-s X Y .Biproduct.id-+ = B.id-+ X Y
