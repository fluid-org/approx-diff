{-# OPTIONS --prop --postfix-projections --safe #-}

-- The fused initial-algebra laws over a grammar of shapes, in any CMon-enriched category with
-- biproducts and a lifting. Every value former carries a root above its payload, in the fibre of a
-- value and in the carrier interpretation alike, so an algebra is an ordinary morphism out of the
-- carrier, which by the lifting's laws is a constant together with a linear part at every node.
--
-- The fold applies the algebra to a payload whose recursive positions are already folded, splitting
-- the continuation where the structure demands: at a root into its constant and its linear part, at
-- a product additively, so that the context is not counted twice. No map of a lifted object in
-- context is ever needed, which is the map the lifting does not admit. The single law determines
-- the fold.
open import Level using (_⊔_)
open import categories using (Category)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)
open import lifting using (Lifting)

module lifting-fold
  {o m e} {𝒞 : Category o m e} (CM : CMonEnriched 𝒞)
  (BP : ∀ x y → Biproduct CM x y)
  {𝟙c : Category.obj 𝒞} (Lft : Lifting 𝒞 𝟙c)
  where

open Category 𝒞
open CMonEnriched CM
open Lifting Lft

infixr 30 _⊗_
infixr 25 _⊞_

private
  _⊕_ : obj → obj → obj
  x ⊕ y = Biproduct.prod (BP x y)

  cop : ∀ {x y z} → x ⇒ z → y ⇒ z → (x ⊕ y) ⇒ z
  cop {x} {y} f g = Biproduct.copair (BP x y) f g

  cop-cong : ∀ {x y z} {f f' : x ⇒ z} {g g' : y ⇒ z} → f ≈ f' → g ≈ g' → cop f g ≈ cop f' g'
  cop-cong {x} {y} = Biproduct.copair-cong (BP x y)

  pairb : ∀ {x y z} → x ⇒ y → x ⇒ z → x ⇒ (y ⊕ z)
  pairb {x} {y} {z} f g = Biproduct.pair (BP y z) f g

  pairb-cong : ∀ {x y z} {f f' : x ⇒ y} {g g' : x ⇒ z} → f ≈ f' → g ≈ g' → pairb f g ≈ pairb f' g'
  pairb-cong {x} {y} {z} = Biproduct.pair-cong (BP y z)

  π₁ : ∀ {x y} → (x ⊕ y) ⇒ x
  π₁ {x} {y} = Biproduct.p₁ (BP x y)

  ι₁ : ∀ {x y} → x ⇒ (x ⊕ y)
  ι₁ {x} {y} = Biproduct.in₁ (BP x y)

  ι₂ : ∀ {x y} → y ⇒ (x ⊕ y)
  ι₂ {x} {y} = Biproduct.in₂ (BP x y)

  +m-cong : ∀ {x y} {f f' g g' : x ⇒ y} → f ≈ f' → g ≈ g' → (f +m g) ≈ (f' +m g')
  +m-cong = homCM _ _ .CommutativeMonoid.+-cong

data Poly : Set o where
  konst : obj → Poly
  var   : Poly
  _⊗_   : Poly → Poly → Poly
  _⊞_   : Poly → Poly → Poly

-- Values and the index data of one layer: which branch each sum took, and the sub-values at the
-- recursive positions.
mutual
  data Val (B : Poly) : Set o where
    sup : Shape B B → Val B

  data Shape (B : Poly) : Poly → Set o where
    kon : ∀ {K} → Shape B (konst K)
    rec : Val B → Shape B var
    prd : ∀ {Q₁ Q₂} → Shape B Q₁ → Shape B Q₂ → Shape B (Q₁ ⊗ Q₂)
    inl : ∀ {Q₁ Q₂} → Shape B Q₁ → Shape B (Q₁ ⊞ Q₂)
    inr : ∀ {Q₁ Q₂} → Shape B Q₂ → Shape B (Q₁ ⊞ Q₂)

-- The fibre of a value: a root above each former.
mutual
  fibV : ∀ {B} → Val B → obj
  fibV (sup s) = fibS s

  fibS : ∀ {B Q} → Shape B Q → obj
  fibS (kon {K})   = K
  fibS (rec v)     = fibV v
  fibS (prd s₁ s₂) = L (fibS s₁ ⊕ fibS s₂)
  fibS (inl s)     = L (fibS s)
  fibS (inr s)     = L (fibS s)

-- The carrier interpretation of a layer: the same structure, with the carrier at the recursive
-- positions and the roots kept.
sh : ∀ (R : obj) {B Q} → Shape B Q → obj
sh R (kon {K})   = K
sh R (rec v)     = R
sh R (prd s₁ s₂) = L (sh R s₁ ⊕ sh R s₂)
sh R (inl s)     = L (sh R s)
sh R (inr s)     = L (sh R s)

module _ (W R : obj) where

  ⟦_⟧ : ∀ {B Q} → Shape B Q → obj
  ⟦_⟧ = sh R

  -- One step of the recursion at each node. At a recursive position the folded sub-value is fed to
  -- the continuation with the context retained.
  varStep : ∀ (X : obj) → (W ⊕ R) ⇒ R → (W ⊕ X) ⇒ R → (W ⊕ X) ⇒ R
  varStep X k g = k ∘ pairb π₁ g

  varStep-cong : ∀ (X : obj) (k : (W ⊕ R) ⇒ R) {g g' : (W ⊕ X) ⇒ R} →
                 g ≈ g' → varStep X k g ≈ varStep X k g'
  varStep-cong X k eg = ∘-cong ≈-refl (pairb-cong ≈-refl eg)

  -- Under a root, a product splits the continuation additively, the context going to the first
  -- component only, so that it is not counted twice.
  prodCont₁ : ∀ (X₁ X₂ : obj) → (W ⊕ (X₁ ⊕ X₂)) ⇒ R → (W ⊕ X₁) ⇒ R
  prodCont₁ X₁ X₂ k = cop (k ∘ ι₁) ((k ∘ ι₂) ∘ ι₁)

  prodCont₂ : ∀ (X₁ X₂ : obj) → (W ⊕ (X₁ ⊕ X₂)) ⇒ R → (W ⊕ X₂) ⇒ R
  prodCont₂ X₁ X₂ k = cop εm ((k ∘ ι₂) ∘ ι₂)

  prodStep : ∀ (F₁ F₂ : obj) → (W ⊕ F₁) ⇒ R → (W ⊕ F₂) ⇒ R → (W ⊕ (F₁ ⊕ F₂)) ⇒ R
  prodStep F₁ F₂ r₁ r₂ = cop ((r₁ ∘ ι₁) +m (r₂ ∘ ι₁)) (cop (r₁ ∘ ι₂) (r₂ ∘ ι₂))

  prodStep-cong : ∀ (F₁ F₂ : obj) {r₁ r₁' : (W ⊕ F₁) ⇒ R} {r₂ r₂' : (W ⊕ F₂) ⇒ R} →
                  r₁ ≈ r₁' → r₂ ≈ r₂' → prodStep F₁ F₂ r₁ r₂ ≈ prodStep F₁ F₂ r₁' r₂'
  prodStep-cong F₁ F₂ e₁ e₂ =
    cop-cong (+m-cong (∘-cong e₁ ≈-refl) (∘-cong e₂ ≈-refl))
             (cop-cong (∘-cong e₁ ≈-refl) (∘-cong e₂ ≈-refl))

  -- At a root the continuation splits into its constant and its linear part; the constant is what
  -- the former alone determines and passes through untouched.
  rootCont : ∀ (X : obj) → (W ⊕ L X) ⇒ R → (W ⊕ X) ⇒ R
  rootCont X k = cop (k ∘ ι₁) ((k ∘ ι₂) ∘ inj)

  rootStep : ∀ (X F : obj) → (W ⊕ L X) ⇒ R → (W ⊕ F) ⇒ R → (W ⊕ L F) ⇒ R
  rootStep X F k r = cop (r ∘ ι₁) (affine ((k ∘ ι₂) ∘ root) (r ∘ ι₂))

  rootStep-cong : ∀ (X F : obj) (k : (W ⊕ L X) ⇒ R) {r r' : (W ⊕ F) ⇒ R} →
                  r ≈ r' → rootStep X F k r ≈ rootStep X F k r'
  rootStep-cong X F k er =
    cop-cong (∘-cong er ≈-refl) (affine-cong ≈-refl (∘-cong er ≈-refl))

  Cand : Poly → Set (o ⊔ m)
  Cand B = (v : Val B) → (W ⊕ fibV v) ⇒ R

  -- Applying an algebra to a payload whose recursive positions have already been folded.
  applyG : ∀ {B} → Cand B → ∀ {Q} (s : Shape B Q) → (W ⊕ ⟦ s ⟧) ⇒ R → (W ⊕ fibS s) ⇒ R
  applyG f kon         k = k
  applyG f (rec v)     k = varStep (fibV v) k (f v)
  applyG f (prd s₁ s₂) k =
    rootStep (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) (fibS s₁ ⊕ fibS s₂) k
      (prodStep (fibS s₁) (fibS s₂)
        (applyG f s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
        (applyG f s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k))))
  applyG f (inl s) k = rootStep ⟦ s ⟧ (fibS s) k (applyG f s (rootCont ⟦ s ⟧ k))
  applyG f (inr s) k = rootStep ⟦ s ⟧ (fibS s) k (applyG f s (rootCont ⟦ s ⟧ k))

  module _ {B : Poly} (alg : (s : Shape B B) → (W ⊕ ⟦ s ⟧) ⇒ R) where

    -- The fold repeats that recursion with itself at the recursive positions, which is what makes
    -- it structurally recursive.
    mutual
      fold : Cand B
      fold (sup s) = foldS s (alg s)

      foldS : ∀ {Q} (s : Shape B Q) → (W ⊕ ⟦ s ⟧) ⇒ R → (W ⊕ fibS s) ⇒ R
      foldS kon         k = k
      foldS (rec v)     k = varStep (fibV v) k (fold v)
      foldS (prd s₁ s₂) k =
        rootStep (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) (fibS s₁ ⊕ fibS s₂) k
          (prodStep (fibS s₁) (fibS s₂)
            (foldS s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
            (foldS s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k))))
      foldS (inl s) k = rootStep ⟦ s ⟧ (fibS s) k (foldS s (rootCont ⟦ s ⟧ k))
      foldS (inr s) k = rootStep ⟦ s ⟧ (fibS s) k (foldS s (rootCont ⟦ s ⟧ k))

    -- The fused law: one equation per value, with the algebra applied to the folded payload.
    IsFold : Cand B → Prop (o ⊔ e)
    IsFold h = ∀ (s : Shape B B) → h (sup s) ≈ applyG h s (alg s)

    foldS-applyG : ∀ {Q} (s : Shape B Q) (k : (W ⊕ ⟦ s ⟧) ⇒ R) → foldS s k ≈ applyG fold s k
    foldS-applyG kon k = ≈-refl
    foldS-applyG (rec v) k = ≈-refl
    foldS-applyG (prd s₁ s₂) k =
      rootStep-cong (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) (fibS s₁ ⊕ fibS s₂) k
        (prodStep-cong (fibS s₁) (fibS s₂)
          (foldS-applyG s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
          (foldS-applyG s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k))))
    foldS-applyG (inl s) k =
      rootStep-cong ⟦ s ⟧ (fibS s) k (foldS-applyG s (rootCont ⟦ s ⟧ k))
    foldS-applyG (inr s) k =
      rootStep-cong ⟦ s ⟧ (fibS s) k (foldS-applyG s (rootCont ⟦ s ⟧ k))

    fold-is-fold : IsFold fold
    fold-is-fold s = foldS-applyG s (alg s)

    -- The law determines the fold, by induction on the value together with its shape.
    mutual
      fold-unique : (h : Cand B) → IsFold h → ∀ v → h v ≈ fold v
      fold-unique h H (sup s) = ≈-trans (H s) (fold-uniqueS h H s (alg s))

      fold-uniqueS : (h : Cand B) → IsFold h → ∀ {Q} (s : Shape B Q) (k : (W ⊕ ⟦ s ⟧) ⇒ R) →
                     applyG h s k ≈ foldS s k
      fold-uniqueS h H kon k = ≈-refl
      fold-uniqueS h H (rec v) k = varStep-cong (fibV v) k (fold-unique h H v)
      fold-uniqueS h H (prd s₁ s₂) k =
        rootStep-cong (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) (fibS s₁ ⊕ fibS s₂) k
          (prodStep-cong (fibS s₁) (fibS s₂)
            (fold-uniqueS h H s₁ (prodCont₁ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k)))
            (fold-uniqueS h H s₂ (prodCont₂ ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) k))))
      fold-uniqueS h H (inl s) k =
        rootStep-cong ⟦ s ⟧ (fibS s) k (fold-uniqueS h H s (rootCont ⟦ s ⟧ k))
      fold-uniqueS h H (inr s) k =
        rootStep-cong ⟦ s ⟧ (fibS s) k (fold-uniqueS h H s (rootCont ⟦ s ⟧ k))
