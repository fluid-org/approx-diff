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
  {𝟙c : Category.obj 𝒞} (Lft : Lifting CM 𝟙c)
  where

open Category 𝒞
open CMonEnriched CM
open Lifting Lft

infixr 30 _⊗_
infixr 25 _⊞_

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

π₂ : ∀ {x y} → (x ⊕ y) ⇒ y
π₂ {x} {y} = Biproduct.p₂ (BP x y)

ι₁ : ∀ {x y} → x ⇒ (x ⊕ y)
ι₁ {x} {y} = Biproduct.in₁ (BP x y)

ι₂ : ∀ {x y} → y ⇒ (x ⊕ y)
ι₂ {x} {y} = Biproduct.in₂ (BP x y)

+m-cong : ∀ {x y} {f f' g g' : x ⇒ y} → f ≈ f' → g ≈ g' → (f +m g) ≈ (f' +m g')
+m-cong = homCM _ _ .CommutativeMonoid.+-cong

-- Generic biproduct consequences the rooted machinery threads.
pm : ∀ {a₁ a₂ b₁ b₂} → a₁ ⇒ a₂ → b₁ ⇒ b₂ → (a₁ ⊕ b₁) ⇒ (a₂ ⊕ b₂)
pm g h = pairb (g ∘ π₁) (h ∘ π₂)

pm-in₁ : ∀ {a₁ a₂ b₁ b₂} (g : a₁ ⇒ a₂) (h : b₁ ⇒ b₂) → (pm g h ∘ ι₁) ≈ (ι₁ ∘ g)
pm-in₁ {a₁} {a₂} {b₁} {b₂} g h =
  ≈-trans (Biproduct.pair-natural (BP a₂ b₂) _ _ _)
  (≈-trans (pairb-cong
             (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl (Biproduct.id-1 (BP a₁ b₁))) id-right))
             (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl (Biproduct.zero-2 (BP a₁ b₁))) (comp-bilinear-ε₂ h))))
           (≈-trans (+m-cong ≈-refl (comp-bilinear-ε₂ ι₂)) +m-runit))

pm-in₂ : ∀ {a₁ a₂ b₁ b₂} (g : a₁ ⇒ a₂) (h : b₁ ⇒ b₂) → (pm g h ∘ ι₂) ≈ (ι₂ ∘ h)
pm-in₂ {a₁} {a₂} {b₁} {b₂} g h =
  ≈-trans (Biproduct.pair-natural (BP a₂ b₂) _ _ _)
  (≈-trans (pairb-cong
             (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl (Biproduct.zero-1 (BP a₁ b₁))) (comp-bilinear-ε₂ g)))
             (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl (Biproduct.id-2 (BP a₁ b₁))) id-right)))
           (≈-trans (+m-cong (comp-bilinear-ε₂ ι₁) ≈-refl)
                    (homCM _ _ .CommutativeMonoid.+-lunit)))

bp-ext : ∀ {a b c} {h k : (a ⊕ b) ⇒ c} → (h ∘ ι₁) ≈ (k ∘ ι₁) → (h ∘ ι₂) ≈ (k ∘ ι₂) → h ≈ k
bp-ext {a} {b} {c} {h} {k} e₁ e₂ =
  ≈-trans (≈-sym (Biproduct.copair-ext (BP a b) h))
  (≈-trans (cop-cong e₁ e₂) (Biproduct.copair-ext (BP a b) k))

-- Reindexing a context-paired morphism under a root: the root passes through, the context enters
-- the payload, and absorption records under the target root whatever the context contributes.
under-root : ∀ {G X Y} → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ L Y)
under-root r = cop (inj ∘ (r ∘ ι₁)) (affine root (inj ∘ (r ∘ ι₂)))

under-root-cong : ∀ {G X Y} {r r' : (G ⊕ X) ⇒ Y} → r ≈ r' → under-root r ≈ under-root r'
under-root-cong er =
  cop-cong (∘-cong ≈-refl (∘-cong er ≈-refl))
           (affine-cong ≈-refl (∘-cong ≈-refl (∘-cong er ≈-refl)))

-- Transport across the lifting fuses with composition on either side: with an isomorphism after,
-- through the action, and with a context-paired map before.
under-root-post : ∀ {G X Y₁ Y₂} {h : Y₁ ⇒ Y₂} {h' : Y₂ ⇒ Y₁} →
                  (h ∘ h') ≈ id Y₂ → (h' ∘ h) ≈ id Y₁ →
                  (r : (G ⊕ X) ⇒ Y₁) → (Lmap h ∘ under-root r) ≈ under-root (h ∘ r)
under-root-post {G} {X} {Y₁} {Y₂} {h} {h'} hi₁ hi₂ r =
  bp-ext {h = Lmap h ∘ under-root r} {k = under-root (h ∘ r)}
    (≈-trans (assoc _ _ _)
     (≈-trans (∘-cong ≈-refl (Biproduct.copair-in₁ (BP G (L X)) _ _))
      (≈-trans (≈-sym (assoc _ _ _))
       (≈-trans (∘-cong (Lmap-inj hi₁ hi₂) ≈-refl)
        (≈-trans (assoc _ _ _)
         (≈-trans (∘-cong ≈-refl (≈-sym (assoc _ _ _)))
          (≈-sym (Biproduct.copair-in₁ (BP G (L X)) _ _))))))))
    (≈-trans (assoc _ _ _)
     (≈-trans (∘-cong ≈-refl (Biproduct.copair-in₂ (BP G (L X)) _ _))
      (≈-trans part₂ (≈-sym (Biproduct.copair-in₂ (BP G (L X)) _ _)))))
  where
  part₂ : (Lmap h ∘ affine root (inj ∘ (r ∘ ι₂))) ≈ affine root (inj ∘ ((h ∘ r) ∘ ι₂))
  part₂ = lifting-ext _ _
    (≈-trans (assoc _ _ _)
     (≈-trans (∘-cong ≈-refl (affine-root _ _))
      (≈-trans (Lmap-root h) (≈-sym (affine-root _ _)))))
    (≈-trans (assoc _ _ _)
     (≈-trans (∘-cong ≈-refl (affine-inj _ _))
      (≈-trans (comp-bilinear₂ _ _ _)
       (≈-trans (+m-cong
                  (≈-trans (≈-sym (assoc _ _ _)) (∘-cong (Lmap-root h) ≈-refl))
                  (≈-trans (≈-sym (assoc _ _ _))
                   (≈-trans (∘-cong (Lmap-inj hi₁ hi₂) ≈-refl)
                    (≈-trans (assoc _ _ _)
                     (∘-cong ≈-refl (≈-sym (assoc _ _ _)))))))
        (≈-sym (affine-inj _ _))))))

-- Transporting the projection across the lifting is the projection: the context part vanishes and
-- the assembly of the root with the injection is the identity.
under-root-p₂ : ∀ {G X} → under-root (π₂ {G} {X}) ≈ π₂ {G} {L X}
under-root-p₂ {G} {X} =
  ≈-trans (cop-cong
            (≈-trans (∘-cong ≈-refl (Biproduct.zero-2 (BP G X))) (comp-bilinear-ε₂ inj))
            (≈-trans (affine-cong ≈-refl
                       (≈-trans (∘-cong ≈-refl (Biproduct.id-2 (BP G X))) id-right))
             (≈-trans (affine-cong (≈-sym id-left) (≈-sym id-left)) (affine-η (id (L X))))))
  (≈-trans (+m-cong (comp-bilinear-ε₁ π₁) id-left)
           (homCM _ _ .CommutativeMonoid.+-lunit))

-- Reindexing under a root commutes with transports along isomorphisms, which is what naturality of
-- the fold and of reindexing in the tree demands. The context map is arbitrary; the payload and
-- result maps must be isomorphisms, since the injection and the support are natural only there.
under-root-natural :
  ∀ {G₁ G₂ X₁ X₂ Y₁ Y₂} (g : G₁ ⇒ G₂)
    {x : X₁ ⇒ X₂} {x' : X₂ ⇒ X₁} (xi₁ : (x ∘ x') ≈ id X₂) (xi₂ : (x' ∘ x) ≈ id X₁)
    {y : Y₁ ⇒ Y₂} {y' : Y₂ ⇒ Y₁} (yi₁ : (y ∘ y') ≈ id Y₂) (yi₂ : (y' ∘ y) ≈ id Y₁)
    (f₁ : (G₁ ⊕ X₁) ⇒ Y₁) (f₂ : (G₂ ⊕ X₂) ⇒ Y₂) →
    (f₂ ∘ pm g x) ≈ (y ∘ f₁) →
    (under-root f₂ ∘ pm g (Lmap x)) ≈ (Lmap y ∘ under-root f₁)
under-root-natural {G₁} {G₂} {X₁} {X₂} {Y₁} {Y₂} g {x} {x'} xi₁ xi₂ {y} {y'} yi₁ yi₂ f₁ f₂ sq =
  bp-ext side₁ side₂
  where
  square-ι₁ : ((f₂ ∘ ι₁) ∘ g) ≈ (y ∘ (f₁ ∘ ι₁))
  square-ι₁ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-sym (pm-in₁ g x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong sq ≈-refl) (assoc _ _ _))))

  square-ι₂ : ((f₂ ∘ ι₂) ∘ x) ≈ (y ∘ (f₁ ∘ ι₂))
  square-ι₂ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-sym (pm-in₂ g x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong sq ≈-refl) (assoc _ _ _))))

  side₁ : ((under-root f₂ ∘ pm g (Lmap x)) ∘ ι₁) ≈ ((Lmap y ∘ under-root f₁) ∘ ι₁)
  side₁ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (pm-in₁ g (Lmap x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong (Biproduct.copair-in₁ (BP G₂ (L X₂)) _ _) ≈-refl)
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl square-ι₁)
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong (≈-sym (Lmap-inj yi₁ yi₂)) ≈-refl)
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-sym (Biproduct.copair-in₁ (BP G₁ (L X₁)) _ _)))
             (≈-sym (assoc _ _ _)))))))))))

  lift-part : (affine root (inj ∘ (f₂ ∘ ι₂)) ∘ Lmap x) ≈ (Lmap y ∘ affine root (inj ∘ (f₁ ∘ ι₂)))
  lift-part = lifting-ext _ _ root-side inj-side
    where
    root-side : ((affine root (inj ∘ (f₂ ∘ ι₂)) ∘ Lmap x) ∘ root)
                ≈ ((Lmap y ∘ affine root (inj ∘ (f₁ ∘ ι₂))) ∘ root)
    root-side =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (Lmap-root x))
      (≈-trans (affine-root _ _)
      (≈-sym
        (≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (affine-root _ _)) (Lmap-root y))))))

    left-inj : ((affine root (inj ∘ (f₂ ∘ ι₂)) ∘ Lmap x) ∘ inj)
               ≈ ((root ∘ spt) +m (Lmap y ∘ (inj ∘ (f₁ ∘ ι₂))))
    left-inj =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (Lmap-inj xi₁ xi₂))
      (≈-trans (≈-sym (assoc _ _ _))
      (≈-trans (∘-cong (affine-inj _ _) ≈-refl)
      (≈-trans (comp-bilinear₁ _ _ _)
        (+m-cong
          (≈-trans (assoc _ _ _) (∘-cong ≈-refl (spt-natural xi₁ xi₂)))
          (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl square-ι₂)
          (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong (≈-sym (Lmap-inj yi₁ yi₂)) ≈-refl) (assoc _ _ _))))))))))

    right-inj : ((Lmap y ∘ affine root (inj ∘ (f₁ ∘ ι₂))) ∘ inj)
                ≈ ((root ∘ spt) +m (Lmap y ∘ (inj ∘ (f₁ ∘ ι₂))))
    right-inj =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (affine-inj _ _))
      (≈-trans (comp-bilinear₂ _ _ _)
        (+m-cong (≈-trans (≈-sym (assoc _ _ _)) (∘-cong (Lmap-root y) ≈-refl)) ≈-refl)))

    inj-side : ((affine root (inj ∘ (f₂ ∘ ι₂)) ∘ Lmap x) ∘ inj)
               ≈ ((Lmap y ∘ affine root (inj ∘ (f₁ ∘ ι₂))) ∘ inj)
    inj-side = ≈-trans left-inj (≈-sym right-inj)

  side₂ : ((under-root f₂ ∘ pm g (Lmap x)) ∘ ι₂) ≈ ((Lmap y ∘ under-root f₁) ∘ ι₂)
  side₂ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (pm-in₂ g (Lmap x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong (Biproduct.copair-in₂ (BP G₂ (L X₂)) _ _) ≈-refl)
    (≈-trans lift-part
    (≈-trans (∘-cong ≈-refl (≈-sym (Biproduct.copair-in₂ (BP G₁ (L X₁)) _ _)))
             (≈-sym (assoc _ _ _)))))))

under-root-pre : ∀ {G₁ G₂ X₁ X₂ Y} (g : G₁ ⇒ G₂)
                 {x : X₁ ⇒ X₂} {x' : X₂ ⇒ X₁} (xi₁ : (x ∘ x') ≈ id X₂) (xi₂ : (x' ∘ x) ≈ id X₁)
                 (r : (G₂ ⊕ X₂) ⇒ Y) →
                 (under-root r ∘ pm g (Lmap x)) ≈ under-root (r ∘ pm g x)
under-root-pre {G₁} {G₂} {X₁} {X₂} {Y} g {x} {x'} xi₁ xi₂ r =
  ≈-trans (under-root-natural g xi₁ xi₂ {y = id Y} {y' = id Y} id-left id-left
            (r ∘ pm g x) r (≈-sym id-left))
          (≈-trans (∘-cong Lmap-id ≈-refl) id-left)

-- Eliminating a root in context against a chosen constant: the context and the payload pass to the
-- continuation, and the root produces the constant.
strip-root : ∀ {G X Y} → (𝟙c ⇒ Y) → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ Y)
strip-root c r = cop (r ∘ ι₁) (affine c (r ∘ ι₂))

strip-root-cong : ∀ {G X Y} {c c' : 𝟙c ⇒ Y} {r r' : (G ⊕ X) ⇒ Y} →
                  c ≈ c' → r ≈ r' → strip-root c r ≈ strip-root c' r'
strip-root-cong ec er = cop-cong (∘-cong er ≈-refl) (affine-cong ec (∘-cong er ≈-refl))

-- Transport across the lifting is the elimination whose constant is the root itself.
under-root-strip : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) →
                   under-root r ≈ strip-root root (inj ∘ r)
under-root-strip r =
  cop-cong (≈-sym (assoc _ _ _)) (affine-cong ≈-refl (≈-sym (assoc _ _ _)))

-- Root elimination commutes with transports: the payload map must be an isomorphism, as for
-- under-root, but the result map is arbitrary provided it carries one constant to the other.
strip-root-natural :
  ∀ {G₁ G₂ X₁ X₂ Y₁ Y₂} (g : G₁ ⇒ G₂)
    {x : X₁ ⇒ X₂} {x' : X₂ ⇒ X₁} (xi₁ : (x ∘ x') ≈ id X₂) (xi₂ : (x' ∘ x) ≈ id X₁)
    {y : Y₁ ⇒ Y₂} {c₁ : 𝟙c ⇒ Y₁} {c₂ : 𝟙c ⇒ Y₂} → (y ∘ c₁) ≈ c₂ →
    (f₁ : (G₁ ⊕ X₁) ⇒ Y₁) (f₂ : (G₂ ⊕ X₂) ⇒ Y₂) →
    (f₂ ∘ pm g x) ≈ (y ∘ f₁) →
    (strip-root c₂ f₂ ∘ pm g (Lmap x)) ≈ (y ∘ strip-root c₁ f₁)
strip-root-natural {G₁} {G₂} {X₁} {X₂} {Y₁} {Y₂} g {x} {x'} xi₁ xi₂ {y} {c₁} {c₂} yc f₁ f₂ sq =
  bp-ext side₁ side₂
  where
  side₁ : ((strip-root c₂ f₂ ∘ pm g (Lmap x)) ∘ ι₁) ≈ ((y ∘ strip-root c₁ f₁) ∘ ι₁)
  side₁ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (pm-in₁ g (Lmap x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (Biproduct.copair-in₁ (BP G₂ (L X₂)) _ _))
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (≈-sym (pm-in₁ g x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ sq)
    (≈-trans (assoc _ _ _)
             (≈-sym (≈-trans (assoc _ _ _)
                             (∘-cong₂ (Biproduct.copair-in₁ (BP G₁ (L X₁)) _ _))))))))))))

  affine-side : (affine c₂ (f₂ ∘ ι₂) ∘ Lmap x) ≈ (y ∘ affine c₁ (f₁ ∘ ι₂))
  affine-side = lifting-ext _ _
    (≈-trans (assoc _ _ _)
     (≈-trans (∘-cong₂ (Lmap-root x))
      (≈-trans (affine-root _ _)
       (≈-sym (≈-trans (assoc _ _ _)
                       (≈-trans (∘-cong₂ (affine-root _ _)) yc))))))
    (≈-trans (assoc _ _ _)
     (≈-trans (∘-cong₂ (Lmap-inj xi₁ xi₂))
      (≈-trans (≈-sym (assoc _ _ _))
       (≈-trans (∘-cong₁ (affine-inj _ _))
        (≈-trans (comp-bilinear₁ _ _ _)
         (≈-trans (+m-cong
                    (≈-trans (assoc _ _ _) (∘-cong₂ (spt-natural xi₁ xi₂)))
                    (≈-trans (assoc _ _ _)
                     (≈-trans (∘-cong₂ (≈-sym (pm-in₂ g x)))
                      (≈-trans (≈-sym (assoc _ _ _))
                       (≈-trans (∘-cong₁ sq) (assoc _ _ _))))))
          (≈-sym
            (≈-trans (assoc _ _ _)
             (≈-trans (∘-cong₂ (affine-inj _ _))
              (≈-trans (comp-bilinear₂ _ _ _)
                       (+m-cong (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ yc))
                                ≈-refl)))))))))))

  side₂ : ((strip-root c₂ f₂ ∘ pm g (Lmap x)) ∘ ι₂) ≈ ((y ∘ strip-root c₁ f₁) ∘ ι₂)
  side₂ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (pm-in₂ g (Lmap x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (Biproduct.copair-in₂ (BP G₂ (L X₂)) _ _))
    (≈-trans affine-side
             (≈-sym (≈-trans (assoc _ _ _)
                             (∘-cong₂ (Biproduct.copair-in₂ (BP G₁ (L X₁)) _ _))))))))


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

  -- Full congruences, in the continuation as well, which the substitution lemma threads.
  varStep-cong₂ : ∀ (X : obj) {k k' : (W ⊕ R) ⇒ R} {g g' : (W ⊕ X) ⇒ R} →
                  k ≈ k' → g ≈ g' → varStep X k g ≈ varStep X k' g'
  varStep-cong₂ X ek eg = ∘-cong ek (pairb-cong ≈-refl eg)

  rootStep-cong₂ : ∀ (X F : obj) {k k' : (W ⊕ L X) ⇒ R} {r r' : (W ⊕ F) ⇒ R} →
                   k ≈ k' → r ≈ r' → rootStep X F k r ≈ rootStep X F k' r'
  rootStep-cong₂ X F ek er =
    cop-cong (∘-cong er ≈-refl)
             (affine-cong (∘-cong (∘-cong ek ≈-refl) ≈-refl) (∘-cong er ≈-refl))

  prodCont₁-cong : ∀ (X₁ X₂ : obj) {k k' : (W ⊕ (X₁ ⊕ X₂)) ⇒ R} →
                   k ≈ k' → prodCont₁ X₁ X₂ k ≈ prodCont₁ X₁ X₂ k'
  prodCont₁-cong X₁ X₂ ek =
    cop-cong (∘-cong ek ≈-refl) (∘-cong (∘-cong ek ≈-refl) ≈-refl)

  prodCont₂-cong : ∀ (X₁ X₂ : obj) {k k' : (W ⊕ (X₁ ⊕ X₂)) ⇒ R} →
                   k ≈ k' → prodCont₂ X₁ X₂ k ≈ prodCont₂ X₁ X₂ k'
  prodCont₂-cong X₁ X₂ ek = cop-cong ≈-refl (∘-cong (∘-cong ek ≈-refl) ≈-refl)

  rootCont-cong : ∀ (X : obj) {k k' : (W ⊕ L X) ⇒ R} →
                  k ≈ k' → rootCont X k ≈ rootCont X k'
  rootCont-cong X ek = cop-cong (∘-cong ek ≈-refl) (∘-cong (∘-cong ek ≈-refl) ≈-refl)

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

    -- The fold is congruent in its continuation.
    foldS-cong : ∀ {Q} (s : Shape B Q) {k k' : (W ⊕ ⟦ s ⟧) ⇒ R} →
                 k ≈ k' → foldS s k ≈ foldS s k'
    foldS-cong kon ek = ek
    foldS-cong (rec v) ek = varStep-cong₂ (fibV v) ek ≈-refl
    foldS-cong (prd s₁ s₂) ek =
      rootStep-cong₂ (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) (fibS s₁ ⊕ fibS s₂) ek
        (prodStep-cong (fibS s₁) (fibS s₂)
          (foldS-cong s₁ (prodCont₁-cong ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont-cong (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) ek)))
          (foldS-cong s₂ (prodCont₂-cong ⟦ s₁ ⟧ ⟦ s₂ ⟧ (rootCont-cong (⟦ s₁ ⟧ ⊕ ⟦ s₂ ⟧) ek))))
    foldS-cong (inl s) ek =
      rootStep-cong₂ ⟦ s ⟧ (fibS s) ek (foldS-cong s (rootCont-cong ⟦ s ⟧ ek))
    foldS-cong (inr s) ek =
      rootStep-cong₂ ⟦ s ⟧ (fibS s) ek (foldS-cong s (rootCont-cong ⟦ s ⟧ ek))

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

-- Substitution: changing the context commutes with the fold, the reindexed fold being the fold of
-- the reindexed algebra. The constant consumed at each root is the continuation's root column,
-- which a change of context does not touch.
module Reindex (W W' R : obj) (u : W' ⇒ W) where

  private
    ctx-map : ∀ (F : obj) → (W' ⊕ F) ⇒ (W ⊕ F)
    ctx-map F = pairb (u ∘ π₁) π₂

    bp-pair-ι₁ : ∀ {x y z} (f : x ⇒ y) → pairb f (εm {x} {z}) ≈ (ι₁ ∘ f)
    bp-pair-ι₁ f = ≈-trans (+m-cong ≈-refl (comp-bilinear-ε₂ ι₂)) +m-runit

    bp-pair-ι₂ : ∀ {x y z} (g : x ⇒ z) → pairb (εm {x} {y}) g ≈ (ι₂ ∘ g)
    bp-pair-ι₂ {x} {y} {z} g =
      ≈-trans (+m-cong (comp-bilinear-ε₂ ι₁) ≈-refl)
              (homCM _ _ .CommutativeMonoid.+-lunit)

    ctx-map-ι₁ : ∀ (F : obj) → (ctx-map F ∘ ι₁) ≈ (ι₁ ∘ u)
    ctx-map-ι₁ F =
      ≈-trans (Biproduct.pair-natural (BP W F) _ _ _)
      (≈-trans (pairb-cong
                 (≈-trans (assoc _ _ _)
                   (≈-trans (∘-cong ≈-refl (Biproduct.id-1 (BP W' F))) id-right))
                 (Biproduct.zero-2 (BP W' F)))
               (bp-pair-ι₁ u))

    ctx-map-ι₂ : ∀ (F : obj) → (ctx-map F ∘ ι₂) ≈ ι₂
    ctx-map-ι₂ F =
      ≈-trans (Biproduct.pair-natural (BP W F) _ _ _)
      (≈-trans (pairb-cong
                 (≈-trans (assoc _ _ _)
                   (≈-trans (∘-cong ≈-refl (Biproduct.zero-1 (BP W' F)))
                            (comp-bilinear-ε₂ u)))
                 (Biproduct.id-2 (BP W' F)))
               (≈-trans (bp-pair-ι₂ (id F)) id-right))

    push-ι₁ : ∀ (F : obj) {T} (f : (W ⊕ F) ⇒ T) → ((f ∘ ι₁) ∘ u) ≈ ((f ∘ ctx-map F) ∘ ι₁)
    push-ι₁ F f =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (≈-sym (ctx-map-ι₁ F))) (≈-sym (assoc _ _ _)))

    push-ι₂ : ∀ (F : obj) {T} (f : (W ⊕ F) ⇒ T) → (f ∘ ι₂) ≈ ((f ∘ ctx-map F) ∘ ι₂)
    push-ι₂ F f =
      ≈-trans (∘-cong ≈-refl (≈-sym (ctx-map-ι₂ F))) (≈-sym (assoc _ _ _))

    biproduct-ext : ∀ {x y z} {h k : (x ⊕ y) ⇒ z} →
                    (h ∘ ι₁) ≈ (k ∘ ι₁) → (h ∘ ι₂) ≈ (k ∘ ι₂) → h ≈ k
    biproduct-ext {x} {y} {z} {h} {k} e₁ e₂ =
      ≈-trans (≈-sym (Biproduct.copair-ext (BP x y) h))
      (≈-trans (cop-cong e₁ e₂) (Biproduct.copair-ext (BP x y) k))

    cop-ctx : ∀ {F T} (f : W ⇒ T) (g : F ⇒ T) → (cop f g ∘ ctx-map F) ≈ cop (f ∘ u) g
    cop-ctx {F} {T} f g =
      biproduct-ext
        (≈-trans (assoc _ _ _)
         (≈-trans (∘-cong ≈-refl (ctx-map-ι₁ F))
          (≈-trans (≈-sym (assoc _ _ _))
           (≈-trans (∘-cong (Biproduct.copair-in₁ (BP W F) f g) ≈-refl)
                    (≈-sym (Biproduct.copair-in₁ (BP W' F) (f ∘ u) g))))))
        (≈-trans (assoc _ _ _)
         (≈-trans (∘-cong ≈-refl (ctx-map-ι₂ F))
          (≈-trans (Biproduct.copair-in₂ (BP W F) f g)
                   (≈-sym (Biproduct.copair-in₂ (BP W' F) (f ∘ u) g)))))

    varStep-ctx : ∀ (X : obj) (k : (W ⊕ R) ⇒ R) (g : (W ⊕ X) ⇒ R) →
                  (varStep W R X k g ∘ ctx-map X)
                  ≈ varStep W' R X (k ∘ ctx-map R) (g ∘ ctx-map X)
    varStep-ctx X k g =
      ≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl inner) (≈-sym (assoc _ _ _)))
      where
      inner : (pairb π₁ g ∘ ctx-map X) ≈ (ctx-map R ∘ pairb π₁ (g ∘ ctx-map X))
      inner =
        ≈-trans (Biproduct.pair-natural (BP W R) _ _ _)
        (≈-trans (pairb-cong (Biproduct.pair-p₁ (BP W X) _ _) ≈-refl)
        (≈-sym (≈-trans (Biproduct.pair-natural (BP W R) _ _ _)
                (pairb-cong
                  (≈-trans (assoc _ _ _)
                           (∘-cong ≈-refl (Biproduct.pair-p₁ (BP W' R) _ _)))
                  (Biproduct.pair-p₂ (BP W' R) _ _)))))

    prodCont₁-ctx : ∀ (X₁ X₂ : obj) (k : (W ⊕ (X₁ ⊕ X₂)) ⇒ R) →
                    (prodCont₁ W R X₁ X₂ k ∘ ctx-map X₁)
                    ≈ prodCont₁ W' R X₁ X₂ (k ∘ ctx-map (X₁ ⊕ X₂))
    prodCont₁-ctx X₁ X₂ k =
      ≈-trans (cop-ctx _ _)
              (cop-cong (push-ι₁ (X₁ ⊕ X₂) k) (∘-cong (push-ι₂ (X₁ ⊕ X₂) k) ≈-refl))

    prodCont₂-ctx : ∀ (X₁ X₂ : obj) (k : (W ⊕ (X₁ ⊕ X₂)) ⇒ R) →
                    (prodCont₂ W R X₁ X₂ k ∘ ctx-map X₂)
                    ≈ prodCont₂ W' R X₁ X₂ (k ∘ ctx-map (X₁ ⊕ X₂))
    prodCont₂-ctx X₁ X₂ k =
      ≈-trans (cop-ctx _ _)
              (cop-cong (comp-bilinear-ε₁ u) (∘-cong (push-ι₂ (X₁ ⊕ X₂) k) ≈-refl))

    rootCont-ctx : ∀ (X : obj) (k : (W ⊕ L X) ⇒ R) →
                   (rootCont W R X k ∘ ctx-map X) ≈ rootCont W' R X (k ∘ ctx-map (L X))
    rootCont-ctx X k =
      ≈-trans (cop-ctx _ _)
              (cop-cong (push-ι₁ (L X) k) (∘-cong (push-ι₂ (L X) k) ≈-refl))

    prodStep-ctx : ∀ (F₁ F₂ : obj) (r₁ : (W ⊕ F₁) ⇒ R) (r₂ : (W ⊕ F₂) ⇒ R) →
                   (prodStep W R F₁ F₂ r₁ r₂ ∘ ctx-map (F₁ ⊕ F₂))
                   ≈ prodStep W' R F₁ F₂ (r₁ ∘ ctx-map F₁) (r₂ ∘ ctx-map F₂)
    prodStep-ctx F₁ F₂ r₁ r₂ =
      ≈-trans (cop-ctx _ _)
        (cop-cong (≈-trans (comp-bilinear₁ _ _ u)
                           (+m-cong (push-ι₁ F₁ r₁) (push-ι₁ F₂ r₂)))
                  (cop-cong (push-ι₂ F₁ r₁) (push-ι₂ F₂ r₂)))

    rootStep-ctx : ∀ (X F : obj) (k : (W ⊕ L X) ⇒ R) (r : (W ⊕ F) ⇒ R) →
                   (rootStep W R X F k r ∘ ctx-map (L F))
                   ≈ rootStep W' R X F (k ∘ ctx-map (L X)) (r ∘ ctx-map F)
    rootStep-ctx X F k r =
      ≈-trans (cop-ctx _ _)
        (cop-cong (push-ι₁ F r)
                  (affine-cong (∘-cong (push-ι₂ (L X) k) ≈-refl) (push-ι₂ F r)))

  module _ {B : Poly} (alg : (s : Shape B B) → (W ⊕ sh R s) ⇒ R) where

    alg-ctx : (s : Shape B B) → (W' ⊕ sh R s) ⇒ R
    alg-ctx s = alg s ∘ ctx-map (sh R s)

    mutual
      fold-ctx : ∀ (v : Val B) →
                 (fold W R alg v ∘ ctx-map (fibV v)) ≈ fold W' R alg-ctx v
      fold-ctx (sup s) = foldS-ctx s (alg s)

      foldS-ctx : ∀ {Q} (s : Shape B Q) (k : (W ⊕ sh R s) ⇒ R) →
                  (foldS W R alg s k ∘ ctx-map (fibS s))
                  ≈ foldS W' R alg-ctx s (k ∘ ctx-map (sh R s))
      foldS-ctx kon k = ≈-refl
      foldS-ctx (rec v) k =
        ≈-trans (varStep-ctx (fibV v) k (fold W R alg v))
                (varStep-cong₂ W' R (fibV v) ≈-refl (fold-ctx v))
      foldS-ctx (prd s₁ s₂) k =
        ≈-trans (rootStep-ctx (sh R s₁ ⊕ sh R s₂) (fibS s₁ ⊕ fibS s₂) k _)
        (rootStep-cong₂ W' R (sh R s₁ ⊕ sh R s₂) (fibS s₁ ⊕ fibS s₂) ≈-refl
          (≈-trans (prodStep-ctx (fibS s₁) (fibS s₂) _ _)
           (prodStep-cong W' R (fibS s₁) (fibS s₂)
             (≈-trans (foldS-ctx s₁ _)
              (foldS-cong W' R alg-ctx s₁
                (≈-trans (prodCont₁-ctx (sh R s₁) (sh R s₂) _)
                  (prodCont₁-cong W' R (sh R s₁) (sh R s₂)
                    (rootCont-ctx (sh R s₁ ⊕ sh R s₂) k)))))
             (≈-trans (foldS-ctx s₂ _)
              (foldS-cong W' R alg-ctx s₂
                (≈-trans (prodCont₂-ctx (sh R s₁) (sh R s₂) _)
                  (prodCont₂-cong W' R (sh R s₁) (sh R s₂)
                    (rootCont-ctx (sh R s₁ ⊕ sh R s₂) k))))))))
      foldS-ctx (inl s) k =
        ≈-trans (rootStep-ctx (sh R s) (fibS s) k _)
        (rootStep-cong₂ W' R (sh R s) (fibS s) ≈-refl
          (≈-trans (foldS-ctx s _)
                   (foldS-cong W' R alg-ctx s (rootCont-ctx (sh R s) k))))
      foldS-ctx (inr s) k =
        ≈-trans (rootStep-ctx (sh R s) (fibS s) k _)
        (rootStep-cong₂ W' R (sh R s) (fibS s) ≈-refl
          (≈-trans (foldS-ctx s _)
                   (foldS-cong W' R alg-ctx s (rootCont-ctx (sh R s) k))))

-- Single-application forms of the transport and elimination combinators: the inner morphism is
-- applied once, to the context recombined with the payload, instead of once per copairing arm.
-- The classic forms split the inner morphism linearly across the arms, so nesting them squares
-- the evaluation work per lifting layer; these are equal as morphisms but evaluate the
-- continuation once per node.
payloadL : ∀ {X} → L X ⇒ X
payloadL {X} = affine εm (id X)

tagL : ∀ {X} → L X ⇒ 𝟙c
tagL {X} = affine (id 𝟙c) εm

payloadL-root : ∀ {X} → (payloadL {X} ∘ root) ≈ εm
payloadL-root {X} = affine-root εm (id X)

payloadL-inj : ∀ {X} → (payloadL {X} ∘ inj) ≈ id X
payloadL-inj {X} =
  ≈-trans (affine-inj εm (id X))
  (≈-trans (+m-cong (comp-bilinear-ε₁ spt) ≈-refl)
           (homCM _ _ .CommutativeMonoid.+-lunit))

tagL-root : ∀ {X} → (tagL {X} ∘ root) ≈ id 𝟙c
tagL-root {X} = affine-root (id 𝟙c) εm

tagL-inj : ∀ {X} → (tagL {X} ∘ inj) ≈ spt
tagL-inj {X} =
  ≈-trans (affine-inj (id 𝟙c) εm) (≈-trans (+m-cong id-left ≈-refl) +m-runit)

under-root-alt : ∀ {G X Y} → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ L Y)
under-root-alt {G} r = (inj ∘ (r ∘ pm (id G) payloadL)) +m ((root ∘ tagL) ∘ π₂)

strip-root-alt : ∀ {G X Y} → (𝟙c ⇒ Y) → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ Y)
strip-root-alt {G} c r = (r ∘ pm (id G) payloadL) +m ((c ∘ tagL) ∘ π₂)

private
  pm-arm-ι₁ : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) → ((r ∘ pm (id G) payloadL) ∘ ι₁) ≈ (r ∘ ι₁)
  pm-arm-ι₁ {G} r =
    ≈-trans (assoc _ _ _) (∘-cong ≈-refl (≈-trans (pm-in₁ (id G) payloadL) id-right))

  pm-arm-ι₂ : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) →
              ((r ∘ pm (id G) payloadL) ∘ ι₂) ≈ (r ∘ (ι₂ ∘ payloadL))
  pm-arm-ι₂ {G} r = ≈-trans (assoc _ _ _) (∘-cong ≈-refl (pm-in₂ (id G) payloadL))

  tag-arm-ι₁ : ∀ {G X Y} (c : 𝟙c ⇒ Y) → (((c ∘ tagL {X}) ∘ π₂) ∘ ι₁ {G}) ≈ εm
  tag-arm-ι₁ {G} {X} c =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (Biproduct.zero-2 (BP G (L X)))) (comp-bilinear-ε₂ _))

  tag-arm-ι₂ : ∀ {G X Y} (c : 𝟙c ⇒ Y) → (((c ∘ tagL {X}) ∘ π₂) ∘ ι₂ {G}) ≈ (c ∘ tagL)
  tag-arm-ι₂ {G} {X} c =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (Biproduct.id-2 (BP G (L X)))) id-right)

  -- The recombined arm restricted along root and inj.
  payload-comp-root : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) → ((r ∘ (ι₂ ∘ payloadL)) ∘ root) ≈ εm
  payload-comp-root r =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl payloadL-root) (comp-bilinear-ε₂ ι₂))))
             (comp-bilinear-ε₂ r))

  payload-comp-inj : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) → ((r ∘ (ι₂ ∘ payloadL)) ∘ inj) ≈ (r ∘ ι₂)
  payload-comp-inj r =
    ≈-trans (assoc _ _ _)
    (∘-cong ≈-refl (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl payloadL-inj) id-right)))

-- The bridges: each single-application form equals its classic counterpart, so every law about
-- the classic combinators transfers by congruence.
under-root-alt-≈ : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) → under-root-alt r ≈ under-root r
under-root-alt-≈ {G} {X} {Y} r = bp-ext leg₁ leg₂
  where
  M = inj ∘ (r ∘ ι₂)

  leg₁ : (under-root-alt r ∘ ι₁) ≈ (under-root r ∘ ι₁)
  leg₁ =
    ≈-trans (comp-bilinear₁ _ _ ι₁)
    (≈-trans (+m-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (pm-arm-ι₁ r)))
                      (tag-arm-ι₁ root))
    (≈-trans +m-runit
             (≈-sym (Biproduct.copair-in₁ (BP G (L X)) (inj ∘ (r ∘ ι₁)) (affine root M)))))

  E : L X ⇒ L Y
  E = (inj ∘ (r ∘ (ι₂ ∘ payloadL))) +m (root ∘ tagL)

  E-root : (E ∘ root) ≈ (affine root M ∘ root)
  E-root =
    ≈-trans (comp-bilinear₁ _ _ root)
    (≈-trans (+m-cong (≈-trans (assoc _ _ _)
                        (≈-trans (∘-cong ≈-refl (payload-comp-root r)) (comp-bilinear-ε₂ inj)))
                      (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl tagL-root) id-right)))
    (≈-trans (homCM _ _ .CommutativeMonoid.+-lunit)
             (≈-sym (affine-root root M))))

  E-inj : (E ∘ inj) ≈ (affine root M ∘ inj)
  E-inj =
    ≈-trans (comp-bilinear₁ _ _ inj)
    (≈-trans (+m-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (payload-comp-inj r)))
                      (≈-trans (assoc _ _ _) (∘-cong ≈-refl tagL-inj)))
    (≈-trans (homCM _ _ .CommutativeMonoid.+-comm)
             (≈-sym (affine-inj root M))))

  leg₂ : (under-root-alt r ∘ ι₂) ≈ (under-root r ∘ ι₂)
  leg₂ =
    ≈-trans (comp-bilinear₁ _ _ ι₂)
    (≈-trans (+m-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (pm-arm-ι₂ r)))
                      (tag-arm-ι₂ root))
    (≈-trans (lifting-ext E (affine root M) E-root E-inj)
             (≈-sym (Biproduct.copair-in₂ (BP G (L X)) (inj ∘ (r ∘ ι₁)) (affine root M)))))

strip-root-alt-≈ : ∀ {G X Y} (c : 𝟙c ⇒ Y) (r : (G ⊕ X) ⇒ Y) →
                   strip-root-alt c r ≈ strip-root c r
strip-root-alt-≈ {G} {X} {Y} c r = bp-ext leg₁ leg₂
  where
  M = r ∘ ι₂

  leg₁ : (strip-root-alt c r ∘ ι₁) ≈ (strip-root c r ∘ ι₁)
  leg₁ =
    ≈-trans (comp-bilinear₁ _ _ ι₁)
    (≈-trans (+m-cong (pm-arm-ι₁ r) (tag-arm-ι₁ c))
    (≈-trans +m-runit
             (≈-sym (Biproduct.copair-in₁ (BP G (L X)) (r ∘ ι₁) (affine c M)))))

  E : L X ⇒ Y
  E = (r ∘ (ι₂ ∘ payloadL)) +m (c ∘ tagL)

  E-root : (E ∘ root) ≈ (affine c M ∘ root)
  E-root =
    ≈-trans (comp-bilinear₁ _ _ root)
    (≈-trans (+m-cong (payload-comp-root r)
                      (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl tagL-root) id-right)))
    (≈-trans (homCM _ _ .CommutativeMonoid.+-lunit)
             (≈-sym (affine-root c M))))

  E-inj : (E ∘ inj) ≈ (affine c M ∘ inj)
  E-inj =
    ≈-trans (comp-bilinear₁ _ _ inj)
    (≈-trans (+m-cong (payload-comp-inj r)
                      (≈-trans (assoc _ _ _) (∘-cong ≈-refl tagL-inj)))
    (≈-trans (homCM _ _ .CommutativeMonoid.+-comm)
             (≈-sym (affine-inj c M))))

  leg₂ : (strip-root-alt c r ∘ ι₂) ≈ (strip-root c r ∘ ι₂)
  leg₂ =
    ≈-trans (comp-bilinear₁ _ _ ι₂)
    (≈-trans (+m-cong (pm-arm-ι₂ r) (tag-arm-ι₂ c))
    (≈-trans (lifting-ext E (affine c M) E-root E-inj)
             (≈-sym (Biproduct.copair-in₂ (BP G (L X)) (r ∘ ι₁) (affine c M)))))
