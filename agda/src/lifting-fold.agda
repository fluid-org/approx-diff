{-# OPTIONS --prop --postfix-projections --safe #-}

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

_⊕_ : obj → obj → obj
x ⊕ y = Biproduct.prod (BP x y)

copair : ∀ {x y z} → x ⇒ z → y ⇒ z → (x ⊕ y) ⇒ z
copair {x} {y} f g = Biproduct.copair (BP x y) f g

copair-cong : ∀ {x y z} {f f' : x ⇒ z} {g g' : y ⇒ z} → f ≈ f' → g ≈ g' → copair f g ≈ copair f' g'
copair-cong {x} {y} = Biproduct.copair-cong (BP x y)

pair : ∀ {x y z} → x ⇒ y → x ⇒ z → x ⇒ (y ⊕ z)
pair {x} {y} {z} f g = Biproduct.pair (BP y z) f g

pair-cong : ∀ {x y z} {f f' : x ⇒ y} {g g' : x ⇒ z} → f ≈ f' → g ≈ g' → pair f g ≈ pair f' g'
pair-cong {x} {y} {z} = Biproduct.pair-cong (BP y z)

p₁ : ∀ {x y} → (x ⊕ y) ⇒ x
p₁ {x} {y} = Biproduct.p₁ (BP x y)

p₂ : ∀ {x y} → (x ⊕ y) ⇒ y
p₂ {x} {y} = Biproduct.p₂ (BP x y)

in₁ : ∀ {x y} → x ⇒ (x ⊕ y)
in₁ {x} {y} = Biproduct.in₁ (BP x y)

in₂ : ∀ {x y} → y ⇒ (x ⊕ y)
in₂ {x} {y} = Biproduct.in₂ (BP x y)

+m-cong : ∀ {x y} {f f' g g' : x ⇒ y} → f ≈ f' → g ≈ g' → (f +m g) ≈ (f' +m g')
+m-cong = homCM _ _ .CommutativeMonoid.+-cong

prod-m : ∀ {a₁ a₂ b₁ b₂} → a₁ ⇒ a₂ → b₁ ⇒ b₂ → (a₁ ⊕ b₁) ⇒ (a₂ ⊕ b₂)
prod-m g h = pair (g ∘ p₁) (h ∘ p₂)

prod-m-in₁ : ∀ {a₁ a₂ b₁ b₂} (g : a₁ ⇒ a₂) (h : b₁ ⇒ b₂) → (prod-m g h ∘ in₁) ≈ (in₁ ∘ g)
prod-m-in₁ {a₁} {a₂} {b₁} {b₂} g h =
  ≈-trans (Biproduct.pair-natural (BP a₂ b₂) _ _ _)
  (≈-trans (pair-cong
             (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl (Biproduct.id-1 (BP a₁ b₁))) id-right))
             (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl (Biproduct.zero-2 (BP a₁ b₁))) (comp-bilinear-ε₂ h))))
           (≈-trans (+m-cong ≈-refl (comp-bilinear-ε₂ in₂)) +m-runit))

prod-m-in₂ : ∀ {a₁ a₂ b₁ b₂} (g : a₁ ⇒ a₂) (h : b₁ ⇒ b₂) → (prod-m g h ∘ in₂) ≈ (in₂ ∘ h)
prod-m-in₂ {a₁} {a₂} {b₁} {b₂} g h =
  ≈-trans (Biproduct.pair-natural (BP a₂ b₂) _ _ _)
  (≈-trans (pair-cong
             (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl (Biproduct.zero-1 (BP a₁ b₁))) (comp-bilinear-ε₂ g)))
             (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl (Biproduct.id-2 (BP a₁ b₁))) id-right)))
           (≈-trans (+m-cong (comp-bilinear-ε₂ in₁) ≈-refl)
                    (homCM _ _ .CommutativeMonoid.+-lunit)))

bp-ext : ∀ {a b c} {h k : (a ⊕ b) ⇒ c} → (h ∘ in₁) ≈ (k ∘ in₁) → (h ∘ in₂) ≈ (k ∘ in₂) → h ≈ k
bp-ext {a} {b} {c} {h} {k} e₁ e₂ =
  ≈-trans (≈-sym (Biproduct.copair-ext (BP a b) h))
  (≈-trans (copair-cong e₁ e₂) (Biproduct.copair-ext (BP a b) k))

-- Reindexing a context-paired morphism under a root: the root passes through, the context enters
-- the payload, and absorption records under the target root whatever the context contributes.
under-root-split : ∀ {G X Y} → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ L Y)
under-root-split r = copair (inj ∘ (r ∘ in₁)) (affine root (inj ∘ (r ∘ in₂)))

under-root-split-cong : ∀ {G X Y} {r r' : (G ⊕ X) ⇒ Y} → r ≈ r' → under-root-split r ≈ under-root-split r'
under-root-split-cong er =
  copair-cong (∘-cong ≈-refl (∘-cong er ≈-refl))
           (affine-cong ≈-refl (∘-cong ≈-refl (∘-cong er ≈-refl)))

-- Transport across the lifting fuses with composition on either side: with an isomorphism after,
-- through the action, and with a context-paired map before.
under-root-split-post : ∀ {G X Y₁ Y₂} {h : Y₁ ⇒ Y₂} {h' : Y₂ ⇒ Y₁} →
                  (h ∘ h') ≈ id Y₂ → (h' ∘ h) ≈ id Y₁ →
                  (r : (G ⊕ X) ⇒ Y₁) → (Lmap h ∘ under-root-split r) ≈ under-root-split (h ∘ r)
under-root-split-post {G} {X} {Y₁} {Y₂} {h} {h'} hi₁ hi₂ r =
  bp-ext {h = Lmap h ∘ under-root-split r} {k = under-root-split (h ∘ r)}
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
  part₂ : (Lmap h ∘ affine root (inj ∘ (r ∘ in₂))) ≈ affine root (inj ∘ ((h ∘ r) ∘ in₂))
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
under-root-split-p₂ : ∀ {G X} → under-root-split (p₂ {G} {X}) ≈ p₂ {G} {L X}
under-root-split-p₂ {G} {X} =
  ≈-trans (copair-cong
            (≈-trans (∘-cong ≈-refl (Biproduct.zero-2 (BP G X))) (comp-bilinear-ε₂ inj))
            (≈-trans (affine-cong ≈-refl
                       (≈-trans (∘-cong ≈-refl (Biproduct.id-2 (BP G X))) id-right))
             (≈-trans (affine-cong (≈-sym id-left) (≈-sym id-left)) (affine-η (id (L X))))))
  (≈-trans (+m-cong (comp-bilinear-ε₁ p₁) id-left)
           (homCM _ _ .CommutativeMonoid.+-lunit))

-- Reindexing under a root commutes with transports along isomorphisms, which is what naturality of
-- the fold and of reindexing in the tree demands. The context map is arbitrary; the payload and
-- result maps must be isomorphisms, since the injection and the support are natural only there.
under-root-split-natural :
  ∀ {G₁ G₂ X₁ X₂ Y₁ Y₂} (g : G₁ ⇒ G₂)
    {x : X₁ ⇒ X₂} {x' : X₂ ⇒ X₁} (xi₁ : (x ∘ x') ≈ id X₂) (xi₂ : (x' ∘ x) ≈ id X₁)
    {y : Y₁ ⇒ Y₂} {y' : Y₂ ⇒ Y₁} (yi₁ : (y ∘ y') ≈ id Y₂) (yi₂ : (y' ∘ y) ≈ id Y₁)
    (f₁ : (G₁ ⊕ X₁) ⇒ Y₁) (f₂ : (G₂ ⊕ X₂) ⇒ Y₂) →
    (f₂ ∘ prod-m g x) ≈ (y ∘ f₁) →
    (under-root-split f₂ ∘ prod-m g (Lmap x)) ≈ (Lmap y ∘ under-root-split f₁)
under-root-split-natural {G₁} {G₂} {X₁} {X₂} {Y₁} {Y₂} g {x} {x'} xi₁ xi₂ {y} {y'} yi₁ yi₂ f₁ f₂ sq =
  bp-ext side₁ side₂
  where
  square-in₁ : ((f₂ ∘ in₁) ∘ g) ≈ (y ∘ (f₁ ∘ in₁))
  square-in₁ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-sym (prod-m-in₁ g x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong sq ≈-refl) (assoc _ _ _))))

  square-in₂ : ((f₂ ∘ in₂) ∘ x) ≈ (y ∘ (f₁ ∘ in₂))
  square-in₂ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-sym (prod-m-in₂ g x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong sq ≈-refl) (assoc _ _ _))))

  side₁ : ((under-root-split f₂ ∘ prod-m g (Lmap x)) ∘ in₁) ≈ ((Lmap y ∘ under-root-split f₁) ∘ in₁)
  side₁ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (prod-m-in₁ g (Lmap x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong (Biproduct.copair-in₁ (BP G₂ (L X₂)) _ _) ≈-refl)
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl square-in₁)
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong (≈-sym (Lmap-inj yi₁ yi₂)) ≈-refl)
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-sym (Biproduct.copair-in₁ (BP G₁ (L X₁)) _ _)))
             (≈-sym (assoc _ _ _)))))))))))

  lift-part : (affine root (inj ∘ (f₂ ∘ in₂)) ∘ Lmap x) ≈ (Lmap y ∘ affine root (inj ∘ (f₁ ∘ in₂)))
  lift-part = lifting-ext _ _ root-side inj-side
    where
    root-side : ((affine root (inj ∘ (f₂ ∘ in₂)) ∘ Lmap x) ∘ root)
                ≈ ((Lmap y ∘ affine root (inj ∘ (f₁ ∘ in₂))) ∘ root)
    root-side =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (Lmap-root x))
      (≈-trans (affine-root _ _)
      (≈-sym
        (≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (affine-root _ _)) (Lmap-root y))))))

    left-inj : ((affine root (inj ∘ (f₂ ∘ in₂)) ∘ Lmap x) ∘ inj)
               ≈ ((root ∘ spt) +m (Lmap y ∘ (inj ∘ (f₁ ∘ in₂))))
    left-inj =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (Lmap-inj xi₁ xi₂))
      (≈-trans (≈-sym (assoc _ _ _))
      (≈-trans (∘-cong (affine-inj _ _) ≈-refl)
      (≈-trans (comp-bilinear₁ _ _ _)
        (+m-cong
          (≈-trans (assoc _ _ _) (∘-cong ≈-refl (spt-natural xi₁ xi₂)))
          (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl square-in₂)
          (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong (≈-sym (Lmap-inj yi₁ yi₂)) ≈-refl) (assoc _ _ _))))))))))

    right-inj : ((Lmap y ∘ affine root (inj ∘ (f₁ ∘ in₂))) ∘ inj)
                ≈ ((root ∘ spt) +m (Lmap y ∘ (inj ∘ (f₁ ∘ in₂))))
    right-inj =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (affine-inj _ _))
      (≈-trans (comp-bilinear₂ _ _ _)
        (+m-cong (≈-trans (≈-sym (assoc _ _ _)) (∘-cong (Lmap-root y) ≈-refl)) ≈-refl)))

    inj-side : ((affine root (inj ∘ (f₂ ∘ in₂)) ∘ Lmap x) ∘ inj)
               ≈ ((Lmap y ∘ affine root (inj ∘ (f₁ ∘ in₂))) ∘ inj)
    inj-side = ≈-trans left-inj (≈-sym right-inj)

  side₂ : ((under-root-split f₂ ∘ prod-m g (Lmap x)) ∘ in₂) ≈ ((Lmap y ∘ under-root-split f₁) ∘ in₂)
  side₂ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (prod-m-in₂ g (Lmap x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong (Biproduct.copair-in₂ (BP G₂ (L X₂)) _ _) ≈-refl)
    (≈-trans lift-part
    (≈-trans (∘-cong ≈-refl (≈-sym (Biproduct.copair-in₂ (BP G₁ (L X₁)) _ _)))
             (≈-sym (assoc _ _ _)))))))

under-root-split-pre : ∀ {G₁ G₂ X₁ X₂ Y} (g : G₁ ⇒ G₂)
                 {x : X₁ ⇒ X₂} {x' : X₂ ⇒ X₁} (xi₁ : (x ∘ x') ≈ id X₂) (xi₂ : (x' ∘ x) ≈ id X₁)
                 (r : (G₂ ⊕ X₂) ⇒ Y) →
                 (under-root-split r ∘ prod-m g (Lmap x)) ≈ under-root-split (r ∘ prod-m g x)
under-root-split-pre {G₁} {G₂} {X₁} {X₂} {Y} g {x} {x'} xi₁ xi₂ r =
  ≈-trans (under-root-split-natural g xi₁ xi₂ {y = id Y} {y' = id Y} id-left id-left
            (r ∘ prod-m g x) r (≈-sym id-left))
          (≈-trans (∘-cong Lmap-id ≈-refl) id-left)

-- Eliminating a root in context against a chosen constant: the context and the payload pass to the
-- continuation, and the root produces the constant.
strip-root-split : ∀ {G X Y} → (𝟙c ⇒ Y) → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ Y)
strip-root-split c r = copair (r ∘ in₁) (affine c (r ∘ in₂))

strip-root-split-cong : ∀ {G X Y} {c c' : 𝟙c ⇒ Y} {r r' : (G ⊕ X) ⇒ Y} →
                  c ≈ c' → r ≈ r' → strip-root-split c r ≈ strip-root-split c' r'
strip-root-split-cong ec er = copair-cong (∘-cong er ≈-refl) (affine-cong ec (∘-cong er ≈-refl))

-- Transport across the lifting is the elimination whose constant is the root itself.
under-root-split-strip : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) →
                   under-root-split r ≈ strip-root-split root (inj ∘ r)
under-root-split-strip r =
  copair-cong (≈-sym (assoc _ _ _)) (affine-cong ≈-refl (≈-sym (assoc _ _ _)))

-- Root elimination commutes with transports; the payload map must be an isomorphism, since the
-- injection is natural only there.
strip-root-split-natural :
  ∀ {G₁ G₂ X₁ X₂ Y₁ Y₂} (g : G₁ ⇒ G₂)
    {x : X₁ ⇒ X₂} {x' : X₂ ⇒ X₁} (xi₁ : (x ∘ x') ≈ id X₂) (xi₂ : (x' ∘ x) ≈ id X₁)
    {y : Y₁ ⇒ Y₂} {c₁ : 𝟙c ⇒ Y₁} {c₂ : 𝟙c ⇒ Y₂} → (y ∘ c₁) ≈ c₂ →
    (f₁ : (G₁ ⊕ X₁) ⇒ Y₁) (f₂ : (G₂ ⊕ X₂) ⇒ Y₂) →
    (f₂ ∘ prod-m g x) ≈ (y ∘ f₁) →
    (strip-root-split c₂ f₂ ∘ prod-m g (Lmap x)) ≈ (y ∘ strip-root-split c₁ f₁)
strip-root-split-natural {G₁} {G₂} {X₁} {X₂} {Y₁} {Y₂} g {x} {x'} xi₁ xi₂ {y} {c₁} {c₂} yc f₁ f₂ sq =
  bp-ext side₁ side₂
  where
  side₁ : ((strip-root-split c₂ f₂ ∘ prod-m g (Lmap x)) ∘ in₁) ≈ ((y ∘ strip-root-split c₁ f₁) ∘ in₁)
  side₁ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (prod-m-in₁ g (Lmap x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (Biproduct.copair-in₁ (BP G₂ (L X₂)) _ _))
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (≈-sym (prod-m-in₁ g x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ sq)
    (≈-trans (assoc _ _ _)
             (≈-sym (≈-trans (assoc _ _ _)
                             (∘-cong₂ (Biproduct.copair-in₁ (BP G₁ (L X₁)) _ _))))))))))))

  affine-side : (affine c₂ (f₂ ∘ in₂) ∘ Lmap x) ≈ (y ∘ affine c₁ (f₁ ∘ in₂))
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
                     (≈-trans (∘-cong₂ (≈-sym (prod-m-in₂ g x)))
                      (≈-trans (≈-sym (assoc _ _ _))
                       (≈-trans (∘-cong₁ sq) (assoc _ _ _))))))
          (≈-sym
            (≈-trans (assoc _ _ _)
             (≈-trans (∘-cong₂ (affine-inj _ _))
              (≈-trans (comp-bilinear₂ _ _ _)
                       (+m-cong (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ yc))
                                ≈-refl)))))))))))

  side₂ : ((strip-root-split c₂ f₂ ∘ prod-m g (Lmap x)) ∘ in₂) ≈ ((y ∘ strip-root-split c₁ f₁) ∘ in₂)
  side₂ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (prod-m-in₂ g (Lmap x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (Biproduct.copair-in₂ (BP G₂ (L X₂)) _ _))
    (≈-trans affine-side
             (≈-sym (≈-trans (assoc _ _ _)
                             (∘-cong₂ (Biproduct.copair-in₂ (BP G₁ (L X₁)) _ _))))))))


-- Single-application forms as the public combinators: the inner morphism is applied once, to the
-- context recombined with the extracted payload. The split forms apply it once per copairing arm,
-- so nesting them multiplies evaluations of the continuation per lifting layer. Each public lemma
-- is the split-form law transported across the unfolding bridge.
payload-L : ∀ {X} → L X ⇒ X
payload-L {X} = affine εm (id X)

tag-L : ∀ {X} → L X ⇒ 𝟙c
tag-L {X} = affine (id 𝟙c) εm

payload-L-root : ∀ {X} → (payload-L {X} ∘ root) ≈ εm
payload-L-root {X} = affine-root εm (id X)

payload-L-inj : ∀ {X} → (payload-L {X} ∘ inj) ≈ id X
payload-L-inj {X} =
  ≈-trans (affine-inj εm (id X))
  (≈-trans (+m-cong (comp-bilinear-ε₁ spt) ≈-refl)
           (homCM _ _ .CommutativeMonoid.+-lunit))

tag-L-root : ∀ {X} → (tag-L {X} ∘ root) ≈ id 𝟙c
tag-L-root {X} = affine-root (id 𝟙c) εm

tag-L-inj : ∀ {X} → (tag-L {X} ∘ inj) ≈ spt
tag-L-inj {X} =
  ≈-trans (affine-inj (id 𝟙c) εm) (≈-trans (+m-cong id-left ≈-refl) +m-runit)

-- Evaluation-critical shape: exactly one application of r per element.
under-root : ∀ {G X Y} → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ L Y)
under-root {G} r = (inj ∘ (r ∘ prod-m (id G) payload-L)) +m ((root ∘ tag-L) ∘ p₂)

-- Evaluation-critical shape: exactly one application of r per element.
strip-root : ∀ {G X Y} → (𝟙c ⇒ Y) → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ Y)
strip-root {G} c r = (r ∘ prod-m (id G) payload-L) +m ((c ∘ tag-L) ∘ p₂)

private
  prod-m-arm-in₁ : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) → ((r ∘ prod-m (id G) payload-L) ∘ in₁) ≈ (r ∘ in₁)
  prod-m-arm-in₁ {G} r =
    ≈-trans (assoc _ _ _) (∘-cong ≈-refl (≈-trans (prod-m-in₁ (id G) payload-L) id-right))

  prod-m-arm-in₂ : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) →
              ((r ∘ prod-m (id G) payload-L) ∘ in₂) ≈ (r ∘ (in₂ ∘ payload-L))
  prod-m-arm-in₂ {G} r = ≈-trans (assoc _ _ _) (∘-cong ≈-refl (prod-m-in₂ (id G) payload-L))

  tag-arm-in₁ : ∀ {G X Y} (c : 𝟙c ⇒ Y) → (((c ∘ tag-L {X}) ∘ p₂) ∘ in₁ {G}) ≈ εm
  tag-arm-in₁ {G} {X} c =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (Biproduct.zero-2 (BP G (L X)))) (comp-bilinear-ε₂ _))

  tag-arm-in₂ : ∀ {G X Y} (c : 𝟙c ⇒ Y) → (((c ∘ tag-L {X}) ∘ p₂) ∘ in₂ {G}) ≈ (c ∘ tag-L)
  tag-arm-in₂ {G} {X} c =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (Biproduct.id-2 (BP G (L X)))) id-right)

  payload-comp-root : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) → ((r ∘ (in₂ ∘ payload-L)) ∘ root) ≈ εm
  payload-comp-root r =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl payload-L-root) (comp-bilinear-ε₂ in₂))))
             (comp-bilinear-ε₂ r))

  payload-comp-inj : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) → ((r ∘ (in₂ ∘ payload-L)) ∘ inj) ≈ (r ∘ in₂)
  payload-comp-inj r =
    ≈-trans (assoc _ _ _)
    (∘-cong ≈-refl (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl payload-L-inj) id-right)))

under-root-unfold : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) → under-root r ≈ under-root-split r
under-root-unfold {G} {X} {Y} r = bp-ext leg₁ leg₂
  where
  M = inj ∘ (r ∘ in₂)

  leg₁ : (under-root r ∘ in₁) ≈ (under-root-split r ∘ in₁)
  leg₁ =
    ≈-trans (comp-bilinear₁ _ _ in₁)
    (≈-trans (+m-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (prod-m-arm-in₁ r)))
                      (tag-arm-in₁ root))
    (≈-trans +m-runit
             (≈-sym (Biproduct.copair-in₁ (BP G (L X)) (inj ∘ (r ∘ in₁)) (affine root M)))))

  E : L X ⇒ L Y
  E = (inj ∘ (r ∘ (in₂ ∘ payload-L))) +m (root ∘ tag-L)

  E-root : (E ∘ root) ≈ (affine root M ∘ root)
  E-root =
    ≈-trans (comp-bilinear₁ _ _ root)
    (≈-trans (+m-cong (≈-trans (assoc _ _ _)
                        (≈-trans (∘-cong ≈-refl (payload-comp-root r)) (comp-bilinear-ε₂ inj)))
                      (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl tag-L-root) id-right)))
    (≈-trans (homCM _ _ .CommutativeMonoid.+-lunit)
             (≈-sym (affine-root root M))))

  E-inj : (E ∘ inj) ≈ (affine root M ∘ inj)
  E-inj =
    ≈-trans (comp-bilinear₁ _ _ inj)
    (≈-trans (+m-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (payload-comp-inj r)))
                      (≈-trans (assoc _ _ _) (∘-cong ≈-refl tag-L-inj)))
    (≈-trans (homCM _ _ .CommutativeMonoid.+-comm)
             (≈-sym (affine-inj root M))))

  leg₂ : (under-root r ∘ in₂) ≈ (under-root-split r ∘ in₂)
  leg₂ =
    ≈-trans (comp-bilinear₁ _ _ in₂)
    (≈-trans (+m-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (prod-m-arm-in₂ r)))
                      (tag-arm-in₂ root))
    (≈-trans (lifting-ext E (affine root M) E-root E-inj)
             (≈-sym (Biproduct.copair-in₂ (BP G (L X)) (inj ∘ (r ∘ in₁)) (affine root M)))))

strip-root-unfold : ∀ {G X Y} (c : 𝟙c ⇒ Y) (r : (G ⊕ X) ⇒ Y) →
                    strip-root c r ≈ strip-root-split c r
strip-root-unfold {G} {X} {Y} c r = bp-ext leg₁ leg₂
  where
  M = r ∘ in₂

  leg₁ : (strip-root c r ∘ in₁) ≈ (strip-root-split c r ∘ in₁)
  leg₁ =
    ≈-trans (comp-bilinear₁ _ _ in₁)
    (≈-trans (+m-cong (prod-m-arm-in₁ r) (tag-arm-in₁ c))
    (≈-trans +m-runit
             (≈-sym (Biproduct.copair-in₁ (BP G (L X)) (r ∘ in₁) (affine c M)))))

  E : L X ⇒ Y
  E = (r ∘ (in₂ ∘ payload-L)) +m (c ∘ tag-L)

  E-root : (E ∘ root) ≈ (affine c M ∘ root)
  E-root =
    ≈-trans (comp-bilinear₁ _ _ root)
    (≈-trans (+m-cong (payload-comp-root r)
                      (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl tag-L-root) id-right)))
    (≈-trans (homCM _ _ .CommutativeMonoid.+-lunit)
             (≈-sym (affine-root c M))))

  E-inj : (E ∘ inj) ≈ (affine c M ∘ inj)
  E-inj =
    ≈-trans (comp-bilinear₁ _ _ inj)
    (≈-trans (+m-cong (payload-comp-inj r)
                      (≈-trans (assoc _ _ _) (∘-cong ≈-refl tag-L-inj)))
    (≈-trans (homCM _ _ .CommutativeMonoid.+-comm)
             (≈-sym (affine-inj c M))))

  leg₂ : (strip-root c r ∘ in₂) ≈ (strip-root-split c r ∘ in₂)
  leg₂ =
    ≈-trans (comp-bilinear₁ _ _ in₂)
    (≈-trans (+m-cong (prod-m-arm-in₂ r) (tag-arm-in₂ c))
    (≈-trans (lifting-ext E (affine c M) E-root E-inj)
             (≈-sym (Biproduct.copair-in₂ (BP G (L X)) (r ∘ in₁) (affine c M)))))

under-root-cong : ∀ {G X Y} {r r' : (G ⊕ X) ⇒ Y} → r ≈ r' → under-root r ≈ under-root r'
under-root-cong {r = r} {r'} er =
  ≈-trans (under-root-unfold r)
  (≈-trans (under-root-split-cong er) (≈-sym (under-root-unfold r')))

under-root-post : ∀ {G X Y₁ Y₂} {h : Y₁ ⇒ Y₂} {h' : Y₂ ⇒ Y₁} →
                  (h ∘ h') ≈ id Y₂ → (h' ∘ h) ≈ id Y₁ →
                  (r : (G ⊕ X) ⇒ Y₁) → (Lmap h ∘ under-root r) ≈ under-root (h ∘ r)
under-root-post {h = h} hi₁ hi₂ r =
  ≈-trans (∘-cong ≈-refl (under-root-unfold r))
  (≈-trans (under-root-split-post hi₁ hi₂ r) (≈-sym (under-root-unfold (h ∘ r))))

under-root-p₂ : ∀ {G X} → under-root (p₂ {G} {X}) ≈ p₂ {G} {L X}
under-root-p₂ {G} {X} =
  ≈-trans (under-root-unfold (p₂ {G} {X})) under-root-split-p₂

under-root-natural :
  ∀ {G₁ G₂ X₁ X₂ Y₁ Y₂} (g : G₁ ⇒ G₂)
    {x : X₁ ⇒ X₂} {x' : X₂ ⇒ X₁} (xi₁ : (x ∘ x') ≈ id X₂) (xi₂ : (x' ∘ x) ≈ id X₁)
    {y : Y₁ ⇒ Y₂} {y' : Y₂ ⇒ Y₁} (yi₁ : (y ∘ y') ≈ id Y₂) (yi₂ : (y' ∘ y) ≈ id Y₁)
    (f₁ : (G₁ ⊕ X₁) ⇒ Y₁) (f₂ : (G₂ ⊕ X₂) ⇒ Y₂) →
    (f₂ ∘ prod-m g x) ≈ (y ∘ f₁) →
    (under-root f₂ ∘ prod-m g (Lmap x)) ≈ (Lmap y ∘ under-root f₁)
under-root-natural g {x} {x'} xi₁ xi₂ {y} {y'} yi₁ yi₂ f₁ f₂ sq =
  ≈-trans (∘-cong (under-root-unfold f₂) ≈-refl)
  (≈-trans (under-root-split-natural g {x} {x'} xi₁ xi₂ {y} {y'} yi₁ yi₂ f₁ f₂ sq)
           (∘-cong ≈-refl (≈-sym (under-root-unfold f₁))))

under-root-pre : ∀ {G₁ G₂ X₁ X₂ Y} (g : G₁ ⇒ G₂)
                 {x : X₁ ⇒ X₂} {x' : X₂ ⇒ X₁} (xi₁ : (x ∘ x') ≈ id X₂) (xi₂ : (x' ∘ x) ≈ id X₁)
                 (r : (G₂ ⊕ X₂) ⇒ Y) →
                 (under-root r ∘ prod-m g (Lmap x)) ≈ under-root (r ∘ prod-m g x)
under-root-pre g {x} {x'} xi₁ xi₂ r =
  ≈-trans (∘-cong (under-root-unfold r) ≈-refl)
  (≈-trans (under-root-split-pre g {x} {x'} xi₁ xi₂ r)
           (≈-sym (under-root-unfold (r ∘ prod-m g x))))

strip-root-cong : ∀ {G X Y} {c c' : 𝟙c ⇒ Y} {r r' : (G ⊕ X) ⇒ Y} →
                  c ≈ c' → r ≈ r' → strip-root c r ≈ strip-root c' r'
strip-root-cong {c = c} {c'} {r} {r'} ec er =
  ≈-trans (strip-root-unfold c r)
  (≈-trans (strip-root-split-cong ec er) (≈-sym (strip-root-unfold c' r')))

under-root-strip : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) →
                   under-root r ≈ strip-root root (inj ∘ r)
under-root-strip r =
  ≈-trans (under-root-unfold r)
  (≈-trans (under-root-split-strip r) (≈-sym (strip-root-unfold root (inj ∘ r))))

strip-root-natural :
  ∀ {G₁ G₂ X₁ X₂ Y₁ Y₂} (g : G₁ ⇒ G₂)
    {x : X₁ ⇒ X₂} {x' : X₂ ⇒ X₁} (xi₁ : (x ∘ x') ≈ id X₂) (xi₂ : (x' ∘ x) ≈ id X₁)
    {y : Y₁ ⇒ Y₂} {c₁ : 𝟙c ⇒ Y₁} {c₂ : 𝟙c ⇒ Y₂} → (y ∘ c₁) ≈ c₂ →
    (f₁ : (G₁ ⊕ X₁) ⇒ Y₁) (f₂ : (G₂ ⊕ X₂) ⇒ Y₂) →
    (f₂ ∘ prod-m g x) ≈ (y ∘ f₁) →
    (strip-root c₂ f₂ ∘ prod-m g (Lmap x)) ≈ (y ∘ strip-root c₁ f₁)
strip-root-natural g {x} {x'} xi₁ xi₂ {y} {c₁} {c₂} yc f₁ f₂ sq =
  ≈-trans (∘-cong (strip-root-unfold c₂ f₂) ≈-refl)
  (≈-trans (strip-root-split-natural g {x} {x'} xi₁ xi₂ {y} {c₁} {c₂} yc f₁ f₂ sq)
           (∘-cong ≈-refl (≈-sym (strip-root-unfold c₁ f₁))))
