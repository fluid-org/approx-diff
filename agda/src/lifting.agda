{-# OPTIONS --prop --postfix-projections --safe #-}

-- The lifting adjoins a root: L P is the biproduct of the chosen unit object with P, with the root
-- and the payload injection its two coproduct injections, so a map out of a lifted object is the
-- copairing of an element at the root with a map on the payload, and the action on morphisms is
-- natural outright. The transport combinators reindex a context-paired morphism across the lifting
-- (strong-Lmap, the action of the lifting on morphisms in context) and eliminate a root in context
-- against a chosen element (elim-root), in single-application forms whose inner morphism is applied
-- once; the split forms and the unfolding bridge supply their laws. The lifting is a strong
-- endofunctor, with the strength the transport of the identity.
open import Level using (_⊔_)
open import categories using (Category)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import commutative-monoid using (CommutativeMonoid)
open import functor using (Functor; StrongFunctor)

module lifting
  {o m e} {𝒞 : Category o m e} (CM : CMonEnriched 𝒞)
  (BP : ∀ x y → Biproduct CM x y)
  (𝟙c : Category.obj 𝒞)
  where

open Category 𝒞
open CMonEnriched CM

private
  module B (x y : obj) = Biproduct (BP x y)

_⊕_ : obj → obj → obj
x ⊕ y = B.prod x y

copair : ∀ {x y z} → x ⇒ z → y ⇒ z → (x ⊕ y) ⇒ z
copair {x} {y} f g = B.copair x y f g

copair-cong : ∀ {x y z} {f f' : x ⇒ z} {g g' : y ⇒ z} → f ≈ f' → g ≈ g' → copair f g ≈ copair f' g'
copair-cong {x} {y} = B.copair-cong x y

pair : ∀ {x y z} → x ⇒ y → x ⇒ z → x ⇒ (y ⊕ z)
pair {x} {y} {z} f g = B.pair y z f g

pair-cong : ∀ {x y z} {f f' : x ⇒ y} {g g' : x ⇒ z} → f ≈ f' → g ≈ g' → pair f g ≈ pair f' g'
pair-cong {x} {y} {z} = B.pair-cong y z

p₁ : ∀ {x y} → (x ⊕ y) ⇒ x
p₁ {x} {y} = B.p₁ x y

p₂ : ∀ {x y} → (x ⊕ y) ⇒ y
p₂ {x} {y} = B.p₂ x y

in₁ : ∀ {x y} → x ⇒ (x ⊕ y)
in₁ {x} {y} = B.in₁ x y

in₂ : ∀ {x y} → y ⇒ (x ⊕ y)
in₂ {x} {y} = B.in₂ x y

+m-cong : ∀ {x y} {f f' g g' : x ⇒ y} → f ≈ f' → g ≈ g' → (f +m g) ≈ (f' +m g')
+m-cong = homCM _ _ .CommutativeMonoid.+-cong

prod-m : ∀ {a₁ a₂ b₁ b₂} → a₁ ⇒ a₂ → b₁ ⇒ b₂ → (a₁ ⊕ b₁) ⇒ (a₂ ⊕ b₂)
prod-m g h = pair (g ∘ p₁) (h ∘ p₂)

prod-m-in₁ : ∀ {a₁ a₂ b₁ b₂} (g : a₁ ⇒ a₂) (h : b₁ ⇒ b₂) → (prod-m g h ∘ in₁) ≈ (in₁ ∘ g)
prod-m-in₁ {a₁} {a₂} {b₁} {b₂} g h =
  ≈-trans (B.pair-natural a₂ b₂ _ _ _)
  (≈-trans (pair-cong
             (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl (B.id-1 a₁ b₁)) id-right))
             (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl (B.zero-2 a₁ b₁)) (comp-bilinear-ε₂ h))))
           (≈-trans (+m-cong ≈-refl (comp-bilinear-ε₂ in₂)) +m-runit))

prod-m-in₂ : ∀ {a₁ a₂ b₁ b₂} (g : a₁ ⇒ a₂) (h : b₁ ⇒ b₂) → (prod-m g h ∘ in₂) ≈ (in₂ ∘ h)
prod-m-in₂ {a₁} {a₂} {b₁} {b₂} g h =
  ≈-trans (B.pair-natural a₂ b₂ _ _ _)
  (≈-trans (pair-cong
             (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl (B.zero-1 a₁ b₁)) (comp-bilinear-ε₂ g)))
             (≈-trans (assoc _ _ _)
               (≈-trans (∘-cong ≈-refl (B.id-2 a₁ b₁)) id-right)))
           (≈-trans (+m-cong (comp-bilinear-ε₂ in₁) ≈-refl)
                    (homCM _ _ .CommutativeMonoid.+-lunit)))

bp-ext : ∀ {a b c} {h k : (a ⊕ b) ⇒ c} → (h ∘ in₁) ≈ (k ∘ in₁) → (h ∘ in₂) ≈ (k ∘ in₂) → h ≈ k
bp-ext {a} {b} {c} {h} {k} e₁ e₂ =
  ≈-trans (≈-sym (B.copair-ext a b h))
  (≈-trans (copair-cong e₁ e₂) (B.copair-ext a b k))

L : obj → obj
L x = 𝟙c ⊕ x

root : ∀ {P} → 𝟙c ⇒ L P
root {P} = in₁

inj : ∀ {P} → P ⇒ L P
inj {P} = in₂

-- The root recovers the element and the injection the payload map.
copair-root : ∀ {P C} (c : 𝟙c ⇒ C) (M : P ⇒ C) → (copair c M ∘ root) ≈ c
copair-root {P} c M = B.copair-in₁ 𝟙c P c M

copair-inj : ∀ {P C} (c : 𝟙c ⇒ C) (M : P ⇒ C) → (copair c M ∘ inj) ≈ M
copair-inj {P} c M = B.copair-in₂ 𝟙c P c M

-- Two maps out of a lifted object agreeing on the root and on the payload are equal, which is the
-- uniqueness principle the initial-algebra laws use.
lifting-ext : ∀ {P C} (h k : L P ⇒ C) →
              (h ∘ root) ≈ (k ∘ root) → (h ∘ inj) ≈ (k ∘ inj) → h ≈ k
lifting-ext h k = bp-ext

Lmap : ∀ {P Q} → P ⇒ Q → L P ⇒ L Q
Lmap f = copair root (inj ∘ f)

Lmap-cong : ∀ {P Q} {f g : P ⇒ Q} → f ≈ g → Lmap f ≈ Lmap g
Lmap-cong e = copair-cong ≈-refl (∘-cong ≈-refl e)

Lmap-root : ∀ {P Q} (f : P ⇒ Q) → (Lmap f ∘ root) ≈ root
Lmap-root f = copair-root root (inj ∘ f)

Lmap-inj : ∀ {P Q} (f : P ⇒ Q) → (Lmap f ∘ inj) ≈ (inj ∘ f)
Lmap-inj f = copair-inj root (inj ∘ f)

Lmap-id : ∀ {P} → Lmap (id P) ≈ id (L P)
Lmap-id {P} =
  ≈-trans (copair-cong ≈-refl id-right)
  (≈-trans (copair-cong (≈-sym id-left) (≈-sym id-left)) (B.copair-ext 𝟙c P (id (L P))))

-- Extending an element across the lifting: unit weight at the root, the given element on the
-- payload.
L-elem : ∀ {X} → (𝟙c ⇒ X) → (𝟙c ⇒ L X)
L-elem c = root +m (inj ∘ c)

L-elem-cong : ∀ {X} {c c' : 𝟙c ⇒ X} → c ≈ c' → L-elem c ≈ L-elem c'
L-elem-cong e = +m-cong ≈-refl (∘-cong ≈-refl e)

L-elem-natural : ∀ {X Y} (f : X ⇒ Y) (c : 𝟙c ⇒ X) → (Lmap f ∘ L-elem c) ≈ L-elem (f ∘ c)
L-elem-natural f c =
  ≈-trans (comp-bilinear₂ (Lmap f) root (inj ∘ c))
    (+m-cong (Lmap-root f)
      (≈-trans (≈-sym (assoc (Lmap f) inj c))
        (≈-trans (∘-cong (Lmap-inj f) ≈-refl) (assoc inj f c))))

private
  -- Postcomposition distributes over the copairing, since composition is bilinear.
  copair-post : ∀ {x y z w} (h : z ⇒ w) (f : x ⇒ z) (g : y ⇒ z) →
                (h ∘ copair f g) ≈ copair (h ∘ f) (h ∘ g)
  copair-post {x} {y} h f g =
    ≈-trans (comp-bilinear₂ h (f ∘ B.p₁ x y) (g ∘ B.p₂ x y))
      (+m-cong (≈-sym (assoc h f (B.p₁ x y))) (≈-sym (assoc h g (B.p₂ x y))))

Lmap-comp : ∀ {P Q R} (g : Q ⇒ R) (f : P ⇒ Q) → Lmap (g ∘ f) ≈ (Lmap g ∘ Lmap f)
Lmap-comp {P} {Q} {R} g f =
  ≈-sym (≈-trans (copair-post (Lmap g) root (inj ∘ f))
    (copair-cong
      (Lmap-root g)
      (≈-trans (≈-sym (assoc (Lmap g) inj f))
      (≈-trans (∘-cong (Lmap-inj g) ≈-refl) (assoc inj g f)))))

-- Reindexing a context-paired morphism under a root: the root passes through and the context
-- enters the payload.
strong-Lmap-split : ∀ {G X Y} → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ L Y)
strong-Lmap-split r = copair (inj ∘ (r ∘ in₁)) (copair root (inj ∘ (r ∘ in₂)))

strong-Lmap-split-cong : ∀ {G X Y} {r r' : (G ⊕ X) ⇒ Y} → r ≈ r' → strong-Lmap-split r ≈ strong-Lmap-split r'
strong-Lmap-split-cong er =
  copair-cong (∘-cong ≈-refl (∘-cong er ≈-refl))
           (copair-cong ≈-refl (∘-cong ≈-refl (∘-cong er ≈-refl)))

-- Transport across the lifting fuses with composition on either side: through the action after,
-- and with a context-paired map before.
strong-Lmap-split-post : ∀ {G X Y₁ Y₂} (h : Y₁ ⇒ Y₂) (r : (G ⊕ X) ⇒ Y₁) →
                        (Lmap h ∘ strong-Lmap-split r) ≈ strong-Lmap-split (h ∘ r)
strong-Lmap-split-post {G} {X} {Y₁} {Y₂} h r =
  bp-ext {h = Lmap h ∘ strong-Lmap-split r} {k = strong-Lmap-split (h ∘ r)}
    (≈-trans (assoc _ _ _)
     (≈-trans (∘-cong ≈-refl (B.copair-in₁ G (L X) _ _))
      (≈-trans (≈-sym (assoc _ _ _))
       (≈-trans (∘-cong (Lmap-inj h) ≈-refl)
        (≈-trans (assoc _ _ _)
         (≈-trans (∘-cong ≈-refl (≈-sym (assoc _ _ _)))
          (≈-sym (B.copair-in₁ G (L X) _ _))))))))
    (≈-trans (assoc _ _ _)
     (≈-trans (∘-cong ≈-refl (B.copair-in₂ G (L X) _ _))
      (≈-trans part₂ (≈-sym (B.copair-in₂ G (L X) _ _)))))
  where
  part₂ : (Lmap h ∘ copair root (inj ∘ (r ∘ in₂))) ≈ copair root (inj ∘ ((h ∘ r) ∘ in₂))
  part₂ = lifting-ext _ _
    (≈-trans (assoc _ _ _)
     (≈-trans (∘-cong ≈-refl (copair-root _ _))
      (≈-trans (Lmap-root h) (≈-sym (copair-root _ _)))))
    (≈-trans (assoc _ _ _)
     (≈-trans (∘-cong ≈-refl (copair-inj _ _))
      (≈-trans (≈-sym (assoc _ _ _))
       (≈-trans (∘-cong (Lmap-inj h) ≈-refl)
        (≈-trans (assoc _ _ _)
         (≈-trans (∘-cong ≈-refl (≈-sym (assoc _ _ _)))
          (≈-sym (copair-inj _ _))))))))

-- Transporting the projection across the lifting is the projection: the context part vanishes and
-- the copairing of the root with the injection is the identity.
strong-Lmap-split-p₂ : ∀ {G X} → strong-Lmap-split (p₂ {G} {X}) ≈ p₂ {G} {L X}
strong-Lmap-split-p₂ {G} {X} =
  ≈-trans (copair-cong
            (≈-trans (∘-cong ≈-refl (B.zero-2 G X)) (comp-bilinear-ε₂ inj))
            (≈-trans (copair-cong ≈-refl
                       (≈-trans (∘-cong ≈-refl (B.id-2 G X)) id-right))
             (≈-trans (copair-cong (≈-sym id-left) (≈-sym id-left))
                      (B.copair-ext 𝟙c X (id (L X))))))
  (≈-trans (+m-cong (comp-bilinear-ε₁ p₁) id-left)
           (homCM _ _ .CommutativeMonoid.+-lunit))

-- Reindexing under a root commutes with transports, which is what naturality of the fold and of
-- reindexing in the tree demands.
strong-Lmap-split-natural :
  ∀ {G₁ G₂ X₁ X₂ Y₁ Y₂} (g : G₁ ⇒ G₂) (x : X₁ ⇒ X₂) (y : Y₁ ⇒ Y₂)
    (f₁ : (G₁ ⊕ X₁) ⇒ Y₁) (f₂ : (G₂ ⊕ X₂) ⇒ Y₂) →
    (f₂ ∘ prod-m g x) ≈ (y ∘ f₁) →
    (strong-Lmap-split f₂ ∘ prod-m g (Lmap x)) ≈ (Lmap y ∘ strong-Lmap-split f₁)
strong-Lmap-split-natural {G₁} {G₂} {X₁} {X₂} {Y₁} {Y₂} g x y f₁ f₂ sq =
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

  side₁ : ((strong-Lmap-split f₂ ∘ prod-m g (Lmap x)) ∘ in₁) ≈ ((Lmap y ∘ strong-Lmap-split f₁) ∘ in₁)
  side₁ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (prod-m-in₁ g (Lmap x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong (B.copair-in₁ G₂ (L X₂) _ _) ≈-refl)
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl square-in₁)
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong (≈-sym (Lmap-inj y)) ≈-refl)
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-sym (B.copair-in₁ G₁ (L X₁) _ _)))
             (≈-sym (assoc _ _ _)))))))))))

  lift-part : (copair root (inj ∘ (f₂ ∘ in₂)) ∘ Lmap x) ≈ (Lmap y ∘ copair root (inj ∘ (f₁ ∘ in₂)))
  lift-part = lifting-ext _ _ root-side inj-side
    where
    root-side : ((copair root (inj ∘ (f₂ ∘ in₂)) ∘ Lmap x) ∘ root)
                ≈ ((Lmap y ∘ copair root (inj ∘ (f₁ ∘ in₂))) ∘ root)
    root-side =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (Lmap-root x))
      (≈-trans (copair-root _ _)
      (≈-sym
        (≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (copair-root _ _)) (Lmap-root y))))))

    inj-side : ((copair root (inj ∘ (f₂ ∘ in₂)) ∘ Lmap x) ∘ inj)
               ≈ ((Lmap y ∘ copair root (inj ∘ (f₁ ∘ in₂))) ∘ inj)
    inj-side =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (Lmap-inj x))
      (≈-trans (≈-sym (assoc _ _ _))
      (≈-trans (∘-cong (copair-inj _ _) ≈-refl)
      (≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl square-in₂)
      (≈-trans (≈-sym (assoc _ _ _))
      (≈-trans (∘-cong (≈-sym (Lmap-inj y)) ≈-refl)
      (≈-trans (assoc _ _ _)
               (≈-sym (≈-trans (assoc _ _ _) (∘-cong ≈-refl (copair-inj _ _))))))))))))

  side₂ : ((strong-Lmap-split f₂ ∘ prod-m g (Lmap x)) ∘ in₂) ≈ ((Lmap y ∘ strong-Lmap-split f₁) ∘ in₂)
  side₂ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (prod-m-in₂ g (Lmap x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong (B.copair-in₂ G₂ (L X₂) _ _) ≈-refl)
    (≈-trans lift-part
    (≈-trans (∘-cong ≈-refl (≈-sym (B.copair-in₂ G₁ (L X₁) _ _)))
             (≈-sym (assoc _ _ _)))))))

copair-pair : ∀ {a b c d} (f : a ⇒ d) (g : b ⇒ d) (h : c ⇒ a) (k : c ⇒ b) →
              (copair f g ∘ pair h k) ≈ ((f ∘ h) +m (g ∘ k))
copair-pair {a} {b} f g h k =
  ≈-trans (comp-bilinear₁ _ _ _)
          (+m-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (B.pair-p₁ a b h k)))
                   (≈-trans (assoc _ _ _) (∘-cong ≈-refl (B.pair-p₂ a b h k))))

-- Transport across the lifting fuses with composition in context.
strong-Lmap-split-co : ∀ {G X Y Z} (r : (G ⊕ Y) ⇒ Z) (s : (G ⊕ X) ⇒ Y) →
                      (strong-Lmap-split r ∘ pair p₁ (strong-Lmap-split s)) ≈ strong-Lmap-split (r ∘ pair p₁ s)
strong-Lmap-split-co {G} {X} {Y} {Z} r s = bp-ext leg₁ (lifting-ext _ _ leg₂-root leg₂-inj)
  where
  A = strong-Lmap-split r
  u = strong-Lmap-split s
  R = r ∘ pair p₁ s
  leg₁ : ((A ∘ pair p₁ u) ∘ in₁) ≈ (strong-Lmap-split R ∘ in₁)
  leg₁ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-trans (B.pair-natural G (L Y) _ _ _)
                                     (pair-cong (B.id-1 G (L X)) (B.copair-in₁ G (L X) _ _))))
    (≈-trans (copair-pair _ _ _ _)
    (≈-trans (+m-cong id-right (≈-trans (≈-sym (assoc _ _ _)) (∘-cong (copair-inj _ _) ≈-refl)))
    (≈-sym
      (≈-trans (B.copair-in₁ G (L X) _ _)
      (≈-trans (∘-cong ≈-refl (assoc _ _ _))
      (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (≈-trans (B.pair-natural G Y _ _ _) (pair-cong (B.id-1 G X) ≈-refl))))
      (≈-trans (∘-cong ≈-refl (comp-bilinear₂ _ _ _))
      (≈-trans (comp-bilinear₂ _ _ _)
               (+m-cong (∘-cong ≈-refl (∘-cong ≈-refl id-right))
                        (≈-trans (∘-cong ≈-refl (≈-sym (assoc _ _ _))) (≈-sym (assoc _ _ _)))))))))))))
  leg₂-root : (((A ∘ pair p₁ u) ∘ in₂) ∘ root) ≈ ((strong-Lmap-split R ∘ in₂) ∘ root)
  leg₂-root =
    ≈-trans (assoc _ _ _)
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-trans (B.pair-natural G (L Y) _ _ _)
                                     (pair-cong (≈-trans (≈-sym (assoc _ _ _))
                                                         (≈-trans (∘-cong (B.zero-1 G (L X)) ≈-refl) (comp-bilinear-ε₁ _)))
                                                (≈-trans (≈-sym (assoc _ _ _))
                                                         (≈-trans (∘-cong (B.copair-in₂ G (L X) _ _) ≈-refl)
                                                                  (copair-root _ _))))))
    (≈-trans (copair-pair _ _ _ _)
    (≈-trans (+m-cong (comp-bilinear-ε₂ _) (copair-root _ _))
    (≈-trans (homCM _ _ .CommutativeMonoid.+-lunit)
             (≈-sym (≈-trans (∘-cong (B.copair-in₂ G (L X) _ _) ≈-refl) (copair-root _ _))))))))
  leg₂-inj : (((A ∘ pair p₁ u) ∘ in₂) ∘ inj) ≈ ((strong-Lmap-split R ∘ in₂) ∘ inj)
  leg₂-inj =
    ≈-trans (assoc _ _ _)
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (≈-trans (B.pair-natural G (L Y) _ _ _)
                                     (pair-cong (≈-trans (≈-sym (assoc _ _ _))
                                                         (≈-trans (∘-cong (B.zero-1 G (L X)) ≈-refl) (comp-bilinear-ε₁ _)))
                                                (≈-trans (≈-sym (assoc _ _ _))
                                                         (≈-trans (∘-cong (B.copair-in₂ G (L X) _ _) ≈-refl)
                                                                  (copair-inj _ _))))))
    (≈-trans (copair-pair _ _ _ _)
    (≈-trans (+m-cong (comp-bilinear-ε₂ _) (≈-trans (≈-sym (assoc _ _ _)) (∘-cong (copair-inj _ _) ≈-refl)))
    (≈-trans (homCM _ _ .CommutativeMonoid.+-lunit)
    (≈-sym
      (≈-trans (∘-cong (B.copair-in₂ G (L X) _ _) ≈-refl)
      (≈-trans (copair-inj _ _)
      (≈-trans (∘-cong ≈-refl (assoc _ _ _))
      (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (≈-trans (B.pair-natural G Y _ _ _) (pair-cong (B.zero-1 G X) ≈-refl))))
      (≈-trans (∘-cong ≈-refl (comp-bilinear₂ _ _ _))
      (≈-trans (∘-cong ≈-refl (+m-cong (≈-trans (∘-cong ≈-refl (comp-bilinear-ε₂ _)) (comp-bilinear-ε₂ _)) ≈-refl))
      (≈-trans (∘-cong ≈-refl (homCM _ _ .CommutativeMonoid.+-lunit))
      (≈-trans (∘-cong ≈-refl (≈-sym (assoc _ _ _))) (≈-sym (assoc _ _ _))))))))))))))))

strong-Lmap-split-pre : ∀ {G₁ G₂ X₁ X₂ Y} (g : G₁ ⇒ G₂) (x : X₁ ⇒ X₂) (r : (G₂ ⊕ X₂) ⇒ Y) →
                 (strong-Lmap-split r ∘ prod-m g (Lmap x)) ≈ strong-Lmap-split (r ∘ prod-m g x)
strong-Lmap-split-pre {G₁} {G₂} {X₁} {X₂} {Y} g x r =
  ≈-trans (strong-Lmap-split-natural g x (id Y) (r ∘ prod-m g x) r (≈-sym id-left))
          (≈-trans (∘-cong Lmap-id ≈-refl) id-left)

-- Eliminating a root in context against a chosen element: the context and the payload pass to the
-- continuation, and the root produces the element.
elim-root-split : ∀ {G X Y} → (𝟙c ⇒ Y) → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ Y)
elim-root-split c r = copair (r ∘ in₁) (copair c (r ∘ in₂))

elim-root-split-cong : ∀ {G X Y} {c c' : 𝟙c ⇒ Y} {r r' : (G ⊕ X) ⇒ Y} →
                  c ≈ c' → r ≈ r' → elim-root-split c r ≈ elim-root-split c' r'
elim-root-split-cong ec er = copair-cong (∘-cong er ≈-refl) (copair-cong ec (∘-cong er ≈-refl))

-- Transport across the lifting is the elimination whose element is the root itself.
strong-Lmap-split-strip : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) →
                   strong-Lmap-split r ≈ elim-root-split root (inj ∘ r)
strong-Lmap-split-strip r =
  copair-cong (≈-sym (assoc _ _ _)) (copair-cong ≈-refl (≈-sym (assoc _ _ _)))

-- Root elimination commutes with transports.
elim-root-split-natural :
  ∀ {G₁ G₂ X₁ X₂ Y₁ Y₂} (g : G₁ ⇒ G₂) (x : X₁ ⇒ X₂)
    {y : Y₁ ⇒ Y₂} {c₁ : 𝟙c ⇒ Y₁} {c₂ : 𝟙c ⇒ Y₂} → (y ∘ c₁) ≈ c₂ →
    (f₁ : (G₁ ⊕ X₁) ⇒ Y₁) (f₂ : (G₂ ⊕ X₂) ⇒ Y₂) →
    (f₂ ∘ prod-m g x) ≈ (y ∘ f₁) →
    (elim-root-split c₂ f₂ ∘ prod-m g (Lmap x)) ≈ (y ∘ elim-root-split c₁ f₁)
elim-root-split-natural {G₁} {G₂} {X₁} {X₂} {Y₁} {Y₂} g x {y} {c₁} {c₂} yc f₁ f₂ sq =
  bp-ext side₁ side₂
  where
  square-in₂ : ((f₂ ∘ in₂) ∘ x) ≈ (y ∘ (f₁ ∘ in₂))
  square-in₂ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (≈-sym (prod-m-in₂ g x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ sq) (assoc _ _ _))))

  side₁ : ((elim-root-split c₂ f₂ ∘ prod-m g (Lmap x)) ∘ in₁) ≈ ((y ∘ elim-root-split c₁ f₁) ∘ in₁)
  side₁ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (prod-m-in₁ g (Lmap x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (B.copair-in₁ G₂ (L X₂) _ _))
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (≈-sym (prod-m-in₁ g x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ sq)
    (≈-trans (assoc _ _ _)
             (≈-sym (≈-trans (assoc _ _ _)
                             (∘-cong₂ (B.copair-in₁ G₁ (L X₁) _ _))))))))))))

  const-side : (copair c₂ (f₂ ∘ in₂) ∘ Lmap x) ≈ (y ∘ copair c₁ (f₁ ∘ in₂))
  const-side = lifting-ext _ _
    (≈-trans (assoc _ _ _)
     (≈-trans (∘-cong₂ (Lmap-root x))
      (≈-trans (copair-root _ _)
       (≈-sym (≈-trans (assoc _ _ _)
                       (≈-trans (∘-cong₂ (copair-root _ _)) yc))))))
    (≈-trans (assoc _ _ _)
     (≈-trans (∘-cong₂ (Lmap-inj x))
      (≈-trans (≈-sym (assoc _ _ _))
       (≈-trans (∘-cong₁ (copair-inj _ _))
        (≈-trans square-in₂
         (≈-sym (≈-trans (assoc _ _ _) (∘-cong₂ (copair-inj _ _)))))))))

  side₂ : ((elim-root-split c₂ f₂ ∘ prod-m g (Lmap x)) ∘ in₂) ≈ ((y ∘ elim-root-split c₁ f₁) ∘ in₂)
  side₂ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (prod-m-in₂ g (Lmap x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (B.copair-in₂ G₂ (L X₂) _ _))
    (≈-trans const-side
             (≈-sym (≈-trans (assoc _ _ _)
                             (∘-cong₂ (B.copair-in₂ G₁ (L X₁) _ _))))))))


-- Single-application forms as the public combinators: the inner morphism is applied once, to the
-- context recombined with the extracted payload. The split forms apply it once per copairing arm,
-- so nesting them multiplies evaluations of the continuation per lifting layer. Each public lemma
-- is the split-form law transported across the unfolding bridge.
payload-L : ∀ {X} → L X ⇒ X
payload-L {X} = copair εm (id X)

tag-L : ∀ {X} → L X ⇒ 𝟙c
tag-L {X} = copair (id 𝟙c) εm

payload-L-root : ∀ {X} → (payload-L {X} ∘ root) ≈ εm
payload-L-root {X} = copair-root εm (id X)

payload-L-inj : ∀ {X} → (payload-L {X} ∘ inj) ≈ id X
payload-L-inj {X} = copair-inj εm (id X)

tag-L-root : ∀ {X} → (tag-L {X} ∘ root) ≈ id 𝟙c
tag-L-root {X} = copair-root (id 𝟙c) εm

tag-L-inj : ∀ {X} → (tag-L {X} ∘ inj) ≈ εm
tag-L-inj {X} = copair-inj (id 𝟙c) εm

-- Evaluation-critical shape: exactly one application of r per element.
strong-Lmap : ∀ {G X Y} → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ L Y)
strong-Lmap {G} r = (inj ∘ (r ∘ prod-m (id G) payload-L)) +m ((root ∘ tag-L) ∘ p₂)

-- Evaluation-critical shape: exactly one application of r per element.
elim-root : ∀ {G X Y} → (𝟙c ⇒ Y) → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ Y)
elim-root {G} c r = (r ∘ prod-m (id G) payload-L) +m ((c ∘ tag-L) ∘ p₂)

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
    (≈-trans (∘-cong ≈-refl (B.zero-2 G (L X))) (comp-bilinear-ε₂ _))

  tag-arm-in₂ : ∀ {G X Y} (c : 𝟙c ⇒ Y) → (((c ∘ tag-L {X}) ∘ p₂) ∘ in₂ {G}) ≈ (c ∘ tag-L)
  tag-arm-in₂ {G} {X} c =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (B.id-2 G (L X))) id-right)

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

strong-Lmap-unfold : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) → strong-Lmap r ≈ strong-Lmap-split r
strong-Lmap-unfold {G} {X} {Y} r = bp-ext leg₁ leg₂
  where
  M = inj ∘ (r ∘ in₂)

  leg₁ : (strong-Lmap r ∘ in₁) ≈ (strong-Lmap-split r ∘ in₁)
  leg₁ =
    ≈-trans (comp-bilinear₁ _ _ in₁)
    (≈-trans (+m-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (prod-m-arm-in₁ r)))
                      (tag-arm-in₁ root))
    (≈-trans +m-runit
             (≈-sym (B.copair-in₁ G (L X) (inj ∘ (r ∘ in₁)) (copair root M)))))

  E : L X ⇒ L Y
  E = (inj ∘ (r ∘ (in₂ ∘ payload-L))) +m (root ∘ tag-L)

  E-root : (E ∘ root) ≈ (copair root M ∘ root)
  E-root =
    ≈-trans (comp-bilinear₁ _ _ root)
    (≈-trans (+m-cong (≈-trans (assoc _ _ _)
                        (≈-trans (∘-cong ≈-refl (payload-comp-root r)) (comp-bilinear-ε₂ inj)))
                      (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl tag-L-root) id-right)))
    (≈-trans (homCM _ _ .CommutativeMonoid.+-lunit)
             (≈-sym (copair-root root M))))

  E-inj : (E ∘ inj) ≈ (copair root M ∘ inj)
  E-inj =
    ≈-trans (comp-bilinear₁ _ _ inj)
    (≈-trans (+m-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (payload-comp-inj r)))
                      (≈-trans (assoc _ _ _)
                       (≈-trans (∘-cong ≈-refl tag-L-inj) (comp-bilinear-ε₂ root))))
    (≈-trans +m-runit (≈-sym (copair-inj root M))))

  leg₂ : (strong-Lmap r ∘ in₂) ≈ (strong-Lmap-split r ∘ in₂)
  leg₂ =
    ≈-trans (comp-bilinear₁ _ _ in₂)
    (≈-trans (+m-cong (≈-trans (assoc _ _ _) (∘-cong ≈-refl (prod-m-arm-in₂ r)))
                      (tag-arm-in₂ root))
    (≈-trans (lifting-ext E (copair root M) E-root E-inj)
             (≈-sym (B.copair-in₂ G (L X) (inj ∘ (r ∘ in₁)) (copair root M)))))

elim-root-unfold : ∀ {G X Y} (c : 𝟙c ⇒ Y) (r : (G ⊕ X) ⇒ Y) →
                    elim-root c r ≈ elim-root-split c r
elim-root-unfold {G} {X} {Y} c r = bp-ext leg₁ leg₂
  where
  M = r ∘ in₂

  leg₁ : (elim-root c r ∘ in₁) ≈ (elim-root-split c r ∘ in₁)
  leg₁ =
    ≈-trans (comp-bilinear₁ _ _ in₁)
    (≈-trans (+m-cong (prod-m-arm-in₁ r) (tag-arm-in₁ c))
    (≈-trans +m-runit
             (≈-sym (B.copair-in₁ G (L X) (r ∘ in₁) (copair c M)))))

  E : L X ⇒ Y
  E = (r ∘ (in₂ ∘ payload-L)) +m (c ∘ tag-L)

  E-root : (E ∘ root) ≈ (copair c M ∘ root)
  E-root =
    ≈-trans (comp-bilinear₁ _ _ root)
    (≈-trans (+m-cong (payload-comp-root r)
                      (≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl tag-L-root) id-right)))
    (≈-trans (homCM _ _ .CommutativeMonoid.+-lunit)
             (≈-sym (copair-root c M))))

  E-inj : (E ∘ inj) ≈ (copair c M ∘ inj)
  E-inj =
    ≈-trans (comp-bilinear₁ _ _ inj)
    (≈-trans (+m-cong (payload-comp-inj r)
                      (≈-trans (assoc _ _ _)
                       (≈-trans (∘-cong ≈-refl tag-L-inj) (comp-bilinear-ε₂ c))))
    (≈-trans +m-runit (≈-sym (copair-inj c M))))

  leg₂ : (elim-root c r ∘ in₂) ≈ (elim-root-split c r ∘ in₂)
  leg₂ =
    ≈-trans (comp-bilinear₁ _ _ in₂)
    (≈-trans (+m-cong (prod-m-arm-in₂ r) (tag-arm-in₂ c))
    (≈-trans (lifting-ext E (copair c M) E-root E-inj)
             (≈-sym (B.copair-in₂ G (L X) (r ∘ in₁) (copair c M)))))

strong-Lmap-cong : ∀ {G X Y} {r r' : (G ⊕ X) ⇒ Y} → r ≈ r' → strong-Lmap r ≈ strong-Lmap r'
strong-Lmap-cong {r = r} {r'} er =
  ≈-trans (strong-Lmap-unfold r)
  (≈-trans (strong-Lmap-split-cong er) (≈-sym (strong-Lmap-unfold r')))

strong-Lmap-post : ∀ {G X Y₁ Y₂} (h : Y₁ ⇒ Y₂) (r : (G ⊕ X) ⇒ Y₁) →
                  (Lmap h ∘ strong-Lmap r) ≈ strong-Lmap (h ∘ r)
strong-Lmap-post h r =
  ≈-trans (∘-cong ≈-refl (strong-Lmap-unfold r))
  (≈-trans (strong-Lmap-split-post h r) (≈-sym (strong-Lmap-unfold (h ∘ r))))

strong-Lmap-p₂ : ∀ {G X} → strong-Lmap (p₂ {G} {X}) ≈ p₂ {G} {L X}
strong-Lmap-p₂ {G} {X} =
  ≈-trans (strong-Lmap-unfold (p₂ {G} {X})) strong-Lmap-split-p₂

strong-Lmap-natural :
  ∀ {G₁ G₂ X₁ X₂ Y₁ Y₂} (g : G₁ ⇒ G₂) (x : X₁ ⇒ X₂) (y : Y₁ ⇒ Y₂)
    (f₁ : (G₁ ⊕ X₁) ⇒ Y₁) (f₂ : (G₂ ⊕ X₂) ⇒ Y₂) →
    (f₂ ∘ prod-m g x) ≈ (y ∘ f₁) →
    (strong-Lmap f₂ ∘ prod-m g (Lmap x)) ≈ (Lmap y ∘ strong-Lmap f₁)
strong-Lmap-natural g x y f₁ f₂ sq =
  ≈-trans (∘-cong (strong-Lmap-unfold f₂) ≈-refl)
  (≈-trans (strong-Lmap-split-natural g x y f₁ f₂ sq)
           (∘-cong ≈-refl (≈-sym (strong-Lmap-unfold f₁))))

strong-Lmap-pre : ∀ {G₁ G₂ X₁ X₂ Y} (g : G₁ ⇒ G₂) (x : X₁ ⇒ X₂) (r : (G₂ ⊕ X₂) ⇒ Y) →
                 (strong-Lmap r ∘ prod-m g (Lmap x)) ≈ strong-Lmap (r ∘ prod-m g x)
strong-Lmap-pre g x r =
  ≈-trans (∘-cong (strong-Lmap-unfold r) ≈-refl)
  (≈-trans (strong-Lmap-split-pre g x r)
           (≈-sym (strong-Lmap-unfold (r ∘ prod-m g x))))

strong-Lmap-inj : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) → (strong-Lmap r ∘ prod-m (id G) inj) ≈ (inj ∘ r)
strong-Lmap-inj {G} {X} {Y} r =
  ≈-trans (comp-bilinear₁ _ _ _)
  (≈-trans (+m-cong payload-part root-part) +m-runit)
  where
  collapse : (prod-m (id G) payload-L ∘ prod-m (id G) inj) ≈ id _
  collapse =
    ≈-trans (B.pair-natural G X _ _ _)
    (≈-trans (pair-cong
        (≈-trans (∘-cong id-left ≈-refl) (≈-trans (B.pair-p₁ G (L X) _ _) id-left))
        (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl (B.pair-p₂ G (L X) _ _))
            (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong payload-L-inj ≈-refl) id-left)))))
      (B.pair-ext0 G X))

  payload-part : ((inj ∘ (r ∘ prod-m (id G) payload-L)) ∘ prod-m (id G) inj) ≈ (inj ∘ r)
  payload-part =
    ≈-trans (assoc _ _ _)
    (∘-cong ≈-refl
      (≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl collapse) id-right)))

  root-part : (((root ∘ tag-L) ∘ p₂) ∘ prod-m (id G) inj) ≈ εm
  root-part =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (B.pair-p₂ G (L X) _ _))
      (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong (≈-trans (assoc _ _ _)
                           (≈-trans (∘-cong ≈-refl tag-L-inj) (comp-bilinear-ε₂ root))) ≈-refl)
          (comp-bilinear-ε₁ p₂))))

strong-Lmap-co : ∀ {G X Y Z} (r : (G ⊕ Y) ⇒ Z) (s : (G ⊕ X) ⇒ Y) →
                (strong-Lmap r ∘ pair p₁ (strong-Lmap s)) ≈ strong-Lmap (r ∘ pair p₁ s)
strong-Lmap-co r s =
  ≈-trans (∘-cong (strong-Lmap-unfold r) (pair-cong ≈-refl (strong-Lmap-unfold s)))
  (≈-trans (strong-Lmap-split-co r s) (≈-sym (strong-Lmap-unfold _)))

strong-Lmap-split-elem : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) (g : 𝟙c ⇒ G) (c : 𝟙c ⇒ X) →
                        (strong-Lmap-split r ∘ pair g (L-elem c)) ≈ L-elem (r ∘ pair g c)
strong-Lmap-split-elem {G} {X} {Y} r g c =
  ≈-trans (comp-bilinear₂ S (in₁ ∘ g) (in₂ ∘ L-elem c))
  (≈-trans (+m-cong summand₁ summand₂)
  (≈-trans (≈-sym (homCM _ _ .CommutativeMonoid.+-assoc))
  (≈-trans (+m-cong (homCM _ _ .CommutativeMonoid.+-comm) ≈-refl)
  (≈-trans (homCM _ _ .CommutativeMonoid.+-assoc)
           (+m-cong ≈-refl payload)))))
  where
  S = strong-Lmap-split r
  C = copair root (inj ∘ (r ∘ in₂))

  summand₁ : (S ∘ (in₁ ∘ g)) ≈ (inj ∘ (r ∘ (in₁ ∘ g)))
  summand₁ =
    ≈-trans (≈-sym (assoc S in₁ g))
    (≈-trans (∘-cong (B.copair-in₁ G (L X) (inj ∘ (r ∘ in₁)) C) ≈-refl)
    (≈-trans (assoc inj (r ∘ in₁) g) (∘-cong ≈-refl (assoc r in₁ g))))

  summand₂ : (S ∘ (in₂ ∘ L-elem c)) ≈ (root +m (inj ∘ (r ∘ (in₂ ∘ c))))
  summand₂ =
    ≈-trans (≈-sym (assoc S in₂ (L-elem c)))
    (≈-trans (∘-cong (B.copair-in₂ G (L X) (inj ∘ (r ∘ in₁)) C) ≈-refl)
    (≈-trans (comp-bilinear₂ C root (inj ∘ c))
             (+m-cong (copair-root root (inj ∘ (r ∘ in₂)))
                      (≈-trans (≈-sym (assoc C inj c))
                      (≈-trans (∘-cong (copair-inj root (inj ∘ (r ∘ in₂))) ≈-refl)
                      (≈-trans (assoc inj (r ∘ in₂) c) (∘-cong ≈-refl (assoc r in₂ c))))))))

  payload : ((inj ∘ (r ∘ (in₁ ∘ g))) +m (inj ∘ (r ∘ (in₂ ∘ c)))) ≈ (inj ∘ (r ∘ pair g c))
  payload =
    ≈-trans (≈-sym (comp-bilinear₂ inj (r ∘ (in₁ ∘ g)) (r ∘ (in₂ ∘ c))))
            (∘-cong ≈-refl (≈-sym (comp-bilinear₂ r (in₁ ∘ g) (in₂ ∘ c))))

strong-Lmap-elem : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) (g : 𝟙c ⇒ G) (c : 𝟙c ⇒ X) →
                  (strong-Lmap r ∘ pair g (L-elem c)) ≈ L-elem (r ∘ pair g c)
strong-Lmap-elem r g c =
  ≈-trans (∘-cong (strong-Lmap-unfold r) ≈-refl) (strong-Lmap-split-elem r g c)

elim-root-cong : ∀ {G X Y} {c c' : 𝟙c ⇒ Y} {r r' : (G ⊕ X) ⇒ Y} →
                  c ≈ c' → r ≈ r' → elim-root c r ≈ elim-root c' r'
elim-root-cong {c = c} {c'} {r} {r'} ec er =
  ≈-trans (elim-root-unfold c r)
  (≈-trans (elim-root-split-cong ec er) (≈-sym (elim-root-unfold c' r')))

strong-Lmap-strip : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) →
                   strong-Lmap r ≈ elim-root root (inj ∘ r)
strong-Lmap-strip r =
  ≈-trans (strong-Lmap-unfold r)
  (≈-trans (strong-Lmap-split-strip r) (≈-sym (elim-root-unfold root (inj ∘ r))))

elim-root-natural :
  ∀ {G₁ G₂ X₁ X₂ Y₁ Y₂} (g : G₁ ⇒ G₂) (x : X₁ ⇒ X₂)
    {y : Y₁ ⇒ Y₂} {c₁ : 𝟙c ⇒ Y₁} {c₂ : 𝟙c ⇒ Y₂} → (y ∘ c₁) ≈ c₂ →
    (f₁ : (G₁ ⊕ X₁) ⇒ Y₁) (f₂ : (G₂ ⊕ X₂) ⇒ Y₂) →
    (f₂ ∘ prod-m g x) ≈ (y ∘ f₁) →
    (elim-root c₂ f₂ ∘ prod-m g (Lmap x)) ≈ (y ∘ elim-root c₁ f₁)
elim-root-natural g x {y} {c₁} {c₂} yc f₁ f₂ sq =
  ≈-trans (∘-cong (elim-root-unfold c₂ f₂) ≈-refl)
  (≈-trans (elim-root-split-natural g x {y} {c₁} {c₂} yc f₁ f₂ sq)
           (∘-cong ≈-refl (≈-sym (elim-root-unfold c₁ f₁))))

-- The lifting as a strong endofunctor: the strength is the transport of the identity, so the
-- transport of any morphism is its action after the strength.
L-functor : Functor 𝒞 𝒞
L-functor .Functor.fobj = L
L-functor .Functor.fmor = Lmap
L-functor .Functor.fmor-cong = Lmap-cong
L-functor .Functor.fmor-id = Lmap-id
L-functor .Functor.fmor-comp = Lmap-comp

L-strong : StrongFunctor (biproducts→products CM BP)
L-strong .StrongFunctor.F = L-functor
L-strong .StrongFunctor.strengthᵣ = strong-Lmap (id _)
L-strong .StrongFunctor.strengthᵣ-natural f g =
  ≈-sym (strong-Lmap-natural f g (prod-m f g) (id _) (id _) (≈-trans id-left (≈-sym id-right)))
L-strong .StrongFunctor.strengthᵣ-p₂ =
  ≈-trans (strong-Lmap-post _ _) (≈-trans (strong-Lmap-cong id-right) strong-Lmap-p₂)
L-strong .StrongFunctor.strengthᵣ-assoc =
  ≈-trans (strong-Lmap-co _ _)
          (≈-sym (≈-trans (strong-Lmap-post _ _) (strong-Lmap-cong (≈-trans id-right (≈-sym id-left)))))
