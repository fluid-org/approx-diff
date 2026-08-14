{-# OPTIONS --prop --postfix-projections --safe #-}

-- The lifting adjoins a root: L P is the biproduct of the chosen unit object with P, with the root
-- and the payload injection its two coproduct injections, so a map out of a lifted object is the
-- copairing of a constant at the root with a map on the payload, and the action on morphisms is
-- natural outright. The transport combinators reindex a context-paired morphism across the lifting
-- (under-root) and eliminate a root in context against a chosen constant (elim-root), in
-- single-application forms whose inner morphism is applied once; the split forms and the unfolding
-- bridge supply their laws.
open import Level using (_⊔_)
open import categories using (Category)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)

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

-- The root recovers the constant and the injection the payload map.
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

-- Extending a constant across the lifting: unit weight at the root, the given constant on the
-- payload.
L-const : ∀ {X} → (𝟙c ⇒ X) → (𝟙c ⇒ L X)
L-const c = root +m (inj ∘ c)

L-const-cong : ∀ {X} {c c' : 𝟙c ⇒ X} → c ≈ c' → L-const c ≈ L-const c'
L-const-cong e = +m-cong ≈-refl (∘-cong ≈-refl e)

L-const-natural : ∀ {X Y} (f : X ⇒ Y) (c : 𝟙c ⇒ X) → (Lmap f ∘ L-const c) ≈ L-const (f ∘ c)
L-const-natural f c =
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
under-root-split : ∀ {G X Y} → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ L Y)
under-root-split r = copair (inj ∘ (r ∘ in₁)) (copair root (inj ∘ (r ∘ in₂)))

under-root-split-cong : ∀ {G X Y} {r r' : (G ⊕ X) ⇒ Y} → r ≈ r' → under-root-split r ≈ under-root-split r'
under-root-split-cong er =
  copair-cong (∘-cong ≈-refl (∘-cong er ≈-refl))
           (copair-cong ≈-refl (∘-cong ≈-refl (∘-cong er ≈-refl)))

-- Transport across the lifting fuses with composition on either side: through the action after,
-- and with a context-paired map before.
under-root-split-post : ∀ {G X Y₁ Y₂} (h : Y₁ ⇒ Y₂) (r : (G ⊕ X) ⇒ Y₁) →
                        (Lmap h ∘ under-root-split r) ≈ under-root-split (h ∘ r)
under-root-split-post {G} {X} {Y₁} {Y₂} h r =
  bp-ext {h = Lmap h ∘ under-root-split r} {k = under-root-split (h ∘ r)}
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
under-root-split-p₂ : ∀ {G X} → under-root-split (p₂ {G} {X}) ≈ p₂ {G} {L X}
under-root-split-p₂ {G} {X} =
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
under-root-split-natural :
  ∀ {G₁ G₂ X₁ X₂ Y₁ Y₂} (g : G₁ ⇒ G₂) (x : X₁ ⇒ X₂) (y : Y₁ ⇒ Y₂)
    (f₁ : (G₁ ⊕ X₁) ⇒ Y₁) (f₂ : (G₂ ⊕ X₂) ⇒ Y₂) →
    (f₂ ∘ prod-m g x) ≈ (y ∘ f₁) →
    (under-root-split f₂ ∘ prod-m g (Lmap x)) ≈ (Lmap y ∘ under-root-split f₁)
under-root-split-natural {G₁} {G₂} {X₁} {X₂} {Y₁} {Y₂} g x y f₁ f₂ sq =
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

  side₂ : ((under-root-split f₂ ∘ prod-m g (Lmap x)) ∘ in₂) ≈ ((Lmap y ∘ under-root-split f₁) ∘ in₂)
  side₂ =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong ≈-refl (prod-m-in₂ g (Lmap x)))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong (B.copair-in₂ G₂ (L X₂) _ _) ≈-refl)
    (≈-trans lift-part
    (≈-trans (∘-cong ≈-refl (≈-sym (B.copair-in₂ G₁ (L X₁) _ _)))
             (≈-sym (assoc _ _ _)))))))

under-root-split-pre : ∀ {G₁ G₂ X₁ X₂ Y} (g : G₁ ⇒ G₂) (x : X₁ ⇒ X₂) (r : (G₂ ⊕ X₂) ⇒ Y) →
                 (under-root-split r ∘ prod-m g (Lmap x)) ≈ under-root-split (r ∘ prod-m g x)
under-root-split-pre {G₁} {G₂} {X₁} {X₂} {Y} g x r =
  ≈-trans (under-root-split-natural g x (id Y) (r ∘ prod-m g x) r (≈-sym id-left))
          (≈-trans (∘-cong Lmap-id ≈-refl) id-left)

-- Eliminating a root in context against a chosen constant: the context and the payload pass to the
-- continuation, and the root produces the constant.
elim-root-split : ∀ {G X Y} → (𝟙c ⇒ Y) → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ Y)
elim-root-split c r = copair (r ∘ in₁) (copair c (r ∘ in₂))

elim-root-split-cong : ∀ {G X Y} {c c' : 𝟙c ⇒ Y} {r r' : (G ⊕ X) ⇒ Y} →
                  c ≈ c' → r ≈ r' → elim-root-split c r ≈ elim-root-split c' r'
elim-root-split-cong ec er = copair-cong (∘-cong er ≈-refl) (copair-cong ec (∘-cong er ≈-refl))

-- Transport across the lifting is the elimination whose constant is the root itself.
under-root-split-strip : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) →
                   under-root-split r ≈ elim-root-split root (inj ∘ r)
under-root-split-strip r =
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
under-root : ∀ {G X Y} → ((G ⊕ X) ⇒ Y) → ((G ⊕ L X) ⇒ L Y)
under-root {G} r = (inj ∘ (r ∘ prod-m (id G) payload-L)) +m ((root ∘ tag-L) ∘ p₂)

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

  leg₂ : (under-root r ∘ in₂) ≈ (under-root-split r ∘ in₂)
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

under-root-cong : ∀ {G X Y} {r r' : (G ⊕ X) ⇒ Y} → r ≈ r' → under-root r ≈ under-root r'
under-root-cong {r = r} {r'} er =
  ≈-trans (under-root-unfold r)
  (≈-trans (under-root-split-cong er) (≈-sym (under-root-unfold r')))

under-root-post : ∀ {G X Y₁ Y₂} (h : Y₁ ⇒ Y₂) (r : (G ⊕ X) ⇒ Y₁) →
                  (Lmap h ∘ under-root r) ≈ under-root (h ∘ r)
under-root-post h r =
  ≈-trans (∘-cong ≈-refl (under-root-unfold r))
  (≈-trans (under-root-split-post h r) (≈-sym (under-root-unfold (h ∘ r))))

under-root-p₂ : ∀ {G X} → under-root (p₂ {G} {X}) ≈ p₂ {G} {L X}
under-root-p₂ {G} {X} =
  ≈-trans (under-root-unfold (p₂ {G} {X})) under-root-split-p₂

under-root-natural :
  ∀ {G₁ G₂ X₁ X₂ Y₁ Y₂} (g : G₁ ⇒ G₂) (x : X₁ ⇒ X₂) (y : Y₁ ⇒ Y₂)
    (f₁ : (G₁ ⊕ X₁) ⇒ Y₁) (f₂ : (G₂ ⊕ X₂) ⇒ Y₂) →
    (f₂ ∘ prod-m g x) ≈ (y ∘ f₁) →
    (under-root f₂ ∘ prod-m g (Lmap x)) ≈ (Lmap y ∘ under-root f₁)
under-root-natural g x y f₁ f₂ sq =
  ≈-trans (∘-cong (under-root-unfold f₂) ≈-refl)
  (≈-trans (under-root-split-natural g x y f₁ f₂ sq)
           (∘-cong ≈-refl (≈-sym (under-root-unfold f₁))))

under-root-pre : ∀ {G₁ G₂ X₁ X₂ Y} (g : G₁ ⇒ G₂) (x : X₁ ⇒ X₂) (r : (G₂ ⊕ X₂) ⇒ Y) →
                 (under-root r ∘ prod-m g (Lmap x)) ≈ under-root (r ∘ prod-m g x)
under-root-pre g x r =
  ≈-trans (∘-cong (under-root-unfold r) ≈-refl)
  (≈-trans (under-root-split-pre g x r)
           (≈-sym (under-root-unfold (r ∘ prod-m g x))))

elim-root-cong : ∀ {G X Y} {c c' : 𝟙c ⇒ Y} {r r' : (G ⊕ X) ⇒ Y} →
                  c ≈ c' → r ≈ r' → elim-root c r ≈ elim-root c' r'
elim-root-cong {c = c} {c'} {r} {r'} ec er =
  ≈-trans (elim-root-unfold c r)
  (≈-trans (elim-root-split-cong ec er) (≈-sym (elim-root-unfold c' r')))

under-root-strip : ∀ {G X Y} (r : (G ⊕ X) ⇒ Y) →
                   under-root r ≈ elim-root root (inj ∘ r)
under-root-strip r =
  ≈-trans (under-root-unfold r)
  (≈-trans (under-root-split-strip r) (≈-sym (elim-root-unfold root (inj ∘ r))))

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
