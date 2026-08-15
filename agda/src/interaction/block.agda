{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; map; foldl)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Level using (Level; Lift) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
import matrix
import two

-- A dependence graph as a value rather than a family indexed by a derivation: a block is a set of
-- interior vertices with widths, a distinguished root of given width, and the entries between them.
-- The root has no outgoing entries, so it is a sink by construction.
module interaction.block (ℓ : Level) where

private
  module M = matrix.Mat two.semiring

open import categories using (Category)
open Category M.cat using (_∘_; _≈_; ∘-cong; ∘-cong₁; ∘-cong₂; assoc; id-left; ≈-refl; ≈-sym; ≈-trans)

≈-of-≡ : ∀ {m n} {X Y : M.Matrix m n} → X ≡ Y → X ≈ Y
≈-of-≡ ≡-refl = ≈-refl

data Root : Set ℓ where
  root : Root

Void : Set ℓ
Void = Lift ℓ ⊥

-- A map on input columns, linear so that it commutes with hiding. A premise evaluated in a
-- substituted environment reaches the conclusion's inputs through one of these.
record Linear {Inp' : Set ℓ} (iw' : Inp' → ℕ) {Inp : Set ℓ} (iw : Inp → ℕ) : Set (lsuc ℓ) where
  field
    ap      : ∀ {m} → ((i' : Inp') → M.Matrix m (iw' i')) → (i : Inp) → M.Matrix m (iw i)
    ap-+    : ∀ {m} (f g : (i' : Inp') → M.Matrix m (iw' i')) (i : Inp) →
              ap (λ i' → f i' M.+ₘ g i') i ≈ (ap f i M.+ₘ ap g i)
    ap-∘    : ∀ {m k} (X : M.Matrix k m) (f : (i' : Inp') → M.Matrix m (iw' i')) (i : Inp) →
              ap (λ i' → X ∘ f i') i ≈ (X ∘ ap f i)
    ap-cong : ∀ {m} {f g : (i' : Inp') → M.Matrix m (iw' i')} → (∀ i' → f i' ≈ g i') →
              ∀ i → ap f i ≈ ap g i

open Linear public

-- The same into a single column: how a premise's inputs are reached from an earlier premise's root.
record Link {Inp' : Set ℓ} (iw' : Inp' → ℕ) (n : ℕ) : Set (lsuc ℓ) where
  field
    at      : ∀ {m} → ((i' : Inp') → M.Matrix m (iw' i')) → M.Matrix m n
    at-+    : ∀ {m} (f g : (i' : Inp') → M.Matrix m (iw' i')) →
              at (λ i' → f i' M.+ₘ g i') ≈ (at f M.+ₘ at g)
    at-∘    : ∀ {m k} (X : M.Matrix k m) (f : (i' : Inp') → M.Matrix m (iw' i')) →
              at (λ i' → X ∘ f i') ≈ (X ∘ at f)
    at-cong : ∀ {m} {f g : (i' : Inp') → M.Matrix m (iw' i')} → (∀ i' → f i' ≈ g i') →
              at f ≈ at g

open Link public

id-linear : {Inp : Set ℓ} (iw : Inp → ℕ) → Linear iw iw
id-linear iw .ap f i = f i
id-linear iw .ap-+ f g i = ≈-refl
id-linear iw .ap-∘ X f i = ≈-refl
id-linear iw .ap-cong e i = e i

no-link : {Inp' : Set ℓ} (iw' : Inp' → ℕ) (n : ℕ) → Link iw' n
no-link iw' n .at {m} _ = M.εₘ {m} {n}
no-link iw' n .at-+ {m} f g =
  ≈-sym {f = M.εₘ {m} {n} M.+ₘ M.εₘ {m} {n}} {g = M.εₘ {m} {n}} (M.+ₘ-lunit (M.εₘ {m} {n}))
no-link iw' n .at-∘ {m} {k} X f =
  ≈-sym {f = X ∘ M.εₘ {m} {n}} {g = M.εₘ {k} {n}} (M.comp-bilinear-ε₂ X)
no-link iw' n .at-cong {m} e = ≈-refl {f = M.εₘ {m} {n}}

record Block (Inp : Set ℓ) (iw : Inp → ℕ) (n : ℕ) : Set (lsuc ℓ) where
  field
    Q      : Set ℓ
    qw     : Q → ℕ
    qs     : List Q
    into   : (i : Inp) (q : Q) → M.Matrix (qw q) (iw i)
    inside : (p q : Q) → M.Matrix (qw q) (qw p)
    out    : (i : Inp) → M.Matrix n (iw i)
    up     : (p : Q) → M.Matrix n (qw p)

-- Graphs over an arbitrary vertex set, and hiding, as in interaction.hide-algebra but stated at the
-- ≈ of the matrix category rather than entrywise.
Gr : {V : Set ℓ} → (V → ℕ) → Set ℓ
Gr {V} vw = (x y : V) → M.Matrix (vw y) (vw x)

hide : {V : Set ℓ} (vw : V → ℕ) → Gr vw → V → Gr vw
hide vw G r x y = G x y M.+ₘ (G r y ∘ G x r)

hide-all : {V : Set ℓ} (vw : V → ℕ) → Gr vw → List V → Gr vw
hide-all vw = foldl (hide vw)

_≐_ : {V : Set ℓ} {vw : V → ℕ} → Gr vw → Gr vw → Prop ℓ
_≐_ {V} G G' = ∀ x y → G x y ≈ G' x y

hide-cong : {V : Set ℓ} (vw : V → ℕ) {G G' : Gr vw} (r : V) →
            G ≐ G' → hide vw G r ≐ hide vw G' r
hide-cong vw r e x y = M.+ₘ-cong (e x y) (∘-cong (e r y) (e x r))

hide-all-cong : {V : Set ℓ} (vw : V → ℕ) {G G' : Gr vw} (rs : List V) →
                G ≐ G' → hide-all vw G rs ≐ hide-all vw G' rs
hide-all-cong vw []       e = e
hide-all-cong vw (r ∷ rs) e = hide-all-cong vw rs (hide-cong vw r e)

-- Hiding a sink leaves every entry unchanged.
hide-sink : {V : Set ℓ} (vw : V → ℕ) (G : Gr vw) (r : V) →
            (∀ y → G r y ≈ M.εₘ) → hide vw G r ≐ G
hide-sink vw G r z x y = ≈-trans (M.+ₘ-cong ≈-refl (∘-cong₁ (z y))) (M.absorb₁ (G x y) (G x r))

hide-all-++ : {V : Set ℓ} (vw : V → ℕ) (G : Gr vw) (xs ys : List V) →
              hide-all vw G (xs ++ ys) ≡ hide-all vw (hide-all vw G xs) ys
hide-all-++ vw G []       ys = ≡-refl
hide-all-++ vw G (x ∷ xs) ys = hide-all-++ vw (hide vw G x) xs ys

module _ {Inp : Set ℓ} {iw : Inp → ℕ} {n : ℕ} (B : Block Inp iw n) where
  open Block B

  -- The interior vertices with the root adjoined: what a block contributes to a larger block.
  Q⁺ : Set ℓ
  Q⁺ = Q ⊎ Root

  qw⁺ : Q⁺ → ℕ
  qw⁺ = [ qw , (λ _ → n) ]

  into⁺ : (i : Inp) (q : Q⁺) → M.Matrix (qw⁺ q) (iw i)
  into⁺ i (inj₁ q) = into i q
  into⁺ i (inj₂ _) = out i

  inside⁺ : (p q : Q⁺) → M.Matrix (qw⁺ q) (qw⁺ p)
  inside⁺ (inj₁ p) (inj₁ q) = inside p q
  inside⁺ (inj₁ p) (inj₂ _) = up p
  inside⁺ (inj₂ _) _        = M.εₘ

  qs⁺ : List Q⁺
  qs⁺ = inj₂ root ∷ map inj₁ qs

  V : Set ℓ
  V = Inp ⊎ Q⁺

  vw : V → ℕ
  vw = [ iw , qw⁺ ]

  gr : Gr vw
  gr (inj₁ i) (inj₂ q) = into⁺ i q
  gr (inj₂ p) (inj₂ q) = inside⁺ p q
  gr _        (inj₁ _) = M.εₘ

  collapse : (i : Inp) → M.Matrix n (iw i)
  collapse i = hide-all vw gr (map (λ q → inj₂ (inj₁ q)) qs) (inj₁ i) (inj₂ (inj₂ root))

-- One block's vertices being hidden inside a larger graph. The state records the block's own
-- entries as they accumulate; Φ maps the block's input columns to the ambient graph's input
-- columns, which for a premise evaluated in a substituted environment is not the identity.
module Sweep
  {V : Set ℓ} (vw : V → ℕ)
  {Inp : Set ℓ} (inp : Inp → V)
  {Q : Set ℓ} (blk : Q ⊎ Root → V)
  {T : Set ℓ} (tgt : T → V)
  {Inp' : Set ℓ} {iw' : Inp' → ℕ}
  (Φ : Linear iw' (λ i → vw (inp i)))
  (P : (t : T) → M.Matrix (vw (tgt t)) (vw (blk (inj₂ root))))
  (K : (t : T) (i : Inp) → M.Matrix (vw (tgt t)) (vw (inp i)))
  where

  Qs : Set ℓ
  Qs = Q ⊎ Root

  record St : Set ℓ where
    field
      into   : (i' : Inp') (q : Qs) → M.Matrix (vw (blk q)) (iw' i')
      inside : (p q : Qs) → M.Matrix (vw (blk q)) (vw (blk p))

  open St public

  step : St → Qs → St
  step H w .into i' q = H .into i' q M.+ₘ (H .inside w q ∘ H .into i' w)
  step H w .inside p q = H .inside p q M.+ₘ (H .inside w q ∘ H .inside p w)

  steps : St → List Qs → St
  steps = foldl step

  folds : ∀ {A V' : Set ℓ} (prem : A → St) (ι : Qs → V') (h' : A → V' → A) →
          (∀ G w → step (prem G) w ≡ prem (h' G (ι w))) →
          (ws : List Qs) (G : A) → steps (prem G) ws ≡ prem (foldl h' G (map ι ws))
  folds prem ι h' ok []       G = ≡-refl
  folds prem ι h' ok (w ∷ ws) G =
    ≡-trans (≡-cong (λ H → steps H ws) (ok G w)) (folds prem ι h' ok ws (h' G (ι w)))

  private
    Φ-step : ∀ (H : St) (w : Qs) (i : Inp) (q : Qs) →
             Φ .ap (λ i' → step H w .into i' q) i
             ≈ (Φ .ap (λ i' → H .into i' q) i M.+ₘ (H .inside w q ∘ Φ .ap (λ i' → H .into i' w) i))
    Φ-step H w i q =
      ≈-trans (Φ .ap-+ (λ i' → H .into i' q) (λ i' → H .inside w q ∘ H .into i' w) i)
              (M.+ₘ-cong ≈-refl (Φ .ap-∘ (H .inside w q) (λ i' → H .into i' w) i))

  record Agrees (G : Gr vw) (H : St) : Set ℓ where
    field
      into-ok   : ∀ i q → G (inp i) (blk q) ≈ Φ .ap (λ i' → H .into i' q) i
      inside-ok : ∀ p q → G (blk p) (blk q) ≈ H .inside p q
      tgt-ok    : ∀ t i → G (inp i) (tgt t)
                          ≈ (K t i M.+ₘ (P t ∘ Φ .ap (λ i' → H .into i' (inj₂ root)) i))
      up-ok     : ∀ t (p : Q) → G (blk (inj₁ p)) (tgt t)
                                ≈ (P t ∘ H .inside (inj₁ p) (inj₂ root))

  open Agrees public

  agrees-hide : ∀ {G H} (w : Q) → Agrees G H → Agrees (hide vw G (blk (inj₁ w))) (step H (inj₁ w))
  agrees-hide {H = H} w s .into-ok i q =
    ≈-trans (M.+ₘ-cong (s .into-ok i q) (∘-cong (s .inside-ok (inj₁ w) q) (s .into-ok i (inj₁ w))))
            (≈-sym (Φ-step H (inj₁ w) i q))
  agrees-hide w s .inside-ok p q =
    M.+ₘ-cong (s .inside-ok p q) (∘-cong (s .inside-ok (inj₁ w) q) (s .inside-ok p (inj₁ w)))
  agrees-hide {H = H} w s .tgt-ok t i =
    ≈-trans (M.offset-step {K = K t i} {P = P t}
                         {X = Φ .ap (λ i' → H .into i' (inj₂ root)) i}
                         {Y = H .inside (inj₁ w) (inj₂ root)}
                         {Z = Φ .ap (λ i' → H .into i' (inj₁ w)) i}
              (s .tgt-ok t i) (s .up-ok t w) (s .into-ok i (inj₁ w)))
            (M.+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (Φ-step H (inj₁ w) i (inj₂ root)))))
  agrees-hide {H = H} w s .up-ok t p =
    M.root-step {P = P t} {X = H .inside (inj₁ p) (inj₂ root)}
              {Y = H .inside (inj₁ w) (inj₂ root)} {Z = H .inside (inj₁ p) (inj₁ w)}
      (s .up-ok t p) (s .up-ok t w) (s .inside-ok (inj₁ p) (inj₁ w))

  agrees-hide-all : ∀ {G H} (ws : List Q) → Agrees G H →
                    Agrees (hide-all vw G (map (λ w → blk (inj₁ w)) ws)) (steps H (map inj₁ ws))
  agrees-hide-all []       s = s
  agrees-hide-all (w ∷ ws) s = agrees-hide-all ws (agrees-hide w s)

  -- The entries a rule contributes, before the block's root is hidden. Every edge from the block to
  -- a target leaves the block's root, which here is a matter of the vertex set rather than a lemma.
  record Start (G : Gr vw) (H : St) : Set ℓ where
    field
      into-start   : ∀ i q → G (inp i) (blk q) ≈ Φ .ap (λ i' → H .into i' q) i
      inside-start : ∀ p q → G (blk p) (blk q) ≈ H .inside p q
      tgt-start    : ∀ t i → G (inp i) (tgt t) ≈ K t i
      up-start     : ∀ t → G (blk (inj₂ root)) (tgt t) ≈ P t
      off-start    : ∀ t (p : Q) → G (blk (inj₁ p)) (tgt t) ≈ M.εₘ
      sink         : ∀ q → H .inside (inj₂ root) q ≈ M.εₘ

  open Start public

  agrees-start : ∀ {G H} → Start G H →
                 Agrees (hide vw G (blk (inj₂ root))) (step H (inj₂ root))
  agrees-start {H = H} r .into-ok i q =
    ≈-trans (M.+ₘ-cong (r .into-start i q)
                     (∘-cong (r .inside-start (inj₂ root) q) (r .into-start i (inj₂ root))))
            (≈-sym (Φ-step H (inj₂ root) i q))
  agrees-start r .inside-ok p q =
    M.+ₘ-cong (r .inside-start p q)
            (∘-cong (r .inside-start (inj₂ root) q) (r .inside-start p (inj₂ root)))
  agrees-start {H = H} r .tgt-ok t i =
    ≈-trans (M.+ₘ-cong (r .tgt-start t i)
                     (∘-cong (r .up-start t) (r .into-start i (inj₂ root))))
            (M.+ₘ-cong ≈-refl (∘-cong₂ (≈-sym unchanged)))
    where
    unchanged : Φ .ap (λ i' → step H (inj₂ root) .into i' (inj₂ root)) i
                ≈ Φ .ap (λ i' → H .into i' (inj₂ root)) i
    unchanged =
      ≈-trans (Φ-step H (inj₂ root) i (inj₂ root))
              (≈-trans (M.+ₘ-cong ≈-refl (∘-cong₁ (r .sink (inj₂ root))))
                       (M.absorb₁ (Φ .ap (λ i' → H .into i' (inj₂ root)) i)
                               (Φ .ap (λ i' → H .into i' (inj₂ root)) i)))
  agrees-start {H = H} r .up-ok t p =
    ≈-trans (M.+ₘ-cong (r .off-start t p)
                     (∘-cong (r .up-start t) (r .inside-start (inj₁ p) (inj₂ root))))
    (≈-trans (M.+ₘ-lunit (P t ∘ H .inside (inj₁ p) (inj₂ root)))
             (∘-cong₂ (≈-sym unchanged)))
    where
    unchanged : step H (inj₂ root) .inside (inj₁ p) (inj₂ root)
                ≈ H .inside (inj₁ p) (inj₂ root)
    unchanged =
      ≈-trans (M.+ₘ-cong ≈-refl (∘-cong₁ (r .sink (inj₂ root))))
              (M.absorb₁ (H .inside (inj₁ p) (inj₂ root)) (H .inside (inj₁ p) (inj₂ root)))

-- Rows out of vertices that have no entries into the hidden set survive hiding.
module Behind
  {V : Set ℓ} (vw : V → ℕ)
  {W : Set ℓ} (hid : W → V)
  {S : Set ℓ} (src : S → V)
  {T : Set ℓ} (col : T → V)
  (B : (s : S) (t : T) → M.Matrix (vw (col t)) (vw (src s)))
  where

  record Keeps (G : Gr vw) : Set ℓ where
    field
      keeps : ∀ s t → G (src s) (col t) ≈ B s t
      blind : ∀ s w → G (src s) (hid w) ≈ M.εₘ

  open Keeps public

  keeps-hide : ∀ {G} (w : W) → Keeps G → Keeps (hide vw G (hid w))
  keeps-hide {G} w k .keeps s t =
    ≈-trans (M.+ₘ-cong (k .keeps s t) (∘-cong₂ (k .blind s w)))
            (M.absorb₂ (B s t) (G (hid w) (col t)))
  keeps-hide {G} w k .blind s w' =
    ≈-trans (M.+ₘ-cong (k .blind s w') (∘-cong₂ (k .blind s w)))
            (M.absorb₂ M.εₘ (G (hid w) (hid w')))

  keeps-hide-all : ∀ {G} {W' : Set ℓ} (f : W' → W) (ws : List W') →
                   Keeps G → Keeps (hide-all vw G (map (λ w → hid (f w)) ws))
  keeps-hide-all f []       k = k
  keeps-hide-all f (w ∷ ws) k = keeps-hide-all f ws (keeps-hide (f w) k)

map-map : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (g : B → C) (f : A → B) (xs : List A) →
          map g (map f xs) ≡ map (λ x → g (f x)) xs
map-map g f []       = ≡-refl
map-map g f (x ∷ xs) = ≡-cong (g (f x) ∷_) (map-map g f xs)

map-++ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (xs ys : List A) →
         map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = ≡-refl
map-++ f (x ∷ xs) ys = ≡-cong (f x ∷_) (map-++ f xs ys)

-- Hiding a block's own vertices, its root first, computes its collapse: the root has no outgoing
-- entries, so hiding it changes nothing.
module _ {Inp : Set ℓ} {iw : Inp → ℕ} {n : ℕ} (B : Block Inp iw n) where

  root-row : ∀ y → gr B (inj₂ (inj₂ root)) y ≈ M.εₘ
  root-row (inj₁ _) = ≈-refl {f = M.εₘ}
  root-row (inj₂ _) = ≈-refl {f = M.εₘ}

  hide-qs⁺ : ∀ (i : Inp) →
             hide-all (vw B) (gr B) (map inj₂ (qs⁺ B)) (inj₁ i) (inj₂ (inj₂ root))
             ≈ collapse B i
  hide-qs⁺ i =
    ≈-trans (≈-of-≡ (≡-cong (λ l → hide-all (vw B) (gr B) l (inj₁ i) (inj₂ (inj₂ root)))
                            (≡-cong (inj₂ (inj₂ root) ∷_) (map-map inj₂ inj₁ (Block.qs B)))))
            (hide-all-cong (vw B) (map (λ q → inj₂ (inj₁ q)) (Block.qs B))
                           (hide-sink (vw B) (gr B) (inj₂ (inj₂ root)) root-row)
                           (inj₁ i) (inj₂ (inj₂ root)))

-- Two blocks in sequence: the second block's inputs are supplied by the conclusion's inputs
-- through route and by the first block's root through link, and the conclusion's root is fed by
-- Columns into vertices that the hidden set has no entries into survive hiding.
module Frozen
  {V : Set ℓ} (vw : V → ℕ)
  {W : Set ℓ} (hid : W → V)
  {S : Set ℓ} (src : S → V)
  {T : Set ℓ} (col : T → V)
  (B : (s : S) (t : T) → M.Matrix (vw (col t)) (vw (src s)))
  where

  record Keeps (G : Gr vw) : Set ℓ where
    field
      keeps : ∀ s t → G (src s) (col t) ≈ B s t
      blind : ∀ w t → G (hid w) (col t) ≈ M.εₘ

  open Keeps public

  keeps-hide : ∀ {G} (w : W) → Keeps G → Keeps (hide vw G (hid w))
  keeps-hide {G} w k .keeps s t =
    ≈-trans (M.+ₘ-cong (k .keeps s t) (∘-cong₁ (k .blind w t)))
            (M.absorb₁ (B s t) (G (src s) (hid w)))
  keeps-hide {G} w k .blind w' t =
    ≈-trans (M.+ₘ-cong (k .blind w' t) (∘-cong₁ (k .blind w t)))
            (M.absorb₁ M.εₘ (G (hid w') (hid w)))

  keeps-hide-all : ∀ {G} {W' : Set ℓ} (f : W' → W) (ws : List W') →
                   Keeps G → Keeps (hide-all vw G (map (λ w → hid (f w)) ws))
  keeps-hide-all f []       k = k
  keeps-hide-all f (w ∷ ws) k = keeps-hide-all f ws (keeps-hide (f w) k)

-- A rule with no premises: the root and the inputs, and nothing between.
module Leaf
  {Inp : Set ℓ} {iw : Inp → ℕ} {n : ℕ} (out-root : (i : Inp) → M.Matrix n (iw i))
  where

  E : Block Inp iw n
  E .Block.Q = Void
  E .Block.qw ()
  E .Block.qs = []
  E .Block.into i ()
  E .Block.inside ()
  E .Block.out = out-root
  E .Block.up ()

  agree : ∀ i → collapse E i ≈ out-root i
  agree i = ≈-refl {f = out-root i}

-- A rule with one premise: the conclusion's root is the premise's root through up-root, offset by
-- out-root, and the premise's inputs are the conclusion's through route.
module One
  {Inp : Set ℓ} {iw : Inp → ℕ}
  {Inp' : Set ℓ} {iw' : Inp' → ℕ} {n₀ : ℕ} (B : Block Inp' iw' n₀)
  {n : ℕ}
  (route : Linear iw' iw)
  (out-root : (i : Inp) → M.Matrix n (iw i))
  (up-root : M.Matrix n n₀)
  where

  E : Block Inp iw n
  E .Block.Q = Q⁺ B
  E .Block.qw = qw⁺ B
  E .Block.qs = qs⁺ B
  E .Block.into i q = route .ap (λ i' → into⁺ B i' q) i
  E .Block.inside = inside⁺ B
  E .Block.out = out-root
  E .Block.up (inj₁ _) = M.εₘ
  E .Block.up (inj₂ _) = up-root

  private
    b : Q⁺ B → V E
    b q = inj₂ (inj₁ q)

    er : V E
    er = inj₂ (inj₂ root)

    module S = Sweep (vw E) inj₁ b (λ (_ : Root) → er) route (λ _ → up-root) (λ _ → out-root)

    H⁰ : S.St
    H⁰ .S.into i' q = into⁺ B i' q
    H⁰ .S.inside p q = inside⁺ B p q

    start : S.Start (gr E) H⁰
    start .S.into-start i q = ≈-refl
    start .S.inside-start p q = ≈-refl
    start .S.tgt-start _ i = ≈-refl {f = out-root i}
    start .S.up-start _ = ≈-refl {f = up-root}
    start .S.off-start _ p = ≈-refl {f = M.εₘ}
    start .S.sink q = ≈-refl {f = M.εₘ}

    H : S.St
    H = S.steps (S.step H⁰ (inj₂ root)) (map inj₁ (Block.qs B))

    done : S.Agrees (hide-all (vw E) (hide (vw E) (gr E) (b (inj₂ root)))
                              (map (λ w → b (inj₁ w)) (Block.qs B))) H
    done = S.agrees-hide-all (Block.qs B) (S.agrees-start start)

    prem : Gr (vw B) → S.St
    prem G .S.into i' q = G (inj₁ i') (inj₂ q)
    prem G .S.inside p q = G (inj₂ p) (inj₂ q)

    κ : ∀ i' → H .S.into i' (inj₂ root) ≈ collapse B i'
    κ i' =
      ≈-trans (≈-of-≡ (≡-cong (λ H' → H' .S.into i' (inj₂ root))
                              (S.folds prem inj₂ (hide (vw B)) (λ G w → ≡-refl)
                                       (qs⁺ B) (gr B))))
              (hide-qs⁺ B i')

    plumb : ∀ i → collapse E i
                  ≡ hide-all (vw E) (hide (vw E) (gr E) (b (inj₂ root)))
                             (map (λ w → b (inj₁ w)) (Block.qs B)) (inj₁ i) er
    plumb i = ≡-cong (λ l → hide-all (vw E) (gr E) l (inj₁ i) er)
                     (≡-cong (b (inj₂ root) ∷_) (map-map b inj₁ (Block.qs B)))

  agree : ∀ i → collapse E i ≈ (out-root i M.+ₘ (up-root ∘ route .ap (collapse B) i))
  agree i =
    ≈-trans (≈-of-≡ (plumb i))
            (≈-trans (done .S.tgt-ok root i)
                     (M.+ₘ-cong ≈-refl (∘-cong₂ (route .ap-cong κ i))))

-- Two premises in sequence: each reaches the conclusion's inputs through its own routing, and the
-- second also reaches the first premise's root through link. Both roots feed the conclusion's.
module Seq
  {Inp : Set ℓ} {iw : Inp → ℕ}
  {Inp₁ : Set ℓ} {iw₁ : Inp₁ → ℕ} {n₁ : ℕ} (B₁ : Block Inp₁ iw₁ n₁)
  {Inp₂ : Set ℓ} {iw₂ : Inp₂ → ℕ} {n₂ : ℕ} (B₂ : Block Inp₂ iw₂ n₂)
  {n : ℕ}
  (route₁ : Linear iw₁ iw)
  (route₂ : Linear iw₂ iw)
  (link : Link iw₂ n₁)
  (out-root : (i : Inp) → M.Matrix n (iw i))
  (up₁ : M.Matrix n n₁)
  (up₂ : M.Matrix n n₂)
  where

  private
    qs₁ = Block.qs B₁
    qs₂ = Block.qs B₂

    upE : (s : Q⁺ B₂) → M.Matrix n (qw⁺ B₂ s)
    upE (inj₁ _) = M.εₘ
    upE (inj₂ _) = up₂

  E : Block Inp iw n
  E .Block.Q = Q⁺ B₁ ⊎ Q⁺ B₂
  E .Block.qw = [ qw⁺ B₁ , qw⁺ B₂ ]
  E .Block.qs = map inj₁ (qs⁺ B₁) ++ map inj₂ (qs⁺ B₂)
  E .Block.into i (inj₁ q) = route₁ .ap (λ i' → into⁺ B₁ i' q) i
  E .Block.into i (inj₂ q) = route₂ .ap (λ i' → into⁺ B₂ i' q) i
  E .Block.inside (inj₁ p)        (inj₁ q) = inside⁺ B₁ p q
  E .Block.inside (inj₁ (inj₁ p)) (inj₂ q) = M.εₘ
  E .Block.inside (inj₁ (inj₂ _)) (inj₂ q) = link .at (λ i' → into⁺ B₂ i' q)
  E .Block.inside (inj₂ p)        (inj₁ q) = M.εₘ
  E .Block.inside (inj₂ p)        (inj₂ q) = inside⁺ B₂ p q
  E .Block.out = out-root
  E .Block.up (inj₁ (inj₁ p)) = M.εₘ
  E .Block.up (inj₁ (inj₂ _)) = up₁
  E .Block.up (inj₂ s) = upE s

  private
    b1 : Q⁺ B₁ → V E
    b1 q = inj₂ (inj₁ (inj₁ q))

    b2 : Q⁺ B₂ → V E
    b2 q = inj₂ (inj₁ (inj₂ q))

    er : V E
    er = inj₂ (inj₂ root)

    tgt₁ : Q⁺ B₂ ⊎ Root → V E
    tgt₁ (inj₁ q) = b2 q
    tgt₁ (inj₂ _) = er

    P₁ : (t : Q⁺ B₂ ⊎ Root) → M.Matrix (vw E (tgt₁ t)) n₁
    P₁ (inj₁ q) = link .at (λ i' → into⁺ B₂ i' q)
    P₁ (inj₂ _) = up₁

    K₁ : (t : Q⁺ B₂ ⊎ Root) (i : Inp) → M.Matrix (vw E (tgt₁ t)) (iw i)
    K₁ (inj₁ q) i = route₂ .ap (λ i' → into⁺ B₂ i' q) i
    K₁ (inj₂ _) i = out-root i

    module S1 = Sweep (vw E) inj₁ b1 tgt₁ route₁ P₁ K₁

    H₁⁰ : S1.St
    H₁⁰ .S1.into i q = into⁺ B₁ i q
    H₁⁰ .S1.inside p q = inside⁺ B₁ p q

    start₁ : S1.Start (gr E) H₁⁰
    start₁ .S1.into-start i q = ≈-refl
    start₁ .S1.inside-start p q = ≈-refl
    start₁ .S1.tgt-start (inj₁ q) i = ≈-refl
    start₁ .S1.tgt-start (inj₂ _) i = ≈-refl {f = out-root i}
    start₁ .S1.up-start (inj₁ q) = ≈-refl
    start₁ .S1.up-start (inj₂ _) = ≈-refl {f = up₁}
    start₁ .S1.off-start (inj₁ q) p = ≈-refl {f = M.εₘ}
    start₁ .S1.off-start (inj₂ _) p = ≈-refl {f = M.εₘ}
    start₁ .S1.sink q = ≈-refl {f = M.εₘ}

    G₁ : Gr (vw E)
    G₁ = hide-all (vw E) (hide (vw E) (gr E) (b1 (inj₂ root))) (map (λ w → b1 (inj₁ w)) qs₁)

    H₁ : S1.St
    H₁ = S1.steps (S1.step H₁⁰ (inj₂ root)) (map inj₁ qs₁)

    done₁ : S1.Agrees G₁ H₁
    done₁ = S1.agrees-hide-all qs₁ (S1.agrees-start start₁)

    prem₁ : Gr (vw B₁) → S1.St
    prem₁ G .S1.into i q = G (inj₁ i) (inj₂ q)
    prem₁ G .S1.inside p q = G (inj₂ p) (inj₂ q)

    κ₁ : ∀ i → H₁ .S1.into i (inj₂ root) ≈ collapse B₁ i
    κ₁ i =
      ≈-trans (≈-of-≡ (≡-cong (λ H → H .S1.into i (inj₂ root))
                              (S1.folds prem₁ inj₂ (hide (vw B₁)) (λ G w → ≡-refl)
                                        (qs⁺ B₁) (gr B₁))))
              (hide-qs⁺ B₁ i)

  -- The second premise's inputs once the first premise has collapsed.
  Φ₂ : Linear iw₂ iw
  Φ₂ .ap f i = route₂ .ap f i M.+ₘ (link .at f ∘ route₁ .ap (collapse B₁) i)
  Φ₂ .ap-+ f g i =
    ≈-trans (M.+ₘ-cong (route₂ .ap-+ f g i)
                       (≈-trans (∘-cong₁ (link .at-+ f g))
                                (M.comp-bilinear₁ (link .at f) (link .at g)
                                                  (route₁ .ap (collapse B₁) i))))
            (M.+ₘ-interchange (route₂ .ap f i) (route₂ .ap g i)
                              (link .at f ∘ route₁ .ap (collapse B₁) i)
                              (link .at g ∘ route₁ .ap (collapse B₁) i))
  Φ₂ .ap-∘ X f i =
    ≈-trans (M.+ₘ-cong (route₂ .ap-∘ X f i)
                       (≈-trans (∘-cong₁ (link .at-∘ X f))
                                (assoc X (link .at f) (route₁ .ap (collapse B₁) i))))
            (≈-sym (M.comp-bilinear₂ X (route₂ .ap f i)
                                     (link .at f ∘ route₁ .ap (collapse B₁) i)))
  Φ₂ .ap-cong e i = M.+ₘ-cong (route₂ .ap-cong e i) (∘-cong₁ (link .at-cong e))

  private
    P₂ : (t : Root) → M.Matrix n n₂
    P₂ _ = up₂

    K₂ : (t : Root) (i : Inp) → M.Matrix n (iw i)
    K₂ _ i = out-root i M.+ₘ (up₁ ∘ route₁ .ap (collapse B₁) i)

    module S2 = Sweep (vw E) inj₁ b2 (λ (_ : Root) → er) Φ₂ P₂ K₂

    col₂ : Q⁺ B₂ ⊎ Root → V E
    col₂ (inj₁ q) = b2 q
    col₂ (inj₂ _) = er

    Bh : (s : Q⁺ B₂) (t : Q⁺ B₂ ⊎ Root) → M.Matrix (vw E (col₂ t)) (qw⁺ B₂ s)
    Bh s (inj₁ q) = inside⁺ B₂ s q
    Bh s (inj₂ _) = upE s

    module Bd = Behind (vw E) b1 b2 col₂ Bh

    keeps₀ : Bd.Keeps (gr E)
    keeps₀ .Bd.keeps s (inj₁ q) = ≈-refl
    keeps₀ .Bd.keeps s (inj₂ _) = ≈-refl {f = upE s}
    keeps₀ .Bd.blind s w = ≈-refl {f = M.εₘ}

    keeps₁ : Bd.Keeps G₁
    keeps₁ = Bd.keeps-hide-all inj₁ qs₁ (Bd.keeps-hide (inj₂ root) keeps₀)

    H₂⁰ : S2.St
    H₂⁰ .S2.into i' q = into⁺ B₂ i' q
    H₂⁰ .S2.inside p q = inside⁺ B₂ p q

    start₂ : S2.Start G₁ H₂⁰
    start₂ .S2.into-start i q =
      ≈-trans (done₁ .S1.tgt-ok (inj₁ q) i)
              (M.+ₘ-cong ≈-refl (∘-cong₂ (route₁ .ap-cong κ₁ i)))
    start₂ .S2.inside-start p q = keeps₁ .Bd.keeps p (inj₁ q)
    start₂ .S2.tgt-start _ i =
      ≈-trans (done₁ .S1.tgt-ok (inj₂ root) i)
              (M.+ₘ-cong ≈-refl (∘-cong₂ (route₁ .ap-cong κ₁ i)))
    start₂ .S2.up-start _ = keeps₁ .Bd.keeps (inj₂ root) (inj₂ root)
    start₂ .S2.off-start _ p = keeps₁ .Bd.keeps (inj₁ p) (inj₂ root)
    start₂ .S2.sink q = ≈-refl {f = M.εₘ}

    G₂ : Gr (vw E)
    G₂ = hide-all (vw E) (hide (vw E) G₁ (b2 (inj₂ root))) (map (λ w → b2 (inj₁ w)) qs₂)

    H₂ : S2.St
    H₂ = S2.steps (S2.step H₂⁰ (inj₂ root)) (map inj₁ qs₂)

    done₂ : S2.Agrees G₂ H₂
    done₂ = S2.agrees-hide-all qs₂ (S2.agrees-start start₂)

    prem₂ : Gr (vw B₂) → S2.St
    prem₂ G .S2.into i' q = G (inj₁ i') (inj₂ q)
    prem₂ G .S2.inside p q = G (inj₂ p) (inj₂ q)

    κ₂ : ∀ i' → H₂ .S2.into i' (inj₂ root) ≈ collapse B₂ i'
    κ₂ i' =
      ≈-trans (≈-of-≡ (≡-cong (λ H → H .S2.into i' (inj₂ root))
                              (S2.folds prem₂ inj₂ (hide (vw B₂)) (λ G w → ≡-refl)
                                        (qs⁺ B₂) (gr B₂))))
              (hide-qs⁺ B₂ i')

    lst : map (λ q → inj₂ {A = Inp} (inj₁ q)) (Block.qs E)
          ≡ (b1 (inj₂ root) ∷ map (λ w → b1 (inj₁ w)) qs₁)
            ++ (b2 (inj₂ root) ∷ map (λ w → b2 (inj₁ w)) qs₂)
    lst =
      ≡-trans (map-++ (λ q → inj₂ (inj₁ q)) (map inj₁ (qs⁺ B₁)) (map inj₂ (qs⁺ B₂)))
              (≡-cong₂ _++_
                (≡-trans (map-map (λ q → inj₂ (inj₁ q)) inj₁ (qs⁺ B₁))
                         (≡-cong (b1 (inj₂ root) ∷_) (map-map b1 inj₁ qs₁)))
                (≡-trans (map-map (λ q → inj₂ (inj₁ q)) inj₂ (qs⁺ B₂))
                         (≡-cong (b2 (inj₂ root) ∷_) (map-map b2 inj₁ qs₂))))

    plumb : ∀ i → collapse E i ≡ G₂ (inj₁ i) er
    plumb i =
      ≡-trans (≡-cong (λ l → hide-all (vw E) (gr E) l (inj₁ i) er) lst)
              (≡-cong (λ G → G (inj₁ i) er)
                      (hide-all-++ (vw E) (gr E)
                        (b1 (inj₂ root) ∷ map (λ w → b1 (inj₁ w)) qs₁)
                        (b2 (inj₂ root) ∷ map (λ w → b2 (inj₁ w)) qs₂)))

  agree : ∀ i → collapse E i
                ≈ ((out-root i M.+ₘ (up₁ ∘ route₁ .ap (collapse B₁) i))
                   M.+ₘ (up₂ ∘ Φ₂ .ap (collapse B₂) i))
  agree i =
    ≈-trans (≈-of-≡ (plumb i))
            (≈-trans (done₂ .S2.tgt-ok root i)
                     (M.+ₘ-cong ≈-refl (∘-cong₂ (Φ₂ .ap-cong κ₂ i))))

-- A single premise evaluated in the conclusion's environment.
module Same
  {Inp : Set ℓ} {iw : Inp → ℕ} {n₀ n : ℕ} (B : Block Inp iw n₀)
  (out-root : (i : Inp) → M.Matrix n (iw i))
  (up-root : M.Matrix n n₀)
  where

  private
    module O = One B (id-linear iw) out-root up-root

  E : Block Inp iw n
  E = O.E

  agree : ∀ i → collapse E i ≈ (out-root i M.+ₘ (up-root ∘ collapse B i))
  agree = O.agree

-- Two premises with no entries between them, both feeding the conclusion's root.
module Par
  {Inp : Set ℓ} {iw : Inp → ℕ}
  {Inp₁ : Set ℓ} {iw₁ : Inp₁ → ℕ} {n₁ : ℕ} (B₁ : Block Inp₁ iw₁ n₁)
  {Inp₂ : Set ℓ} {iw₂ : Inp₂ → ℕ} {n₂ : ℕ} (B₂ : Block Inp₂ iw₂ n₂)
  {n : ℕ}
  (route₁ : Linear iw₁ iw)
  (route₂ : Linear iw₂ iw)
  (out-root : (i : Inp) → M.Matrix n (iw i))
  (up₁ : M.Matrix n n₁)
  (up₂ : M.Matrix n n₂)
  where

  private
    module S = Seq B₁ B₂ route₁ route₂ (no-link iw₂ n₁) out-root up₁ up₂

  E : Block Inp iw n
  E = S.E

  agree : ∀ i → collapse E i
                ≈ ((out-root i M.+ₘ (up₁ ∘ route₁ .ap (collapse B₁) i))
                   M.+ₘ (up₂ ∘ route₂ .ap (collapse B₂) i))
  agree i =
    ≈-trans (S.agree i)
            (M.+ₘ-cong ≈-refl
                       (∘-cong₂ (M.absorb₁ (route₂ .ap (collapse B₂) i)
                                           (route₁ .ap (collapse B₁) i))))
