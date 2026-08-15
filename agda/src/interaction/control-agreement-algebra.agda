{-# OPTIONS --prop --postfix-projections --safe #-}

open import signature using (Signature)
open import primitives using (Primitives)
open import commutative-semiring using (CommutativeSemiring)
import matrix
import two

-- Matrix algebra for the agreement proofs over the control-source graph, together with the lemmas
-- that read off a derivation's root: its row is zero, hiding it changes nothing, and an edge out of
-- a non-root path is zero. Stated for each of the three path families.
module interaction.control-agreement-algebra {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-operational.evaluation Sig two.semiring 𝒫 two.I
  using (Val; Env; width; width-env; width-subst; lookup; bool→val; ctrl-row; proj-var;
         brel-deps)
open Val
open Env
open import language-operational.control Sig two.semiring 𝒫 two.I
open import interaction.control-path Sig 𝒫
open import interaction.control-graph Sig 𝒫
open import interaction.control-hide Sig 𝒫

private
  module M = matrix.Mat two.semiring

open CommutativeSemiring two.semiring
  using (+-comm; +-cong; +-lunit; +-assoc; +-interchange; refl; trans)
import Data.Bool as Bool
import Data.Nat as Nat
open import Data.List using (List; []; _∷_; _++_; map)
open import every using (Every; []; _∷_)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Relation.Unary.All.Properties using (map⁺; ++⁺)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
  renaming (refl to ≡-refl; cong to ≡-cong; trans to ≡-trans; sym to ≡-sym)
open import prop-setoid using () renaming (_⇒_ to _⇒ₛ_)
open _⇒ₛ_ using (func)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤')
open import Level using (0ℓ)
open import categories using (Category; HasTerminal)
open Category M.cat
  using (_⇒_; _∘_; _≈_; ∘-cong; ∘-cong₁; ∘-cong₂; assoc; id-left; id-right;
         ≈-refl; ≈-sym; ≈-trans; isEquiv)
  renaming (id to idm)
open HasTerminal M.terminal using (to-terminal)

+ₘ-runit : ∀ {m n} (R : M.Matrix m n) → (R M.+ₘ M.εₘ) ≈ R
+ₘ-runit R i j = +-comm {x = R i j} {y = two.O}

+ₘ-lunit : ∀ {m n} (R : M.Matrix m n) → (M.εₘ M.+ₘ R) ≈ R
+ₘ-lunit R i j = +-lunit {x = R i j}

+ₘ-cong : ∀ {m n} {R R' S S' : M.Matrix m n} →
          R ≈ R' → S ≈ S' → (R M.+ₘ S) ≈ (R' M.+ₘ S')
+ₘ-cong h k i j = +-cong (h i j) (k i j)

+ₘ-comm : ∀ {m n} (R S : M.Matrix m n) → (R M.+ₘ S) ≈ (S M.+ₘ R)
+ₘ-comm R S i j = +-comm {x = R i j} {y = S i j}

+ₘ-assoc : ∀ {m n} (X Y Z : M.Matrix m n) → ((X M.+ₘ Y) M.+ₘ Z) ≈ (X M.+ₘ (Y M.+ₘ Z))
+ₘ-assoc X Y Z i j = +-assoc {x = X i j} {y = Y i j} {z = Z i j}

+ₘ-interchangeₘ : ∀ {m n} (P Q R S : M.Matrix m n) →
                  ((P M.+ₘ Q) M.+ₘ (R M.+ₘ S)) ≈ ((P M.+ₘ R) M.+ₘ (Q M.+ₘ S))
+ₘ-interchangeₘ P Q R S i j =
  +-interchange {w = P i j} {x = Q i j} {y = R i j} {z = S i j}

+ₘ-swap : ∀ {m n} (A C B : M.Matrix m n) → ((A M.+ₘ C) M.+ₘ B) ≈ ((A M.+ₘ B) M.+ₘ C)
+ₘ-swap A C B i j =
  trans (+-cong (+-comm {x = A i j} {y = C i j}) (refl {x = B i j}))
        (trans (+-assoc {x = C i j} {y = A i j} {z = B i j})
               (+-comm {x = C i j} {y = A i j two.⊔ B i j}))

+ₘ-swap-mid : ∀ {m n} (X Y Z : M.Matrix m n) → (X M.+ₘ (Y M.+ₘ Z)) ≈ (Y M.+ₘ (X M.+ₘ Z))
+ₘ-swap-mid X Y Z =
  ≈-trans (≈-sym (+ₘ-assoc X Y Z))
          (≈-trans (+ₘ-cong (+ₘ-comm X Y) ≈-refl) (+ₘ-assoc Y X Z))

-- A composite with a zero factor drops out of a sum.
absorb : ∀ {m n k} (R : M.Matrix m n) (S : M.Matrix k n) → (R M.+ₘ (M.εₘ ∘ S)) ≈ R
absorb R S i j = trans (+-cong (refl {x = R i j}) (M.comp-bilinear-ε₁ S i j))
                       (+-comm {x = R i j} {y = two.O})

absorb-r : ∀ {m n k} (R : M.Matrix m n) (S : M.Matrix m k) → (R M.+ₘ (S ∘ M.εₘ)) ≈ R
absorb-r R S = ≈-trans (+ₘ-cong ≈-refl (M.comp-bilinear-ε₂ S)) (+ₘ-runit R)

≈-of-≡ : ∀ {m n} {X Y : M.Matrix m n} → X ≡ Y → X ≈ Y
≈-of-≡ ≡-refl = ≈-refl

-- The root of a graph is a sink: its row is zero.
root-sink : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) (y : Vertex D) →
            graph D (at ε) y ≈ M.εₘ
root-sink (⇓-var x) env i j = refl {x = two.O}
root-sink (⇓-var x) src i j = refl {x = two.O}
root-sink (⇓-var x) (at ε) i j = refl {x = two.O}
root-sink ⇓-unit env i j = refl {x = two.O}
root-sink ⇓-unit src i j = refl {x = two.O}
root-sink ⇓-unit (at ε) i j = refl {x = two.O}
root-sink ⇓-lam env i j = refl {x = two.O}
root-sink ⇓-lam src i j = refl {x = two.O}
root-sink ⇓-lam (at ε) i j = refl {x = two.O}
root-sink (⇓-inl D) env i j = refl {x = two.O}
root-sink (⇓-inl D) src i j = refl {x = two.O}
root-sink (⇓-inl D) (at ε) i j = refl {x = two.O}
root-sink (⇓-inl D) (at (inl q)) i j = refl {x = two.O}
root-sink (⇓-inr D) env i j = refl {x = two.O}
root-sink (⇓-inr D) src i j = refl {x = two.O}
root-sink (⇓-inr D) (at ε) i j = refl {x = two.O}
root-sink (⇓-inr D) (at (inr q)) i j = refl {x = two.O}
root-sink (⇓-fst D) env i j = refl {x = two.O}
root-sink (⇓-fst D) src i j = refl {x = two.O}
root-sink (⇓-fst D) (at ε) i j = refl {x = two.O}
root-sink (⇓-fst D) (at (fst q)) i j = refl {x = two.O}
root-sink (⇓-snd D) env i j = refl {x = two.O}
root-sink (⇓-snd D) src i j = refl {x = two.O}
root-sink (⇓-snd D) (at ε) i j = refl {x = two.O}
root-sink (⇓-snd D) (at (snd q)) i j = refl {x = two.O}
root-sink (⇓-roll D) env i j = refl {x = two.O}
root-sink (⇓-roll D) src i j = refl {x = two.O}
root-sink (⇓-roll D) (at ε) i j = refl {x = two.O}
root-sink (⇓-roll D) (at (roll q)) i j = refl {x = two.O}
root-sink (⇓-case-l D₁ D₂) env i j = refl {x = two.O}
root-sink (⇓-case-l D₁ D₂) src i j = refl {x = two.O}
root-sink (⇓-case-l D₁ D₂) (at ε) i j = refl {x = two.O}
root-sink (⇓-case-l D₁ D₂) (at (case-l₁ q)) i j = refl {x = two.O}
root-sink (⇓-case-l D₁ D₂) (at (case-l₂ q)) i j = refl {x = two.O}
root-sink (⇓-case-r D₁ D₂) env i j = refl {x = two.O}
root-sink (⇓-case-r D₁ D₂) src i j = refl {x = two.O}
root-sink (⇓-case-r D₁ D₂) (at ε) i j = refl {x = two.O}
root-sink (⇓-case-r D₁ D₂) (at (case-r₁ q)) i j = refl {x = two.O}
root-sink (⇓-case-r D₁ D₂) (at (case-r₂ q)) i j = refl {x = two.O}
root-sink (⇓-pair D₁ D₂) env i j = refl {x = two.O}
root-sink (⇓-pair D₁ D₂) src i j = refl {x = two.O}
root-sink (⇓-pair D₁ D₂) (at ε) i j = refl {x = two.O}
root-sink (⇓-pair D₁ D₂) (at (pair₁ q)) i j = refl {x = two.O}
root-sink (⇓-pair D₁ D₂) (at (pair₂ q)) i j = refl {x = two.O}
root-sink (⇓-app D₁ D₂ D₃) env i j = refl {x = two.O}
root-sink (⇓-app D₁ D₂ D₃) src i j = refl {x = two.O}
root-sink (⇓-app D₁ D₂ D₃) (at ε) i j = refl {x = two.O}
root-sink (⇓-app D₁ D₂ D₃) (at (app₁ q)) i j = refl {x = two.O}
root-sink (⇓-app D₁ D₂ D₃) (at (app₂ q)) i j = refl {x = two.O}
root-sink (⇓-app D₁ D₂ D₃) (at (app₃ q)) i j = refl {x = two.O}
root-sink (⇓-bop D) env i j = refl {x = two.O}
root-sink (⇓-bop D) src i j = refl {x = two.O}
root-sink (⇓-bop D) (at ε) i j = refl {x = two.O}
root-sink (⇓-bop D) (at (bop q)) i j = refl {x = two.O}
root-sink (⇓-brel D) env i j = refl {x = two.O}
root-sink (⇓-brel D) src i j = refl {x = two.O}
root-sink (⇓-brel D) (at ε) i j = refl {x = two.O}
root-sink (⇓-brel D) (at (brel q)) i j = refl {x = two.O}
root-sink (⇓-fold D₁ D₂) env i j = refl {x = two.O}
root-sink (⇓-fold D₁ D₂) src i j = refl {x = two.O}
root-sink (⇓-fold D₁ D₂) (at ε) i j = refl {x = two.O}
root-sink (⇓-fold D₁ D₂) (at (fold₁ q)) i j = refl {x = two.O}
root-sink (⇓-fold D₁ D₂) (at (fold₂ q)) i j = refl {x = two.O}

-- Hiding the root changes nothing, its row being zero.
hide-root : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) (x y : Vertex D) →
            hide (graph D) (at ε) x y ≈ graph D x y
hide-root D x y =
  ≈-trans (+ₘ-cong ≈-refl (∘-cong (root-sink D y) ≈-refl))
          (absorb (graph D x y) (graph D x (at ε)))

-- The two initial hides, in terms of the underlying graph's entries.
hide-hide-root : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) (r x y : Vertex D) →
                 hide (hide (graph D) (at ε)) r x y
                 ≈ (graph D x y M.+ₘ (graph D r y ∘ graph D x r))
hide-hide-root D r x y = +ₘ-cong (hide-root D x y) (∘-cong (hide-root D r y) (hide-root D x r))

-- Clean a zero direct entry against a routed one, and restore the premise's hidden root.
into-hidden : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) {m}
              (P : M.Matrix m (width v)) (x : Vertex D) →
              (M.εₘ M.+ₘ (P ∘ graph D x (at ε))) ≈ (P ∘ hide (graph D) (at ε) x (at ε))
into-hidden D P x =
  ≈-trans (+ₘ-lunit (P ∘ graph D x (at ε))) (∘-cong₂ (≈-sym (hide-root D x (at ε))))

-- The same in the presence of a constant offset.
into-hidden-off : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) {m} (x : Vertex D)
                  (K : M.Matrix m (vertex-width x)) (P : M.Matrix m (width v)) →
                  (K M.+ₘ (P ∘ graph D x (at ε))) ≈ (K M.+ₘ (P ∘ hide (graph D) (at ε) x (at ε)))
into-hidden-off D x K P = +ₘ-cong ≈-refl (∘-cong₂ (≈-sym (hide-root D x (at ε))))

-- Off the root, a root edge contributes nothing.
edge-off : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} {m}
           (S : M.Matrix m (width v)) (p : Path D) → is-ε p ≡ Bool.false →
           edge S p ≈ M.εₘ
edge-off S ε ()
edge-off S (inl p) np i j = refl {x = two.O}
edge-off S (inr p) np i j = refl {x = two.O}
edge-off S (case-l₁ p) np i j = refl {x = two.O}
edge-off S (case-l₂ p) np i j = refl {x = two.O}
edge-off S (case-r₁ p) np i j = refl {x = two.O}
edge-off S (case-r₂ p) np i j = refl {x = two.O}
edge-off S (pair₁ p) np i j = refl {x = two.O}
edge-off S (pair₂ p) np i j = refl {x = two.O}
edge-off S (fst p) np i j = refl {x = two.O}
edge-off S (snd p) np i j = refl {x = two.O}
edge-off S (app₁ p) np i j = refl {x = two.O}
edge-off S (app₂ p) np i j = refl {x = two.O}
edge-off S (app₃ p) np i j = refl {x = two.O}
edge-off S (roll p) np i j = refl {x = two.O}
edge-off S (fold₁ p) np i j = refl {x = two.O}
edge-off S (bop p) np i j = refl {x = two.O}
edge-off S (brel p) np i j = refl {x = two.O}
edge-off S (fold₂ p) np i j = refl {x = two.O}

-- Interior paths are never the root.
interior-not-root : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) →
                    All (λ p → is-ε p ≡ Bool.false) (interior D)
interior-not-root (⇓-var x) = []
interior-not-root ⇓-unit = []
interior-not-root ⇓-lam = []
interior-not-root (⇓-inl D) = map⁺ (universal (λ _ → ≡-refl) (paths D))
interior-not-root (⇓-inr D) = map⁺ (universal (λ _ → ≡-refl) (paths D))
interior-not-root (⇓-fst D) = map⁺ (universal (λ _ → ≡-refl) (paths D))
interior-not-root (⇓-snd D) = map⁺ (universal (λ _ → ≡-refl) (paths D))
interior-not-root (⇓-roll D) = map⁺ (universal (λ _ → ≡-refl) (paths D))
interior-not-root (⇓-case-l D₁ D₂) =
  ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths D₁))) (map⁺ (universal (λ _ → ≡-refl) (paths D₂)))
interior-not-root (⇓-case-r D₁ D₂) =
  ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths D₁))) (map⁺ (universal (λ _ → ≡-refl) (paths D₂)))
interior-not-root (⇓-pair D₁ D₂) =
  ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths D₁))) (map⁺ (universal (λ _ → ≡-refl) (paths D₂)))
interior-not-root (⇓-app D₁ D₂ D₃) =
  ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths D₁)))
      (++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths D₂)))
           (map⁺ (universal (λ _ → ≡-refl) (paths D₃))))
interior-not-root (⇓-bop D) = map⁺ (universal (λ _ → ≡-refl) (paths-s D))
interior-not-root (⇓-brel D) = map⁺ (universal (λ _ → ≡-refl) (paths-s D))
interior-not-root (⇓-fold D₁ D₂) =
  ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths D₁))) (map⁺ (universal (λ _ → ≡-refl) (paths-m D₂)))

hide-all-++ : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
              (G : Graph D) (xs ys : List (Vertex D)) →
              hide-all G (xs ++ ys) ≡ hide-all (hide-all G xs) ys
hide-all-++ G []       ys = ≡-refl
hide-all-++ G (x ∷ xs) ys = hide-all-++ (hide G x) xs ys

distrib-root : ∀ {m n k l} (P : M.Matrix m n) (X : M.Matrix n k)
               (Y : M.Matrix n l) (Z : M.Matrix l k) →
               ((P ∘ X) M.+ₘ ((P ∘ Y) ∘ Z)) ≈ (P ∘ (X M.+ₘ (Y ∘ Z)))
distrib-root P X Y Z =
  ≈-trans (+ₘ-cong ≈-refl (assoc P Y Z)) (≈-sym (M.comp-bilinear₂ P X (Y ∘ Z)))

offset-distrib : ∀ {m n l k} (K : M.Matrix m k) (P : M.Matrix m n) (X : M.Matrix n k)
                 (Y : M.Matrix n l) (Z : M.Matrix l k) →
                 ((K M.+ₘ (P ∘ X)) M.+ₘ ((P ∘ Y) ∘ Z)) ≈ (K M.+ₘ (P ∘ (X M.+ₘ (Y ∘ Z))))
offset-distrib K P X Y Z =
  ≈-trans (+ₘ-assoc K (P ∘ X) ((P ∘ Y) ∘ Z)) (+ₘ-cong ≈-refl (distrib-root P X Y Z))

-- One hide step on related entries, root columns distributing through P.
root-step : ∀ {m n l k} {P : M.Matrix m n} {G₁ : M.Matrix m k} {X : M.Matrix n k}
            {G₂ : M.Matrix m l} {Y : M.Matrix n l} {G₃ Z : M.Matrix l k} →
            G₁ ≈ (P ∘ X) → G₂ ≈ (P ∘ Y) → G₃ ≈ Z →
            (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ (P ∘ (X M.+ₘ (Y ∘ Z)))
root-step {P = P} {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c)) (distrib-root P X Y Z)

offset-step : ∀ {m n l k} {K : M.Matrix m k} {P : M.Matrix m n} {G₁ : M.Matrix m k}
              {X : M.Matrix n k} {G₂ : M.Matrix m l} {Y : M.Matrix n l} {G₃ Z : M.Matrix l k} →
              G₁ ≈ (K M.+ₘ (P ∘ X)) → G₂ ≈ (P ∘ Y) → G₃ ≈ Z →
              (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ (K M.+ₘ (P ∘ (X M.+ₘ (Y ∘ Z))))
offset-step {K = K} {P} {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c)) (offset-distrib K P X Y Z)

-- One hide step under a fixed post-composition W.
step-under : ∀ {m l n n'} {W : M.Matrix n n'} {G₁ : M.Matrix m n'} {X : M.Matrix m n}
             {G₂ : M.Matrix m l} {Y : M.Matrix m l} {G₃ : M.Matrix l n'} {Z : M.Matrix l n} →
             G₁ ≈ (X ∘ W) → G₂ ≈ Y → G₃ ≈ (Z ∘ W) →
             (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ ((X M.+ₘ (Y ∘ Z)) ∘ W)
step-under {W = W} {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c))
  (≈-trans (+ₘ-cong ≈-refl (≈-sym (assoc Y Z W))) (≈-sym (M.comp-bilinear₁ X (Y ∘ Z) W)))

-- One hide step under two fixed post-compositions carried side by side, as when a branch's env
-- and source substitutions evolve together.
pair-step : ∀ {m l n n' n''} {W : M.Matrix n' n} {U : M.Matrix n'' n}
            {G₁ : M.Matrix m n} {A : M.Matrix m n'} {B : M.Matrix m n''}
            {G₂ : M.Matrix m l} {Y : M.Matrix m l}
            {G₃ : M.Matrix l n} {Aw : M.Matrix l n'} {Bw : M.Matrix l n''} →
            G₁ ≈ ((A ∘ W) M.+ₘ (B ∘ U)) → G₂ ≈ Y → G₃ ≈ ((Aw ∘ W) M.+ₘ (Bw ∘ U)) →
            (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ (((A M.+ₘ (Y ∘ Aw)) ∘ W) M.+ₘ ((B M.+ₘ (Y ∘ Bw)) ∘ U))
pair-step {W = W} {U = U} {A = A} {B = B} {Y = Y} {Aw = Aw} {Bw = Bw} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c))
  (≈-trans (+ₘ-cong ≈-refl
             (≈-trans (M.comp-bilinear₂ Y (Aw ∘ W) (Bw ∘ U))
                      (+ₘ-cong (≈-sym (assoc Y Aw W)) (≈-sym (assoc Y Bw U)))))
  (≈-trans (+ₘ-interchangeₘ (A ∘ W) (B ∘ U) ((Y ∘ Aw) ∘ W) ((Y ∘ Bw) ∘ U))
           (+ₘ-cong (≈-sym (M.comp-bilinear₁ A (Y ∘ Aw) W))
                    (≈-sym (M.comp-bilinear₁ B (Y ∘ Bw) U)))))

-- The same where the second column is carried unchanged.
pair-step-id : ∀ {m l n n'} {W : M.Matrix n' n}
               {G₁ : M.Matrix m n} {A : M.Matrix m n'} {B : M.Matrix m n}
               {G₂ : M.Matrix m l} {Y : M.Matrix m l}
               {G₃ : M.Matrix l n} {Aw : M.Matrix l n'} {Bw : M.Matrix l n} →
               G₁ ≈ ((A ∘ W) M.+ₘ B) → G₂ ≈ Y → G₃ ≈ ((Aw ∘ W) M.+ₘ Bw) →
               (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ (((A M.+ₘ (Y ∘ Aw)) ∘ W) M.+ₘ (B M.+ₘ (Y ∘ Bw)))
pair-step-id {W = W} {A = A} {B = B} {Y = Y} {Aw = Aw} {Bw = Bw} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c))
  (≈-trans (+ₘ-cong ≈-refl (M.comp-bilinear₂ Y (Aw ∘ W) Bw))
  (≈-trans (+ₘ-interchangeₘ (A ∘ W) B (Y ∘ (Aw ∘ W)) (Y ∘ Bw))
           (+ₘ-cong (≈-trans (+ₘ-cong ≈-refl (≈-sym (assoc Y Aw W)))
                             (≈-sym (M.comp-bilinear₁ A (Y ∘ Aw) W)))
                    ≈-refl)))

-- Operand lists: the S-family analogues of the root and edge lemmas.
root-sink-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
              (D : γ , Ms ⇓s vs [ R ]) (y : VertexS D) → graph-s D (at ε) y ≈ M.εₘ
root-sink-s []       env    i j = refl {x = two.O}
root-sink-s []       src    i j = refl {x = two.O}
root-sink-s []       (at ε) i j = refl {x = two.O}
root-sink-s (D ∷ D₁) env    i j = refl {x = two.O}
root-sink-s (D ∷ D₁) src    i j = refl {x = two.O}
root-sink-s (D ∷ D₁) (at ε) i j = refl {x = two.O}
root-sink-s (D ∷ D₁) (at (hd q)) i j = refl {x = two.O}
root-sink-s (D ∷ D₁) (at (tl q)) i j = refl {x = two.O}

hide-root-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
              (D : γ , Ms ⇓s vs [ R ]) (x y : VertexS D) →
              hide-s (graph-s D) (at ε) x y ≈ graph-s D x y
hide-root-s D x y =
  ≈-trans (+ₘ-cong ≈-refl (∘-cong₁ (root-sink-s D y)))
          (absorb (graph-s D x y) (graph-s D x (at ε)))

hide-hide-root-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
                   (D : γ , Ms ⇓s vs [ R ]) (r x y : VertexS D) →
                   hide-s (hide-s (graph-s D) (at ε)) r x y
                   ≈ (graph-s D x y M.+ₘ (graph-s D r y ∘ graph-s D x r))
hide-hide-root-s D r x y =
  +ₘ-cong (hide-root-s D x y) (∘-cong (hide-root-s D r y) (hide-root-s D x r))

edge-off-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
             {D : γ , Ms ⇓s vs [ R ]} {m}
             (S : M.Matrix m (bases-width is)) (p : PathS D) → is-ε-s p ≡ Bool.false →
             edge-s S p ≈ M.εₘ
edge-off-s S ε ()
edge-off-s S (hd p) np i j = refl {x = two.O}
edge-off-s S (tl p) np i j = refl {x = two.O}

into-hidden-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
                (D : γ , Ms ⇓s vs [ R ]) {m}
                (P : M.Matrix m (bases-width is)) (x : VertexS D) →
                (M.εₘ M.+ₘ (P ∘ graph-s D x (at ε)))
                ≈ (P ∘ hide-s (graph-s D) (at ε) x (at ε))
into-hidden-s D P x =
  ≈-trans (+ₘ-lunit (P ∘ graph-s D x (at ε))) (∘-cong₂ (≈-sym (hide-root-s D x (at ε))))

into-hidden-off-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
                    (D : γ , Ms ⇓s vs [ R ]) {m} (x : VertexS D)
                    (K : M.Matrix m (vertex-width-s x)) (P : M.Matrix m (bases-width is)) →
                    (K M.+ₘ (P ∘ graph-s D x (at ε)))
                    ≈ (K M.+ₘ (P ∘ hide-s (graph-s D) (at ε) x (at ε)))
into-hidden-off-s D x K P = +ₘ-cong ≈-refl (∘-cong₂ (≈-sym (hide-root-s D x (at ε))))

interior-not-root-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
                      (D : γ , Ms ⇓s vs [ R ]) →
                      All (λ p → is-ε-s p ≡ Bool.false) (interior-s D)
interior-not-root-s []       = []
interior-not-root-s (D ∷ D₁) =
  ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths D))) (map⁺ (universal (λ _ → ≡-refl) (paths-s D₁)))

hide-all-s-++ : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
                {D : γ , Ms ⇓s vs [ R ]} (G : GraphS D) (xs ys : List (VertexS D)) →
                hide-all-s G (xs ++ ys) ≡ hide-all-s (hide-all-s G xs) ys
hide-all-s-++ G []       ys = ≡-refl
hide-all-s-++ G (x ∷ xs) ys = hide-all-s-++ (hide-s G x) xs ys

-- The fold-action family: mirrors of the root and edge lemmas.
root-sink-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : Nat.suc (width-env γ) ⇒ width v}
              {v' : Val (σ' [ σr ])} {R' : Nat.suc (width-env γ) ⇒ width v'}
              (D : Map γ s σ' v R v' R') (y : VertexM D) → graph-m D (at ε) y ≈ M.εₘ
root-sink-m (m-rec D₁ D₂) env i j = refl {x = two.O}
root-sink-m (m-rec D₁ D₂) src i j = refl {x = two.O}
root-sink-m (m-rec D₁ D₂) input i j = refl {x = two.O}
root-sink-m (m-rec D₁ D₂) (at ε) i j = refl {x = two.O}
root-sink-m (m-rec D₁ D₂) (at (m-rec₁ q)) i j = refl {x = two.O}
root-sink-m (m-rec D₁ D₂) (at (m-rec₂ q)) i j = refl {x = two.O}
root-sink-m m-unit env i j = refl {x = two.O}
root-sink-m m-unit src i j = refl {x = two.O}
root-sink-m m-unit input i j = refl {x = two.O}
root-sink-m m-unit (at ε) i j = refl {x = two.O}
root-sink-m m-base env i j = refl {x = two.O}
root-sink-m m-base src i j = refl {x = two.O}
root-sink-m m-base input i j = refl {x = two.O}
root-sink-m m-base (at ε) i j = refl {x = two.O}
root-sink-m m-arrow env i j = refl {x = two.O}
root-sink-m m-arrow src i j = refl {x = two.O}
root-sink-m m-arrow input i j = refl {x = two.O}
root-sink-m m-arrow (at ε) i j = refl {x = two.O}
root-sink-m (m-inl D) env i j = refl {x = two.O}
root-sink-m (m-inl D) src i j = refl {x = two.O}
root-sink-m (m-inl D) input i j = refl {x = two.O}
root-sink-m (m-inl D) (at ε) i j = refl {x = two.O}
root-sink-m (m-inl D) (at (m-inl q)) i j = refl {x = two.O}
root-sink-m (m-inr D) env i j = refl {x = two.O}
root-sink-m (m-inr D) src i j = refl {x = two.O}
root-sink-m (m-inr D) input i j = refl {x = two.O}
root-sink-m (m-inr D) (at ε) i j = refl {x = two.O}
root-sink-m (m-inr D) (at (m-inr q)) i j = refl {x = two.O}
root-sink-m (m-pair D₁ D₂) env i j = refl {x = two.O}
root-sink-m (m-pair D₁ D₂) src i j = refl {x = two.O}
root-sink-m (m-pair D₁ D₂) input i j = refl {x = two.O}
root-sink-m (m-pair D₁ D₂) (at ε) i j = refl {x = two.O}
root-sink-m (m-pair D₁ D₂) (at (m-pair₁ q)) i j = refl {x = two.O}
root-sink-m (m-pair D₁ D₂) (at (m-pair₂ q)) i j = refl {x = two.O}
root-sink-m (m-mu D) env i j = refl {x = two.O}
root-sink-m (m-mu D) src i j = refl {x = two.O}
root-sink-m (m-mu D) input i j = refl {x = two.O}
root-sink-m (m-mu D) (at ε) i j = refl {x = two.O}
root-sink-m (m-mu D) (at (m-mu q)) i j = refl {x = two.O}

hide-root-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : Nat.suc (width-env γ) ⇒ width v}
              {v' : Val (σ' [ σr ])} {R' : Nat.suc (width-env γ) ⇒ width v'}
              (D : Map γ s σ' v R v' R') (x y : VertexM D) →
              hide-m (graph-m D) (at ε) x y ≈ graph-m D x y
hide-root-m D x y =
  ≈-trans (+ₘ-cong ≈-refl (∘-cong₁ (root-sink-m D y)))
          (absorb (graph-m D x y) (graph-m D x (at ε)))

hide-hide-root-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                   {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : Nat.suc (width-env γ) ⇒ width v}
                   {v' : Val (σ' [ σr ])} {R' : Nat.suc (width-env γ) ⇒ width v'}
                   (D : Map γ s σ' v R v' R') (r x y : VertexM D) →
                   hide-m (hide-m (graph-m D) (at ε)) r x y
                   ≈ (graph-m D x y M.+ₘ (graph-m D r y ∘ graph-m D x r))
hide-hide-root-m D r x y =
  +ₘ-cong (hide-root-m D x y) (∘-cong (hide-root-m D r y) (hide-root-m D x r))

edge-off-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
             {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : Nat.suc (width-env γ) ⇒ width v}
             {v' : Val (σ' [ σr ])} {R' : Nat.suc (width-env γ) ⇒ width v'}
             {D : Map γ s σ' v R v' R'} {m}
             (S : M.Matrix m (width v')) (p : PathM D) → is-ε-m p ≡ Bool.false →
             edge-m S p ≈ M.εₘ
edge-off-m S ε ()
edge-off-m S (m-rec₁ p) np i j = refl {x = two.O}
edge-off-m S (m-rec₂ p) np i j = refl {x = two.O}
edge-off-m S (m-inl p) np i j = refl {x = two.O}
edge-off-m S (m-inr p) np i j = refl {x = two.O}
edge-off-m S (m-pair₁ p) np i j = refl {x = two.O}
edge-off-m S (m-pair₂ p) np i j = refl {x = two.O}
edge-off-m S (m-mu p) np i j = refl {x = two.O}

into-hidden-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : Nat.suc (width-env γ) ⇒ width v}
                {v' : Val (σ' [ σr ])} {R' : Nat.suc (width-env γ) ⇒ width v'}
                (D : Map γ s σ' v R v' R') {m}
                (P : M.Matrix m (width v')) (x : VertexM D) →
                (M.εₘ M.+ₘ (P ∘ graph-m D x (at ε)))
                ≈ (P ∘ hide-m (graph-m D) (at ε) x (at ε))
into-hidden-m D P x =
  ≈-trans (+ₘ-lunit (P ∘ graph-m D x (at ε))) (∘-cong₂ (≈-sym (hide-root-m D x (at ε))))

into-hidden-off-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                    {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : Nat.suc (width-env γ) ⇒ width v}
                    {v' : Val (σ' [ σr ])} {R' : Nat.suc (width-env γ) ⇒ width v'}
                    (D : Map γ s σ' v R v' R') {m} (x : VertexM D)
                    (K : M.Matrix m (vertex-width-m x)) (P : M.Matrix m (width v')) →
                    (K M.+ₘ (P ∘ graph-m D x (at ε)))
                    ≈ (K M.+ₘ (P ∘ hide-m (graph-m D) (at ε) x (at ε)))
into-hidden-off-m D x K P = +ₘ-cong ≈-refl (∘-cong₂ (≈-sym (hide-root-m D x (at ε))))

interior-not-root-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                      {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : Nat.suc (width-env γ) ⇒ width v}
                      {v' : Val (σ' [ σr ])} {R' : Nat.suc (width-env γ) ⇒ width v'}
                      (D : Map γ s σ' v R v' R') →
                      All (λ p → is-ε-m p ≡ Bool.false) (interior-m D)
interior-not-root-m (m-rec D₁ D₂) =
  ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths-m D₁))) (map⁺ (universal (λ _ → ≡-refl) (paths D₂)))
interior-not-root-m m-unit  = []
interior-not-root-m m-base  = []
interior-not-root-m m-arrow = []
interior-not-root-m (m-inl D) = map⁺ (universal (λ _ → ≡-refl) (paths-m D))
interior-not-root-m (m-inr D) = map⁺ (universal (λ _ → ≡-refl) (paths-m D))
interior-not-root-m (m-pair D₁ D₂) =
  ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths-m D₁))) (map⁺ (universal (λ _ → ≡-refl) (paths-m D₂)))
interior-not-root-m (m-mu D) = map⁺ (universal (λ _ → ≡-refl) (paths-m D))

hide-all-m-++ : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : Nat.suc (width-env γ) ⇒ width v}
                {v' : Val (σ' [ σr ])} {R' : Nat.suc (width-env γ) ⇒ width v'}
                {D : Map γ s σ' v R v' R'}
                (G : GraphM D) (xs ys : List (VertexM D)) →
                hide-all-m G (xs ++ ys) ≡ hide-all-m (hide-all-m G xs) ys
hide-all-m-++ G []       ys = ≡-refl
hide-all-m-++ G (x ∷ xs) ys = hide-all-m-++ (hide-m G x) xs ys

-- One hide step where the root columns carry both a pre-composition P and a post-composition W.
root-under : ∀ {m l g g' n} (P : M.Matrix m l) {W : M.Matrix g g'}
             {G₁ : M.Matrix m g'} {X : M.Matrix l g} {G₂ : M.Matrix m n} {Y : M.Matrix l n}
             {G₃ : M.Matrix n g'} {Z : M.Matrix n g} →
             G₁ ≈ ((P ∘ X) ∘ W) → G₂ ≈ (P ∘ Y) → G₃ ≈ (Z ∘ W) →
             (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ ((P ∘ (X M.+ₘ (Y ∘ Z))) ∘ W)
root-under P {W} {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c))
  (≈-trans (+ₘ-cong (≈-refl {f = (P ∘ X) ∘ W}) (≈-sym (assoc (P ∘ Y) Z W)))
  (≈-trans (≈-sym (M.comp-bilinear₁ (P ∘ X) ((P ∘ Y) ∘ Z) W))
           (∘-cong₁ (distrib-root P X Y Z))))

offset-under : ∀ {m l g g' n} (P : M.Matrix m l) {W : M.Matrix g g'} {K : M.Matrix m g'}
               {G₁ : M.Matrix m g'} {X : M.Matrix l g} {G₂ : M.Matrix m n} {Y : M.Matrix l n}
               {G₃ : M.Matrix n g'} {Z : M.Matrix n g} →
               G₁ ≈ (K M.+ₘ ((P ∘ X) ∘ W)) → G₂ ≈ (P ∘ Y) → G₃ ≈ (Z ∘ W) →
               (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ (K M.+ₘ ((P ∘ (X M.+ₘ (Y ∘ Z))) ∘ W))
offset-under P {W} {K} {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c))
  (≈-trans (+ₘ-assoc K ((P ∘ X) ∘ W) ((P ∘ Y) ∘ (Z ∘ W)))
           (+ₘ-cong (≈-refl {f = K})
                    (root-under P {W} {X = X} {Y = Y} {Z = Z}
                                (≈-refl {f = (P ∘ X) ∘ W}) (≈-refl {f = P ∘ Y})
                                (≈-refl {f = Z ∘ W}))))

-- Casts along width equalities, and their interaction with the matrix algebra. Each is proved by
-- matching the equality, so they apply at neutral width proofs.
ccast-∘ : ∀ {m k n n'} (e : n ≡ n') (X : M.Matrix m k) (Y : M.Matrix k n) →
          (X ∘ ccast e Y) ≈ ccast e (X ∘ Y)
ccast-∘ ≡-refl X Y = ≈-refl

ccast-cong : ∀ {m n n'} (e : n ≡ n') {X Y : M.Matrix m n} → X ≈ Y → ccast e X ≈ ccast e Y
ccast-cong ≡-refl h = h

+ₘ-ccast : ∀ {m n n'} (e : n ≡ n') (X Y : M.Matrix m n) →
           (ccast e X M.+ₘ ccast e Y) ≈ ccast e (X M.+ₘ Y)
+ₘ-ccast ≡-refl X Y = ≈-refl

rcast-∘ : ∀ {m m' k n} (e : m ≡ m') (X : M.Matrix m k) (Y : M.Matrix k n) →
          (rcast e X ∘ Y) ≈ rcast e (X ∘ Y)
rcast-∘ ≡-refl X Y = ≈-refl

rcast-cong : ∀ {m m' n} (e : m ≡ m') {X Y : M.Matrix m n} → X ≈ Y → rcast e X ≈ rcast e Y
rcast-cong ≡-refl h = h

ccast-step : ∀ {m k n n'} (e : n ≡ n') {G₁ : M.Matrix m n'} {X : M.Matrix m n}
             {G₂ Y : M.Matrix m k} {G₃ : M.Matrix k n'} {Z : M.Matrix k n} →
             G₁ ≈ ccast e X → G₂ ≈ Y → G₃ ≈ ccast e Z →
             (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ ccast e (X M.+ₘ (Y ∘ Z))
ccast-step e {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (≈-trans (∘-cong b c) (ccast-∘ e Y Z))) (+ₘ-ccast e X (Y ∘ Z))

root-step-cast : ∀ {m l g n n'} (e : n ≡ n') (P : M.Matrix m l)
                 {G₁ : M.Matrix m n'} {X : M.Matrix l n} {G₂ : M.Matrix m g} {Y : M.Matrix l g}
                 {G₃ : M.Matrix g n'} {Z : M.Matrix g n} →
                 G₁ ≈ (P ∘ ccast e X) → G₂ ≈ (P ∘ Y) → G₃ ≈ ccast e Z →
                 (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ (P ∘ ccast e (X M.+ₘ (Y ∘ Z)))
root-step-cast e P {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c))
  (≈-trans (+ₘ-cong ≈-refl (≈-trans (assoc P Y (ccast e Z)) (∘-cong₂ (ccast-∘ e Y Z))))
  (≈-trans (≈-sym (M.comp-bilinear₂ P (ccast e X) (ccast e (Y ∘ Z))))
           (∘-cong₂ (+ₘ-ccast e X (Y ∘ Z)))))

-- One summand survives because a factor of the other is zero.
keep-l : ∀ {m n k} {G₁ C : M.Matrix m n} {G₂ : M.Matrix m k} {G₃ : M.Matrix k n} →
         G₁ ≈ C → G₂ ≈ M.εₘ → (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ C
keep-l {C = C} {G₃ = G₃} a b = ≈-trans (+ₘ-cong a (∘-cong₁ b)) (absorb C G₃)

keep-r : ∀ {m n k} {G₁ C : M.Matrix m n} {G₂ : M.Matrix m k} {G₃ : M.Matrix k n} →
         G₁ ≈ C → G₃ ≈ M.εₘ → (G₁ M.+ₘ (G₂ ∘ G₃)) ≈ C
keep-r {C = C} {G₂ = G₂} a c = ≈-trans (+ₘ-cong a (∘-cong₂ c)) (absorb-r C G₂)
