{-# OPTIONS --prop --postfix-projections --safe #-}

open import signature using (Signature)
open import primitives using (Primitives)
open import commutative-semiring using (CommutativeSemiring)
import matrix
import two

-- Agreement of the graph judgement with control-source evaluation: collapsing a derivation's graph
-- recovers the run's dependence relation, the source column through collapse-src and the
-- environment block through collapse, case by case on the rules.
module interaction.control-agreement {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

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

-- Axiom rules: the only path is the root, and hiding it composes a zero column, so both collapses
-- are the rule's columns on the nose.
agree-var : ∀ {Γ τ} {γ : Env Γ} (x : Γ ∋ τ) → collapse (⇓-var x) ≈ proj-var x γ
agree-var {γ = γ} x = absorb (proj-var x γ) (proj-var x γ)

agree-var-src : ∀ {Γ τ} {γ : Env Γ} (x : Γ ∋ τ) → collapse-src (⇓-var {γ = γ} x) ≈ ctrl-row
agree-var-src {γ = γ} x =
  absorb (ctrl-row {width (lookup x γ)}) (ctrl-row {width (lookup x γ)})

agree-unit : ∀ {Γ} {γ : Env Γ} → collapse (⇓-unit {γ = γ}) ≈ M.εₘ
agree-unit {γ = γ} = absorb {k = 1} (M.εₘ {1} {width-env γ}) (M.εₘ {1} {width-env γ})

agree-unit-src : ∀ {Γ} {γ : Env Γ} → collapse-src (⇓-unit {γ = γ}) ≈ ctrl-row
agree-unit-src {γ = γ} = absorb (ctrl-row {1}) (ctrl-row {1})

agree-lam : ∀ {Γ σ τ} {γ : Env Γ} {t : Γ ▸ σ ⊢ τ} →
            collapse (⇓-lam {γ = γ} {t = t}) ≈ M.in₂ {1} {width-env γ}
agree-lam {γ = γ} =
  absorb {k = Nat.suc (width-env γ)} (M.in₂ {1} {width-env γ}) (M.in₂ {1} {width-env γ})

agree-lam-src : ∀ {Γ σ τ} {γ : Env Γ} {t : Γ ▸ σ ⊢ τ} →
                collapse-src (⇓-lam {γ = γ} {t = t}) ≈ src-root
agree-lam-src {γ = γ} =
  absorb {k = Nat.suc (width-env γ)} (src-root {width-env γ}) (src-root {width-env γ})

-- Collapsing an inl derivation collapses its premise; the fresh root points at the source.
module Inl {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁} {v : Val τ₁}
           {R : Nat.suc (width-env γ) ⇒ width v} {D : γ , t ⇓ v [ R ]} where

  record Embeds (G : Graph (⇓-inl {τ₂ = τ₂} D)) (H : Graph D)
                (P : M.Matrix (Nat.suc (width v)) (width v))
                (K : M.Matrix (Nat.suc (width v)) 1) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (inl q)) ≈ H env (at q)
      src-embed   : ∀ q → G src (at (inl q)) ≈ H src (at q)
      embed-embed : ∀ p q → G (at (inl p)) (at (inl q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (P ∘ H env (at ε))
      source-root : G src (at ε) ≈ (K M.+ₘ (P ∘ H src (at ε)))
      embed-root  : ∀ p → is-ε p ≡ Bool.false →
                    G (at (inl p)) (at ε) ≈ (P ∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P K} (w : Path D) → is-ε w ≡ Bool.false →
                Embeds G H P K → Embeds (hide G (at (inl w))) (hide H (at w)) P K
  embeds-hide w nw s .env-embed q =
    +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .src-embed q =
    +ₘ-cong (s .src-embed q) (∘-cong (s .embed-embed w q) (s .src-embed w))
  embeds-hide w nw s .embed-embed p q =
    +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {H = H} {P = P} w nw s .env-root =
    root-step {P = P} {X = H env (at ε)} {Y = H (at w) (at ε)} {Z = H env (at w)}
      (s .env-root) (s .embed-root w nw) (s .env-embed w)
  embeds-hide {H = H} {P = P} {K = K} w nw s .source-root =
    offset-step {K = K} {P = P} {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
      (s .source-root) (s .embed-root w nw) (s .src-embed w)
  embeds-hide {H = H} {P = P} w nw s .embed-root p np =
    root-step {P = P} {X = H (at p) (at ε)} {Y = H (at w) (at ε)} {Z = H (at p) (at w)}
      (s .embed-root p np) (s .embed-root w nw) (s .embed-embed p w)

  embeds-hide-all : ∀ {G H P K} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
                    Embeds G H P K →
                    Embeds (hide-all G (map at (map inl ws))) (hide-all H (map at ws)) P K
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    embeds₀ : Embeds (hide (hide (graph (⇓-inl {τ₂ = τ₂} D)) (at ε)) (at (inl ε)))
                     (hide (graph D) (at ε)) (M.in₂ {1} {width v}) src-root
    embeds₀ .env-embed q = hide-hide-root (⇓-inl {τ₂ = τ₂} D) (at (inl ε)) env (at (inl q))
    embeds₀ .src-embed q = hide-hide-root (⇓-inl {τ₂ = τ₂} D) (at (inl ε)) src (at (inl q))
    embeds₀ .embed-embed p q =
      hide-hide-root (⇓-inl {τ₂ = τ₂} D) (at (inl ε)) (at (inl p)) (at (inl q))
    embeds₀ .env-root =
      ≈-trans (hide-hide-root (⇓-inl {τ₂ = τ₂} D) (at (inl ε)) env (at ε))
              (into-hidden D (M.in₂ {1} {width v}) env)
    embeds₀ .source-root =
      ≈-trans (hide-hide-root (⇓-inl {τ₂ = τ₂} D) (at (inl ε)) src (at ε))
              (into-hidden-off D src src-root (M.in₂ {1} {width v}))
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root (⇓-inl {τ₂ = τ₂} D) (at (inl ε)) (at (inl p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off (M.in₂ {1} {width v}) p np) ≈-refl)
               (into-hidden D (M.in₂ {1} {width v}) (at p)))

  agree : collapse (⇓-inl {τ₂ = τ₂} D) ≈ (M.in₂ {1} {width v} ∘ collapse D)
  agree = embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root

  agree-src : collapse-src (⇓-inl {τ₂ = τ₂} D)
              ≈ (src-root M.+ₘ (M.in₂ {1} {width v} ∘ collapse-src D))
  agree-src = embeds-hide-all (interior D) (interior-not-root D) embeds₀ .source-root

-- Collapsing an inr derivation collapses its premise; the fresh root points at the source.
module Inr {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₂} {v : Val τ₂}
           {R : Nat.suc (width-env γ) ⇒ width v} {D : γ , t ⇓ v [ R ]} where

  record Embeds (G : Graph (⇓-inr {τ₁ = τ₁} D)) (H : Graph D)
                (P : M.Matrix (Nat.suc (width v)) (width v))
                (K : M.Matrix (Nat.suc (width v)) 1) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (inr q)) ≈ H env (at q)
      src-embed   : ∀ q → G src (at (inr q)) ≈ H src (at q)
      embed-embed : ∀ p q → G (at (inr p)) (at (inr q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (P ∘ H env (at ε))
      source-root : G src (at ε) ≈ (K M.+ₘ (P ∘ H src (at ε)))
      embed-root  : ∀ p → is-ε p ≡ Bool.false →
                    G (at (inr p)) (at ε) ≈ (P ∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P K} (w : Path D) → is-ε w ≡ Bool.false →
                Embeds G H P K → Embeds (hide G (at (inr w))) (hide H (at w)) P K
  embeds-hide w nw s .env-embed q =
    +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .src-embed q =
    +ₘ-cong (s .src-embed q) (∘-cong (s .embed-embed w q) (s .src-embed w))
  embeds-hide w nw s .embed-embed p q =
    +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {H = H} {P = P} w nw s .env-root =
    root-step {P = P} {X = H env (at ε)} {Y = H (at w) (at ε)} {Z = H env (at w)}
      (s .env-root) (s .embed-root w nw) (s .env-embed w)
  embeds-hide {H = H} {P = P} {K = K} w nw s .source-root =
    offset-step {K = K} {P = P} {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
      (s .source-root) (s .embed-root w nw) (s .src-embed w)
  embeds-hide {H = H} {P = P} w nw s .embed-root p np =
    root-step {P = P} {X = H (at p) (at ε)} {Y = H (at w) (at ε)} {Z = H (at p) (at w)}
      (s .embed-root p np) (s .embed-root w nw) (s .embed-embed p w)

  embeds-hide-all : ∀ {G H P K} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
                    Embeds G H P K →
                    Embeds (hide-all G (map at (map inr ws))) (hide-all H (map at ws)) P K
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    embeds₀ : Embeds (hide (hide (graph (⇓-inr {τ₁ = τ₁} D)) (at ε)) (at (inr ε)))
                     (hide (graph D) (at ε)) (M.in₂ {1} {width v}) src-root
    embeds₀ .env-embed q = hide-hide-root (⇓-inr {τ₁ = τ₁} D) (at (inr ε)) env (at (inr q))
    embeds₀ .src-embed q = hide-hide-root (⇓-inr {τ₁ = τ₁} D) (at (inr ε)) src (at (inr q))
    embeds₀ .embed-embed p q =
      hide-hide-root (⇓-inr {τ₁ = τ₁} D) (at (inr ε)) (at (inr p)) (at (inr q))
    embeds₀ .env-root =
      ≈-trans (hide-hide-root (⇓-inr {τ₁ = τ₁} D) (at (inr ε)) env (at ε))
              (into-hidden D (M.in₂ {1} {width v}) env)
    embeds₀ .source-root =
      ≈-trans (hide-hide-root (⇓-inr {τ₁ = τ₁} D) (at (inr ε)) src (at ε))
              (into-hidden-off D src src-root (M.in₂ {1} {width v}))
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root (⇓-inr {τ₁ = τ₁} D) (at (inr ε)) (at (inr p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off (M.in₂ {1} {width v}) p np) ≈-refl)
               (into-hidden D (M.in₂ {1} {width v}) (at p)))

  agree : collapse (⇓-inr {τ₁ = τ₁} D) ≈ (M.in₂ {1} {width v} ∘ collapse D)
  agree = embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root

  agree-src : collapse-src (⇓-inr {τ₁ = τ₁} D)
              ≈ (src-root M.+ₘ (M.in₂ {1} {width v} ∘ collapse-src D))
  agree-src = embeds-hide-all (interior D) (interior-not-root D) embeds₀ .source-root

-- Collapsing a fst derivation projects its premise's collapse and charges the control weight to the
-- pair's control row; the source column also charges the current source.
module Fst {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v : Val τ₁} {u : Val τ₂}
           {R : Nat.suc (width-env γ) ⇒ width (pair v u)} {D : γ , t ⇓ pair v u [ R ]} where

  private
    P₀ : M.Matrix (width v) (width (pair v u))
    P₀ = (M.p₁ {width v} {width u} ∘ M.p₂ {1} {width v Nat.+ width u}) M.+ₘ (ctrl-row ∘ M.p₁ {1})

    K₀ : M.Matrix (width v) 1
    K₀ = ctrl-row ∘ ctrl-row {1}

  record Embeds (G : Graph (⇓-fst D)) (H : Graph D)
                (P : M.Matrix (width v) (width (pair v u)))
                (K : M.Matrix (width v) 1) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (fst q)) ≈ H env (at q)
      src-embed   : ∀ q → G src (at (fst q)) ≈ H src (at q)
      embed-embed : ∀ p q → G (at (fst p)) (at (fst q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (P ∘ H env (at ε))
      source-root : G src (at ε) ≈ (K M.+ₘ (P ∘ H src (at ε)))
      embed-root  : ∀ p → is-ε p ≡ Bool.false →
                    G (at (fst p)) (at ε) ≈ (P ∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P K} (w : Path D) → is-ε w ≡ Bool.false →
                Embeds G H P K → Embeds (hide G (at (fst w))) (hide H (at w)) P K
  embeds-hide w nw s .env-embed q =
    +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .src-embed q =
    +ₘ-cong (s .src-embed q) (∘-cong (s .embed-embed w q) (s .src-embed w))
  embeds-hide w nw s .embed-embed p q =
    +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {H = H} {P = P} w nw s .env-root =
    root-step {P = P} {X = H env (at ε)} {Y = H (at w) (at ε)} {Z = H env (at w)}
      (s .env-root) (s .embed-root w nw) (s .env-embed w)
  embeds-hide {H = H} {P = P} {K = K} w nw s .source-root =
    offset-step {K = K} {P = P} {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
      (s .source-root) (s .embed-root w nw) (s .src-embed w)
  embeds-hide {H = H} {P = P} w nw s .embed-root p np =
    root-step {P = P} {X = H (at p) (at ε)} {Y = H (at w) (at ε)} {Z = H (at p) (at w)}
      (s .embed-root p np) (s .embed-root w nw) (s .embed-embed p w)

  embeds-hide-all : ∀ {G H P K} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
                    Embeds G H P K →
                    Embeds (hide-all G (map at (map fst ws))) (hide-all H (map at ws)) P K
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    embeds₀ : Embeds (hide (hide (graph (⇓-fst D)) (at ε)) (at (fst ε)))
                     (hide (graph D) (at ε)) P₀ K₀
    embeds₀ .env-embed q = hide-hide-root (⇓-fst D) (at (fst ε)) env (at (fst q))
    embeds₀ .src-embed q = hide-hide-root (⇓-fst D) (at (fst ε)) src (at (fst q))
    embeds₀ .embed-embed p q =
      hide-hide-root (⇓-fst D) (at (fst ε)) (at (fst p)) (at (fst q))
    embeds₀ .env-root =
      ≈-trans (hide-hide-root (⇓-fst D) (at (fst ε)) env (at ε))
              (into-hidden D P₀ env)
    embeds₀ .source-root =
      ≈-trans {f = hide (hide (graph (⇓-fst D)) (at ε)) (at (fst ε)) src (at ε)}
              {g = K₀ M.+ₘ (P₀ ∘ graph D src (at ε))}
              {h = K₀ M.+ₘ (P₀ ∘ hide (graph D) (at ε) src (at ε))}
              (hide-hide-root (⇓-fst D) (at (fst ε)) src (at ε))
              (into-hidden-off D src K₀ P₀)
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root (⇓-fst D) (at (fst ε)) (at (fst p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off P₀ p np) ≈-refl)
               (into-hidden D P₀ (at p)))

  agree : collapse (⇓-fst D) ≈ (P₀ ∘ collapse D)
  agree = embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root

  agree-src : collapse-src (⇓-fst D) ≈ (K₀ M.+ₘ (P₀ ∘ collapse-src D))
  agree-src = embeds-hide-all (interior D) (interior-not-root D) embeds₀ .source-root

-- Collapsing a snd derivation, symmetrically.
module Snd {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v : Val τ₁} {u : Val τ₂}
           {R : Nat.suc (width-env γ) ⇒ width (pair v u)} {D : γ , t ⇓ pair v u [ R ]} where

  private
    P₀ : M.Matrix (width u) (width (pair v u))
    P₀ = (M.p₂ {width v} {width u} ∘ M.p₂ {1} {width v Nat.+ width u}) M.+ₘ (ctrl-row ∘ M.p₁ {1})

    K₀ : M.Matrix (width u) 1
    K₀ = ctrl-row ∘ ctrl-row {1}

  record Embeds (G : Graph (⇓-snd D)) (H : Graph D)
                (P : M.Matrix (width u) (width (pair v u)))
                (K : M.Matrix (width u) 1) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (snd q)) ≈ H env (at q)
      src-embed   : ∀ q → G src (at (snd q)) ≈ H src (at q)
      embed-embed : ∀ p q → G (at (snd p)) (at (snd q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (P ∘ H env (at ε))
      source-root : G src (at ε) ≈ (K M.+ₘ (P ∘ H src (at ε)))
      embed-root  : ∀ p → is-ε p ≡ Bool.false →
                    G (at (snd p)) (at ε) ≈ (P ∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P K} (w : Path D) → is-ε w ≡ Bool.false →
                Embeds G H P K → Embeds (hide G (at (snd w))) (hide H (at w)) P K
  embeds-hide w nw s .env-embed q =
    +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .src-embed q =
    +ₘ-cong (s .src-embed q) (∘-cong (s .embed-embed w q) (s .src-embed w))
  embeds-hide w nw s .embed-embed p q =
    +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {H = H} {P = P} w nw s .env-root =
    root-step {P = P} {X = H env (at ε)} {Y = H (at w) (at ε)} {Z = H env (at w)}
      (s .env-root) (s .embed-root w nw) (s .env-embed w)
  embeds-hide {H = H} {P = P} {K = K} w nw s .source-root =
    offset-step {K = K} {P = P} {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
      (s .source-root) (s .embed-root w nw) (s .src-embed w)
  embeds-hide {H = H} {P = P} w nw s .embed-root p np =
    root-step {P = P} {X = H (at p) (at ε)} {Y = H (at w) (at ε)} {Z = H (at p) (at w)}
      (s .embed-root p np) (s .embed-root w nw) (s .embed-embed p w)

  embeds-hide-all : ∀ {G H P K} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
                    Embeds G H P K →
                    Embeds (hide-all G (map at (map snd ws))) (hide-all H (map at ws)) P K
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    embeds₀ : Embeds (hide (hide (graph (⇓-snd D)) (at ε)) (at (snd ε)))
                     (hide (graph D) (at ε)) P₀ K₀
    embeds₀ .env-embed q = hide-hide-root (⇓-snd D) (at (snd ε)) env (at (snd q))
    embeds₀ .src-embed q = hide-hide-root (⇓-snd D) (at (snd ε)) src (at (snd q))
    embeds₀ .embed-embed p q =
      hide-hide-root (⇓-snd D) (at (snd ε)) (at (snd p)) (at (snd q))
    embeds₀ .env-root =
      ≈-trans (hide-hide-root (⇓-snd D) (at (snd ε)) env (at ε))
              (into-hidden D P₀ env)
    embeds₀ .source-root =
      ≈-trans {f = hide (hide (graph (⇓-snd D)) (at ε)) (at (snd ε)) src (at ε)}
              {g = K₀ M.+ₘ (P₀ ∘ graph D src (at ε))}
              {h = K₀ M.+ₘ (P₀ ∘ hide (graph D) (at ε) src (at ε))}
              (hide-hide-root (⇓-snd D) (at (snd ε)) src (at ε))
              (into-hidden-off D src K₀ P₀)
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root (⇓-snd D) (at (snd ε)) (at (snd p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off P₀ p np) ≈-refl)
               (into-hidden D P₀ (at p)))

  agree : collapse (⇓-snd D) ≈ (P₀ ∘ collapse D)
  agree = embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root

  agree-src : collapse-src (⇓-snd D) ≈ (K₀ M.+ₘ (P₀ ∘ collapse-src D))
  agree-src = embeds-hide-all (interior D) (interior-not-root D) embeds₀ .source-root

-- Collapsing a roll derivation collapses its premise; both columns pass through unchanged.
module Roll {Γ} {τ : type 1} {γ : Env Γ} {t : Γ ⊢ τ [ μ τ ]} {v : Val (τ [ μ τ ])}
            {R : Nat.suc (width-env γ) ⇒ width v} {D : γ , t ⇓ v [ R ]} where

  record Embeds (G : Graph (⇓-roll {τ = τ} D)) (H : Graph D)
                (P : M.Matrix (width v) (width v)) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (roll q)) ≈ H env (at q)
      src-embed   : ∀ q → G src (at (roll q)) ≈ H src (at q)
      embed-embed : ∀ p q → G (at (roll p)) (at (roll q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (P ∘ H env (at ε))
      source-root : G src (at ε) ≈ (P ∘ H src (at ε))
      embed-root  : ∀ p → is-ε p ≡ Bool.false →
                    G (at (roll p)) (at ε) ≈ (P ∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : Path D) → is-ε w ≡ Bool.false →
                Embeds G H P → Embeds (hide G (at (roll w))) (hide H (at w)) P
  embeds-hide w nw s .env-embed q =
    +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .src-embed q =
    +ₘ-cong (s .src-embed q) (∘-cong (s .embed-embed w q) (s .src-embed w))
  embeds-hide w nw s .embed-embed p q =
    +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {H = H} {P = P} w nw s .env-root =
    root-step {P = P} {X = H env (at ε)} {Y = H (at w) (at ε)} {Z = H env (at w)}
      (s .env-root) (s .embed-root w nw) (s .env-embed w)
  embeds-hide {H = H} {P = P} w nw s .source-root =
    root-step {P = P} {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
      (s .source-root) (s .embed-root w nw) (s .src-embed w)
  embeds-hide {H = H} {P = P} w nw s .embed-root p np =
    root-step {P = P} {X = H (at p) (at ε)} {Y = H (at w) (at ε)} {Z = H (at p) (at w)}
      (s .embed-root p np) (s .embed-root w nw) (s .embed-embed p w)

  embeds-hide-all : ∀ {G H P} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
                    Embeds G H P →
                    Embeds (hide-all G (map at (map roll ws))) (hide-all H (map at ws)) P
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    embeds₀ : Embeds (hide (hide (graph (⇓-roll {τ = τ} D)) (at ε)) (at (roll ε)))
                     (hide (graph D) (at ε)) M.I
    embeds₀ .env-embed q = hide-hide-root (⇓-roll {τ = τ} D) (at (roll ε)) env (at (roll q))
    embeds₀ .src-embed q = hide-hide-root (⇓-roll {τ = τ} D) (at (roll ε)) src (at (roll q))
    embeds₀ .embed-embed p q =
      hide-hide-root (⇓-roll {τ = τ} D) (at (roll ε)) (at (roll p)) (at (roll q))
    embeds₀ .env-root =
      ≈-trans (hide-hide-root (⇓-roll {τ = τ} D) (at (roll ε)) env (at ε))
              (into-hidden D M.I env)
    embeds₀ .source-root =
      ≈-trans (hide-hide-root (⇓-roll {τ = τ} D) (at (roll ε)) src (at ε))
              (into-hidden D M.I src)
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root (⇓-roll {τ = τ} D) (at (roll ε)) (at (roll p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off M.I p np) ≈-refl) (into-hidden D M.I (at p)))

  agree : collapse (⇓-roll {τ = τ} D) ≈ collapse D
  agree = ≈-trans (embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root) id-left

  agree-src : collapse-src (⇓-roll {τ = τ} D) ≈ collapse-src D
  agree-src =
    ≈-trans (embeds-hide-all (interior D) (interior-not-root D) embeds₀ .source-root) id-left

-- Two same-environment premises: while the first premise folds, the second premise's entries and
-- the cross entries must be seen undisturbed; the second phase then folds the second premise
-- against the finished first contribution as a constant offset. The source column travels with
-- both phases, its root offset by the fresh root's control weight.
module Pair {Γ τ₁ τ₂} {γ : Env Γ} {ts : Γ ⊢ τ₁} {tt : Γ ⊢ τ₂} {v : Val τ₁} {u : Val τ₂}
            {R : Nat.suc (width-env γ) ⇒ width v} {S : Nat.suc (width-env γ) ⇒ width u}
            {D₁ : γ , ts ⇓ v [ R ]} {D₂ : γ , tt ⇓ u [ S ]} where

  private
    P₁ : M.Matrix (width (pair v u)) (width v)
    P₁ = M.in₂ {1} {width v Nat.+ width u} ∘ M.in₁ {width v} {width u}

    P₂ : M.Matrix (width (pair v u)) (width u)
    P₂ = M.in₂ {1} {width v Nat.+ width u} ∘ M.in₂ {width v} {width u}

  record Phase₁ (G : Graph (⇓-pair D₁ D₂)) (H : Graph D₁) : Set ℓ where
    field
      env-left    : ∀ q → G env (at (pair₁ q)) ≈ H env (at q)
      src-left    : ∀ q → G src (at (pair₁ q)) ≈ H src (at q)
      left-left   : ∀ p q → G (at (pair₁ p)) (at (pair₁ q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (P₁ ∘ H env (at ε))
      source-root : G src (at ε) ≈ (src-root M.+ₘ (P₁ ∘ H src (at ε)))
      left-root   : ∀ p → is-ε p ≡ Bool.false →
                    G (at (pair₁ p)) (at ε) ≈ (P₁ ∘ H (at p) (at ε))
      env-right   : ∀ q → G env (at (pair₂ q)) ≈ graph D₂ env (at q)
      src-right   : ∀ q → G src (at (pair₂ q)) ≈ graph D₂ src (at q)
      right-right : ∀ p q → G (at (pair₂ p)) (at (pair₂ q)) ≈ graph D₂ (at p) (at q)
      right-root  : ∀ p → G (at (pair₂ p)) (at ε) ≈ edge P₂ p
      left-right  : ∀ p q → G (at (pair₁ p)) (at (pair₂ q)) ≈ M.εₘ
      right-left  : ∀ p q → G (at (pair₂ p)) (at (pair₁ q)) ≈ M.εₘ

  open Phase₁

  step₁ : ∀ {G H} (w : Path D₁) → is-ε w ≡ Bool.false →
          Phase₁ G H → Phase₁ (hide G (at (pair₁ w))) (hide H (at w))
  step₁ w nw r .env-left q = +ₘ-cong (r .env-left q) (∘-cong (r .left-left w q) (r .env-left w))
  step₁ w nw r .src-left q = +ₘ-cong (r .src-left q) (∘-cong (r .left-left w q) (r .src-left w))
  step₁ w nw r .left-left p q =
    +ₘ-cong (r .left-left p q) (∘-cong (r .left-left w q) (r .left-left p w))
  step₁ w nw r .env-root =
    root-step {P = P₁} (r .env-root) (r .left-root w nw) (r .env-left w)
  step₁ w nw r .source-root =
    offset-step {K = src-root} {P = P₁} (r .source-root) (r .left-root w nw) (r .src-left w)
  step₁ w nw r .left-root p np =
    root-step {P = P₁} (r .left-root p np) (r .left-root w nw) (r .left-left p w)
  step₁ {G} w nw r .env-right q =
    ≈-trans (+ₘ-cong (r .env-right q) (∘-cong₁ (r .left-right w q)))
            (absorb (graph D₂ env (at q)) (G env (at (pair₁ w))))
  step₁ {G} w nw r .src-right q =
    ≈-trans (+ₘ-cong (r .src-right q) (∘-cong₁ (r .left-right w q)))
            (absorb (graph D₂ src (at q)) (G src (at (pair₁ w))))
  step₁ {G} w nw r .right-right p q =
    ≈-trans (+ₘ-cong (r .right-right p q) (∘-cong₁ (r .left-right w q)))
            (absorb (graph D₂ (at p) (at q)) (G (at (pair₂ p)) (at (pair₁ w))))
  step₁ {G} w nw r .right-root p =
    ≈-trans (+ₘ-cong (r .right-root p) (∘-cong₂ (r .right-left p w)))
            (absorb-r (edge P₂ p) (G (at (pair₁ w)) (at ε)))
  step₁ {G} w nw r .left-right p q =
    ≈-trans (+ₘ-cong (r .left-right p q) (∘-cong₁ (r .left-right w q)))
            (absorb M.εₘ (G (at (pair₁ p)) (at (pair₁ w))))
  step₁ {G} w nw r .right-left p q =
    ≈-trans (+ₘ-cong (r .right-left p q) (∘-cong₂ (r .right-left p w)))
            (absorb-r M.εₘ (G (at (pair₁ w)) (at (pair₁ q))))

  steps₁ : ∀ {G H} (ws : List (Path D₁)) → All (λ w → is-ε w ≡ Bool.false) ws →
           Phase₁ G H → Phase₁ (hide-all G (map at (map pair₁ ws))) (hide-all H (map at ws))
  steps₁ []       []         r = r
  steps₁ (w ∷ ws) (nw ∷ nws) r = steps₁ ws nws (step₁ w nw r)

  private
    hh : ∀ x y → hide (hide (graph (⇓-pair D₁ D₂)) (at ε)) (at (pair₁ ε)) x y
         ≈ (graph (⇓-pair D₁ D₂) x y
               M.+ₘ (graph (⇓-pair D₁ D₂) (at (pair₁ ε)) y ∘ graph (⇓-pair D₁ D₂) x (at (pair₁ ε))))
    hh = hide-hide-root (⇓-pair D₁ D₂) (at (pair₁ ε))

    base₁ : Phase₁ (hide (hide (graph (⇓-pair D₁ D₂)) (at ε)) (at (pair₁ ε)))
                   (hide (graph D₁) (at ε))
    base₁ .env-left q = hh env (at (pair₁ q))
    base₁ .src-left q = hh src (at (pair₁ q))
    base₁ .left-left p q = hh (at (pair₁ p)) (at (pair₁ q))
    base₁ .env-root = ≈-trans (hh env (at ε)) (into-hidden D₁ P₁ env)
    base₁ .source-root = ≈-trans (hh src (at ε)) (into-hidden-off D₁ src src-root P₁)
    base₁ .left-root p np =
      ≈-trans (hh (at (pair₁ p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off P₁ p np) ≈-refl) (into-hidden D₁ P₁ (at p)))
    base₁ .env-right q =
      ≈-trans (hh env (at (pair₂ q))) (absorb (graph D₂ env (at q)) (graph D₁ env (at ε)))
    base₁ .src-right q =
      ≈-trans (hh src (at (pair₂ q))) (absorb (graph D₂ src (at q)) (graph D₁ src (at ε)))
    base₁ .right-right p q =
      ≈-trans (hh (at (pair₂ p)) (at (pair₂ q)))
              (absorb (graph D₂ (at p) (at q)) (graph (⇓-pair D₁ D₂) (at (pair₂ p)) (at (pair₁ ε))))
    base₁ .right-root p =
      ≈-trans (hh (at (pair₂ p)) (at ε))
              (absorb-r (edge P₂ p) (graph (⇓-pair D₁ D₂) (at (pair₁ ε)) (at ε)))
    base₁ .left-right p q =
      ≈-trans (hh (at (pair₁ p)) (at (pair₂ q))) (absorb M.εₘ (graph D₁ (at p) (at ε)))
    base₁ .right-left p q =
      ≈-trans (hh (at (pair₂ p)) (at (pair₁ q))) (absorb-r M.εₘ (graph D₁ (at ε) (at q)))

  record Phase₂ (G : Graph (⇓-pair D₁ D₂)) (H : Graph D₂)
                (K : M.Matrix (width (pair v u)) (width-env γ))
                (Kₛ : M.Matrix (width (pair v u)) 1) : Set ℓ where
    field
      env-right   : ∀ q → G env (at (pair₂ q)) ≈ H env (at q)
      src-right   : ∀ q → G src (at (pair₂ q)) ≈ H src (at q)
      right-right : ∀ p q → G (at (pair₂ p)) (at (pair₂ q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (K M.+ₘ (P₂ ∘ H env (at ε)))
      source-root : G src (at ε) ≈ (Kₛ M.+ₘ (P₂ ∘ H src (at ε)))
      right-root  : ∀ p → is-ε p ≡ Bool.false →
                    G (at (pair₂ p)) (at ε) ≈ (P₂ ∘ H (at p) (at ε))

  open Phase₂

  step₂ : ∀ {G H K Kₛ} (w : Path D₂) → is-ε w ≡ Bool.false →
          Phase₂ G H K Kₛ → Phase₂ (hide G (at (pair₂ w))) (hide H (at w)) K Kₛ
  step₂ w nw r .env-right q = +ₘ-cong (r .env-right q) (∘-cong (r .right-right w q) (r .env-right w))
  step₂ w nw r .src-right q = +ₘ-cong (r .src-right q) (∘-cong (r .right-right w q) (r .src-right w))
  step₂ w nw r .right-right p q =
    +ₘ-cong (r .right-right p q) (∘-cong (r .right-right w q) (r .right-right p w))
  step₂ w nw r .env-root =
    offset-step {P = P₂} (r .env-root) (r .right-root w nw) (r .env-right w)
  step₂ w nw r .source-root =
    offset-step {P = P₂} (r .source-root) (r .right-root w nw) (r .src-right w)
  step₂ w nw r .right-root p np =
    root-step {P = P₂} (r .right-root p np) (r .right-root w nw) (r .right-right p w)

  steps₂ : ∀ {G H K Kₛ} (ws : List (Path D₂)) → All (λ w → is-ε w ≡ Bool.false) ws →
           Phase₂ G H K Kₛ → Phase₂ (hide-all G (map at (map pair₂ ws))) (hide-all H (map at ws)) K Kₛ
  steps₂ []       []         r = r
  steps₂ (w ∷ ws) (nw ∷ nws) r = steps₂ ws nws (step₂ w nw r)

  private
    r1 : Phase₁ (hide-all (hide (hide (graph (⇓-pair D₁ D₂)) (at ε)) (at (pair₁ ε)))
                          (map at (map pair₁ (interior D₁))))
                (hide-all (hide (graph D₁) (at ε)) (map at (interior D₁)))
    r1 = steps₁ (interior D₁) (interior-not-root D₁) base₁

    base₂ : Phase₂ (hide (hide-all (hide (hide (graph (⇓-pair D₁ D₂)) (at ε)) (at (pair₁ ε)))
                                   (map at (map pair₁ (interior D₁))))
                         (at (pair₂ ε)))
                   (hide (graph D₂) (at ε))
                   (P₁ ∘ collapse D₁)
                   (src-root M.+ₘ (P₁ ∘ collapse-src D₁))
    base₂ .env-right q = +ₘ-cong (r1 .env-right q) (∘-cong (r1 .right-right ε q) (r1 .env-right ε))
    base₂ .src-right q = +ₘ-cong (r1 .src-right q) (∘-cong (r1 .right-right ε q) (r1 .src-right ε))
    base₂ .right-right p q =
      +ₘ-cong (r1 .right-right p q) (∘-cong (r1 .right-right ε q) (r1 .right-right p ε))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (r1 .env-root) (∘-cong (r1 .right-root ε) (r1 .env-right ε)))
              (+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (hide-root D₂ env (at ε)))))
    base₂ .source-root =
      ≈-trans (+ₘ-cong (r1 .source-root) (∘-cong (r1 .right-root ε) (r1 .src-right ε)))
              (+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (hide-root D₂ src (at ε)))))
    base₂ .right-root p np =
      ≈-trans (+ₘ-cong (r1 .right-root p) (∘-cong (r1 .right-root ε) (r1 .right-right p ε)))
      (≈-trans (+ₘ-cong (edge-off P₂ p np) ≈-refl) (into-hidden D₂ P₂ (at p)))

    plumb : ∀ (x : Vertex (⇓-pair D₁ D₂)) →
            hide-all (hide (graph (⇓-pair D₁ D₂)) (at ε))
                     (map at (map pair₁ (paths D₁) ++ map pair₂ (paths D₂))) x (at ε)
            ≡ hide-all (hide-all (hide (graph (⇓-pair D₁ D₂)) (at ε))
                                 (map at (map pair₁ (paths D₁))))
                       (map at (map pair₂ (paths D₂))) x (at ε)
    plumb x =
      ≡-trans (≡-cong (λ L → hide-all (hide (graph (⇓-pair D₁ D₂)) (at ε)) L x (at ε))
                      (map-++ at (map pair₁ (paths D₁)) (map pair₂ (paths D₂))))
              (≡-cong (λ Gg → Gg x (at ε))
                      (hide-all-++ (hide (graph (⇓-pair D₁ D₂)) (at ε))
                                   (map at (map pair₁ (paths D₁)))
                                   (map at (map pair₂ (paths D₂)))))

  -- Collapsing a pair derivation pairs its premises' collapses.
  agree : collapse (⇓-pair D₁ D₂) ≈ ((P₁ ∘ collapse D₁) M.+ₘ (P₂ ∘ collapse D₂))
  agree =
    ≈-trans (≈-of-≡ (plumb env)) (steps₂ (interior D₂) (interior-not-root D₂) base₂ .env-root)

  agree-src : collapse-src (⇓-pair D₁ D₂)
              ≈ ((src-root M.+ₘ (P₁ ∘ collapse-src D₁)) M.+ₘ (P₂ ∘ collapse-src D₂))
  agree-src =
    ≈-trans (≈-of-≡ (plumb src)) (steps₂ (interior D₂) (interior-not-root D₂) base₂ .source-root)

-- Left case branch. The branch's environment and source columns are wired to the scrutinee root
-- together: the bound variable through the scrutinee's value, the branch's source through the
-- scrutinee's control column. Both collapses of the case derivation are therefore the branch's two
-- collapses composed with a pair of substitutions.
module CaseL {Γ τ₁ τ₂ τ} {γ : Env Γ} {ts : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
             {v : Val τ₁} {u : Val τ}
             {R : Nat.suc (width-env γ) ⇒ Nat.suc (width v)}
             {S : Nat.suc (width-env (γ · v)) ⇒ width u}
             {D₁ : γ , ts ⇓ inl v [ R ]} {D₂ : γ · v , t₁ ⇓ u [ S ]} where

  private
    iₗ : M.Matrix (width-env γ Nat.+ width v) (width-env γ)
    iₗ = M.in₁ {width-env γ} {width v}

    iᵣ : M.Matrix (width-env γ Nat.+ width v) (width v)
    iᵣ = M.in₂ {width-env γ} {width v}

    p1 : M.Matrix 1 (Nat.suc (width v))
    p1 = M.p₁ {1} {width v}

    p2 : M.Matrix (width v) (Nat.suc (width v))
    p2 = M.p₂ {1} {width v}

  B : (q : Path D₂) → M.Matrix (width-at q) (width-env γ Nat.+ width v)
  B q = graph D₂ env (at q)

  Bₛ : (q : Path D₂) → M.Matrix (width-at q) 1
  Bₛ q = graph D₂ src (at q)

  -- The branch's dependence on the scrutinee root: the bound variable through the value columns,
  -- the branch's source through the control column.
  Rt : (q : Path D₂) → M.Matrix (width-at q) (Nat.suc (width v))
  Rt q = ((B q ∘ iᵣ) ∘ p2) M.+ₘ (Bₛ q ∘ p1)

  W : M.Matrix (width-env γ Nat.+ width v) (width-env γ)
  W = iₗ M.+ₘ ((iᵣ ∘ p2) ∘ collapse D₁)

  U : M.Matrix 1 (width-env γ)
  U = p1 ∘ collapse D₁

  Wₛ : M.Matrix (width-env γ Nat.+ width v) 1
  Wₛ = (iᵣ ∘ p2) ∘ collapse-src D₁

  Uₛ : M.Matrix 1 1
  Uₛ = ctrl-row {1} M.+ₘ (p1 ∘ collapse-src D₁)

  private
    route-env : ∀ {m} (A : M.Matrix m (width-env γ Nat.+ width v)) (Bs : M.Matrix m 1) →
                ((A ∘ iₗ) M.+ₘ ((((A ∘ iᵣ) ∘ p2) M.+ₘ (Bs ∘ p1)) ∘ collapse D₁))
                ≈ ((A ∘ W) M.+ₘ (Bs ∘ U))
    route-env A Bs =
      ≈-trans (+ₘ-cong (≈-refl {f = A ∘ iₗ})
                       (M.comp-bilinear₁ ((A ∘ iᵣ) ∘ p2) (Bs ∘ p1) (collapse D₁)))
      (≈-trans (≈-sym (+ₘ-assoc (A ∘ iₗ) (((A ∘ iᵣ) ∘ p2) ∘ collapse D₁)
                                ((Bs ∘ p1) ∘ collapse D₁)))
               (+ₘ-cong (≈-trans (+ₘ-cong (≈-refl {f = A ∘ iₗ})
                                   (≈-trans (∘-cong₁ {g = collapse D₁} (assoc A iᵣ p2))
                                            (assoc A (iᵣ ∘ p2) (collapse D₁))))
                                 (≈-sym (M.comp-bilinear₂ A iₗ ((iᵣ ∘ p2) ∘ collapse D₁))))
                        (assoc Bs p1 (collapse D₁))))

    route-src : ∀ {m} (A : M.Matrix m (width-env γ Nat.+ width v)) (Bs : M.Matrix m 1) →
                ((Bs ∘ ctrl-row {1})
                   M.+ₘ ((((A ∘ iᵣ) ∘ p2) M.+ₘ (Bs ∘ p1)) ∘ collapse-src D₁))
                ≈ ((A ∘ Wₛ) M.+ₘ (Bs ∘ Uₛ))
    route-src A Bs =
      ≈-trans (+ₘ-cong (≈-refl {f = Bs ∘ ctrl-row {1}})
                       (M.comp-bilinear₁ ((A ∘ iᵣ) ∘ p2) (Bs ∘ p1) (collapse-src D₁)))
      (≈-trans (+ₘ-swap-mid (Bs ∘ ctrl-row {1}) (((A ∘ iᵣ) ∘ p2) ∘ collapse-src D₁)
                            ((Bs ∘ p1) ∘ collapse-src D₁))
               (+ₘ-cong (≈-trans (∘-cong₁ {g = collapse-src D₁} (assoc A iᵣ p2))
                                 (assoc A (iᵣ ∘ p2) (collapse-src D₁)))
                        (≈-trans (+ₘ-cong (≈-refl {f = Bs ∘ ctrl-row {1}})
                                          (assoc Bs p1 (collapse-src D₁)))
                                 (≈-sym (M.comp-bilinear₂ Bs (ctrl-row {1})
                                                          (p1 ∘ collapse-src D₁))))))

  record Phase₁ (G : Graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (H : Graph D₁) : Set ℓ where
    field
      env-scrut     : ∀ q → G env (at (case-l₁ q)) ≈ H env (at q)
      src-scrut     : ∀ q → G src (at (case-l₁ q)) ≈ H src (at q)
      scrut-scrut   : ∀ p q → G (at (case-l₁ p)) (at (case-l₁ q)) ≈ H (at p) (at q)
      env-branch    : ∀ q → G env (at (case-l₂ q))
                      ≈ ((B q ∘ iₗ) M.+ₘ (Rt q ∘ H env (at ε)))
      src-branch    : ∀ q → G src (at (case-l₂ q))
                      ≈ ((Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ H src (at ε)))
      scrut-branch  : ∀ p → is-ε p ≡ Bool.false → ∀ q →
                      G (at (case-l₁ p)) (at (case-l₂ q)) ≈ (Rt q ∘ H (at p) (at ε))
      branch-branch : ∀ p q → G (at (case-l₂ p)) (at (case-l₂ q)) ≈ graph D₂ (at p) (at q)
      branch-scrut  : ∀ p q → G (at (case-l₂ p)) (at (case-l₁ q)) ≈ M.εₘ
      env-root      : G env (at ε) ≈ M.εₘ
      source-root   : G src (at ε) ≈ M.εₘ
      scrut-root    : ∀ p → G (at (case-l₁ p)) (at ε) ≈ M.εₘ
      branch-root   : ∀ p → G (at (case-l₂ p)) (at ε) ≈ edge M.I p

  open Phase₁

  step₁ : ∀ {G H} (w : Path D₁) → is-ε w ≡ Bool.false →
          Phase₁ G H → Phase₁ (hide G (at (case-l₁ w))) (hide H (at w))
  step₁ w nw r .env-scrut q = +ₘ-cong (r .env-scrut q) (∘-cong (r .scrut-scrut w q) (r .env-scrut w))
  step₁ w nw r .src-scrut q = +ₘ-cong (r .src-scrut q) (∘-cong (r .scrut-scrut w q) (r .src-scrut w))
  step₁ w nw r .scrut-scrut p q =
    +ₘ-cong (r .scrut-scrut p q) (∘-cong (r .scrut-scrut w q) (r .scrut-scrut p w))
  step₁ {H = H} w nw r .env-branch q =
    offset-step {K = B q ∘ iₗ} {P = Rt q}
                {X = H env (at ε)} {Y = H (at w) (at ε)} {Z = H env (at w)}
                (r .env-branch q) (r .scrut-branch w nw q) (r .env-scrut w)
  step₁ {H = H} w nw r .src-branch q =
    offset-step {K = Bₛ q ∘ ctrl-row {1}} {P = Rt q}
                {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
                (r .src-branch q) (r .scrut-branch w nw q) (r .src-scrut w)
  step₁ {H = H} w nw r .scrut-branch p np q =
    root-step {P = Rt q} {X = H (at p) (at ε)} {Y = H (at w) (at ε)} {Z = H (at p) (at w)}
              (r .scrut-branch p np q) (r .scrut-branch w nw q) (r .scrut-scrut p w)
  step₁ {G} w nw r .branch-branch p q =
    ≈-trans (+ₘ-cong (r .branch-branch p q) (∘-cong₂ (r .branch-scrut p w)))
            (absorb-r (graph D₂ (at p) (at q)) (G (at (case-l₁ w)) (at (case-l₂ q))))
  step₁ {G} w nw r .branch-scrut p q =
    ≈-trans (+ₘ-cong (r .branch-scrut p q) (∘-cong₂ (r .branch-scrut p w)))
            (absorb-r M.εₘ (G (at (case-l₁ w)) (at (case-l₁ q))))
  step₁ {G} w nw r .env-root =
    ≈-trans (+ₘ-cong (r .env-root) (∘-cong₁ (r .scrut-root w)))
            (absorb M.εₘ (G env (at (case-l₁ w))))
  step₁ {G} w nw r .source-root =
    ≈-trans (+ₘ-cong (r .source-root) (∘-cong₁ (r .scrut-root w)))
            (absorb M.εₘ (G src (at (case-l₁ w))))
  step₁ {G} w nw r .scrut-root p =
    ≈-trans (+ₘ-cong (r .scrut-root p) (∘-cong₁ (r .scrut-root w)))
            (absorb M.εₘ (G (at (case-l₁ p)) (at (case-l₁ w))))
  step₁ {G} w nw r .branch-root p =
    ≈-trans (+ₘ-cong (r .branch-root p) (∘-cong₁ (r .scrut-root w)))
            (absorb (edge M.I p) (G (at (case-l₂ p)) (at (case-l₁ w))))

  steps₁ : ∀ {G H} (ws : List (Path D₁)) → All (λ w → is-ε w ≡ Bool.false) ws →
           Phase₁ G H → Phase₁ (hide-all G (map at (map case-l₁ ws))) (hide-all H (map at ws))
  steps₁ []       []         r = r
  steps₁ (w ∷ ws) (nw ∷ nws) r = steps₁ ws nws (step₁ w nw r)

  private
    hh : ∀ x y → hide (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε)) (at (case-l₁ ε)) x y
         ≈ (graph (⇓-case-l {t₂ = t₂} D₁ D₂) x y
              M.+ₘ (graph (⇓-case-l {t₂ = t₂} D₁ D₂) (at (case-l₁ ε)) y
                      ∘ graph (⇓-case-l {t₂ = t₂} D₁ D₂) x (at (case-l₁ ε))))
    hh = hide-hide-root (⇓-case-l {t₂ = t₂} D₁ D₂) (at (case-l₁ ε))

    base₁ : Phase₁ (hide (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε)) (at (case-l₁ ε)))
                   (hide (graph D₁) (at ε))
    base₁ .env-scrut q = hh env (at (case-l₁ q))
    base₁ .src-scrut q = hh src (at (case-l₁ q))
    base₁ .scrut-scrut p q = hh (at (case-l₁ p)) (at (case-l₁ q))
    base₁ .env-branch q =
      ≈-trans {f = hide (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε)) (at (case-l₁ ε))
                        env (at (case-l₂ q))}
              {g = (B q ∘ iₗ) M.+ₘ (Rt q ∘ graph D₁ env (at ε))}
              {h = (B q ∘ iₗ) M.+ₘ (Rt q ∘ hide (graph D₁) (at ε) env (at ε))}
              (hh env (at (case-l₂ q))) (into-hidden-off D₁ env (B q ∘ iₗ) (Rt q))
    base₁ .src-branch q =
      ≈-trans {f = hide (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε)) (at (case-l₁ ε))
                        src (at (case-l₂ q))}
              {g = (Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ graph D₁ src (at ε))}
              {h = (Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ hide (graph D₁) (at ε) src (at ε))}
              (hh src (at (case-l₂ q))) (into-hidden-off D₁ src (Bₛ q ∘ ctrl-row {1}) (Rt q))
    base₁ .scrut-branch p np q =
      ≈-trans (hh (at (case-l₁ p)) (at (case-l₂ q)))
      (≈-trans (+ₘ-cong (edge-off (Rt q) p np) ≈-refl) (into-hidden D₁ (Rt q) (at p)))
    base₁ .branch-branch p q =
      ≈-trans (hh (at (case-l₂ p)) (at (case-l₂ q)))
              (absorb-r (graph D₂ (at p) (at q)) (Rt q))
    base₁ .branch-scrut p q =
      ≈-trans (hh (at (case-l₂ p)) (at (case-l₁ q))) (absorb-r M.εₘ (graph D₁ (at ε) (at q)))
    base₁ .env-root = ≈-trans (hh env (at ε)) (absorb M.εₘ (graph D₁ env (at ε)))
    base₁ .source-root = ≈-trans (hh src (at ε)) (absorb M.εₘ (graph D₁ src (at ε)))
    base₁ .scrut-root p = ≈-trans (hh (at (case-l₁ p)) (at ε)) (absorb M.εₘ (graph D₁ (at p) (at ε)))
    base₁ .branch-root p =
      ≈-trans (hh (at (case-l₂ p)) (at ε))
              (absorb (edge M.I p)
                      (graph (⇓-case-l {t₂ = t₂} D₁ D₂) (at (case-l₂ p)) (at (case-l₁ ε))))

  record Phase₂ (G : Graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (H : Graph D₂) : Set ℓ where
    field
      env-branch    : ∀ q → G env (at (case-l₂ q))
                      ≈ ((H env (at q) ∘ W) M.+ₘ (H src (at q) ∘ U))
      src-branch    : ∀ q → G src (at (case-l₂ q))
                      ≈ ((H env (at q) ∘ Wₛ) M.+ₘ (H src (at q) ∘ Uₛ))
      branch-branch : ∀ p q → G (at (case-l₂ p)) (at (case-l₂ q)) ≈ H (at p) (at q)
      env-root      : G env (at ε) ≈ ((H env (at ε) ∘ W) M.+ₘ (H src (at ε) ∘ U))
      source-root   : G src (at ε) ≈ ((H env (at ε) ∘ Wₛ) M.+ₘ (H src (at ε) ∘ Uₛ))
      branch-root   : ∀ p → is-ε p ≡ Bool.false → G (at (case-l₂ p)) (at ε) ≈ H (at p) (at ε)

  open Phase₂

  step₂ : ∀ {G H} (w : Path D₂) → is-ε w ≡ Bool.false →
          Phase₂ G H → Phase₂ (hide G (at (case-l₂ w))) (hide H (at w))
  step₂ {H = H} w nw r .env-branch q =
    pair-step {W = W} {U = U} {A = H env (at q)} {B = H src (at q)} {Y = H (at w) (at q)}
              {Aw = H env (at w)} {Bw = H src (at w)}
              (r .env-branch q) (r .branch-branch w q) (r .env-branch w)
  step₂ {H = H} w nw r .src-branch q =
    pair-step {W = Wₛ} {U = Uₛ} {A = H env (at q)} {B = H src (at q)} {Y = H (at w) (at q)}
              {Aw = H env (at w)} {Bw = H src (at w)}
              (r .src-branch q) (r .branch-branch w q) (r .src-branch w)
  step₂ w nw r .branch-branch p q =
    +ₘ-cong (r .branch-branch p q) (∘-cong (r .branch-branch w q) (r .branch-branch p w))
  step₂ {H = H} w nw r .env-root =
    pair-step {W = W} {U = U} {A = H env (at ε)} {B = H src (at ε)} {Y = H (at w) (at ε)}
              {Aw = H env (at w)} {Bw = H src (at w)}
              (r .env-root) (r .branch-root w nw) (r .env-branch w)
  step₂ {H = H} w nw r .source-root =
    pair-step {W = Wₛ} {U = Uₛ} {A = H env (at ε)} {B = H src (at ε)} {Y = H (at w) (at ε)}
              {Aw = H env (at w)} {Bw = H src (at w)}
              (r .source-root) (r .branch-root w nw) (r .src-branch w)
  step₂ w nw r .branch-root p np =
    +ₘ-cong (r .branch-root p np) (∘-cong (r .branch-root w nw) (r .branch-branch p w))

  steps₂ : ∀ {G H} (ws : List (Path D₂)) → All (λ w → is-ε w ≡ Bool.false) ws →
           Phase₂ G H → Phase₂ (hide-all G (map at (map case-l₂ ws))) (hide-all H (map at ws))
  steps₂ []       []         r = r
  steps₂ (w ∷ ws) (nw ∷ nws) r = steps₂ ws nws (step₂ w nw r)

  private
    r1 : Phase₁ (hide-all (hide (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε)) (at (case-l₁ ε)))
                          (map at (map case-l₁ (interior D₁))))
                (hide-all (hide (graph D₁) (at ε)) (map at (interior D₁)))
    r1 = steps₁ (interior D₁) (interior-not-root D₁) base₁

    Zₑ : M.Matrix (width u) (width-env γ)
    Zₑ = (B ε ∘ W) M.+ₘ (Bₛ ε ∘ U)

    Zₛ : M.Matrix (width u) 1
    Zₛ = (B ε ∘ Wₛ) M.+ₘ (Bₛ ε ∘ Uₛ)

    base₂ : Phase₂ (hide (hide-all (hide (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε))
                                         (at (case-l₁ ε)))
                                   (map at (map case-l₁ (interior D₁))))
                         (at (case-l₂ ε)))
                   (hide (graph D₂) (at ε))
    base₂ .env-branch q =
      pair-step {W = W} {U = U} {A = B q} {B = Bₛ q} {Y = graph D₂ (at ε) (at q)}
                {Aw = B ε} {Bw = Bₛ ε}
                (≈-trans (r1 .env-branch q) (route-env (B q) (Bₛ q)))
                (r1 .branch-branch ε q)
                (≈-trans (r1 .env-branch ε) (route-env (B ε) (Bₛ ε)))
    base₂ .src-branch q =
      pair-step {W = Wₛ} {U = Uₛ} {A = B q} {B = Bₛ q} {Y = graph D₂ (at ε) (at q)}
                {Aw = B ε} {Bw = Bₛ ε}
                (≈-trans (r1 .src-branch q) (route-src (B q) (Bₛ q)))
                (r1 .branch-branch ε q)
                (≈-trans (r1 .src-branch ε) (route-src (B ε) (Bₛ ε)))
    base₂ .branch-branch p q =
      +ₘ-cong (r1 .branch-branch p q) (∘-cong (r1 .branch-branch ε q) (r1 .branch-branch p ε))
    base₂ .env-root =
      ≈-trans {g = M.εₘ M.+ₘ (M.I ∘ Zₑ)}
              (+ₘ-cong (r1 .env-root)
                       (∘-cong (r1 .branch-root ε)
                               (≈-trans (r1 .env-branch ε) (route-env (B ε) (Bₛ ε)))))
      (≈-trans {g = M.I ∘ Zₑ} (+ₘ-lunit (M.I ∘ Zₑ))
      (≈-trans {g = Zₑ} id-left
               (+ₘ-cong (∘-cong₁ {g = W} (≈-sym (hide-root D₂ env (at ε))))
                        (∘-cong₁ {g = U} (≈-sym (hide-root D₂ src (at ε)))))))
    base₂ .source-root =
      ≈-trans {g = M.εₘ M.+ₘ (M.I ∘ Zₛ)}
              (+ₘ-cong (r1 .source-root)
                       (∘-cong (r1 .branch-root ε)
                               (≈-trans (r1 .src-branch ε) (route-src (B ε) (Bₛ ε)))))
      (≈-trans {g = M.I ∘ Zₛ} (+ₘ-lunit (M.I ∘ Zₛ))
      (≈-trans {g = Zₛ} id-left
               (+ₘ-cong (∘-cong₁ {g = Wₛ} (≈-sym (hide-root D₂ env (at ε))))
                        (∘-cong₁ {g = Uₛ} (≈-sym (hide-root D₂ src (at ε)))))))
    base₂ .branch-root p np =
      ≈-trans (+ₘ-cong (≈-trans (r1 .branch-root p) (edge-off M.I p np))
                       (∘-cong (r1 .branch-root ε) (r1 .branch-branch p ε)))
      (≈-trans (into-hidden D₂ M.I (at p)) id-left)

    plumb : ∀ (x : Vertex (⇓-case-l {t₂ = t₂} D₁ D₂)) →
            hide-all (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε))
                     (map at (map case-l₁ (paths D₁) ++ map case-l₂ (paths D₂))) x (at ε)
            ≡ hide-all (hide-all (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε))
                                 (map at (map case-l₁ (paths D₁))))
                       (map at (map case-l₂ (paths D₂))) x (at ε)
    plumb x =
      ≡-trans (≡-cong (λ L → hide-all (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε)) L x (at ε))
                      (map-++ at (map case-l₁ (paths D₁)) (map case-l₂ (paths D₂))))
              (≡-cong (λ Gg → Gg x (at ε))
                      (hide-all-++ (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε))
                                   (map at (map case-l₁ (paths D₁)))
                                   (map at (map case-l₂ (paths D₂)))))

  agree : collapse (⇓-case-l {t₂ = t₂} D₁ D₂)
          ≈ ((collapse D₂ ∘ W) M.+ₘ (collapse-src D₂ ∘ U))
  agree =
    ≈-trans (≈-of-≡ (plumb env)) (steps₂ (interior D₂) (interior-not-root D₂) base₂ .env-root)

  agree-src : collapse-src (⇓-case-l {t₂ = t₂} D₁ D₂)
              ≈ ((collapse D₂ ∘ Wₛ) M.+ₘ (collapse-src D₂ ∘ Uₛ))
  agree-src =
    ≈-trans (≈-of-≡ (plumb src)) (steps₂ (interior D₂) (interior-not-root D₂) base₂ .source-root)

-- Right case branch, symmetrically.
module CaseR {Γ τ₁ τ₂ τ} {γ : Env Γ} {ts : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
             {v : Val τ₂} {u : Val τ}
             {R : Nat.suc (width-env γ) ⇒ Nat.suc (width v)}
             {S : Nat.suc (width-env (γ · v)) ⇒ width u}
             {D₁ : γ , ts ⇓ inr v [ R ]} {D₂ : γ · v , t₂ ⇓ u [ S ]} where

  private
    iₗ : M.Matrix (width-env γ Nat.+ width v) (width-env γ)
    iₗ = M.in₁ {width-env γ} {width v}

    iᵣ : M.Matrix (width-env γ Nat.+ width v) (width v)
    iᵣ = M.in₂ {width-env γ} {width v}

    p1 : M.Matrix 1 (Nat.suc (width v))
    p1 = M.p₁ {1} {width v}

    p2 : M.Matrix (width v) (Nat.suc (width v))
    p2 = M.p₂ {1} {width v}

  B : (q : Path D₂) → M.Matrix (width-at q) (width-env γ Nat.+ width v)
  B q = graph D₂ env (at q)

  Bₛ : (q : Path D₂) → M.Matrix (width-at q) 1
  Bₛ q = graph D₂ src (at q)

  -- The branch's dependence on the scrutinee root: the bound variable through the value columns,
  -- the branch's source through the control column.
  Rt : (q : Path D₂) → M.Matrix (width-at q) (Nat.suc (width v))
  Rt q = ((B q ∘ iᵣ) ∘ p2) M.+ₘ (Bₛ q ∘ p1)

  W : M.Matrix (width-env γ Nat.+ width v) (width-env γ)
  W = iₗ M.+ₘ ((iᵣ ∘ p2) ∘ collapse D₁)

  U : M.Matrix 1 (width-env γ)
  U = p1 ∘ collapse D₁

  Wₛ : M.Matrix (width-env γ Nat.+ width v) 1
  Wₛ = (iᵣ ∘ p2) ∘ collapse-src D₁

  Uₛ : M.Matrix 1 1
  Uₛ = ctrl-row {1} M.+ₘ (p1 ∘ collapse-src D₁)

  private
    route-env : ∀ {m} (A : M.Matrix m (width-env γ Nat.+ width v)) (Bs : M.Matrix m 1) →
                ((A ∘ iₗ) M.+ₘ ((((A ∘ iᵣ) ∘ p2) M.+ₘ (Bs ∘ p1)) ∘ collapse D₁))
                ≈ ((A ∘ W) M.+ₘ (Bs ∘ U))
    route-env A Bs =
      ≈-trans (+ₘ-cong (≈-refl {f = A ∘ iₗ})
                       (M.comp-bilinear₁ ((A ∘ iᵣ) ∘ p2) (Bs ∘ p1) (collapse D₁)))
      (≈-trans (≈-sym (+ₘ-assoc (A ∘ iₗ) (((A ∘ iᵣ) ∘ p2) ∘ collapse D₁)
                                ((Bs ∘ p1) ∘ collapse D₁)))
               (+ₘ-cong (≈-trans (+ₘ-cong (≈-refl {f = A ∘ iₗ})
                                   (≈-trans (∘-cong₁ {g = collapse D₁} (assoc A iᵣ p2))
                                            (assoc A (iᵣ ∘ p2) (collapse D₁))))
                                 (≈-sym (M.comp-bilinear₂ A iₗ ((iᵣ ∘ p2) ∘ collapse D₁))))
                        (assoc Bs p1 (collapse D₁))))

    route-src : ∀ {m} (A : M.Matrix m (width-env γ Nat.+ width v)) (Bs : M.Matrix m 1) →
                ((Bs ∘ ctrl-row {1})
                   M.+ₘ ((((A ∘ iᵣ) ∘ p2) M.+ₘ (Bs ∘ p1)) ∘ collapse-src D₁))
                ≈ ((A ∘ Wₛ) M.+ₘ (Bs ∘ Uₛ))
    route-src A Bs =
      ≈-trans (+ₘ-cong (≈-refl {f = Bs ∘ ctrl-row {1}})
                       (M.comp-bilinear₁ ((A ∘ iᵣ) ∘ p2) (Bs ∘ p1) (collapse-src D₁)))
      (≈-trans (+ₘ-swap-mid (Bs ∘ ctrl-row {1}) (((A ∘ iᵣ) ∘ p2) ∘ collapse-src D₁)
                            ((Bs ∘ p1) ∘ collapse-src D₁))
               (+ₘ-cong (≈-trans (∘-cong₁ {g = collapse-src D₁} (assoc A iᵣ p2))
                                 (assoc A (iᵣ ∘ p2) (collapse-src D₁)))
                        (≈-trans (+ₘ-cong (≈-refl {f = Bs ∘ ctrl-row {1}})
                                          (assoc Bs p1 (collapse-src D₁)))
                                 (≈-sym (M.comp-bilinear₂ Bs (ctrl-row {1})
                                                          (p1 ∘ collapse-src D₁))))))

  record Phase₁ (G : Graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (H : Graph D₁) : Set ℓ where
    field
      env-scrut     : ∀ q → G env (at (case-r₁ q)) ≈ H env (at q)
      src-scrut     : ∀ q → G src (at (case-r₁ q)) ≈ H src (at q)
      scrut-scrut   : ∀ p q → G (at (case-r₁ p)) (at (case-r₁ q)) ≈ H (at p) (at q)
      env-branch    : ∀ q → G env (at (case-r₂ q))
                      ≈ ((B q ∘ iₗ) M.+ₘ (Rt q ∘ H env (at ε)))
      src-branch    : ∀ q → G src (at (case-r₂ q))
                      ≈ ((Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ H src (at ε)))
      scrut-branch  : ∀ p → is-ε p ≡ Bool.false → ∀ q →
                      G (at (case-r₁ p)) (at (case-r₂ q)) ≈ (Rt q ∘ H (at p) (at ε))
      branch-branch : ∀ p q → G (at (case-r₂ p)) (at (case-r₂ q)) ≈ graph D₂ (at p) (at q)
      branch-scrut  : ∀ p q → G (at (case-r₂ p)) (at (case-r₁ q)) ≈ M.εₘ
      env-root      : G env (at ε) ≈ M.εₘ
      source-root   : G src (at ε) ≈ M.εₘ
      scrut-root    : ∀ p → G (at (case-r₁ p)) (at ε) ≈ M.εₘ
      branch-root   : ∀ p → G (at (case-r₂ p)) (at ε) ≈ edge M.I p

  open Phase₁

  step₁ : ∀ {G H} (w : Path D₁) → is-ε w ≡ Bool.false →
          Phase₁ G H → Phase₁ (hide G (at (case-r₁ w))) (hide H (at w))
  step₁ w nw r .env-scrut q = +ₘ-cong (r .env-scrut q) (∘-cong (r .scrut-scrut w q) (r .env-scrut w))
  step₁ w nw r .src-scrut q = +ₘ-cong (r .src-scrut q) (∘-cong (r .scrut-scrut w q) (r .src-scrut w))
  step₁ w nw r .scrut-scrut p q =
    +ₘ-cong (r .scrut-scrut p q) (∘-cong (r .scrut-scrut w q) (r .scrut-scrut p w))
  step₁ {H = H} w nw r .env-branch q =
    offset-step {K = B q ∘ iₗ} {P = Rt q}
                {X = H env (at ε)} {Y = H (at w) (at ε)} {Z = H env (at w)}
                (r .env-branch q) (r .scrut-branch w nw q) (r .env-scrut w)
  step₁ {H = H} w nw r .src-branch q =
    offset-step {K = Bₛ q ∘ ctrl-row {1}} {P = Rt q}
                {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
                (r .src-branch q) (r .scrut-branch w nw q) (r .src-scrut w)
  step₁ {H = H} w nw r .scrut-branch p np q =
    root-step {P = Rt q} {X = H (at p) (at ε)} {Y = H (at w) (at ε)} {Z = H (at p) (at w)}
              (r .scrut-branch p np q) (r .scrut-branch w nw q) (r .scrut-scrut p w)
  step₁ {G} w nw r .branch-branch p q =
    ≈-trans (+ₘ-cong (r .branch-branch p q) (∘-cong₂ (r .branch-scrut p w)))
            (absorb-r (graph D₂ (at p) (at q)) (G (at (case-r₁ w)) (at (case-r₂ q))))
  step₁ {G} w nw r .branch-scrut p q =
    ≈-trans (+ₘ-cong (r .branch-scrut p q) (∘-cong₂ (r .branch-scrut p w)))
            (absorb-r M.εₘ (G (at (case-r₁ w)) (at (case-r₁ q))))
  step₁ {G} w nw r .env-root =
    ≈-trans (+ₘ-cong (r .env-root) (∘-cong₁ (r .scrut-root w)))
            (absorb M.εₘ (G env (at (case-r₁ w))))
  step₁ {G} w nw r .source-root =
    ≈-trans (+ₘ-cong (r .source-root) (∘-cong₁ (r .scrut-root w)))
            (absorb M.εₘ (G src (at (case-r₁ w))))
  step₁ {G} w nw r .scrut-root p =
    ≈-trans (+ₘ-cong (r .scrut-root p) (∘-cong₁ (r .scrut-root w)))
            (absorb M.εₘ (G (at (case-r₁ p)) (at (case-r₁ w))))
  step₁ {G} w nw r .branch-root p =
    ≈-trans (+ₘ-cong (r .branch-root p) (∘-cong₁ (r .scrut-root w)))
            (absorb (edge M.I p) (G (at (case-r₂ p)) (at (case-r₁ w))))

  steps₁ : ∀ {G H} (ws : List (Path D₁)) → All (λ w → is-ε w ≡ Bool.false) ws →
           Phase₁ G H → Phase₁ (hide-all G (map at (map case-r₁ ws))) (hide-all H (map at ws))
  steps₁ []       []         r = r
  steps₁ (w ∷ ws) (nw ∷ nws) r = steps₁ ws nws (step₁ w nw r)

  private
    hh : ∀ x y → hide (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε)) (at (case-r₁ ε)) x y
         ≈ (graph (⇓-case-r {t₁ = t₁} D₁ D₂) x y
              M.+ₘ (graph (⇓-case-r {t₁ = t₁} D₁ D₂) (at (case-r₁ ε)) y
                      ∘ graph (⇓-case-r {t₁ = t₁} D₁ D₂) x (at (case-r₁ ε))))
    hh = hide-hide-root (⇓-case-r {t₁ = t₁} D₁ D₂) (at (case-r₁ ε))

    base₁ : Phase₁ (hide (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε)) (at (case-r₁ ε)))
                   (hide (graph D₁) (at ε))
    base₁ .env-scrut q = hh env (at (case-r₁ q))
    base₁ .src-scrut q = hh src (at (case-r₁ q))
    base₁ .scrut-scrut p q = hh (at (case-r₁ p)) (at (case-r₁ q))
    base₁ .env-branch q =
      ≈-trans {f = hide (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε)) (at (case-r₁ ε))
                        env (at (case-r₂ q))}
              {g = (B q ∘ iₗ) M.+ₘ (Rt q ∘ graph D₁ env (at ε))}
              {h = (B q ∘ iₗ) M.+ₘ (Rt q ∘ hide (graph D₁) (at ε) env (at ε))}
              (hh env (at (case-r₂ q))) (into-hidden-off D₁ env (B q ∘ iₗ) (Rt q))
    base₁ .src-branch q =
      ≈-trans {f = hide (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε)) (at (case-r₁ ε))
                        src (at (case-r₂ q))}
              {g = (Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ graph D₁ src (at ε))}
              {h = (Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ hide (graph D₁) (at ε) src (at ε))}
              (hh src (at (case-r₂ q))) (into-hidden-off D₁ src (Bₛ q ∘ ctrl-row {1}) (Rt q))
    base₁ .scrut-branch p np q =
      ≈-trans (hh (at (case-r₁ p)) (at (case-r₂ q)))
      (≈-trans (+ₘ-cong (edge-off (Rt q) p np) ≈-refl) (into-hidden D₁ (Rt q) (at p)))
    base₁ .branch-branch p q =
      ≈-trans (hh (at (case-r₂ p)) (at (case-r₂ q)))
              (absorb-r (graph D₂ (at p) (at q)) (Rt q))
    base₁ .branch-scrut p q =
      ≈-trans (hh (at (case-r₂ p)) (at (case-r₁ q))) (absorb-r M.εₘ (graph D₁ (at ε) (at q)))
    base₁ .env-root = ≈-trans (hh env (at ε)) (absorb M.εₘ (graph D₁ env (at ε)))
    base₁ .source-root = ≈-trans (hh src (at ε)) (absorb M.εₘ (graph D₁ src (at ε)))
    base₁ .scrut-root p = ≈-trans (hh (at (case-r₁ p)) (at ε)) (absorb M.εₘ (graph D₁ (at p) (at ε)))
    base₁ .branch-root p =
      ≈-trans (hh (at (case-r₂ p)) (at ε))
              (absorb (edge M.I p)
                      (graph (⇓-case-r {t₁ = t₁} D₁ D₂) (at (case-r₂ p)) (at (case-r₁ ε))))

  record Phase₂ (G : Graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (H : Graph D₂) : Set ℓ where
    field
      env-branch    : ∀ q → G env (at (case-r₂ q))
                      ≈ ((H env (at q) ∘ W) M.+ₘ (H src (at q) ∘ U))
      src-branch    : ∀ q → G src (at (case-r₂ q))
                      ≈ ((H env (at q) ∘ Wₛ) M.+ₘ (H src (at q) ∘ Uₛ))
      branch-branch : ∀ p q → G (at (case-r₂ p)) (at (case-r₂ q)) ≈ H (at p) (at q)
      env-root      : G env (at ε) ≈ ((H env (at ε) ∘ W) M.+ₘ (H src (at ε) ∘ U))
      source-root   : G src (at ε) ≈ ((H env (at ε) ∘ Wₛ) M.+ₘ (H src (at ε) ∘ Uₛ))
      branch-root   : ∀ p → is-ε p ≡ Bool.false → G (at (case-r₂ p)) (at ε) ≈ H (at p) (at ε)

  open Phase₂

  step₂ : ∀ {G H} (w : Path D₂) → is-ε w ≡ Bool.false →
          Phase₂ G H → Phase₂ (hide G (at (case-r₂ w))) (hide H (at w))
  step₂ {H = H} w nw r .env-branch q =
    pair-step {W = W} {U = U} {A = H env (at q)} {B = H src (at q)} {Y = H (at w) (at q)}
              {Aw = H env (at w)} {Bw = H src (at w)}
              (r .env-branch q) (r .branch-branch w q) (r .env-branch w)
  step₂ {H = H} w nw r .src-branch q =
    pair-step {W = Wₛ} {U = Uₛ} {A = H env (at q)} {B = H src (at q)} {Y = H (at w) (at q)}
              {Aw = H env (at w)} {Bw = H src (at w)}
              (r .src-branch q) (r .branch-branch w q) (r .src-branch w)
  step₂ w nw r .branch-branch p q =
    +ₘ-cong (r .branch-branch p q) (∘-cong (r .branch-branch w q) (r .branch-branch p w))
  step₂ {H = H} w nw r .env-root =
    pair-step {W = W} {U = U} {A = H env (at ε)} {B = H src (at ε)} {Y = H (at w) (at ε)}
              {Aw = H env (at w)} {Bw = H src (at w)}
              (r .env-root) (r .branch-root w nw) (r .env-branch w)
  step₂ {H = H} w nw r .source-root =
    pair-step {W = Wₛ} {U = Uₛ} {A = H env (at ε)} {B = H src (at ε)} {Y = H (at w) (at ε)}
              {Aw = H env (at w)} {Bw = H src (at w)}
              (r .source-root) (r .branch-root w nw) (r .src-branch w)
  step₂ w nw r .branch-root p np =
    +ₘ-cong (r .branch-root p np) (∘-cong (r .branch-root w nw) (r .branch-branch p w))

  steps₂ : ∀ {G H} (ws : List (Path D₂)) → All (λ w → is-ε w ≡ Bool.false) ws →
           Phase₂ G H → Phase₂ (hide-all G (map at (map case-r₂ ws))) (hide-all H (map at ws))
  steps₂ []       []         r = r
  steps₂ (w ∷ ws) (nw ∷ nws) r = steps₂ ws nws (step₂ w nw r)

  private
    r1 : Phase₁ (hide-all (hide (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε)) (at (case-r₁ ε)))
                          (map at (map case-r₁ (interior D₁))))
                (hide-all (hide (graph D₁) (at ε)) (map at (interior D₁)))
    r1 = steps₁ (interior D₁) (interior-not-root D₁) base₁

    Zₑ : M.Matrix (width u) (width-env γ)
    Zₑ = (B ε ∘ W) M.+ₘ (Bₛ ε ∘ U)

    Zₛ : M.Matrix (width u) 1
    Zₛ = (B ε ∘ Wₛ) M.+ₘ (Bₛ ε ∘ Uₛ)

    base₂ : Phase₂ (hide (hide-all (hide (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε))
                                         (at (case-r₁ ε)))
                                   (map at (map case-r₁ (interior D₁))))
                         (at (case-r₂ ε)))
                   (hide (graph D₂) (at ε))
    base₂ .env-branch q =
      pair-step {W = W} {U = U} {A = B q} {B = Bₛ q} {Y = graph D₂ (at ε) (at q)}
                {Aw = B ε} {Bw = Bₛ ε}
                (≈-trans (r1 .env-branch q) (route-env (B q) (Bₛ q)))
                (r1 .branch-branch ε q)
                (≈-trans (r1 .env-branch ε) (route-env (B ε) (Bₛ ε)))
    base₂ .src-branch q =
      pair-step {W = Wₛ} {U = Uₛ} {A = B q} {B = Bₛ q} {Y = graph D₂ (at ε) (at q)}
                {Aw = B ε} {Bw = Bₛ ε}
                (≈-trans (r1 .src-branch q) (route-src (B q) (Bₛ q)))
                (r1 .branch-branch ε q)
                (≈-trans (r1 .src-branch ε) (route-src (B ε) (Bₛ ε)))
    base₂ .branch-branch p q =
      +ₘ-cong (r1 .branch-branch p q) (∘-cong (r1 .branch-branch ε q) (r1 .branch-branch p ε))
    base₂ .env-root =
      ≈-trans {g = M.εₘ M.+ₘ (M.I ∘ Zₑ)}
              (+ₘ-cong (r1 .env-root)
                       (∘-cong (r1 .branch-root ε)
                               (≈-trans (r1 .env-branch ε) (route-env (B ε) (Bₛ ε)))))
      (≈-trans {g = M.I ∘ Zₑ} (+ₘ-lunit (M.I ∘ Zₑ))
      (≈-trans {g = Zₑ} id-left
               (+ₘ-cong (∘-cong₁ {g = W} (≈-sym (hide-root D₂ env (at ε))))
                        (∘-cong₁ {g = U} (≈-sym (hide-root D₂ src (at ε)))))))
    base₂ .source-root =
      ≈-trans {g = M.εₘ M.+ₘ (M.I ∘ Zₛ)}
              (+ₘ-cong (r1 .source-root)
                       (∘-cong (r1 .branch-root ε)
                               (≈-trans (r1 .src-branch ε) (route-src (B ε) (Bₛ ε)))))
      (≈-trans {g = M.I ∘ Zₛ} (+ₘ-lunit (M.I ∘ Zₛ))
      (≈-trans {g = Zₛ} id-left
               (+ₘ-cong (∘-cong₁ {g = Wₛ} (≈-sym (hide-root D₂ env (at ε))))
                        (∘-cong₁ {g = Uₛ} (≈-sym (hide-root D₂ src (at ε)))))))
    base₂ .branch-root p np =
      ≈-trans (+ₘ-cong (≈-trans (r1 .branch-root p) (edge-off M.I p np))
                       (∘-cong (r1 .branch-root ε) (r1 .branch-branch p ε)))
      (≈-trans (into-hidden D₂ M.I (at p)) id-left)

    plumb : ∀ (x : Vertex (⇓-case-r {t₁ = t₁} D₁ D₂)) →
            hide-all (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε))
                     (map at (map case-r₁ (paths D₁) ++ map case-r₂ (paths D₂))) x (at ε)
            ≡ hide-all (hide-all (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε))
                                 (map at (map case-r₁ (paths D₁))))
                       (map at (map case-r₂ (paths D₂))) x (at ε)
    plumb x =
      ≡-trans (≡-cong (λ L → hide-all (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε)) L x (at ε))
                      (map-++ at (map case-r₁ (paths D₁)) (map case-r₂ (paths D₂))))
              (≡-cong (λ Gg → Gg x (at ε))
                      (hide-all-++ (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε))
                                   (map at (map case-r₁ (paths D₁)))
                                   (map at (map case-r₂ (paths D₂)))))

  agree : collapse (⇓-case-r {t₁ = t₁} D₁ D₂)
          ≈ ((collapse D₂ ∘ W) M.+ₘ (collapse-src D₂ ∘ U))
  agree =
    ≈-trans (≈-of-≡ (plumb env)) (steps₂ (interior D₂) (interior-not-root D₂) base₂ .env-root)

  agree-src : collapse-src (⇓-case-r {t₁ = t₁} D₁ D₂)
              ≈ ((collapse D₂ ∘ Wₛ) M.+ₘ (collapse-src D₂ ∘ Uₛ))
  agree-src =
    ≈-trans (≈-of-≡ (plumb src)) (steps₂ (interior D₂) (interior-not-root D₂) base₂ .source-root)

-- Application: function, argument, then body. The body's environment is wired to two premise roots,
-- the closure's environment through the function root and the bound variable through the argument
-- root; its source is wired to the function root's control column. Both collapses are the body's
-- two collapses composed with a pair of substitutions.
module App {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {ts : Γ ⊢ σ [→] τ} {tt : Γ ⊢ σ}
           {tb : Γ' ▸ σ ⊢ τ} {v : Val σ} {u : Val τ}
           {R : Nat.suc (width-env γ) ⇒ Nat.suc (width-env γ')}
           {S : Nat.suc (width-env γ) ⇒ width v}
           {T : Nat.suc (width-env (γ' · v)) ⇒ width u}
           {D₁ : γ , ts ⇓ clo γ' tb [ R ]} {D₂ : γ , tt ⇓ v [ S ]}
           {D₃ : γ' · v , tb ⇓ u [ T ]} where

  private
    iₗ : M.Matrix (width-env γ' Nat.+ width v) (width-env γ')
    iₗ = M.in₁ {width-env γ'} {width v}

    iᵣ : M.Matrix (width-env γ' Nat.+ width v) (width v)
    iᵣ = M.in₂ {width-env γ'} {width v}

    p1 : M.Matrix 1 (Nat.suc (width-env γ'))
    p1 = M.p₁ {1} {width-env γ'}

    p2 : M.Matrix (width-env γ') (Nat.suc (width-env γ'))
    p2 = M.p₂ {1} {width-env γ'}

  B : (q : Path D₃) → M.Matrix (width-at q) (width-env γ' Nat.+ width v)
  B q = graph D₃ env (at q)

  Bₛ : (q : Path D₃) → M.Matrix (width-at q) 1
  Bₛ q = graph D₃ src (at q)

  -- The body's dependence on the function root: the closure environment through the value columns,
  -- the body's source through the control column.
  Rt : (q : Path D₃) → M.Matrix (width-at q) (Nat.suc (width-env γ'))
  Rt q = ((B q ∘ iₗ) ∘ p2) M.+ₘ (Bₛ q ∘ p1)

  W : M.Matrix (width-env γ' Nat.+ width v) (width-env γ)
  W = ((iₗ ∘ p2) ∘ collapse D₁) M.+ₘ (iᵣ ∘ collapse D₂)

  U : M.Matrix 1 (width-env γ)
  U = p1 ∘ collapse D₁

  Wₛ : M.Matrix (width-env γ' Nat.+ width v) 1
  Wₛ = ((iₗ ∘ p2) ∘ collapse-src D₁) M.+ₘ (iᵣ ∘ collapse-src D₂)

  Uₛ : M.Matrix 1 1
  Uₛ = ctrl-row {1} M.+ₘ (p1 ∘ collapse-src D₁)

  private
    route-env : ∀ {m} (A : M.Matrix m (width-env γ' Nat.+ width v)) (Bs : M.Matrix m 1) →
                (((((A ∘ iₗ) ∘ p2) M.+ₘ (Bs ∘ p1)) ∘ collapse D₁)
                   M.+ₘ ((A ∘ iᵣ) ∘ collapse D₂))
                ≈ ((A ∘ W) M.+ₘ (Bs ∘ U))
    route-env A Bs =
      ≈-trans (+ₘ-cong (M.comp-bilinear₁ ((A ∘ iₗ) ∘ p2) (Bs ∘ p1) (collapse D₁))
                       (≈-refl {f = (A ∘ iᵣ) ∘ collapse D₂}))
      (≈-trans (+ₘ-swap (((A ∘ iₗ) ∘ p2) ∘ collapse D₁) ((Bs ∘ p1) ∘ collapse D₁)
                        ((A ∘ iᵣ) ∘ collapse D₂))
               (+ₘ-cong (≈-trans (+ₘ-cong (≈-trans (∘-cong₁ {g = collapse D₁} (assoc A iₗ p2))
                                                   (assoc A (iₗ ∘ p2) (collapse D₁)))
                                          (assoc A iᵣ (collapse D₂)))
                                 (≈-sym (M.comp-bilinear₂ A ((iₗ ∘ p2) ∘ collapse D₁)
                                                            (iᵣ ∘ collapse D₂))))
                        (assoc Bs p1 (collapse D₁))))

    route-src : ∀ {m} (A : M.Matrix m (width-env γ' Nat.+ width v)) (Bs : M.Matrix m 1) →
                (((Bs ∘ ctrl-row {1})
                    M.+ₘ ((((A ∘ iₗ) ∘ p2) M.+ₘ (Bs ∘ p1)) ∘ collapse-src D₁))
                   M.+ₘ ((A ∘ iᵣ) ∘ collapse-src D₂))
                ≈ ((A ∘ Wₛ) M.+ₘ (Bs ∘ Uₛ))
    route-src A Bs =
      ≈-trans (+ₘ-cong (+ₘ-cong (≈-refl {f = Bs ∘ ctrl-row {1}})
                                (M.comp-bilinear₁ ((A ∘ iₗ) ∘ p2) (Bs ∘ p1) (collapse-src D₁)))
                       (≈-refl {f = (A ∘ iᵣ) ∘ collapse-src D₂}))
      (≈-trans (+ₘ-assoc (Bs ∘ ctrl-row {1})
                         ((((A ∘ iₗ) ∘ p2) ∘ collapse-src D₁)
                            M.+ₘ ((Bs ∘ p1) ∘ collapse-src D₁))
                         ((A ∘ iᵣ) ∘ collapse-src D₂))
      (≈-trans (+ₘ-cong (≈-refl {f = Bs ∘ ctrl-row {1}})
                        (+ₘ-swap (((A ∘ iₗ) ∘ p2) ∘ collapse-src D₁)
                                 ((Bs ∘ p1) ∘ collapse-src D₁)
                                 ((A ∘ iᵣ) ∘ collapse-src D₂)))
      (≈-trans (+ₘ-swap-mid (Bs ∘ ctrl-row {1})
                            ((((A ∘ iₗ) ∘ p2) ∘ collapse-src D₁)
                               M.+ₘ ((A ∘ iᵣ) ∘ collapse-src D₂))
                            ((Bs ∘ p1) ∘ collapse-src D₁))
               (+ₘ-cong (≈-trans (+ₘ-cong (≈-trans (∘-cong₁ {g = collapse-src D₁} (assoc A iₗ p2))
                                                   (assoc A (iₗ ∘ p2) (collapse-src D₁)))
                                          (assoc A iᵣ (collapse-src D₂)))
                                 (≈-sym (M.comp-bilinear₂ A ((iₗ ∘ p2) ∘ collapse-src D₁)
                                                            (iᵣ ∘ collapse-src D₂))))
                        (≈-trans (+ₘ-cong (≈-refl {f = Bs ∘ ctrl-row {1}})
                                          (assoc Bs p1 (collapse-src D₁)))
                                 (≈-sym (M.comp-bilinear₂ Bs (ctrl-row {1})
                                                            (p1 ∘ collapse-src D₁))))))))

  record Phase₁ (G : Graph (⇓-app D₁ D₂ D₃)) (H : Graph D₁) : Set ℓ where
    field
      env-fun     : ∀ q → G env (at (app₁ q)) ≈ H env (at q)
      src-fun     : ∀ q → G src (at (app₁ q)) ≈ H src (at q)
      fun-fun     : ∀ p q → G (at (app₁ p)) (at (app₁ q)) ≈ H (at p) (at q)
      env-arg     : ∀ q → G env (at (app₂ q)) ≈ graph D₂ env (at q)
      src-arg     : ∀ q → G src (at (app₂ q)) ≈ graph D₂ src (at q)
      arg-arg     : ∀ p q → G (at (app₂ p)) (at (app₂ q)) ≈ graph D₂ (at p) (at q)
      fun-arg     : ∀ p q → G (at (app₁ p)) (at (app₂ q)) ≈ M.εₘ
      arg-fun     : ∀ p q → G (at (app₂ p)) (at (app₁ q)) ≈ M.εₘ
      env-body    : ∀ q → G env (at (app₃ q)) ≈ (Rt q ∘ H env (at ε))
      src-body    : ∀ q → G src (at (app₃ q))
                    ≈ ((Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ H src (at ε)))
      fun-body    : ∀ p → is-ε p ≡ Bool.false → ∀ q →
                    G (at (app₁ p)) (at (app₃ q)) ≈ (Rt q ∘ H (at p) (at ε))
      arg-body    : ∀ p q → G (at (app₂ p)) (at (app₃ q)) ≈ edge (B q ∘ iᵣ) p
      body-body   : ∀ p q → G (at (app₃ p)) (at (app₃ q)) ≈ graph D₃ (at p) (at q)
      body-fun    : ∀ p q → G (at (app₃ p)) (at (app₁ q)) ≈ M.εₘ
      body-arg    : ∀ p q → G (at (app₃ p)) (at (app₂ q)) ≈ M.εₘ
      env-root    : G env (at ε) ≈ M.εₘ
      source-root : G src (at ε) ≈ M.εₘ
      fun-root    : ∀ p → G (at (app₁ p)) (at ε) ≈ M.εₘ
      arg-root    : ∀ p → G (at (app₂ p)) (at ε) ≈ M.εₘ
      body-root   : ∀ p → G (at (app₃ p)) (at ε) ≈ edge M.I p

  open Phase₁

  step₁ : ∀ {G H} (w : Path D₁) → is-ε w ≡ Bool.false →
          Phase₁ G H → Phase₁ (hide G (at (app₁ w))) (hide H (at w))
  step₁ w nw r .env-fun q = +ₘ-cong (r .env-fun q) (∘-cong (r .fun-fun w q) (r .env-fun w))
  step₁ w nw r .src-fun q = +ₘ-cong (r .src-fun q) (∘-cong (r .fun-fun w q) (r .src-fun w))
  step₁ w nw r .fun-fun p q = +ₘ-cong (r .fun-fun p q) (∘-cong (r .fun-fun w q) (r .fun-fun p w))
  step₁ {G} w nw r .env-arg q =
    ≈-trans (+ₘ-cong (r .env-arg q) (∘-cong₁ (r .fun-arg w q)))
            (absorb (graph D₂ env (at q)) (G env (at (app₁ w))))
  step₁ {G} w nw r .src-arg q =
    ≈-trans (+ₘ-cong (r .src-arg q) (∘-cong₁ (r .fun-arg w q)))
            (absorb (graph D₂ src (at q)) (G src (at (app₁ w))))
  step₁ {G} w nw r .arg-arg p q =
    ≈-trans (+ₘ-cong (r .arg-arg p q) (∘-cong₁ (r .fun-arg w q)))
            (absorb (graph D₂ (at p) (at q)) (G (at (app₂ p)) (at (app₁ w))))
  step₁ {G} w nw r .fun-arg p q =
    ≈-trans (+ₘ-cong (r .fun-arg p q) (∘-cong₁ (r .fun-arg w q)))
            (absorb M.εₘ (G (at (app₁ p)) (at (app₁ w))))
  step₁ {G} w nw r .arg-fun p q =
    ≈-trans (+ₘ-cong (r .arg-fun p q) (∘-cong₂ (r .arg-fun p w)))
            (absorb-r M.εₘ (G (at (app₁ w)) (at (app₁ q))))
  step₁ {H = H} w nw r .env-body q =
    root-step {P = Rt q} {X = H env (at ε)} {Y = H (at w) (at ε)} {Z = H env (at w)}
      (r .env-body q) (r .fun-body w nw q) (r .env-fun w)
  step₁ {H = H} w nw r .src-body q =
    offset-step {K = Bₛ q ∘ ctrl-row {1}} {P = Rt q}
                {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
      (r .src-body q) (r .fun-body w nw q) (r .src-fun w)
  step₁ {H = H} w nw r .fun-body p np q =
    root-step {P = Rt q} {X = H (at p) (at ε)} {Y = H (at w) (at ε)} {Z = H (at p) (at w)}
      (r .fun-body p np q) (r .fun-body w nw q) (r .fun-fun p w)
  step₁ {G} w nw r .arg-body p q =
    ≈-trans (+ₘ-cong (r .arg-body p q) (∘-cong₂ (r .arg-fun p w)))
            (absorb-r (edge (B q ∘ iᵣ) p) (G (at (app₁ w)) (at (app₃ q))))
  step₁ {G} w nw r .body-body p q =
    ≈-trans (+ₘ-cong (r .body-body p q) (∘-cong₂ (r .body-fun p w)))
            (absorb-r (graph D₃ (at p) (at q)) (G (at (app₁ w)) (at (app₃ q))))
  step₁ {G} w nw r .body-fun p q =
    ≈-trans (+ₘ-cong (r .body-fun p q) (∘-cong₂ (r .body-fun p w)))
            (absorb-r M.εₘ (G (at (app₁ w)) (at (app₁ q))))
  step₁ {G} w nw r .body-arg p q =
    ≈-trans (+ₘ-cong (r .body-arg p q) (∘-cong₁ (r .fun-arg w q)))
            (absorb M.εₘ (G (at (app₃ p)) (at (app₁ w))))
  step₁ {G} w nw r .env-root =
    ≈-trans (+ₘ-cong (r .env-root) (∘-cong₁ (r .fun-root w)))
            (absorb M.εₘ (G env (at (app₁ w))))
  step₁ {G} w nw r .source-root =
    ≈-trans (+ₘ-cong (r .source-root) (∘-cong₁ (r .fun-root w)))
            (absorb M.εₘ (G src (at (app₁ w))))
  step₁ {G} w nw r .fun-root p =
    ≈-trans (+ₘ-cong (r .fun-root p) (∘-cong₁ (r .fun-root w)))
            (absorb M.εₘ (G (at (app₁ p)) (at (app₁ w))))
  step₁ {G} w nw r .arg-root p =
    ≈-trans (+ₘ-cong (r .arg-root p) (∘-cong₂ (r .arg-fun p w)))
            (absorb-r M.εₘ (G (at (app₁ w)) (at ε)))
  step₁ {G} w nw r .body-root p =
    ≈-trans (+ₘ-cong (r .body-root p) (∘-cong₂ (r .body-fun p w)))
            (absorb-r (edge M.I p) (G (at (app₁ w)) (at ε)))

  steps₁ : ∀ {G H} (ws : List (Path D₁)) → All (λ w → is-ε w ≡ Bool.false) ws →
           Phase₁ G H → Phase₁ (hide-all G (map at (map app₁ ws))) (hide-all H (map at ws))
  steps₁ []       []         r = r
  steps₁ (w ∷ ws) (nw ∷ nws) r = steps₁ ws nws (step₁ w nw r)

  private
    hh : ∀ x y → hide (hide (graph (⇓-app D₁ D₂ D₃)) (at ε)) (at (app₁ ε)) x y
         ≈ (graph (⇓-app D₁ D₂ D₃) x y
              M.+ₘ (graph (⇓-app D₁ D₂ D₃) (at (app₁ ε)) y
                      ∘ graph (⇓-app D₁ D₂ D₃) x (at (app₁ ε))))
    hh = hide-hide-root (⇓-app D₁ D₂ D₃) (at (app₁ ε))

    base₁ : Phase₁ (hide (hide (graph (⇓-app D₁ D₂ D₃)) (at ε)) (at (app₁ ε)))
                   (hide (graph D₁) (at ε))
    base₁ .env-fun q = hh env (at (app₁ q))
    base₁ .src-fun q = hh src (at (app₁ q))
    base₁ .fun-fun p q = hh (at (app₁ p)) (at (app₁ q))
    base₁ .env-arg q =
      ≈-trans (hh env (at (app₂ q))) (absorb (graph D₂ env (at q)) (graph D₁ env (at ε)))
    base₁ .src-arg q =
      ≈-trans (hh src (at (app₂ q))) (absorb (graph D₂ src (at q)) (graph D₁ src (at ε)))
    base₁ .arg-arg p q =
      ≈-trans (hh (at (app₂ p)) (at (app₂ q)))
              (absorb (graph D₂ (at p) (at q))
                      (graph (⇓-app D₁ D₂ D₃) (at (app₂ p)) (at (app₁ ε))))
    base₁ .fun-arg p q =
      ≈-trans (hh (at (app₁ p)) (at (app₂ q))) (absorb M.εₘ (graph D₁ (at p) (at ε)))
    base₁ .arg-fun p q =
      ≈-trans (hh (at (app₂ p)) (at (app₁ q))) (absorb-r M.εₘ (graph D₁ (at ε) (at q)))
    base₁ .env-body q = ≈-trans (hh env (at (app₃ q))) (into-hidden D₁ (Rt q) env)
    base₁ .src-body q =
      ≈-trans {f = hide (hide (graph (⇓-app D₁ D₂ D₃)) (at ε)) (at (app₁ ε)) src (at (app₃ q))}
              {g = (Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ graph D₁ src (at ε))}
              {h = (Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ hide (graph D₁) (at ε) src (at ε))}
              (hh src (at (app₃ q))) (into-hidden-off D₁ src (Bₛ q ∘ ctrl-row {1}) (Rt q))
    base₁ .fun-body p np q =
      ≈-trans (hh (at (app₁ p)) (at (app₃ q)))
      (≈-trans (+ₘ-cong (edge-off (Rt q) p np) ≈-refl) (into-hidden D₁ (Rt q) (at p)))
    base₁ .arg-body p q =
      ≈-trans (hh (at (app₂ p)) (at (app₃ q))) (absorb-r (edge (B q ∘ iᵣ) p) (Rt q))
    base₁ .body-body p q =
      ≈-trans (hh (at (app₃ p)) (at (app₃ q))) (absorb-r (graph D₃ (at p) (at q)) (Rt q))
    base₁ .body-fun p q =
      ≈-trans (hh (at (app₃ p)) (at (app₁ q))) (absorb-r M.εₘ (graph D₁ (at ε) (at q)))
    base₁ .body-arg p q =
      ≈-trans (hh (at (app₃ p)) (at (app₂ q)))
              (absorb M.εₘ (graph (⇓-app D₁ D₂ D₃) (at (app₃ p)) (at (app₁ ε))))
    base₁ .env-root = ≈-trans (hh env (at ε)) (absorb M.εₘ (graph D₁ env (at ε)))
    base₁ .source-root = ≈-trans (hh src (at ε)) (absorb M.εₘ (graph D₁ src (at ε)))
    base₁ .fun-root p = ≈-trans (hh (at (app₁ p)) (at ε)) (absorb M.εₘ (graph D₁ (at p) (at ε)))
    base₁ .arg-root p =
      ≈-trans (hh (at (app₂ p)) (at ε))
              (absorb M.εₘ (graph (⇓-app D₁ D₂ D₃) (at (app₂ p)) (at (app₁ ε))))
    base₁ .body-root p =
      ≈-trans (hh (at (app₃ p)) (at ε))
              (absorb (edge M.I p) (graph (⇓-app D₁ D₂ D₃) (at (app₃ p)) (at (app₁ ε))))

    PA : Graph (⇓-app D₁ D₂ D₃)
    PA = hide-all (hide (hide (graph (⇓-app D₁ D₂ D₃)) (at ε)) (at (app₁ ε)))
                  (map at (map app₁ (interior D₁)))

    rA : Phase₁ PA (hide-all (hide (graph D₁) (at ε)) (map at (interior D₁)))
    rA = steps₁ (interior D₁) (interior-not-root D₁) base₁

  record Phase₂ (G : Graph (⇓-app D₁ D₂ D₃)) (H : Graph D₂) : Set ℓ where
    field
      env-arg     : ∀ q → G env (at (app₂ q)) ≈ H env (at q)
      src-arg     : ∀ q → G src (at (app₂ q)) ≈ H src (at q)
      arg-arg     : ∀ p q → G (at (app₂ p)) (at (app₂ q)) ≈ H (at p) (at q)
      env-body    : ∀ q → G env (at (app₃ q))
                    ≈ ((Rt q ∘ collapse D₁) M.+ₘ ((B q ∘ iᵣ) ∘ H env (at ε)))
      src-body    : ∀ q → G src (at (app₃ q))
                    ≈ (((Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ collapse-src D₁))
                         M.+ₘ ((B q ∘ iᵣ) ∘ H src (at ε)))
      arg-body    : ∀ p → is-ε p ≡ Bool.false → ∀ q →
                    G (at (app₂ p)) (at (app₃ q)) ≈ ((B q ∘ iᵣ) ∘ H (at p) (at ε))
      body-body   : ∀ p q → G (at (app₃ p)) (at (app₃ q)) ≈ graph D₃ (at p) (at q)
      body-arg    : ∀ p q → G (at (app₃ p)) (at (app₂ q)) ≈ M.εₘ
      env-root    : G env (at ε) ≈ M.εₘ
      source-root : G src (at ε) ≈ M.εₘ
      arg-root    : ∀ p → G (at (app₂ p)) (at ε) ≈ M.εₘ
      body-root   : ∀ p → G (at (app₃ p)) (at ε) ≈ edge M.I p

  open Phase₂

  step₂ : ∀ {G H} (w : Path D₂) → is-ε w ≡ Bool.false →
          Phase₂ G H → Phase₂ (hide G (at (app₂ w))) (hide H (at w))
  step₂ w nw r .env-arg q = +ₘ-cong (r .env-arg q) (∘-cong (r .arg-arg w q) (r .env-arg w))
  step₂ w nw r .src-arg q = +ₘ-cong (r .src-arg q) (∘-cong (r .arg-arg w q) (r .src-arg w))
  step₂ w nw r .arg-arg p q = +ₘ-cong (r .arg-arg p q) (∘-cong (r .arg-arg w q) (r .arg-arg p w))
  step₂ {H = H} w nw r .env-body q =
    offset-step {K = Rt q ∘ collapse D₁} {P = B q ∘ iᵣ}
                {X = H env (at ε)} {Y = H (at w) (at ε)} {Z = H env (at w)}
                (r .env-body q) (r .arg-body w nw q) (r .env-arg w)
  step₂ {H = H} w nw r .src-body q =
    offset-step {K = (Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ collapse-src D₁)} {P = B q ∘ iᵣ}
                {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
                (r .src-body q) (r .arg-body w nw q) (r .src-arg w)
  step₂ {H = H} w nw r .arg-body p np q =
    root-step {P = B q ∘ iᵣ} {X = H (at p) (at ε)} {Y = H (at w) (at ε)} {Z = H (at p) (at w)}
              (r .arg-body p np q) (r .arg-body w nw q) (r .arg-arg p w)
  step₂ {G} w nw r .body-body p q =
    ≈-trans (+ₘ-cong (r .body-body p q) (∘-cong₂ (r .body-arg p w)))
            (absorb-r (graph D₃ (at p) (at q)) (G (at (app₂ w)) (at (app₃ q))))
  step₂ {G} w nw r .body-arg p q =
    ≈-trans (+ₘ-cong (r .body-arg p q) (∘-cong₂ (r .body-arg p w)))
            (absorb-r M.εₘ (G (at (app₂ w)) (at (app₂ q))))
  step₂ {G} w nw r .env-root =
    ≈-trans (+ₘ-cong (r .env-root) (∘-cong₁ (r .arg-root w)))
            (absorb M.εₘ (G env (at (app₂ w))))
  step₂ {G} w nw r .source-root =
    ≈-trans (+ₘ-cong (r .source-root) (∘-cong₁ (r .arg-root w)))
            (absorb M.εₘ (G src (at (app₂ w))))
  step₂ {G} w nw r .arg-root p =
    ≈-trans (+ₘ-cong (r .arg-root p) (∘-cong₁ (r .arg-root w)))
            (absorb M.εₘ (G (at (app₂ p)) (at (app₂ w))))
  step₂ {G} w nw r .body-root p =
    ≈-trans (+ₘ-cong (r .body-root p) (∘-cong₁ (r .arg-root w)))
            (absorb (edge M.I p) (G (at (app₃ p)) (at (app₂ w))))

  steps₂ : ∀ {G H} (ws : List (Path D₂)) → All (λ w → is-ε w ≡ Bool.false) ws →
           Phase₂ G H → Phase₂ (hide-all G (map at (map app₂ ws))) (hide-all H (map at ws))
  steps₂ []       []         r = r
  steps₂ (w ∷ ws) (nw ∷ nws) r = steps₂ ws nws (step₂ w nw r)

  private
    base₂ : Phase₂ (hide PA (at (app₂ ε))) (hide (graph D₂) (at ε))
    base₂ .env-arg q = +ₘ-cong (rA .env-arg q) (∘-cong (rA .arg-arg ε q) (rA .env-arg ε))
    base₂ .src-arg q = +ₘ-cong (rA .src-arg q) (∘-cong (rA .arg-arg ε q) (rA .src-arg ε))
    base₂ .arg-arg p q = +ₘ-cong (rA .arg-arg p q) (∘-cong (rA .arg-arg ε q) (rA .arg-arg p ε))
    base₂ .env-body q =
      ≈-trans (+ₘ-cong (rA .env-body q) (∘-cong (rA .arg-body ε q) (rA .env-arg ε)))
              (+ₘ-cong (≈-refl {f = Rt q ∘ collapse D₁})
                       (∘-cong₂ {f = B q ∘ iᵣ} (≈-sym (hide-root D₂ env (at ε)))))
    base₂ .src-body q =
      ≈-trans (+ₘ-cong (rA .src-body q) (∘-cong (rA .arg-body ε q) (rA .src-arg ε)))
              (+ₘ-cong (≈-refl {f = (Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ collapse-src D₁)})
                       (∘-cong₂ {f = B q ∘ iᵣ} (≈-sym (hide-root D₂ src (at ε)))))
    base₂ .arg-body p np q =
      ≈-trans (+ₘ-cong (≈-trans (rA .arg-body p q) (edge-off (B q ∘ iᵣ) p np))
                       (∘-cong (rA .arg-body ε q) (rA .arg-arg p ε)))
              (into-hidden D₂ (B q ∘ iᵣ) (at p))
    base₂ .body-body p q =
      ≈-trans (+ₘ-cong (rA .body-body p q) (∘-cong (rA .arg-body ε q) (rA .body-arg p ε)))
              (absorb-r (graph D₃ (at p) (at q)) (B q ∘ iᵣ))
    base₂ .body-arg p q =
      ≈-trans (+ₘ-cong (rA .body-arg p q) (∘-cong (rA .arg-arg ε q) (rA .body-arg p ε)))
              (absorb-r M.εₘ (graph D₂ (at ε) (at q)))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (rA .env-root) (∘-cong₁ (rA .arg-root ε)))
              (absorb M.εₘ (PA env (at (app₂ ε))))
    base₂ .source-root =
      ≈-trans (+ₘ-cong (rA .source-root) (∘-cong₁ (rA .arg-root ε)))
              (absorb M.εₘ (PA src (at (app₂ ε))))
    base₂ .arg-root p =
      ≈-trans (+ₘ-cong (rA .arg-root p) (∘-cong₁ (rA .arg-root ε)))
              (absorb M.εₘ (PA (at (app₂ p)) (at (app₂ ε))))
    base₂ .body-root p =
      ≈-trans (+ₘ-cong (rA .body-root p) (∘-cong₁ (rA .arg-root ε)))
              (absorb (edge M.I p) (PA (at (app₃ p)) (at (app₂ ε))))

    PB : Graph (⇓-app D₁ D₂ D₃)
    PB = hide-all (hide PA (at (app₂ ε))) (map at (map app₂ (interior D₂)))

    rB : Phase₂ PB (hide-all (hide (graph D₂) (at ε)) (map at (interior D₂)))
    rB = steps₂ (interior D₂) (interior-not-root D₂) base₂

  record Phase₃ (G : Graph (⇓-app D₁ D₂ D₃)) (H : Graph D₃) : Set ℓ where
    field
      env-body    : ∀ q → G env (at (app₃ q))
                    ≈ ((H env (at q) ∘ W) M.+ₘ (H src (at q) ∘ U))
      src-body    : ∀ q → G src (at (app₃ q))
                    ≈ ((H env (at q) ∘ Wₛ) M.+ₘ (H src (at q) ∘ Uₛ))
      body-body   : ∀ p q → G (at (app₃ p)) (at (app₃ q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ ((H env (at ε) ∘ W) M.+ₘ (H src (at ε) ∘ U))
      source-root : G src (at ε) ≈ ((H env (at ε) ∘ Wₛ) M.+ₘ (H src (at ε) ∘ Uₛ))
      body-root   : ∀ p → is-ε p ≡ Bool.false → G (at (app₃ p)) (at ε) ≈ H (at p) (at ε)

  open Phase₃

  step₃ : ∀ {G H} (w : Path D₃) → is-ε w ≡ Bool.false →
          Phase₃ G H → Phase₃ (hide G (at (app₃ w))) (hide H (at w))
  step₃ {H = H} w nw r .env-body q =
    pair-step {W = W} {U = U} {A = H env (at q)} {B = H src (at q)} {Y = H (at w) (at q)}
              {Aw = H env (at w)} {Bw = H src (at w)}
              (r .env-body q) (r .body-body w q) (r .env-body w)
  step₃ {H = H} w nw r .src-body q =
    pair-step {W = Wₛ} {U = Uₛ} {A = H env (at q)} {B = H src (at q)} {Y = H (at w) (at q)}
              {Aw = H env (at w)} {Bw = H src (at w)}
              (r .src-body q) (r .body-body w q) (r .src-body w)
  step₃ w nw r .body-body p q =
    +ₘ-cong (r .body-body p q) (∘-cong (r .body-body w q) (r .body-body p w))
  step₃ {H = H} w nw r .env-root =
    pair-step {W = W} {U = U} {A = H env (at ε)} {B = H src (at ε)} {Y = H (at w) (at ε)}
              {Aw = H env (at w)} {Bw = H src (at w)}
              (r .env-root) (r .body-root w nw) (r .env-body w)
  step₃ {H = H} w nw r .source-root =
    pair-step {W = Wₛ} {U = Uₛ} {A = H env (at ε)} {B = H src (at ε)} {Y = H (at w) (at ε)}
              {Aw = H env (at w)} {Bw = H src (at w)}
              (r .source-root) (r .body-root w nw) (r .src-body w)
  step₃ w nw r .body-root p np =
    +ₘ-cong (r .body-root p np) (∘-cong (r .body-root w nw) (r .body-body p w))

  steps₃ : ∀ {G H} (ws : List (Path D₃)) → All (λ w → is-ε w ≡ Bool.false) ws →
           Phase₃ G H → Phase₃ (hide-all G (map at (map app₃ ws))) (hide-all H (map at ws))
  steps₃ []       []         r = r
  steps₃ (w ∷ ws) (nw ∷ nws) r = steps₃ ws nws (step₃ w nw r)

  private
    Zₑ : M.Matrix (width u) (width-env γ)
    Zₑ = (B ε ∘ W) M.+ₘ (Bₛ ε ∘ U)

    Zₛ : M.Matrix (width u) 1
    Zₛ = (B ε ∘ Wₛ) M.+ₘ (Bₛ ε ∘ Uₛ)

    base₃ : Phase₃ (hide PB (at (app₃ ε))) (hide (graph D₃) (at ε))
    base₃ .env-body q =
      pair-step {W = W} {U = U} {A = B q} {B = Bₛ q} {Y = graph D₃ (at ε) (at q)}
                {Aw = B ε} {Bw = Bₛ ε}
                (≈-trans (rB .env-body q) (route-env (B q) (Bₛ q)))
                (rB .body-body ε q)
                (≈-trans (rB .env-body ε) (route-env (B ε) (Bₛ ε)))
    base₃ .src-body q =
      pair-step {W = Wₛ} {U = Uₛ} {A = B q} {B = Bₛ q} {Y = graph D₃ (at ε) (at q)}
                {Aw = B ε} {Bw = Bₛ ε}
                (≈-trans (rB .src-body q) (route-src (B q) (Bₛ q)))
                (rB .body-body ε q)
                (≈-trans (rB .src-body ε) (route-src (B ε) (Bₛ ε)))
    base₃ .body-body p q =
      +ₘ-cong (rB .body-body p q) (∘-cong (rB .body-body ε q) (rB .body-body p ε))
    base₃ .env-root =
      ≈-trans {g = M.εₘ M.+ₘ (M.I ∘ Zₑ)}
              (+ₘ-cong (rB .env-root)
                       (∘-cong (rB .body-root ε)
                               (≈-trans (rB .env-body ε) (route-env (B ε) (Bₛ ε)))))
      (≈-trans {g = M.I ∘ Zₑ} (+ₘ-lunit (M.I ∘ Zₑ))
      (≈-trans {g = Zₑ} id-left
               (+ₘ-cong (∘-cong₁ {g = W} (≈-sym (hide-root D₃ env (at ε))))
                        (∘-cong₁ {g = U} (≈-sym (hide-root D₃ src (at ε)))))))
    base₃ .source-root =
      ≈-trans {g = M.εₘ M.+ₘ (M.I ∘ Zₛ)}
              (+ₘ-cong (rB .source-root)
                       (∘-cong (rB .body-root ε)
                               (≈-trans (rB .src-body ε) (route-src (B ε) (Bₛ ε)))))
      (≈-trans {g = M.I ∘ Zₛ} (+ₘ-lunit (M.I ∘ Zₛ))
      (≈-trans {g = Zₛ} id-left
               (+ₘ-cong (∘-cong₁ {g = Wₛ} (≈-sym (hide-root D₃ env (at ε))))
                        (∘-cong₁ {g = Uₛ} (≈-sym (hide-root D₃ src (at ε)))))))
    base₃ .body-root p np =
      ≈-trans (+ₘ-cong (≈-trans (rB .body-root p) (edge-off M.I p np))
                       (∘-cong (rB .body-root ε) (rB .body-body p ε)))
      (≈-trans (into-hidden D₃ M.I (at p)) id-left)

    A₁ : Graph (⇓-app D₁ D₂ D₃)
    A₁ = hide (graph (⇓-app D₁ D₂ D₃)) (at ε)

    plumb : ∀ (x : Vertex (⇓-app D₁ D₂ D₃)) →
            hide-all A₁ (map at (map app₁ (paths D₁)
                                   ++ map app₂ (paths D₂) ++ map app₃ (paths D₃))) x (at ε)
            ≡ hide-all (hide-all (hide-all A₁ (map at (map app₁ (paths D₁))))
                                 (map at (map app₂ (paths D₂))))
                       (map at (map app₃ (paths D₃))) x (at ε)
    plumb x =
      ≡-trans (≡-cong (λ L → hide-all A₁ L x (at ε))
                      (≡-trans (map-++ at (map app₁ (paths D₁))
                                          (map app₂ (paths D₂) ++ map app₃ (paths D₃)))
                               (≡-cong (λ z → map at (map app₁ (paths D₁)) ++ z)
                                       (map-++ at (map app₂ (paths D₂)) (map app₃ (paths D₃))))))
      (≡-trans (≡-cong (λ Gg → Gg x (at ε))
                       (hide-all-++ A₁ (map at (map app₁ (paths D₁)))
                                    (map at (map app₂ (paths D₂))
                                       ++ map at (map app₃ (paths D₃)))))
               (≡-cong (λ Gg → Gg x (at ε))
                       (hide-all-++ (hide-all A₁ (map at (map app₁ (paths D₁))))
                                    (map at (map app₂ (paths D₂)))
                                    (map at (map app₃ (paths D₃))))))

  agree : collapse (⇓-app D₁ D₂ D₃) ≈ ((collapse D₃ ∘ W) M.+ₘ (collapse-src D₃ ∘ U))
  agree =
    ≈-trans (≈-of-≡ (plumb env)) (steps₃ (interior D₃) (interior-not-root D₃) base₃ .env-root)

  agree-src : collapse-src (⇓-app D₁ D₂ D₃) ≈ ((collapse D₃ ∘ Wₛ) M.+ₘ (collapse-src D₃ ∘ Uₛ))
  agree-src =
    ≈-trans (≈-of-≡ (plumb src)) (steps₃ (interior D₃) (interior-not-root D₃) base₃ .source-root)

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

-- An operand cons: head premise then tail premise, as for pair but with the tail in the S family.
module SCons {Γ i is} {γ : Env Γ} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is}
             {v : sort-val i} {vs : sort-vals is}
             {R : Nat.suc (width-env γ) ⇒ width (const {s = i} v)}
             {Rs : Nat.suc (width-env γ) ⇒ bases-width is}
             {D₁ : γ , M ⇓ const v [ R ]} {D₂ : γ , Ms ⇓s vs [ Rs ]} where

  private
    j₁ : M.Matrix (bases-width (i ∷ is)) (sort-width i)
    j₁ = M.in₁ {sort-width i} {bases-width is}

    j₂ : M.Matrix (bases-width (i ∷ is)) (bases-width is)
    j₂ = M.in₂ {sort-width i} {bases-width is}

  record Phase₁ (G : GraphS (D₁ ∷ D₂)) (H : Graph D₁) : Set ℓ where
    field
      env-left    : ∀ q → G env (at (hd q)) ≈ H env (at q)
      src-left    : ∀ q → G src (at (hd q)) ≈ H src (at q)
      left-left   : ∀ p q → G (at (hd p)) (at (hd q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (j₁ ∘ H env (at ε))
      source-root : G src (at ε) ≈ (j₁ ∘ H src (at ε))
      left-root   : ∀ p → is-ε p ≡ Bool.false →
                    G (at (hd p)) (at ε) ≈ (j₁ ∘ H (at p) (at ε))
      env-right   : ∀ q → G env (at (tl q)) ≈ graph-s D₂ env (at q)
      src-right   : ∀ q → G src (at (tl q)) ≈ graph-s D₂ src (at q)
      right-right : ∀ p q → G (at (tl p)) (at (tl q)) ≈ graph-s D₂ (at p) (at q)
      right-root  : ∀ p → G (at (tl p)) (at ε) ≈ edge-s j₂ p
      left-right  : ∀ p q → G (at (hd p)) (at (tl q)) ≈ M.εₘ
      right-left  : ∀ p q → G (at (tl p)) (at (hd q)) ≈ M.εₘ

  open Phase₁

  step₁ : ∀ {G H} (w : Path D₁) → is-ε w ≡ Bool.false →
          Phase₁ G H → Phase₁ (hide-s G (at (hd w))) (hide H (at w))
  step₁ w nw r .env-left q = +ₘ-cong (r .env-left q) (∘-cong (r .left-left w q) (r .env-left w))
  step₁ w nw r .src-left q = +ₘ-cong (r .src-left q) (∘-cong (r .left-left w q) (r .src-left w))
  step₁ w nw r .left-left p q =
    +ₘ-cong (r .left-left p q) (∘-cong (r .left-left w q) (r .left-left p w))
  step₁ w nw r .env-root = root-step {P = j₁} (r .env-root) (r .left-root w nw) (r .env-left w)
  step₁ w nw r .source-root = root-step {P = j₁} (r .source-root) (r .left-root w nw) (r .src-left w)
  step₁ w nw r .left-root p np =
    root-step {P = j₁} (r .left-root p np) (r .left-root w nw) (r .left-left p w)
  step₁ {G} w nw r .env-right q =
    ≈-trans (+ₘ-cong (r .env-right q) (∘-cong₁ (r .left-right w q)))
            (absorb (graph-s D₂ env (at q)) (G env (at (hd w))))
  step₁ {G} w nw r .src-right q =
    ≈-trans (+ₘ-cong (r .src-right q) (∘-cong₁ (r .left-right w q)))
            (absorb (graph-s D₂ src (at q)) (G src (at (hd w))))
  step₁ {G} w nw r .right-right p q =
    ≈-trans (+ₘ-cong (r .right-right p q) (∘-cong₁ (r .left-right w q)))
            (absorb (graph-s D₂ (at p) (at q)) (G (at (tl p)) (at (hd w))))
  step₁ {G} w nw r .right-root p =
    ≈-trans (+ₘ-cong (r .right-root p) (∘-cong₂ (r .right-left p w)))
            (absorb-r (edge-s j₂ p) (G (at (hd w)) (at ε)))
  step₁ {G} w nw r .left-right p q =
    ≈-trans (+ₘ-cong (r .left-right p q) (∘-cong₁ (r .left-right w q)))
            (absorb M.εₘ (G (at (hd p)) (at (hd w))))
  step₁ {G} w nw r .right-left p q =
    ≈-trans (+ₘ-cong (r .right-left p q) (∘-cong₂ (r .right-left p w)))
            (absorb-r M.εₘ (G (at (hd w)) (at (hd q))))

  steps₁ : ∀ {G H} (ws : List (Path D₁)) → All (λ w → is-ε w ≡ Bool.false) ws →
           Phase₁ G H → Phase₁ (hide-all-s G (map at (map hd ws))) (hide-all H (map at ws))
  steps₁ []       []         r = r
  steps₁ (w ∷ ws) (nw ∷ nws) r = steps₁ ws nws (step₁ w nw r)

  private
    hh : ∀ x y → hide-s (hide-s (graph-s (D₁ ∷ D₂)) (at ε)) (at (hd ε)) x y
         ≈ (graph-s (D₁ ∷ D₂) x y
              M.+ₘ (graph-s (D₁ ∷ D₂) (at (hd ε)) y ∘ graph-s (D₁ ∷ D₂) x (at (hd ε))))
    hh = hide-hide-root-s (D₁ ∷ D₂) (at (hd ε))

    base₁ : Phase₁ (hide-s (hide-s (graph-s (D₁ ∷ D₂)) (at ε)) (at (hd ε)))
                   (hide (graph D₁) (at ε))
    base₁ .env-left q = hh env (at (hd q))
    base₁ .src-left q = hh src (at (hd q))
    base₁ .left-left p q = hh (at (hd p)) (at (hd q))
    base₁ .env-root = ≈-trans (hh env (at ε)) (into-hidden D₁ j₁ env)
    base₁ .source-root = ≈-trans (hh src (at ε)) (into-hidden D₁ j₁ src)
    base₁ .left-root p np =
      ≈-trans (hh (at (hd p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off j₁ p np) ≈-refl) (into-hidden D₁ j₁ (at p)))
    base₁ .env-right q =
      ≈-trans (hh env (at (tl q))) (absorb (graph-s D₂ env (at q)) (graph D₁ env (at ε)))
    base₁ .src-right q =
      ≈-trans (hh src (at (tl q))) (absorb (graph-s D₂ src (at q)) (graph D₁ src (at ε)))
    base₁ .right-right p q =
      ≈-trans (hh (at (tl p)) (at (tl q)))
              (absorb (graph-s D₂ (at p) (at q)) (graph-s (D₁ ∷ D₂) (at (tl p)) (at (hd ε))))
    base₁ .right-root p =
      ≈-trans (hh (at (tl p)) (at ε))
              (absorb-r (edge-s j₂ p) (graph-s (D₁ ∷ D₂) (at (hd ε)) (at ε)))
    base₁ .left-right p q =
      ≈-trans (hh (at (hd p)) (at (tl q))) (absorb M.εₘ (graph D₁ (at p) (at ε)))
    base₁ .right-left p q =
      ≈-trans (hh (at (tl p)) (at (hd q))) (absorb-r M.εₘ (graph D₁ (at ε) (at q)))

  record Phase₂ (G : GraphS (D₁ ∷ D₂)) (H : GraphS D₂)
                (K : M.Matrix (bases-width (i ∷ is)) (width-env γ))
                (Kₛ : M.Matrix (bases-width (i ∷ is)) 1) : Set ℓ where
    field
      env-right   : ∀ q → G env (at (tl q)) ≈ H env (at q)
      src-right   : ∀ q → G src (at (tl q)) ≈ H src (at q)
      right-right : ∀ p q → G (at (tl p)) (at (tl q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (K M.+ₘ (j₂ ∘ H env (at ε)))
      source-root : G src (at ε) ≈ (Kₛ M.+ₘ (j₂ ∘ H src (at ε)))
      right-root  : ∀ p → is-ε-s p ≡ Bool.false →
                    G (at (tl p)) (at ε) ≈ (j₂ ∘ H (at p) (at ε))

  open Phase₂

  step₂ : ∀ {G H K Kₛ} (w : PathS D₂) → is-ε-s w ≡ Bool.false →
          Phase₂ G H K Kₛ → Phase₂ (hide-s G (at (tl w))) (hide-s H (at w)) K Kₛ
  step₂ w nw r .env-right q = +ₘ-cong (r .env-right q) (∘-cong (r .right-right w q) (r .env-right w))
  step₂ w nw r .src-right q = +ₘ-cong (r .src-right q) (∘-cong (r .right-right w q) (r .src-right w))
  step₂ w nw r .right-right p q =
    +ₘ-cong (r .right-right p q) (∘-cong (r .right-right w q) (r .right-right p w))
  step₂ w nw r .env-root =
    offset-step {P = j₂} (r .env-root) (r .right-root w nw) (r .env-right w)
  step₂ w nw r .source-root =
    offset-step {P = j₂} (r .source-root) (r .right-root w nw) (r .src-right w)
  step₂ w nw r .right-root p np =
    root-step {P = j₂} (r .right-root p np) (r .right-root w nw) (r .right-right p w)

  steps₂ : ∀ {G H K Kₛ} (ws : List (PathS D₂)) → All (λ w → is-ε-s w ≡ Bool.false) ws →
           Phase₂ G H K Kₛ →
           Phase₂ (hide-all-s G (map at (map tl ws))) (hide-all-s H (map at ws)) K Kₛ
  steps₂ []       []         r = r
  steps₂ (w ∷ ws) (nw ∷ nws) r = steps₂ ws nws (step₂ w nw r)

  private
    r1 : Phase₁ (hide-all-s (hide-s (hide-s (graph-s (D₁ ∷ D₂)) (at ε)) (at (hd ε)))
                            (map at (map hd (interior D₁))))
                (hide-all (hide (graph D₁) (at ε)) (map at (interior D₁)))
    r1 = steps₁ (interior D₁) (interior-not-root D₁) base₁

    base₂ : Phase₂ (hide-s (hide-all-s (hide-s (hide-s (graph-s (D₁ ∷ D₂)) (at ε)) (at (hd ε)))
                                       (map at (map hd (interior D₁))))
                           (at (tl ε)))
                   (hide-s (graph-s D₂) (at ε))
                   (j₁ ∘ collapse D₁)
                   (j₁ ∘ collapse-src D₁)
    base₂ .env-right q = +ₘ-cong (r1 .env-right q) (∘-cong (r1 .right-right ε q) (r1 .env-right ε))
    base₂ .src-right q = +ₘ-cong (r1 .src-right q) (∘-cong (r1 .right-right ε q) (r1 .src-right ε))
    base₂ .right-right p q =
      +ₘ-cong (r1 .right-right p q) (∘-cong (r1 .right-right ε q) (r1 .right-right p ε))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (r1 .env-root) (∘-cong (r1 .right-root ε) (r1 .env-right ε)))
              (+ₘ-cong (≈-refl {f = j₁ ∘ collapse D₁})
                       (∘-cong₂ {f = j₂} (≈-sym (hide-root-s D₂ env (at ε)))))
    base₂ .source-root =
      ≈-trans (+ₘ-cong (r1 .source-root) (∘-cong (r1 .right-root ε) (r1 .src-right ε)))
              (+ₘ-cong (≈-refl {f = j₁ ∘ collapse-src D₁})
                       (∘-cong₂ {f = j₂} (≈-sym (hide-root-s D₂ src (at ε)))))
    base₂ .right-root p np =
      ≈-trans (+ₘ-cong (≈-trans (r1 .right-root p) (edge-off-s j₂ p np))
                       (∘-cong (r1 .right-root ε) (r1 .right-right p ε)))
              (into-hidden-s D₂ j₂ (at p))

    plumb : ∀ (x : VertexS (D₁ ∷ D₂)) →
            hide-all-s (hide-s (graph-s (D₁ ∷ D₂)) (at ε))
                       (map at (map hd (paths D₁) ++ map tl (paths-s D₂))) x (at ε)
            ≡ hide-all-s (hide-all-s (hide-s (graph-s (D₁ ∷ D₂)) (at ε))
                                     (map at (map hd (paths D₁))))
                         (map at (map tl (paths-s D₂))) x (at ε)
    plumb x =
      ≡-trans (≡-cong (λ L → hide-all-s (hide-s (graph-s (D₁ ∷ D₂)) (at ε)) L x (at ε))
                      (map-++ at (map hd (paths D₁)) (map tl (paths-s D₂))))
              (≡-cong (λ Gg → Gg x (at ε))
                      (hide-all-s-++ (hide-s (graph-s (D₁ ∷ D₂)) (at ε))
                                     (map at (map hd (paths D₁)))
                                     (map at (map tl (paths-s D₂)))))

  -- Collapsing an operand cons pairs the head and tail collapses.
  agree : collapse-s (D₁ ∷ D₂) ≈ ((j₁ ∘ collapse D₁) M.+ₘ (j₂ ∘ collapse-s D₂))
  agree =
    ≈-trans (≈-of-≡ (plumb env)) (steps₂ (interior-s D₂) (interior-not-root-s D₂) base₂ .env-root)

  agree-src : collapse-s-src (D₁ ∷ D₂)
              ≈ ((j₁ ∘ collapse-src D₁) M.+ₘ (j₂ ∘ collapse-s-src D₂))
  agree-src =
    ≈-trans (≈-of-≡ (plumb src))
            (steps₂ (interior-s D₂) (interior-not-root-s D₂) base₂ .source-root)

-- A primitive operation: one operand-list premise, with the operator's derivative as root edge.
-- The result is freshly built, so its source column is the control weight.
module Bop {Γ is o'} {γ : Env Γ} {ω : op is o'} {Ms : Every (λ s → Γ ⊢ base s) is}
           {vs : sort-vals is} {Rs : Nat.suc (width-env γ) ⇒ bases-width is}
           {D : γ , Ms ⇓s vs [ Rs ]} where

  record Embeds (G : Graph (⇓-bop {ω = ω} D)) (H : GraphS D)
                (P : M.Matrix (sort-width o') (bases-width is))
                (K : M.Matrix (sort-width o') 1) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (bop q)) ≈ H env (at q)
      src-embed   : ∀ q → G src (at (bop q)) ≈ H src (at q)
      embed-embed : ∀ p q → G (at (bop p)) (at (bop q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (P ∘ H env (at ε))
      source-root : G src (at ε) ≈ (K M.+ₘ (P ∘ H src (at ε)))
      embed-root  : ∀ p → is-ε-s p ≡ Bool.false →
                    G (at (bop p)) (at ε) ≈ (P ∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P K} (w : PathS D) → is-ε-s w ≡ Bool.false →
                Embeds G H P K → Embeds (hide G (at (bop w))) (hide-s H (at w)) P K
  embeds-hide w nw s .env-embed q =
    +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .src-embed q =
    +ₘ-cong (s .src-embed q) (∘-cong (s .embed-embed w q) (s .src-embed w))
  embeds-hide w nw s .embed-embed p q =
    +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {H = H} {P = P} w nw s .env-root =
    root-step {P = P} {X = H env (at ε)} {Y = H (at w) (at ε)} {Z = H env (at w)}
      (s .env-root) (s .embed-root w nw) (s .env-embed w)
  embeds-hide {H = H} {P = P} {K = K} w nw s .source-root =
    offset-step {K = K} {P = P} {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
      (s .source-root) (s .embed-root w nw) (s .src-embed w)
  embeds-hide {H = H} {P = P} w nw s .embed-root p np =
    root-step {P = P} {X = H (at p) (at ε)} {Y = H (at w) (at ε)} {Z = H (at p) (at w)}
      (s .embed-root p np) (s .embed-root w nw) (s .embed-embed p w)

  embeds-hide-all : ∀ {G H P K} (ws : List (PathS D)) → All (λ w → is-ε-s w ≡ Bool.false) ws →
                    Embeds G H P K →
                    Embeds (hide-all G (map at (map bop ws))) (hide-all-s H (map at ws)) P K
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    embeds₀ : Embeds (hide (hide (graph (⇓-bop {ω = ω} D)) (at ε)) (at (bop ε)))
                     (hide-s (graph-s D) (at ε)) (op-deps ω .func vs) ctrl-row
    embeds₀ .env-embed q = hide-hide-root (⇓-bop {ω = ω} D) (at (bop ε)) env (at (bop q))
    embeds₀ .src-embed q = hide-hide-root (⇓-bop {ω = ω} D) (at (bop ε)) src (at (bop q))
    embeds₀ .embed-embed p q =
      hide-hide-root (⇓-bop {ω = ω} D) (at (bop ε)) (at (bop p)) (at (bop q))
    embeds₀ .env-root =
      ≈-trans (hide-hide-root (⇓-bop {ω = ω} D) (at (bop ε)) env (at ε))
              (into-hidden-s D (op-deps ω .func vs) env)
    embeds₀ .source-root =
      ≈-trans {f = hide (hide (graph (⇓-bop {ω = ω} D)) (at ε)) (at (bop ε)) src (at ε)}
              {g = ctrl-row M.+ₘ ((op-deps ω .func vs) ∘ graph-s D src (at ε))}
              {h = ctrl-row M.+ₘ ((op-deps ω .func vs) ∘ hide-s (graph-s D) (at ε) src (at ε))}
              (hide-hide-root (⇓-bop {ω = ω} D) (at (bop ε)) src (at ε))
              (into-hidden-off-s D src ctrl-row (op-deps ω .func vs))
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root (⇓-bop {ω = ω} D) (at (bop ε)) (at (bop p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off-s (op-deps ω .func vs) p np) ≈-refl)
               (into-hidden-s D (op-deps ω .func vs) (at p)))

  agree : collapse (⇓-bop {ω = ω} D) ≈ ((op-deps ω .func vs) ∘ collapse-s D)
  agree = embeds-hide-all (interior-s D) (interior-not-root-s D) embeds₀ .env-root

  agree-src : collapse-src (⇓-bop {ω = ω} D)
              ≈ (ctrl-row M.+ₘ ((op-deps ω .func vs) ∘ collapse-s-src D))
  agree-src = embeds-hide-all (interior-s D) (interior-not-root-s D) embeds₀ .source-root

-- A primitive relation, as for an operation but with the branch-dependent derivative.
module Brel {Γ is} {γ : Env Γ} {ω : rel is} {Ms : Every (λ s → Γ ⊢ base s) is}
            {vs : sort-vals is} {Rs : Nat.suc (width-env γ) ⇒ bases-width is}
            {D : γ , Ms ⇓s vs [ Rs ]} where

  private
    b₀ = rel-pred ω .func vs

  record Embeds (G : Graph (⇓-brel {ω = ω} D)) (H : GraphS D)
                (P : M.Matrix (width (bool→val b₀)) (bases-width is))
                (K : M.Matrix (width (bool→val b₀)) 1) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (brel q)) ≈ H env (at q)
      src-embed   : ∀ q → G src (at (brel q)) ≈ H src (at q)
      embed-embed : ∀ p q → G (at (brel p)) (at (brel q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (P ∘ H env (at ε))
      source-root : G src (at ε) ≈ (K M.+ₘ (P ∘ H src (at ε)))
      embed-root  : ∀ p → is-ε-s p ≡ Bool.false →
                    G (at (brel p)) (at ε) ≈ (P ∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P K} (w : PathS D) → is-ε-s w ≡ Bool.false →
                Embeds G H P K → Embeds (hide G (at (brel w))) (hide-s H (at w)) P K
  embeds-hide w nw s .env-embed q =
    +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .src-embed q =
    +ₘ-cong (s .src-embed q) (∘-cong (s .embed-embed w q) (s .src-embed w))
  embeds-hide w nw s .embed-embed p q =
    +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {H = H} {P = P} w nw s .env-root =
    root-step {P = P} {X = H env (at ε)} {Y = H (at w) (at ε)} {Z = H env (at w)}
      (s .env-root) (s .embed-root w nw) (s .env-embed w)
  embeds-hide {H = H} {P = P} {K = K} w nw s .source-root =
    offset-step {K = K} {P = P} {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
      (s .source-root) (s .embed-root w nw) (s .src-embed w)
  embeds-hide {H = H} {P = P} w nw s .embed-root p np =
    root-step {P = P} {X = H (at p) (at ε)} {Y = H (at w) (at ε)} {Z = H (at p) (at w)}
      (s .embed-root p np) (s .embed-root w nw) (s .embed-embed p w)

  embeds-hide-all : ∀ {G H P K} (ws : List (PathS D)) → All (λ w → is-ε-s w ≡ Bool.false) ws →
                    Embeds G H P K →
                    Embeds (hide-all G (map at (map brel ws))) (hide-all-s H (map at ws)) P K
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    embeds₀ : Embeds (hide (hide (graph (⇓-brel {ω = ω} D)) (at ε)) (at (brel ε)))
                     (hide-s (graph-s D) (at ε)) (brel-deps ω vs b₀) ctrl-row
    embeds₀ .env-embed q = hide-hide-root (⇓-brel {ω = ω} D) (at (brel ε)) env (at (brel q))
    embeds₀ .src-embed q = hide-hide-root (⇓-brel {ω = ω} D) (at (brel ε)) src (at (brel q))
    embeds₀ .embed-embed p q =
      hide-hide-root (⇓-brel {ω = ω} D) (at (brel ε)) (at (brel p)) (at (brel q))
    embeds₀ .env-root =
      ≈-trans (hide-hide-root (⇓-brel {ω = ω} D) (at (brel ε)) env (at ε))
              (into-hidden-s D (brel-deps ω vs b₀) env)
    embeds₀ .source-root =
      ≈-trans {f = hide (hide (graph (⇓-brel {ω = ω} D)) (at ε)) (at (brel ε)) src (at ε)}
              {g = ctrl-row M.+ₘ (brel-deps ω vs b₀ ∘ graph-s D src (at ε))}
              {h = ctrl-row M.+ₘ (brel-deps ω vs b₀ ∘ hide-s (graph-s D) (at ε) src (at ε))}
              (hide-hide-root (⇓-brel {ω = ω} D) (at (brel ε)) src (at ε))
              (into-hidden-off-s D src ctrl-row (brel-deps ω vs b₀))
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root (⇓-brel {ω = ω} D) (at (brel ε)) (at (brel p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off-s (brel-deps ω vs b₀) p np) ≈-refl)
               (into-hidden-s D (brel-deps ω vs b₀) (at p)))

  agree : collapse (⇓-brel {ω = ω} D) ≈ ((brel-deps ω vs b₀) ∘ collapse-s D)
  agree = embeds-hide-all (interior-s D) (interior-not-root-s D) embeds₀ .env-root

  agree-src : collapse-src (⇓-brel {ω = ω} D)
              ≈ (ctrl-row M.+ₘ ((brel-deps ω vs b₀) ∘ collapse-s-src D))
  agree-src = embeds-hide-all (interior-s D) (interior-not-root-s D) embeds₀ .source-root

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

-- Leaf fold actions: the output is the input, so the three collapses are zero, zero and identity.
module _ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr} where

  private
    unit-map : ∀ {v R} → Map γ s unit v R v R
    unit-map {v} {R} = m-unit {γ = γ} {τ₀ = τ₀} {σr = σr} {s = s} {v = v} {R = R}

    base-map : ∀ {b v R} → Map γ s (base b) v R v R
    base-map {b} {v} {R} = m-base {γ = γ} {τ₀ = τ₀} {σr = σr} {s = s} {b = b} {v = v} {R = R}

    arrow-map : ∀ {σ₁ σ₂ v R} → Map γ s (σ₁ [→] σ₂) v R v R
    arrow-map {σ₁} {σ₂} {v} {R} =
      m-arrow {γ = γ} {τ₀ = τ₀} {σr = σr} {s = s} {σ₁ = σ₁} {σ₂ = σ₂} {v = v} {R = R}

  agree-m-unit-env : ∀ {v R} → collapse-m-env (unit-map {v} {R}) ≈ M.εₘ
  agree-m-unit-env {v} {R} = hide-root-m (unit-map {v} {R}) env (at ε)

  agree-m-unit-src : ∀ {v R} → collapse-m-src (unit-map {v} {R}) ≈ M.εₘ
  agree-m-unit-src {v} {R} = hide-root-m (unit-map {v} {R}) src (at ε)

  agree-m-unit-in : ∀ {v R} → collapse-m-in (unit-map {v} {R}) ≈ M.I
  agree-m-unit-in {v} {R} = hide-root-m (unit-map {v} {R}) input (at ε)

  agree-m-base-env : ∀ {b v R} → collapse-m-env (base-map {b} {v} {R}) ≈ M.εₘ
  agree-m-base-env {b} {v} {R} = hide-root-m (base-map {b} {v} {R}) env (at ε)

  agree-m-base-src : ∀ {b v R} → collapse-m-src (base-map {b} {v} {R}) ≈ M.εₘ
  agree-m-base-src {b} {v} {R} = hide-root-m (base-map {b} {v} {R}) src (at ε)

  agree-m-base-in : ∀ {b v R} → collapse-m-in (base-map {b} {v} {R}) ≈ M.I
  agree-m-base-in {b} {v} {R} = hide-root-m (base-map {b} {v} {R}) input (at ε)

  agree-m-arrow-env : ∀ {σ₁ σ₂ v R} → collapse-m-env (arrow-map {σ₁} {σ₂} {v} {R}) ≈ M.εₘ
  agree-m-arrow-env {σ₁} {σ₂} {v} {R} = hide-root-m (arrow-map {σ₁} {σ₂} {v} {R}) env (at ε)

  agree-m-arrow-src : ∀ {σ₁ σ₂ v R} → collapse-m-src (arrow-map {σ₁} {σ₂} {v} {R}) ≈ M.εₘ
  agree-m-arrow-src {σ₁} {σ₂} {v} {R} = hide-root-m (arrow-map {σ₁} {σ₂} {v} {R}) src (at ε)

  agree-m-arrow-in : ∀ {σ₁ σ₂ v R} → collapse-m-in (arrow-map {σ₁} {σ₂} {v} {R}) ≈ M.I
  agree-m-arrow-in {σ₁} {σ₂} {v} {R} = hide-root-m (arrow-map {σ₁} {σ₂} {v} {R}) input (at ε)

-- Injection actions: the premise's collapses are injected, the source column picking up the fresh
-- root's control weight and the input column the copied root.
module MInl {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ₁ σ₂ : type 1} {v : Val (σ₁ [ μ τ₀ ])}
            {R : Nat.suc (width-env γ) ⇒ Nat.suc (width v)}
            {v' : Val (σ₁ [ σr ])} {R' : Nat.suc (width-env γ) ⇒ width v'}
            {D : Map γ s σ₁ v (M.p₂ {1} {width v} ∘ R) v' R'} where

  private
    C : Map γ s (σ₁ [+] σ₂) _ R _ _
    C = m-inl {σ₁ = σ₁} {σ₂ = σ₂} D

    pᵥ = M.p₂ {1} {width v}
    K = M.in₁ {1} {width v'} ∘ M.p₁ {1} {width v}
    Kₛ = src-root {width v'}
    P = M.in₂ {1} {width v'}

  record Embeds (G : GraphM C) (H : GraphM D) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (m-inl q)) ≈ H env (at q)
      src-embed   : ∀ q → G src (at (m-inl q)) ≈ H src (at q)
      input-embed : ∀ q → G input (at (m-inl q)) ≈ (H input (at q) ∘ pᵥ)
      embed-embed : ∀ p q → G (at (m-inl p)) (at (m-inl q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (P ∘ H env (at ε))
      source-root : G src (at ε) ≈ (Kₛ M.+ₘ (P ∘ H src (at ε)))
      input-root  : G input (at ε) ≈ (K M.+ₘ ((P ∘ H input (at ε)) ∘ pᵥ))
      embed-root  : ∀ p → is-ε-m p ≡ Bool.false →
                    G (at (m-inl p)) (at ε) ≈ (P ∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H} (w : PathM D) → is-ε-m w ≡ Bool.false →
                Embeds G H → Embeds (hide-m G (at (m-inl w))) (hide-m H (at w))
  embeds-hide w nw r .env-embed q =
    +ₘ-cong (r .env-embed q) (∘-cong (r .embed-embed w q) (r .env-embed w))
  embeds-hide w nw r .src-embed q =
    +ₘ-cong (r .src-embed q) (∘-cong (r .embed-embed w q) (r .src-embed w))
  embeds-hide {H = H} w nw r .input-embed q =
    step-under {W = pᵥ} {X = H input (at q)} {Y = H (at w) (at q)} {Z = H input (at w)}
      (r .input-embed q) (r .embed-embed w q) (r .input-embed w)
  embeds-hide w nw r .embed-embed p q =
    +ₘ-cong (r .embed-embed p q) (∘-cong (r .embed-embed w q) (r .embed-embed p w))
  embeds-hide w nw r .env-root =
    root-step {P = P} (r .env-root) (r .embed-root w nw) (r .env-embed w)
  embeds-hide {H = H} w nw r .source-root =
    offset-step {K = Kₛ} {P = P} {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
      (r .source-root) (r .embed-root w nw) (r .src-embed w)
  embeds-hide {H = H} w nw r .input-root =
    offset-under P {W = pᵥ} {K = K} {X = H input (at ε)} {Y = H (at w) (at ε)} {Z = H input (at w)}
      (r .input-root) (r .embed-root w nw) (r .input-embed w)
  embeds-hide w nw r .embed-root p np =
    root-step {P = P} (r .embed-root p np) (r .embed-root w nw) (r .embed-embed p w)

  embeds-hide-all : ∀ {G H} (ws : List (PathM D)) → All (λ w → is-ε-m w ≡ Bool.false) ws →
                    Embeds G H →
                    Embeds (hide-all-m G (map at (map m-inl ws))) (hide-all-m H (map at ws))
  embeds-hide-all []       []         r = r
  embeds-hide-all (w ∷ ws) (nw ∷ nws) r = embeds-hide-all ws nws (embeds-hide w nw r)

  private
    embeds₀ : Embeds (hide-m (hide-m (graph-m C) (at ε)) (at (m-inl ε))) (hide-m (graph-m D) (at ε))
    embeds₀ .env-embed q = hide-hide-root-m C (at (m-inl ε)) env (at (m-inl q))
    embeds₀ .src-embed q = hide-hide-root-m C (at (m-inl ε)) src (at (m-inl q))
    embeds₀ .input-embed q =
      ≈-trans (hide-hide-root-m C (at (m-inl ε)) input (at (m-inl q)))
              (step-under {W = pᵥ} {X = graph-m D input (at q)} {Y = graph-m D (at ε) (at q)}
                          {Z = graph-m D input (at ε)}
                          (≈-refl {f = graph-m D input (at q) ∘ pᵥ})
                          (≈-refl {f = graph-m D (at ε) (at q)})
                          (≈-refl {f = graph-m D input (at ε) ∘ pᵥ}))
    embeds₀ .embed-embed p q = hide-hide-root-m C (at (m-inl ε)) (at (m-inl p)) (at (m-inl q))
    embeds₀ .env-root =
      ≈-trans (hide-hide-root-m C (at (m-inl ε)) env (at ε)) (into-hidden-m D P env)
    embeds₀ .source-root =
      ≈-trans {f = hide-m (hide-m (graph-m C) (at ε)) (at (m-inl ε)) src (at ε)}
              {g = Kₛ M.+ₘ (P ∘ graph-m D src (at ε))}
              {h = Kₛ M.+ₘ (P ∘ hide-m (graph-m D) (at ε) src (at ε))}
              (hide-hide-root-m C (at (m-inl ε)) src (at ε))
              (into-hidden-off-m D src Kₛ P)
    embeds₀ .input-root =
      ≈-trans (hide-hide-root-m C (at (m-inl ε)) input (at ε))
              (+ₘ-cong (≈-refl {f = K})
                       (≈-trans (≈-sym (assoc P (graph-m D input (at ε)) pᵥ))
                                (∘-cong₁ (∘-cong₂ (≈-sym (hide-root-m D input (at ε)))))))
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root-m C (at (m-inl ε)) (at (m-inl p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off-m P p np) ≈-refl) (into-hidden-m D P (at p)))

    rfin = embeds-hide-all (interior-m D) (interior-not-root-m D) embeds₀

  agree-env : collapse-m-env C ≈ (P ∘ collapse-m-env D)
  agree-env = rfin .env-root

  agree-src : collapse-m-src C ≈ (Kₛ M.+ₘ (P ∘ collapse-m-src D))
  agree-src = rfin .source-root

  agree-in : collapse-m-in C ≈ (K M.+ₘ ((P ∘ collapse-m-in D) ∘ pᵥ))
  agree-in = rfin .input-root

module MInr {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ₁ σ₂ : type 1} {v : Val (σ₂ [ μ τ₀ ])}
            {R : Nat.suc (width-env γ) ⇒ Nat.suc (width v)}
            {v' : Val (σ₂ [ σr ])} {R' : Nat.suc (width-env γ) ⇒ width v'}
            {D : Map γ s σ₂ v (M.p₂ {1} {width v} ∘ R) v' R'} where

  private
    C : Map γ s (σ₁ [+] σ₂) _ R _ _
    C = m-inr {σ₁ = σ₁} {σ₂ = σ₂} D

    pᵥ = M.p₂ {1} {width v}
    K = M.in₁ {1} {width v'} ∘ M.p₁ {1} {width v}
    Kₛ = src-root {width v'}
    P = M.in₂ {1} {width v'}

  record Embeds (G : GraphM C) (H : GraphM D) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (m-inr q)) ≈ H env (at q)
      src-embed   : ∀ q → G src (at (m-inr q)) ≈ H src (at q)
      input-embed : ∀ q → G input (at (m-inr q)) ≈ (H input (at q) ∘ pᵥ)
      embed-embed : ∀ p q → G (at (m-inr p)) (at (m-inr q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (P ∘ H env (at ε))
      source-root : G src (at ε) ≈ (Kₛ M.+ₘ (P ∘ H src (at ε)))
      input-root  : G input (at ε) ≈ (K M.+ₘ ((P ∘ H input (at ε)) ∘ pᵥ))
      embed-root  : ∀ p → is-ε-m p ≡ Bool.false →
                    G (at (m-inr p)) (at ε) ≈ (P ∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H} (w : PathM D) → is-ε-m w ≡ Bool.false →
                Embeds G H → Embeds (hide-m G (at (m-inr w))) (hide-m H (at w))
  embeds-hide w nw r .env-embed q =
    +ₘ-cong (r .env-embed q) (∘-cong (r .embed-embed w q) (r .env-embed w))
  embeds-hide w nw r .src-embed q =
    +ₘ-cong (r .src-embed q) (∘-cong (r .embed-embed w q) (r .src-embed w))
  embeds-hide {H = H} w nw r .input-embed q =
    step-under {W = pᵥ} {X = H input (at q)} {Y = H (at w) (at q)} {Z = H input (at w)}
      (r .input-embed q) (r .embed-embed w q) (r .input-embed w)
  embeds-hide w nw r .embed-embed p q =
    +ₘ-cong (r .embed-embed p q) (∘-cong (r .embed-embed w q) (r .embed-embed p w))
  embeds-hide w nw r .env-root =
    root-step {P = P} (r .env-root) (r .embed-root w nw) (r .env-embed w)
  embeds-hide {H = H} w nw r .source-root =
    offset-step {K = Kₛ} {P = P} {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
      (r .source-root) (r .embed-root w nw) (r .src-embed w)
  embeds-hide {H = H} w nw r .input-root =
    offset-under P {W = pᵥ} {K = K} {X = H input (at ε)} {Y = H (at w) (at ε)} {Z = H input (at w)}
      (r .input-root) (r .embed-root w nw) (r .input-embed w)
  embeds-hide w nw r .embed-root p np =
    root-step {P = P} (r .embed-root p np) (r .embed-root w nw) (r .embed-embed p w)

  embeds-hide-all : ∀ {G H} (ws : List (PathM D)) → All (λ w → is-ε-m w ≡ Bool.false) ws →
                    Embeds G H →
                    Embeds (hide-all-m G (map at (map m-inr ws))) (hide-all-m H (map at ws))
  embeds-hide-all []       []         r = r
  embeds-hide-all (w ∷ ws) (nw ∷ nws) r = embeds-hide-all ws nws (embeds-hide w nw r)

  private
    embeds₀ : Embeds (hide-m (hide-m (graph-m C) (at ε)) (at (m-inr ε))) (hide-m (graph-m D) (at ε))
    embeds₀ .env-embed q = hide-hide-root-m C (at (m-inr ε)) env (at (m-inr q))
    embeds₀ .src-embed q = hide-hide-root-m C (at (m-inr ε)) src (at (m-inr q))
    embeds₀ .input-embed q =
      ≈-trans (hide-hide-root-m C (at (m-inr ε)) input (at (m-inr q)))
              (step-under {W = pᵥ} {X = graph-m D input (at q)} {Y = graph-m D (at ε) (at q)}
                          {Z = graph-m D input (at ε)}
                          (≈-refl {f = graph-m D input (at q) ∘ pᵥ})
                          (≈-refl {f = graph-m D (at ε) (at q)})
                          (≈-refl {f = graph-m D input (at ε) ∘ pᵥ}))
    embeds₀ .embed-embed p q = hide-hide-root-m C (at (m-inr ε)) (at (m-inr p)) (at (m-inr q))
    embeds₀ .env-root =
      ≈-trans (hide-hide-root-m C (at (m-inr ε)) env (at ε)) (into-hidden-m D P env)
    embeds₀ .source-root =
      ≈-trans {f = hide-m (hide-m (graph-m C) (at ε)) (at (m-inr ε)) src (at ε)}
              {g = Kₛ M.+ₘ (P ∘ graph-m D src (at ε))}
              {h = Kₛ M.+ₘ (P ∘ hide-m (graph-m D) (at ε) src (at ε))}
              (hide-hide-root-m C (at (m-inr ε)) src (at ε))
              (into-hidden-off-m D src Kₛ P)
    embeds₀ .input-root =
      ≈-trans (hide-hide-root-m C (at (m-inr ε)) input (at ε))
              (+ₘ-cong (≈-refl {f = K})
                       (≈-trans (≈-sym (assoc P (graph-m D input (at ε)) pᵥ))
                                (∘-cong₁ (∘-cong₂ (≈-sym (hide-root-m D input (at ε)))))))
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root-m C (at (m-inr ε)) (at (m-inr p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off-m P p np) ≈-refl) (into-hidden-m D P (at p)))

    rfin = embeds-hide-all (interior-m D) (interior-not-root-m D) embeds₀

  agree-env : collapse-m-env C ≈ (P ∘ collapse-m-env D)
  agree-env = rfin .env-root

  agree-src : collapse-m-src C ≈ (Kₛ M.+ₘ (P ∘ collapse-m-src D))
  agree-src = rfin .source-root

  agree-in : collapse-m-in C ≈ (K M.+ₘ ((P ∘ collapse-m-in D) ∘ pᵥ))
  agree-in = rfin .input-root
