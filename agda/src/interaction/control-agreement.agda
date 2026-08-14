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

-- Absorb a correction routed through a zero row or column.
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
