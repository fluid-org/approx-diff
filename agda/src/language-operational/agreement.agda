{-# OPTIONS --prop --postfix-projections --safe #-}

open import signature using (Signature)
open import primitives using (Primitives)
open import commutative-semiring using (CommutativeSemiring)
import matrix
import two

-- Agreement of the graph judgement with evaluation: collapsing a derivation's graph recovers the
-- run's dependency relation, case by case on the rules.
module language-operational.agreement {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig 𝒫
open import language-operational.path Sig 𝒫
open import language-operational.graph Sig 𝒫
open import language-operational.hide Sig 𝒫

private
  module M = matrix.Mat two.semiring

open CommutativeSemiring two.semiring using (+-comm; +-cong; +-lunit; +-assoc; refl; trans)
import Data.Bool as Bool
import Data.Nat
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Relation.Unary.All.Properties using (map⁺; ++⁺)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; cong to ≡-cong; trans to ≡-trans)
open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; HasTerminal)
open Category M.cat using (_⇒_; ∘-cong; ∘-cong₁; ∘-cong₂; assoc; id-left; ≈-refl; ≈-sym; ≈-trans; isEquiv) renaming (id to idm)
open HasTerminal M.terminal using (to-terminal)

+ₘ-runit : ∀ {m n} (R : M.Matrix m n) → (R M.+ₘ M.εₘ) M.≈ₘ R
+ₘ-runit R i j = +-comm {x = R i j} {y = two.O}

-- The root of a graph is a sink: its row is zero.
root-sink : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) (y : Vertex D) →
            graph D (at ε) y M.≈ₘ M.εₘ
root-sink (⇓-var x) env i j = refl {x = two.O}
root-sink (⇓-var x) (at ε) i j = refl {x = two.O}
root-sink ⇓-unit env i j = refl {x = two.O}
root-sink ⇓-unit (at ε) i j = refl {x = two.O}
root-sink ⇓-lam env i j = refl {x = two.O}
root-sink ⇓-lam (at ε) i j = refl {x = two.O}
root-sink (⇓-inl D) env i j = refl {x = two.O}
root-sink (⇓-inl D) (at ε) i j = refl {x = two.O}
root-sink (⇓-inl D) (at (inl q)) i j = refl {x = two.O}
root-sink (⇓-inr D) env i j = refl {x = two.O}
root-sink (⇓-inr D) (at ε) i j = refl {x = two.O}
root-sink (⇓-inr D) (at (inr q)) i j = refl {x = two.O}
root-sink (⇓-fst D) env i j = refl {x = two.O}
root-sink (⇓-fst D) (at ε) i j = refl {x = two.O}
root-sink (⇓-fst D) (at (fst q)) i j = refl {x = two.O}
root-sink (⇓-snd D) env i j = refl {x = two.O}
root-sink (⇓-snd D) (at ε) i j = refl {x = two.O}
root-sink (⇓-snd D) (at (snd q)) i j = refl {x = two.O}
root-sink (⇓-roll D) env i j = refl {x = two.O}
root-sink (⇓-roll D) (at ε) i j = refl {x = two.O}
root-sink (⇓-roll D) (at (roll q)) i j = refl {x = two.O}
root-sink (⇓-case-l Ds D₁) env i j = refl {x = two.O}
root-sink (⇓-case-l Ds D₁) (at ε) i j = refl {x = two.O}
root-sink (⇓-case-l Ds D₁) (at (case-l₁ q)) i j = refl {x = two.O}
root-sink (⇓-case-l Ds D₁) (at (case-l₂ q)) i j = refl {x = two.O}
root-sink (⇓-case-r Ds D₂) env i j = refl {x = two.O}
root-sink (⇓-case-r Ds D₂) (at ε) i j = refl {x = two.O}
root-sink (⇓-case-r Ds D₂) (at (case-r₁ q)) i j = refl {x = two.O}
root-sink (⇓-case-r Ds D₂) (at (case-r₂ q)) i j = refl {x = two.O}
root-sink (⇓-pair Ds Dt) env i j = refl {x = two.O}
root-sink (⇓-pair Ds Dt) (at ε) i j = refl {x = two.O}
root-sink (⇓-pair Ds Dt) (at (pair₁ q)) i j = refl {x = two.O}
root-sink (⇓-pair Ds Dt) (at (pair₂ q)) i j = refl {x = two.O}
root-sink (⇓-app Ds Dt Db) env i j = refl {x = two.O}
root-sink (⇓-app Ds Dt Db) (at ε) i j = refl {x = two.O}
root-sink (⇓-app Ds Dt Db) (at (app₁ q)) i j = refl {x = two.O}
root-sink (⇓-app Ds Dt Db) (at (app₂ q)) i j = refl {x = two.O}
root-sink (⇓-app Ds Dt Db) (at (app₃ q)) i j = refl {x = two.O}
root-sink (⇓-bop Ds) env i j = refl {x = two.O}
root-sink (⇓-bop Ds) (at ε) i j = refl {x = two.O}
root-sink (⇓-bop Ds) (at (bop q)) i j = refl {x = two.O}
root-sink (⇓-brel Ds) env i j = refl {x = two.O}
root-sink (⇓-brel Ds) (at ε) i j = refl {x = two.O}
root-sink (⇓-brel Ds) (at (brel q)) i j = refl {x = two.O}
root-sink (⇓-fold Dt Dm) env i j = refl {x = two.O}
root-sink (⇓-fold Dt Dm) (at ε) i j = refl {x = two.O}
root-sink (⇓-fold Dt Dm) (at (fold₁ q)) i j = refl {x = two.O}
root-sink (⇓-fold Dt Dm) (at (fold₂ q)) i j = refl {x = two.O}

-- Absorb a correction routed through a zero row.
absorb : ∀ {m n k} (R : M.Matrix m n) (S : M.Matrix k n) → (R M.+ₘ (M.εₘ M.∘ S)) M.≈ₘ R
absorb R S i j = trans (+-cong (refl {x = R i j}) (M.comp-bilinear-ε₁ S i j))
                       (+-comm {x = R i j} {y = two.O})

-- Axiom rules: the only path is the root, and hiding it composes a zero column, so the collapse is
-- the rule's relation on the nose.
agree-var : ∀ {Γ τ} {γ : Env Γ} (x : Γ ∋ τ) → collapse (⇓-var x) M.≈ₘ proj-var x γ
agree-var {γ = γ} x = absorb (proj-var x γ) (proj-var x γ)

agree-unit : ∀ {Γ} {γ : Env Γ} → collapse (⇓-unit {γ = γ}) M.≈ₘ to-terminal
agree-unit () j

agree-lam : ∀ {Γ σ τ} {γ : Env Γ} {t : Γ ▸ σ ⊢ τ} →
            collapse (⇓-lam {γ = γ} {t = t}) M.≈ₘ idm (width-env γ)
agree-lam {γ = γ} = absorb (idm (width-env γ)) (idm (width-env γ))

+ₘ-cong : ∀ {m n} {R R' S S' : M.Matrix m n} →
          R M.≈ₘ R' → S M.≈ₘ S' → (R M.+ₘ S) M.≈ₘ (R' M.+ₘ S')
+ₘ-cong h k i j = +-cong (h i j) (k i j)

-- Hiding the root changes nothing, its row being zero.
hide-root : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) (x y : Vertex D) →
            hide (graph D) (at ε) x y M.≈ₘ graph D x y
hide-root D x y =
  ≈-trans (+ₘ-cong ≈-refl (∘-cong (root-sink D y) ≈-refl))
          (absorb (graph D x y) (graph D x (at ε)))


+ₘ-lunit : ∀ {m n} (R : M.Matrix m n) → (M.εₘ M.+ₘ R) M.≈ₘ R
+ₘ-lunit R i j = +-lunit {x = R i j}

-- Off the root, a root edge contributes nothing.
edge-off : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} {m}
           (S : M.Matrix m (width v)) (p : Path D) → is-ε p ≡ Bool.false →
           edge S p M.≈ₘ M.εₘ
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
interior-not-root (⇓-case-l Ds D₁) = ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths Ds))) (map⁺ (universal (λ _ → ≡-refl) (paths D₁)))
interior-not-root (⇓-case-r Ds D₂) = ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths Ds))) (map⁺ (universal (λ _ → ≡-refl) (paths D₂)))
interior-not-root (⇓-pair Ds Dt) = ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths Ds))) (map⁺ (universal (λ _ → ≡-refl) (paths Dt)))
interior-not-root (⇓-app Ds Dt Db) = ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths Ds))) (++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths Dt))) (map⁺ (universal (λ _ → ≡-refl) (paths Db))))
interior-not-root (⇓-bop Ds) = map⁺ (universal (λ _ → ≡-refl) (paths-s Ds))
interior-not-root (⇓-brel Ds) = map⁺ (universal (λ _ → ≡-refl) (paths-s Ds))
interior-not-root (⇓-fold Dt Dm) = ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths Dt))) (map⁺ (universal (λ _ → ≡-refl) (paths-m Dm)))

+ₘ-assoc : ∀ {m n} (X Y Z : M.Matrix m n) → ((X M.+ₘ Y) M.+ₘ Z) M.≈ₘ (X M.+ₘ (Y M.+ₘ Z))
+ₘ-assoc X Y Z i j = +-assoc {x = X i j} {y = Y i j} {z = Z i j}

absorb-r : ∀ {m n k} (R : M.Matrix m n) (S : M.Matrix m k) → (R M.+ₘ (S M.∘ M.εₘ)) M.≈ₘ R
absorb-r R S = ≈-trans (+ₘ-cong ≈-refl (M.comp-bilinear-ε₂ S)) (+ₘ-runit R)

≈-of-≡ : ∀ {m n} {X Y : M.Matrix m n} → X ≡ Y → X M.≈ₘ Y
≈-of-≡ ≡-refl = ≈-refl

hide-all-++ : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
              (G : Graph D) (xs ys : List (Vertex D)) →
              hide-all G (xs ++ ys) ≡ hide-all (hide-all G xs) ys
hide-all-++ G []       ys = ≡-refl
hide-all-++ G (x ∷ xs) ys = hide-all-++ (hide G x) xs ys

distrib-root : ∀ {m n k l} (P : M.Matrix m n) (X : M.Matrix n k)
               (Y : M.Matrix n l) (Z : M.Matrix l k) →
               ((P M.∘ X) M.+ₘ ((P M.∘ Y) M.∘ Z)) M.≈ₘ (P M.∘ (X M.+ₘ (Y M.∘ Z)))
distrib-root P X Y Z =
  ≈-trans (+ₘ-cong ≈-refl (assoc P Y Z)) (≈-sym (M.comp-bilinear₂ P X (Y M.∘ Z)))


-- Collapsing an inl derivation collapses its premise.
offset-distrib : ∀ {m n l g} (K : M.Matrix m g) (P : M.Matrix m n) (X : M.Matrix n g)
                 (Y : M.Matrix n l) (Z : M.Matrix l g) →
                 ((K M.+ₘ (P M.∘ X)) M.+ₘ ((P M.∘ Y) M.∘ Z)) M.≈ₘ (K M.+ₘ (P M.∘ (X M.+ₘ (Y M.∘ Z))))
offset-distrib K P X Y Z =
  ≈-trans (+ₘ-assoc K (P M.∘ X) ((P M.∘ Y) M.∘ Z)) (+ₘ-cong ≈-refl (distrib-root P X Y Z))

-- One hide step on related entries, root columns distributing through P.
root-step : ∀ {m n l g} {P : M.Matrix m n} {G₁ : M.Matrix m g} {X : M.Matrix n g}
            {G₂ : M.Matrix m l} {Y : M.Matrix n l} {G₃ Z : M.Matrix l g} →
            G₁ M.≈ₘ (P M.∘ X) → G₂ M.≈ₘ (P M.∘ Y) → G₃ M.≈ₘ Z →
            (G₁ M.+ₘ (G₂ M.∘ G₃)) M.≈ₘ (P M.∘ (X M.+ₘ (Y M.∘ Z)))
root-step {P = P} {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c)) (distrib-root P X Y Z)

offset-step : ∀ {m n l g} {K : M.Matrix m g} {P : M.Matrix m n} {G₁ : M.Matrix m g}
              {X : M.Matrix n g} {G₂ : M.Matrix m l} {Y : M.Matrix n l} {G₃ Z : M.Matrix l g} →
              G₁ M.≈ₘ (K M.+ₘ (P M.∘ X)) → G₂ M.≈ₘ (P M.∘ Y) → G₃ M.≈ₘ Z →
              (G₁ M.+ₘ (G₂ M.∘ G₃)) M.≈ₘ (K M.+ₘ (P M.∘ (X M.+ₘ (Y M.∘ Z))))
offset-step {K = K} {P} {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c)) (offset-distrib K P X Y Z)

-- The two initial hides, in terms of the underlying graph's entries.
hide-hide-root : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) (r x y : Vertex D) →
                 hide (hide (graph D) (at ε)) r x y
                 M.≈ₘ (graph D x y M.+ₘ (graph D r y M.∘ graph D x r))
hide-hide-root D r x y = +ₘ-cong (hide-root D x y) (∘-cong (hide-root D r y) (hide-root D x r))

-- Clean a zero direct entry against a routed one, and restore the premise's hidden root.
into-hidden : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) {m}
              (P : M.Matrix m (width v)) (x : Vertex D) →
              (M.εₘ M.+ₘ (P M.∘ graph D x (at ε))) M.≈ₘ (P M.∘ hide (graph D) (at ε) x (at ε))
into-hidden D P x =
  ≈-trans (+ₘ-lunit (P M.∘ graph D x (at ε))) (∘-cong₂ (≈-sym (hide-root D x (at ε))))

-- Collapsing an inl derivation collapses its premise.
module Inl {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁} {v : Val τ₁} {R : width-env γ ⇒ width v}
           {D : γ , t ⇓ v [ R ]} where

  record Embeds (G : Graph (⇓-inl {τ₂ = τ₂} D)) (H : Graph D)
                (P : M.Matrix (width v) (width v)) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (inl q)) M.≈ₘ H env (at q)
      embed-embed : ∀ p q → G (at (inl p)) (at (inl q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      embed-root  : ∀ p → is-ε p ≡ Bool.false →
                    G (at (inl p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : Path D) → is-ε w ≡ Bool.false →
                Embeds G H P → Embeds (hide G (at (inl w))) (hide H (at w)) P
  embeds-hide w nw s .env-embed q   = +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .embed-embed p q = +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {P = P} w nw s .env-root = root-step {P = P} (s .env-root) (s .embed-root w nw) (s .env-embed w)
  embeds-hide {P = P} w nw s .embed-root p np =
    root-step {P = P} (s .embed-root p np) (s .embed-root w nw) (s .embed-embed p w)

  embeds-hide-all : ∀ {G H P} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
                    Embeds G H P →
                    Embeds (hide-all G (map at (map inl ws))) (hide-all H (map at ws)) P
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    embeds₀ : Embeds (hide (hide (graph (⇓-inl {τ₂ = τ₂} D)) (at ε)) (at (inl ε)))
                     (hide (graph D) (at ε)) M.I
    embeds₀ .env-embed q   = hide-hide-root (⇓-inl {τ₂ = τ₂} D) (at (inl ε)) env (at (inl q))
    embeds₀ .embed-embed p q = hide-hide-root (⇓-inl {τ₂ = τ₂} D) (at (inl ε)) (at (inl p)) (at (inl q))
    embeds₀ .env-root      =
      ≈-trans (hide-hide-root (⇓-inl {τ₂ = τ₂} D) (at (inl ε)) env (at ε)) (into-hidden D M.I env)
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root (⇓-inl {τ₂ = τ₂} D) (at (inl ε)) (at (inl p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off M.I p np) ≈-refl) (into-hidden D M.I (at p)))

  agree-inl : collapse (⇓-inl {τ₂ = τ₂} D) M.≈ₘ collapse D
  agree-inl = ≈-trans (embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root) id-left

-- Collapsing an inr derivation collapses its premise.
module Inr {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₂} {v : Val τ₂} {R : width-env γ ⇒ width v}
           {D : γ , t ⇓ v [ R ]} where

  record Embeds (G : Graph (⇓-inr {τ₁ = τ₁} D)) (H : Graph D)
                (P : M.Matrix (width v) (width v)) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (inr q)) M.≈ₘ H env (at q)
      embed-embed : ∀ p q → G (at (inr p)) (at (inr q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      embed-root  : ∀ p → is-ε p ≡ Bool.false →
                    G (at (inr p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : Path D) → is-ε w ≡ Bool.false →
                Embeds G H P → Embeds (hide G (at (inr w))) (hide H (at w)) P
  embeds-hide w nw s .env-embed q   = +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .embed-embed p q = +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {P = P} w nw s .env-root = root-step {P = P} (s .env-root) (s .embed-root w nw) (s .env-embed w)
  embeds-hide {P = P} w nw s .embed-root p np =
    root-step {P = P} (s .embed-root p np) (s .embed-root w nw) (s .embed-embed p w)

  embeds-hide-all : ∀ {G H P} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
                    Embeds G H P →
                    Embeds (hide-all G (map at (map inr ws))) (hide-all H (map at ws)) P
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    embeds₀ : Embeds (hide (hide (graph (⇓-inr {τ₁ = τ₁} D)) (at ε)) (at (inr ε)))
                     (hide (graph D) (at ε)) M.I
    embeds₀ .env-embed q   = hide-hide-root (⇓-inr {τ₁ = τ₁} D) (at (inr ε)) env (at (inr q))
    embeds₀ .embed-embed p q = hide-hide-root (⇓-inr {τ₁ = τ₁} D) (at (inr ε)) (at (inr p)) (at (inr q))
    embeds₀ .env-root      =
      ≈-trans (hide-hide-root (⇓-inr {τ₁ = τ₁} D) (at (inr ε)) env (at ε)) (into-hidden D M.I env)
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root (⇓-inr {τ₁ = τ₁} D) (at (inr ε)) (at (inr p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off M.I p np) ≈-refl) (into-hidden D M.I (at p)))

  agree-inr : collapse (⇓-inr {τ₁ = τ₁} D) M.≈ₘ collapse D
  agree-inr = ≈-trans (embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root) id-left

-- Collapsing a fst derivation projects its premise's collapse.
module Fst {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v : Val τ₁} {u : Val τ₂}
           {R : width-env γ ⇒ width (pair v u)} {D : γ , t ⇓ pair v u [ R ]} where

  record Embeds (G : Graph (⇓-fst D)) (H : Graph D)
                (P : M.Matrix (width v) (width (pair v u))) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (fst q)) M.≈ₘ H env (at q)
      embed-embed : ∀ p q → G (at (fst p)) (at (fst q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      embed-root  : ∀ p → is-ε p ≡ Bool.false →
                    G (at (fst p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : Path D) → is-ε w ≡ Bool.false →
                Embeds G H P → Embeds (hide G (at (fst w))) (hide H (at w)) P
  embeds-hide w nw s .env-embed q   = +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .embed-embed p q = +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {P = P} w nw s .env-root = root-step {P = P} (s .env-root) (s .embed-root w nw) (s .env-embed w)
  embeds-hide {P = P} w nw s .embed-root p np =
    root-step {P = P} (s .embed-root p np) (s .embed-root w nw) (s .embed-embed p w)

  embeds-hide-all : ∀ {G H P} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
                    Embeds G H P →
                    Embeds (hide-all G (map at (map fst ws))) (hide-all H (map at ws)) P
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    embeds₀ : Embeds (hide (hide (graph (⇓-fst D)) (at ε)) (at (fst ε)))
                     (hide (graph D) (at ε)) M.p₁
    embeds₀ .env-embed q   = hide-hide-root (⇓-fst D) (at (fst ε)) env (at (fst q))
    embeds₀ .embed-embed p q = hide-hide-root (⇓-fst D) (at (fst ε)) (at (fst p)) (at (fst q))
    embeds₀ .env-root      =
      ≈-trans (hide-hide-root (⇓-fst D) (at (fst ε)) env (at ε)) (into-hidden D M.p₁ env)
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root (⇓-fst D) (at (fst ε)) (at (fst p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off M.p₁ p np) ≈-refl) (into-hidden D M.p₁ (at p)))

  agree-fst : collapse (⇓-fst D) M.≈ₘ (M.p₁ M.∘ collapse D)
  agree-fst = embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root

-- Collapsing a snd derivation projects its premise's collapse.
module Snd {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v : Val τ₁} {u : Val τ₂}
           {R : width-env γ ⇒ width (pair v u)} {D : γ , t ⇓ pair v u [ R ]} where

  record Embeds (G : Graph (⇓-snd D)) (H : Graph D)
                (P : M.Matrix (width u) (width (pair v u))) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (snd q)) M.≈ₘ H env (at q)
      embed-embed : ∀ p q → G (at (snd p)) (at (snd q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      embed-root  : ∀ p → is-ε p ≡ Bool.false →
                    G (at (snd p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : Path D) → is-ε w ≡ Bool.false →
                Embeds G H P → Embeds (hide G (at (snd w))) (hide H (at w)) P
  embeds-hide w nw s .env-embed q   = +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .embed-embed p q = +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {P = P} w nw s .env-root = root-step {P = P} (s .env-root) (s .embed-root w nw) (s .env-embed w)
  embeds-hide {P = P} w nw s .embed-root p np =
    root-step {P = P} (s .embed-root p np) (s .embed-root w nw) (s .embed-embed p w)

  embeds-hide-all : ∀ {G H P} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
                    Embeds G H P →
                    Embeds (hide-all G (map at (map snd ws))) (hide-all H (map at ws)) P
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    embeds₀ : Embeds (hide (hide (graph (⇓-snd D)) (at ε)) (at (snd ε)))
                     (hide (graph D) (at ε)) M.p₂
    embeds₀ .env-embed q   = hide-hide-root (⇓-snd D) (at (snd ε)) env (at (snd q))
    embeds₀ .embed-embed p q = hide-hide-root (⇓-snd D) (at (snd ε)) (at (snd p)) (at (snd q))
    embeds₀ .env-root      =
      ≈-trans (hide-hide-root (⇓-snd D) (at (snd ε)) env (at ε)) (into-hidden D M.p₂ env)
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root (⇓-snd D) (at (snd ε)) (at (snd p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off M.p₂ p np) ≈-refl) (into-hidden D M.p₂ (at p)))

  agree-snd : collapse (⇓-snd D) M.≈ₘ (M.p₂ M.∘ collapse D)
  agree-snd = embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root

-- Collapsing a roll derivation collapses its premise.
module Roll {Γ} {τ : type 1} {γ : Env Γ} {t : Γ ⊢ τ [ μ τ ]} {v : Val (τ [ μ τ ])}
           {R : width-env γ ⇒ width v} {D : γ , t ⇓ v [ R ]} where

  record Embeds (G : Graph (⇓-roll {τ = τ} D)) (H : Graph D)
                (P : M.Matrix (width v) (width v)) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (roll q)) M.≈ₘ H env (at q)
      embed-embed : ∀ p q → G (at (roll p)) (at (roll q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      embed-root  : ∀ p → is-ε p ≡ Bool.false →
                    G (at (roll p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : Path D) → is-ε w ≡ Bool.false →
                Embeds G H P → Embeds (hide G (at (roll w))) (hide H (at w)) P
  embeds-hide w nw s .env-embed q   = +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .embed-embed p q = +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {P = P} w nw s .env-root = root-step {P = P} (s .env-root) (s .embed-root w nw) (s .env-embed w)
  embeds-hide {P = P} w nw s .embed-root p np =
    root-step {P = P} (s .embed-root p np) (s .embed-root w nw) (s .embed-embed p w)

  embeds-hide-all : ∀ {G H P} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
                    Embeds G H P →
                    Embeds (hide-all G (map at (map roll ws))) (hide-all H (map at ws)) P
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    embeds₀ : Embeds (hide (hide (graph (⇓-roll {τ = τ} D)) (at ε)) (at (roll ε)))
                     (hide (graph D) (at ε)) M.I
    embeds₀ .env-embed q   = hide-hide-root (⇓-roll {τ = τ} D) (at (roll ε)) env (at (roll q))
    embeds₀ .embed-embed p q = hide-hide-root (⇓-roll {τ = τ} D) (at (roll ε)) (at (roll p)) (at (roll q))
    embeds₀ .env-root      =
      ≈-trans (hide-hide-root (⇓-roll {τ = τ} D) (at (roll ε)) env (at ε)) (into-hidden D M.I env)
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root (⇓-roll {τ = τ} D) (at (roll ε)) (at (roll p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off M.I p np) ≈-refl) (into-hidden D M.I (at p)))

  agree-roll : collapse (⇓-roll {τ = τ} D) M.≈ₘ collapse D
  agree-roll = ≈-trans (embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root) id-left

-- Two same-environment premises: while the first premise folds, the second premise's entries and
-- the cross entries must be seen undisturbed (nine families); the second phase then folds the
-- second premise against the finished first contribution as a constant offset K.
module Pair {Γ τ₁ τ₂} {γ : Env Γ} {ts : Γ ⊢ τ₁} {tt : Γ ⊢ τ₂} {v : Val τ₁} {u : Val τ₂}
            {R : width-env γ ⇒ width v} {S : width-env γ ⇒ width u}
            {Ds : γ , ts ⇓ v [ R ]} {Dt : γ , tt ⇓ u [ S ]} where

  record Phase₁ (G : Graph (⇓-pair Ds Dt)) (H : Graph Ds) : Set ℓ where
    field
      env-left    : ∀ q → G env (at (pair₁ q)) M.≈ₘ H env (at q)
      left-left   : ∀ p q → G (at (pair₁ p)) (at (pair₁ q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (M.in₁ M.∘ H env (at ε))
      left-root   : ∀ p → is-ε p ≡ Bool.false →
                    G (at (pair₁ p)) (at ε) M.≈ₘ (M.in₁ M.∘ H (at p) (at ε))
      env-right   : ∀ q → G env (at (pair₂ q)) M.≈ₘ graph Dt env (at q)
      right-right : ∀ p q → G (at (pair₂ p)) (at (pair₂ q)) M.≈ₘ graph Dt (at p) (at q)
      right-root  : ∀ p → G (at (pair₂ p)) (at ε) M.≈ₘ edge M.in₂ p
      left-right  : ∀ p q → G (at (pair₁ p)) (at (pair₂ q)) M.≈ₘ M.εₘ
      right-left  : ∀ p q → G (at (pair₂ p)) (at (pair₁ q)) M.≈ₘ M.εₘ

  open Phase₁

  stepₗ : ∀ {G H} (w : Path Ds) → is-ε w ≡ Bool.false →
          Phase₁ G H → Phase₁ (hide G (at (pair₁ w))) (hide H (at w))
  stepₗ w nw r .env-left q  = +ₘ-cong (r .env-left q) (∘-cong (r .left-left w q) (r .env-left w))
  stepₗ w nw r .left-left p q = +ₘ-cong (r .left-left p q) (∘-cong (r .left-left w q) (r .left-left p w))
  stepₗ w nw r .env-root = root-step {P = M.in₁ {width v} {width u}} (r .env-root) (r .left-root w nw) (r .env-left w)
  stepₗ w nw r .left-root p np = root-step {P = M.in₁ {width v} {width u}} (r .left-root p np) (r .left-root w nw) (r .left-left p w)
  stepₗ {G} w nw r .env-right q =
    ≈-trans (+ₘ-cong (r .env-right q) (∘-cong₁ (r .left-right w q)))
            (absorb (graph Dt env (at q)) (G env (at (pair₁ w))))
  stepₗ {G} w nw r .right-right p q =
    ≈-trans (+ₘ-cong (r .right-right p q) (∘-cong₁ (r .left-right w q)))
            (absorb (graph Dt (at p) (at q)) (G (at (pair₂ p)) (at (pair₁ w))))
  stepₗ {G} w nw r .right-root p =
    ≈-trans (+ₘ-cong (r .right-root p) (∘-cong₂ (r .right-left p w)))
            (absorb-r (edge M.in₂ p) (G (at (pair₁ w)) (at ε)))
  stepₗ {G} w nw r .left-right p q =
    ≈-trans (+ₘ-cong (r .left-right p q) (∘-cong₁ (r .left-right w q)))
            (absorb M.εₘ (G (at (pair₁ p)) (at (pair₁ w))))
  stepₗ {G} w nw r .right-left p q =
    ≈-trans (+ₘ-cong (r .right-left p q) (∘-cong₂ (r .right-left p w)))
            (absorb-r M.εₘ (G (at (pair₁ w)) (at (pair₁ q))))

  foldₗ : ∀ {G H} (ws : List (Path Ds)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₁ G H → Phase₁ (hide-all G (map at (map pair₁ ws))) (hide-all H (map at ws))
  foldₗ []       []         r = r
  foldₗ (w ∷ ws) (nw ∷ nws) r = foldₗ ws nws (stepₗ w nw r)

  private
    hh : ∀ x y → hide (hide (graph (⇓-pair Ds Dt)) (at ε)) (at (pair₁ ε)) x y
         M.≈ₘ (graph (⇓-pair Ds Dt) x y
               M.+ₘ (graph (⇓-pair Ds Dt) (at (pair₁ ε)) y M.∘ graph (⇓-pair Ds Dt) x (at (pair₁ ε))))
    hh = hide-hide-root (⇓-pair Ds Dt) (at (pair₁ ε))

    base₁ : Phase₁ (hide (hide (graph (⇓-pair Ds Dt)) (at ε)) (at (pair₁ ε)))
                   (hide (graph Ds) (at ε))
    base₁ .env-left q  = hh env (at (pair₁ q))
    base₁ .left-left p q = hh (at (pair₁ p)) (at (pair₁ q))
    base₁ .env-root = ≈-trans (hh env (at ε)) (into-hidden Ds M.in₁ env)
    base₁ .left-root p np =
      ≈-trans (hh (at (pair₁ p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off M.in₁ p np) ≈-refl) (into-hidden Ds M.in₁ (at p)))
    base₁ .env-right q = ≈-trans (hh env (at (pair₂ q))) (absorb (graph Dt env (at q)) (graph Ds env (at ε)))
    base₁ .right-right p q =
      ≈-trans (hh (at (pair₂ p)) (at (pair₂ q)))
              (absorb (graph Dt (at p) (at q)) (graph (⇓-pair Ds Dt) (at (pair₂ p)) (at (pair₁ ε))))
    base₁ .right-root p =
      ≈-trans (hh (at (pair₂ p)) (at ε))
              (absorb-r (edge M.in₂ p) (graph (⇓-pair Ds Dt) (at (pair₁ ε)) (at ε)))
    base₁ .left-right p q =
      ≈-trans (hh (at (pair₁ p)) (at (pair₂ q))) (absorb M.εₘ (graph Ds (at p) (at ε)))
    base₁ .right-left p q =
      ≈-trans (hh (at (pair₂ p)) (at (pair₁ q))) (absorb-r M.εₘ (graph Ds (at ε) (at q)))

  record Phase₂ (G : Graph (⇓-pair Ds Dt)) (H : Graph Dt)
                (K : M.Matrix (width (pair v u)) (width-env γ)) : Set ℓ where
    field
      env-right   : ∀ q → G env (at (pair₂ q)) M.≈ₘ H env (at q)
      right-right : ∀ p q → G (at (pair₂ p)) (at (pair₂ q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (K M.+ₘ (M.in₂ M.∘ H env (at ε)))
      right-root  : ∀ p → is-ε p ≡ Bool.false →
                    G (at (pair₂ p)) (at ε) M.≈ₘ (M.in₂ M.∘ H (at p) (at ε))

  open Phase₂

  stepᵣ : ∀ {G H K} (w : Path Dt) → is-ε w ≡ Bool.false →
          Phase₂ G H K → Phase₂ (hide G (at (pair₂ w))) (hide H (at w)) K
  stepᵣ w nw r .env-right q  = +ₘ-cong (r .env-right q) (∘-cong (r .right-right w q) (r .env-right w))
  stepᵣ w nw r .right-right p q = +ₘ-cong (r .right-right p q) (∘-cong (r .right-right w q) (r .right-right p w))
  stepᵣ w nw r .env-root = offset-step {P = M.in₂ {width v} {width u}} (r .env-root) (r .right-root w nw) (r .env-right w)
  stepᵣ w nw r .right-root p np = root-step {P = M.in₂ {width v} {width u}} (r .right-root p np) (r .right-root w nw) (r .right-right p w)

  foldᵣ : ∀ {G H K} (ws : List (Path Dt)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₂ G H K → Phase₂ (hide-all G (map at (map pair₂ ws))) (hide-all H (map at ws)) K
  foldᵣ []       []         r = r
  foldᵣ (w ∷ ws) (nw ∷ nws) r = foldᵣ ws nws (stepᵣ w nw r)

  private
    r1 : Phase₁ (hide-all (hide (hide (graph (⇓-pair Ds Dt)) (at ε)) (at (pair₁ ε)))
                          (map at (map pair₁ (interior Ds))))
                (hide-all (hide (graph Ds) (at ε)) (map at (interior Ds)))
    r1 = foldₗ (interior Ds) (interior-not-root Ds) base₁

    base₂ : Phase₂ (hide (hide-all (hide (hide (graph (⇓-pair Ds Dt)) (at ε)) (at (pair₁ ε)))
                                   (map at (map pair₁ (interior Ds))))
                         (at (pair₂ ε)))
                   (hide (graph Dt) (at ε))
                   (M.in₁ M.∘ collapse Ds)
    base₂ .env-right q = +ₘ-cong (r1 .env-right q) (∘-cong (r1 .right-right ε q) (r1 .env-right ε))
    base₂ .right-right p q = +ₘ-cong (r1 .right-right p q) (∘-cong (r1 .right-right ε q) (r1 .right-right p ε))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (r1 .env-root) (∘-cong (r1 .right-root ε) (r1 .env-right ε)))
              (+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (hide-root Dt env (at ε)))))
    base₂ .right-root p np =
      ≈-trans (+ₘ-cong (r1 .right-root p) (∘-cong (r1 .right-root ε) (r1 .right-right p ε)))
      (≈-trans (+ₘ-cong (edge-off M.in₂ p np) ≈-refl) (into-hidden Dt M.in₂ (at p)))

  -- Collapsing a pair derivation pairs its premises' collapses.
  agree-pair : collapse (⇓-pair Ds Dt)
               M.≈ₘ ((M.in₁ M.∘ collapse Ds) M.+ₘ (M.in₂ M.∘ collapse Dt))
  agree-pair =
    ≈-trans (≈-of-≡ plumb) (foldᵣ (interior Dt) (interior-not-root Dt) base₂ .env-root)
    where
      plumb : hide-all (hide (graph (⇓-pair Ds Dt)) (at ε))
                       (map at (map pair₁ (paths Ds) ++ map pair₂ (paths Dt))) env (at ε)
              ≡ hide-all (hide-all (hide (graph (⇓-pair Ds Dt)) (at ε))
                                   (map at (map pair₁ (paths Ds))))
                         (map at (map pair₂ (paths Dt))) env (at ε)
      plumb =
        ≡-trans (≡-cong (λ L → hide-all (hide (graph (⇓-pair Ds Dt)) (at ε)) L env (at ε))
                        (map-++ at (map pair₁ (paths Ds)) (map pair₂ (paths Dt))))
                (≡-cong (λ Gg → Gg env (at ε))
                        (hide-all-++ (hide (graph (⇓-pair Ds Dt)) (at ε))
                                     (map at (map pair₁ (paths Ds)))
                                     (map at (map pair₂ (paths Dt)))))

-- One hide step under a fixed post-composition W.
step-under : ∀ {m l g g'} {W : M.Matrix g g'} {G₁ : M.Matrix m g'} {X : M.Matrix m g}
             {G₂ : M.Matrix m l} {Y : M.Matrix m l} {G₃ : M.Matrix l g'} {Z : M.Matrix l g} →
             G₁ M.≈ₘ (X M.∘ W) → G₂ M.≈ₘ Y → G₃ M.≈ₘ (Z M.∘ W) →
             (G₁ M.+ₘ (G₂ M.∘ G₃)) M.≈ₘ ((X M.+ₘ (Y M.∘ Z)) M.∘ W)
step-under {W = W} {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c))
  (≈-trans (+ₘ-cong ≈-refl (≈-sym (assoc Y Z W))) (≈-sym (M.comp-bilinear₁ X (Y M.∘ Z) W)))

-- Regroup a rewired column: the env slice plus the routed slice factor through the substitution.
factor : ∀ {m g wv} (B : M.Matrix m (g Data.Nat.+ wv)) (C : M.Matrix wv g) →
         ((B M.∘ M.in₁) M.+ₘ ((B M.∘ M.in₂) M.∘ C)) M.≈ₘ (B M.∘ (M.in₁ M.+ₘ (M.in₂ M.∘ C)))
factor B C =
  ≈-trans (+ₘ-cong ≈-refl (assoc B M.in₂ C)) (≈-sym (M.comp-bilinear₂ B M.in₁ (M.in₂ M.∘ C)))

-- Left case branch, evaluated under the extended environment. Phase one folds the scrutinee: the branch's rewired columns carry the env slice
-- plus the routed slice through the evolving scrutinee collapse. Phase two folds the branch with
-- its env columns composed with the substitution W.
module CaseL {Γ τ₁ τ₂ τ} {γ : Env Γ} {ts : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
            {v : Val τ₁} {u : Val τ}
            {R : width-env γ ⇒ width v} {S : width-env (γ · v) ⇒ width u}
            {Ds : γ , ts ⇓ inl v [ R ]} {Db : γ · v , t₁ ⇓ u [ S ]} where

  iₗ : M.Matrix (width-env (γ · v)) (width-env γ)
  iₗ = M.in₁ {width-env γ} {width v}

  iᵣ : M.Matrix (width-env (γ · v)) (width v)
  iᵣ = M.in₂ {width-env γ} {width v}

  B : (q : Path Db) → M.Matrix (width-at q) (width-env (γ · v))
  B q = graph Db env (at q)

  W : M.Matrix (width-env (γ · v)) (width-env γ)
  W = iₗ M.+ₘ (iᵣ M.∘ collapse Ds)

  record Phase₁ (G : Graph (⇓-case-l {t₂ = t₂} Ds Db)) (H : Graph Ds) : Set ℓ where
    field
      env-scrut    : ∀ q → G env (at (case-l₁ q)) M.≈ₘ H env (at q)
      scrut-scrut  : ∀ p q → G (at (case-l₁ p)) (at (case-l₁ q)) M.≈ₘ H (at p) (at q)
      env-branch   : ∀ q → G env (at (case-l₂ q))
                     M.≈ₘ ((B q M.∘ iₗ) M.+ₘ ((B q M.∘ iᵣ) M.∘ H env (at ε)))
      scrut-branch : ∀ p → is-ε p ≡ Bool.false → ∀ q →
                     G (at (case-l₁ p)) (at (case-l₂ q)) M.≈ₘ ((B q M.∘ iᵣ) M.∘ H (at p) (at ε))
      branch-branch : ∀ p q → G (at (case-l₂ p)) (at (case-l₂ q)) M.≈ₘ graph Db (at p) (at q)
      branch-scrut  : ∀ p q → G (at (case-l₂ p)) (at (case-l₁ q)) M.≈ₘ M.εₘ
      env-root      : G env (at ε) M.≈ₘ M.εₘ
      scrut-root    : ∀ p → G (at (case-l₁ p)) (at ε) M.≈ₘ M.εₘ
      branch-root   : ∀ p → G (at (case-l₂ p)) (at ε) M.≈ₘ edge M.I p

  open Phase₁

  stepₛ : ∀ {G H} (w : Path Ds) → is-ε w ≡ Bool.false →
          Phase₁ G H → Phase₁ (hide G (at (case-l₁ w))) (hide H (at w))
  stepₛ w nw r .env-scrut q  = +ₘ-cong (r .env-scrut q) (∘-cong (r .scrut-scrut w q) (r .env-scrut w))
  stepₛ w nw r .scrut-scrut p q = +ₘ-cong (r .scrut-scrut p q) (∘-cong (r .scrut-scrut w q) (r .scrut-scrut p w))
  stepₛ w nw r .env-branch q =
    offset-step {K = B q M.∘ iₗ} {P = B q M.∘ iᵣ}
                (r .env-branch q) (r .scrut-branch w nw q) (r .env-scrut w)
  stepₛ w nw r .scrut-branch p np q =
    root-step {P = B q M.∘ iᵣ} (r .scrut-branch p np q) (r .scrut-branch w nw q) (r .scrut-scrut p w)
  stepₛ {G} w nw r .branch-branch p q =
    ≈-trans (+ₘ-cong (r .branch-branch p q) (∘-cong₂ (r .branch-scrut p w)))
            (absorb-r (graph Db (at p) (at q)) (G (at (case-l₁ w)) (at (case-l₂ q))))
  stepₛ {G} w nw r .branch-scrut p q =
    ≈-trans (+ₘ-cong (r .branch-scrut p q) (∘-cong₂ (r .branch-scrut p w)))
            (absorb-r M.εₘ (G (at (case-l₁ w)) (at (case-l₁ q))))
  stepₛ {G} w nw r .env-root =
    ≈-trans (+ₘ-cong (r .env-root) (∘-cong₁ (r .scrut-root w))) (absorb M.εₘ (G env (at (case-l₁ w))))
  stepₛ {G} w nw r .scrut-root p =
    ≈-trans (+ₘ-cong (r .scrut-root p) (∘-cong₁ (r .scrut-root w)))
            (absorb M.εₘ (G (at (case-l₁ p)) (at (case-l₁ w))))
  stepₛ {G} w nw r .branch-root p =
    ≈-trans (+ₘ-cong (r .branch-root p) (∘-cong₁ (r .scrut-root w)))
            (absorb (edge M.I p) (G (at (case-l₂ p)) (at (case-l₁ w))))

  foldₛ : ∀ {G H} (ws : List (Path Ds)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₁ G H → Phase₁ (hide-all G (map at (map case-l₁ ws))) (hide-all H (map at ws))
  foldₛ []       []         r = r
  foldₛ (w ∷ ws) (nw ∷ nws) r = foldₛ ws nws (stepₛ w nw r)

  private
    hh : ∀ x y → hide (hide (graph (⇓-case-l {t₂ = t₂} Ds Db)) (at ε)) (at (case-l₁ ε)) x y
         M.≈ₘ (graph (⇓-case-l {t₂ = t₂} Ds Db) x y
               M.+ₘ (graph (⇓-case-l {t₂ = t₂} Ds Db) (at (case-l₁ ε)) y M.∘ graph (⇓-case-l {t₂ = t₂} Ds Db) x (at (case-l₁ ε))))
    hh = hide-hide-root (⇓-case-l {t₂ = t₂} Ds Db) (at (case-l₁ ε))

    base₁ : Phase₁ (hide (hide (graph (⇓-case-l {t₂ = t₂} Ds Db)) (at ε)) (at (case-l₁ ε))) (hide (graph Ds) (at ε))
    base₁ .env-scrut q  = hh env (at (case-l₁ q))
    base₁ .scrut-scrut p q = hh (at (case-l₁ p)) (at (case-l₁ q))
    base₁ .env-branch q =
      ≈-trans (hh env (at (case-l₂ q)))
              (+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (hide-root Ds env (at ε)))))
    base₁ .scrut-branch p np q =
      ≈-trans (hh (at (case-l₁ p)) (at (case-l₂ q)))
      (≈-trans (+ₘ-cong (edge-off (B q M.∘ iᵣ) p np) ≈-refl)
               (into-hidden Ds (B q M.∘ iᵣ) (at p)))
    base₁ .branch-branch p q =
      ≈-trans (hh (at (case-l₂ p)) (at (case-l₂ q))) (absorb-r (graph Db (at p) (at q)) (B q M.∘ iᵣ))
    base₁ .branch-scrut p q =
      ≈-trans (hh (at (case-l₂ p)) (at (case-l₁ q))) (absorb-r M.εₘ (graph Ds (at ε) (at q)))
    base₁ .env-root = ≈-trans (hh env (at ε)) (absorb M.εₘ (graph Ds env (at ε)))
    base₁ .scrut-root p = ≈-trans (hh (at (case-l₁ p)) (at ε)) (absorb M.εₘ (graph Ds (at p) (at ε)))
    base₁ .branch-root p =
      ≈-trans (hh (at (case-l₂ p)) (at ε))
              (absorb (edge M.I p) (graph (⇓-case-l {t₂ = t₂} Ds Db) (at (case-l₂ p)) (at (case-l₁ ε))))

  record Phase₂ (G : Graph (⇓-case-l {t₂ = t₂} Ds Db)) (H : Graph Db) : Set ℓ where
    field
      env-branch    : ∀ q → G env (at (case-l₂ q)) M.≈ₘ (H env (at q) M.∘ W)
      branch-branch : ∀ p q → G (at (case-l₂ p)) (at (case-l₂ q)) M.≈ₘ H (at p) (at q)
      env-root      : G env (at ε) M.≈ₘ (H env (at ε) M.∘ W)
      branch-root   : ∀ p → is-ε p ≡ Bool.false → G (at (case-l₂ p)) (at ε) M.≈ₘ H (at p) (at ε)

  open Phase₂

  stepᵦ : ∀ {G H} (w : Path Db) → is-ε w ≡ Bool.false →
          Phase₂ G H → Phase₂ (hide G (at (case-l₂ w))) (hide H (at w))
  stepᵦ w nw r .env-branch q =
    step-under {W = W} (r .env-branch q) (r .branch-branch w q) (r .env-branch w)
  stepᵦ w nw r .branch-branch p q = +ₘ-cong (r .branch-branch p q) (∘-cong (r .branch-branch w q) (r .branch-branch p w))
  stepᵦ w nw r .env-root =
    step-under {W = W} (r .env-root) (r .branch-root w nw) (r .env-branch w)
  stepᵦ w nw r .branch-root p np = +ₘ-cong (r .branch-root p np) (∘-cong (r .branch-root w nw) (r .branch-branch p w))

  foldᵦ : ∀ {G H} (ws : List (Path Db)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₂ G H → Phase₂ (hide-all G (map at (map case-l₂ ws))) (hide-all H (map at ws))
  foldᵦ []       []         r = r
  foldᵦ (w ∷ ws) (nw ∷ nws) r = foldᵦ ws nws (stepᵦ w nw r)

  private
    r1 : Phase₁ (hide-all (hide (hide (graph (⇓-case-l {t₂ = t₂} Ds Db)) (at ε)) (at (case-l₁ ε)))
                          (map at (map case-l₁ (interior Ds))))
                (hide-all (hide (graph Ds) (at ε)) (map at (interior Ds)))
    r1 = foldₛ (interior Ds) (interior-not-root Ds) base₁

    base₂ : Phase₂ (hide (hide-all (hide (hide (graph (⇓-case-l {t₂ = t₂} Ds Db)) (at ε)) (at (case-l₁ ε)))
                                   (map at (map case-l₁ (interior Ds))))
                         (at (case-l₂ ε)))
                   (hide (graph Db) (at ε))
    base₂ .env-branch q =
      ≈-trans (+ₘ-cong (≈-trans (r1 .env-branch q) (factor (B q) (collapse Ds)))
                       (∘-cong₁ (≈-trans (r1 .branch-branch ε q) (root-sink Db (at q)))))
      (≈-trans (absorb (B q M.∘ W) (graph (⇓-case-l {t₂ = t₂} Ds Db) env (at (case-l₂ ε))))
               (≈-sym (∘-cong₁ (hide-root Db env (at q)))))
    base₂ .branch-branch p q =
      +ₘ-cong (r1 .branch-branch p q) (∘-cong (r1 .branch-branch ε q) (r1 .branch-branch p ε))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (r1 .env-root)
                       (∘-cong (r1 .branch-root ε) (≈-trans (r1 .env-branch ε) (factor (B ε) (collapse Ds)))))
      (≈-trans (+ₘ-lunit (M.I M.∘ (B ε M.∘ W)))
      (≈-trans id-left (≈-sym (∘-cong₁ (hide-root Db env (at ε))))))
    base₂ .branch-root p np =
      ≈-trans (+ₘ-cong (≈-trans (r1 .branch-root p) (edge-off M.I p np))
                       (∘-cong (r1 .branch-root ε) (r1 .branch-branch p ε)))
      (≈-trans (into-hidden Db M.I (at p)) id-left)

  -- Collapsing a agree-case-l-branch derivation composes the branch collapse with the substitution.
  agree-case-l : collapse (⇓-case-l {t₂ = t₂} Ds Db)
             M.≈ₘ (collapse Db M.∘ W)
  agree-case-l =
    ≈-trans (≈-of-≡ plumb) (foldᵦ (interior Db) (interior-not-root Db) base₂ .env-root)
    where
      plumb : hide-all (hide (graph (⇓-case-l {t₂ = t₂} Ds Db)) (at ε))
                       (map at (map case-l₁ (paths Ds) ++ map case-l₂ (paths Db))) env (at ε)
              ≡ hide-all (hide-all (hide (graph (⇓-case-l {t₂ = t₂} Ds Db)) (at ε)) (map at (map case-l₁ (paths Ds))))
                         (map at (map case-l₂ (paths Db))) env (at ε)
      plumb =
        ≡-trans (≡-cong (λ L → hide-all (hide (graph (⇓-case-l {t₂ = t₂} Ds Db)) (at ε)) L env (at ε))
                        (map-++ at (map case-l₁ (paths Ds)) (map case-l₂ (paths Db))))
                (≡-cong (λ Gg → Gg env (at ε))
                        (hide-all-++ (hide (graph (⇓-case-l {t₂ = t₂} Ds Db)) (at ε))
                                     (map at (map case-l₁ (paths Ds)))
                                     (map at (map case-l₂ (paths Db)))))

-- Right case branch, evaluated under the extended environment. Phase one folds the scrutinee: the branch's rewired columns carry the env slice
-- plus the routed slice through the evolving scrutinee collapse. Phase two folds the branch with
-- its env columns composed with the substitution W.
module CaseR {Γ τ₁ τ₂ τ} {γ : Env Γ} {ts : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
            {v : Val τ₂} {u : Val τ}
            {R : width-env γ ⇒ width v} {S : width-env (γ · v) ⇒ width u}
            {Ds : γ , ts ⇓ inr v [ R ]} {Db : γ · v , t₂ ⇓ u [ S ]} where

  iₗ : M.Matrix (width-env (γ · v)) (width-env γ)
  iₗ = M.in₁ {width-env γ} {width v}

  iᵣ : M.Matrix (width-env (γ · v)) (width v)
  iᵣ = M.in₂ {width-env γ} {width v}

  B : (q : Path Db) → M.Matrix (width-at q) (width-env (γ · v))
  B q = graph Db env (at q)

  W : M.Matrix (width-env (γ · v)) (width-env γ)
  W = iₗ M.+ₘ (iᵣ M.∘ collapse Ds)

  record Phase₁ (G : Graph (⇓-case-r {t₁ = t₁} Ds Db)) (H : Graph Ds) : Set ℓ where
    field
      env-scrut    : ∀ q → G env (at (case-r₁ q)) M.≈ₘ H env (at q)
      scrut-scrut  : ∀ p q → G (at (case-r₁ p)) (at (case-r₁ q)) M.≈ₘ H (at p) (at q)
      env-branch   : ∀ q → G env (at (case-r₂ q))
                     M.≈ₘ ((B q M.∘ iₗ) M.+ₘ ((B q M.∘ iᵣ) M.∘ H env (at ε)))
      scrut-branch : ∀ p → is-ε p ≡ Bool.false → ∀ q →
                     G (at (case-r₁ p)) (at (case-r₂ q)) M.≈ₘ ((B q M.∘ iᵣ) M.∘ H (at p) (at ε))
      branch-branch : ∀ p q → G (at (case-r₂ p)) (at (case-r₂ q)) M.≈ₘ graph Db (at p) (at q)
      branch-scrut  : ∀ p q → G (at (case-r₂ p)) (at (case-r₁ q)) M.≈ₘ M.εₘ
      env-root      : G env (at ε) M.≈ₘ M.εₘ
      scrut-root    : ∀ p → G (at (case-r₁ p)) (at ε) M.≈ₘ M.εₘ
      branch-root   : ∀ p → G (at (case-r₂ p)) (at ε) M.≈ₘ edge M.I p

  open Phase₁

  stepₛ : ∀ {G H} (w : Path Ds) → is-ε w ≡ Bool.false →
          Phase₁ G H → Phase₁ (hide G (at (case-r₁ w))) (hide H (at w))
  stepₛ w nw r .env-scrut q  = +ₘ-cong (r .env-scrut q) (∘-cong (r .scrut-scrut w q) (r .env-scrut w))
  stepₛ w nw r .scrut-scrut p q = +ₘ-cong (r .scrut-scrut p q) (∘-cong (r .scrut-scrut w q) (r .scrut-scrut p w))
  stepₛ w nw r .env-branch q =
    offset-step {K = B q M.∘ iₗ} {P = B q M.∘ iᵣ}
                (r .env-branch q) (r .scrut-branch w nw q) (r .env-scrut w)
  stepₛ w nw r .scrut-branch p np q =
    root-step {P = B q M.∘ iᵣ} (r .scrut-branch p np q) (r .scrut-branch w nw q) (r .scrut-scrut p w)
  stepₛ {G} w nw r .branch-branch p q =
    ≈-trans (+ₘ-cong (r .branch-branch p q) (∘-cong₂ (r .branch-scrut p w)))
            (absorb-r (graph Db (at p) (at q)) (G (at (case-r₁ w)) (at (case-r₂ q))))
  stepₛ {G} w nw r .branch-scrut p q =
    ≈-trans (+ₘ-cong (r .branch-scrut p q) (∘-cong₂ (r .branch-scrut p w)))
            (absorb-r M.εₘ (G (at (case-r₁ w)) (at (case-r₁ q))))
  stepₛ {G} w nw r .env-root =
    ≈-trans (+ₘ-cong (r .env-root) (∘-cong₁ (r .scrut-root w))) (absorb M.εₘ (G env (at (case-r₁ w))))
  stepₛ {G} w nw r .scrut-root p =
    ≈-trans (+ₘ-cong (r .scrut-root p) (∘-cong₁ (r .scrut-root w)))
            (absorb M.εₘ (G (at (case-r₁ p)) (at (case-r₁ w))))
  stepₛ {G} w nw r .branch-root p =
    ≈-trans (+ₘ-cong (r .branch-root p) (∘-cong₁ (r .scrut-root w)))
            (absorb (edge M.I p) (G (at (case-r₂ p)) (at (case-r₁ w))))

  foldₛ : ∀ {G H} (ws : List (Path Ds)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₁ G H → Phase₁ (hide-all G (map at (map case-r₁ ws))) (hide-all H (map at ws))
  foldₛ []       []         r = r
  foldₛ (w ∷ ws) (nw ∷ nws) r = foldₛ ws nws (stepₛ w nw r)

  private
    hh : ∀ x y → hide (hide (graph (⇓-case-r {t₁ = t₁} Ds Db)) (at ε)) (at (case-r₁ ε)) x y
         M.≈ₘ (graph (⇓-case-r {t₁ = t₁} Ds Db) x y
               M.+ₘ (graph (⇓-case-r {t₁ = t₁} Ds Db) (at (case-r₁ ε)) y M.∘ graph (⇓-case-r {t₁ = t₁} Ds Db) x (at (case-r₁ ε))))
    hh = hide-hide-root (⇓-case-r {t₁ = t₁} Ds Db) (at (case-r₁ ε))

    base₁ : Phase₁ (hide (hide (graph (⇓-case-r {t₁ = t₁} Ds Db)) (at ε)) (at (case-r₁ ε))) (hide (graph Ds) (at ε))
    base₁ .env-scrut q  = hh env (at (case-r₁ q))
    base₁ .scrut-scrut p q = hh (at (case-r₁ p)) (at (case-r₁ q))
    base₁ .env-branch q =
      ≈-trans (hh env (at (case-r₂ q)))
              (+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (hide-root Ds env (at ε)))))
    base₁ .scrut-branch p np q =
      ≈-trans (hh (at (case-r₁ p)) (at (case-r₂ q)))
      (≈-trans (+ₘ-cong (edge-off (B q M.∘ iᵣ) p np) ≈-refl)
               (into-hidden Ds (B q M.∘ iᵣ) (at p)))
    base₁ .branch-branch p q =
      ≈-trans (hh (at (case-r₂ p)) (at (case-r₂ q))) (absorb-r (graph Db (at p) (at q)) (B q M.∘ iᵣ))
    base₁ .branch-scrut p q =
      ≈-trans (hh (at (case-r₂ p)) (at (case-r₁ q))) (absorb-r M.εₘ (graph Ds (at ε) (at q)))
    base₁ .env-root = ≈-trans (hh env (at ε)) (absorb M.εₘ (graph Ds env (at ε)))
    base₁ .scrut-root p = ≈-trans (hh (at (case-r₁ p)) (at ε)) (absorb M.εₘ (graph Ds (at p) (at ε)))
    base₁ .branch-root p =
      ≈-trans (hh (at (case-r₂ p)) (at ε))
              (absorb (edge M.I p) (graph (⇓-case-r {t₁ = t₁} Ds Db) (at (case-r₂ p)) (at (case-r₁ ε))))

  record Phase₂ (G : Graph (⇓-case-r {t₁ = t₁} Ds Db)) (H : Graph Db) : Set ℓ where
    field
      env-branch    : ∀ q → G env (at (case-r₂ q)) M.≈ₘ (H env (at q) M.∘ W)
      branch-branch : ∀ p q → G (at (case-r₂ p)) (at (case-r₂ q)) M.≈ₘ H (at p) (at q)
      env-root      : G env (at ε) M.≈ₘ (H env (at ε) M.∘ W)
      branch-root   : ∀ p → is-ε p ≡ Bool.false → G (at (case-r₂ p)) (at ε) M.≈ₘ H (at p) (at ε)

  open Phase₂

  stepᵦ : ∀ {G H} (w : Path Db) → is-ε w ≡ Bool.false →
          Phase₂ G H → Phase₂ (hide G (at (case-r₂ w))) (hide H (at w))
  stepᵦ w nw r .env-branch q =
    step-under {W = W} (r .env-branch q) (r .branch-branch w q) (r .env-branch w)
  stepᵦ w nw r .branch-branch p q = +ₘ-cong (r .branch-branch p q) (∘-cong (r .branch-branch w q) (r .branch-branch p w))
  stepᵦ w nw r .env-root =
    step-under {W = W} (r .env-root) (r .branch-root w nw) (r .env-branch w)
  stepᵦ w nw r .branch-root p np = +ₘ-cong (r .branch-root p np) (∘-cong (r .branch-root w nw) (r .branch-branch p w))

  foldᵦ : ∀ {G H} (ws : List (Path Db)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₂ G H → Phase₂ (hide-all G (map at (map case-r₂ ws))) (hide-all H (map at ws))
  foldᵦ []       []         r = r
  foldᵦ (w ∷ ws) (nw ∷ nws) r = foldᵦ ws nws (stepᵦ w nw r)

  private
    r1 : Phase₁ (hide-all (hide (hide (graph (⇓-case-r {t₁ = t₁} Ds Db)) (at ε)) (at (case-r₁ ε)))
                          (map at (map case-r₁ (interior Ds))))
                (hide-all (hide (graph Ds) (at ε)) (map at (interior Ds)))
    r1 = foldₛ (interior Ds) (interior-not-root Ds) base₁

    base₂ : Phase₂ (hide (hide-all (hide (hide (graph (⇓-case-r {t₁ = t₁} Ds Db)) (at ε)) (at (case-r₁ ε)))
                                   (map at (map case-r₁ (interior Ds))))
                         (at (case-r₂ ε)))
                   (hide (graph Db) (at ε))
    base₂ .env-branch q =
      ≈-trans (+ₘ-cong (≈-trans (r1 .env-branch q) (factor (B q) (collapse Ds)))
                       (∘-cong₁ (≈-trans (r1 .branch-branch ε q) (root-sink Db (at q)))))
      (≈-trans (absorb (B q M.∘ W) (graph (⇓-case-r {t₁ = t₁} Ds Db) env (at (case-r₂ ε))))
               (≈-sym (∘-cong₁ (hide-root Db env (at q)))))
    base₂ .branch-branch p q =
      +ₘ-cong (r1 .branch-branch p q) (∘-cong (r1 .branch-branch ε q) (r1 .branch-branch p ε))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (r1 .env-root)
                       (∘-cong (r1 .branch-root ε) (≈-trans (r1 .env-branch ε) (factor (B ε) (collapse Ds)))))
      (≈-trans (+ₘ-lunit (M.I M.∘ (B ε M.∘ W)))
      (≈-trans id-left (≈-sym (∘-cong₁ (hide-root Db env (at ε))))))
    base₂ .branch-root p np =
      ≈-trans (+ₘ-cong (≈-trans (r1 .branch-root p) (edge-off M.I p np))
                       (∘-cong (r1 .branch-root ε) (r1 .branch-branch p ε)))
      (≈-trans (into-hidden Db M.I (at p)) id-left)

  -- Collapsing a agree-case-r-branch derivation composes the branch collapse with the substitution.
  agree-case-r : collapse (⇓-case-r {t₁ = t₁} Ds Db)
             M.≈ₘ (collapse Db M.∘ W)
  agree-case-r =
    ≈-trans (≈-of-≡ plumb) (foldᵦ (interior Db) (interior-not-root Db) base₂ .env-root)
    where
      plumb : hide-all (hide (graph (⇓-case-r {t₁ = t₁} Ds Db)) (at ε))
                       (map at (map case-r₁ (paths Ds) ++ map case-r₂ (paths Db))) env (at ε)
              ≡ hide-all (hide-all (hide (graph (⇓-case-r {t₁ = t₁} Ds Db)) (at ε)) (map at (map case-r₁ (paths Ds))))
                         (map at (map case-r₂ (paths Db))) env (at ε)
      plumb =
        ≡-trans (≡-cong (λ L → hide-all (hide (graph (⇓-case-r {t₁ = t₁} Ds Db)) (at ε)) L env (at ε))
                        (map-++ at (map case-r₁ (paths Ds)) (map case-r₂ (paths Db))))
                (≡-cong (λ Gg → Gg env (at ε))
                        (hide-all-++ (hide (graph (⇓-case-r {t₁ = t₁} Ds Db)) (at ε))
                                     (map at (map case-r₁ (paths Ds)))
                                     (map at (map case-r₂ (paths Db)))))
