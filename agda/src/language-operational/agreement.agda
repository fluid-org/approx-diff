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
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_)
open import type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-operational.evaluation Sig 𝒫
open import language-operational.path Sig 𝒫
open import language-operational.graph Sig 𝒫
open import language-operational.hide Sig 𝒫

private
  module M = matrix.Mat two.semiring

open CommutativeSemiring two.semiring using (+-comm; +-cong; +-lunit; +-assoc; +-interchange; refl; trans)
import Data.Bool as Bool
import Data.Nat
open import Data.List using (List; []; _∷_; _++_; map)
open import every using (Every; []; _∷_)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Relation.Unary.All.Properties using (map⁺; ++⁺)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; cong to ≡-cong; trans to ≡-trans; sym to ≡-sym)
  using (subst)
open import prop-setoid using (module ≈-Reasoning) renaming (_⇒_ to _⇒ₛ_)
open _⇒ₛ_ using (func)
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _⊎'_)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤')
import Level
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

hide-all-s-++ : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
                {Ds : γ , Ms ⇓s vs [ R ]}
                (G : GraphS Ds) (xs ys : List (VertexS Ds)) →
                hide-all-s G (xs ++ ys) ≡ hide-all-s (hide-all-s G xs) ys
hide-all-s-++ G []       ys = ≡-refl
hide-all-s-++ G (x ∷ xs) ys = hide-all-s-++ (hide-s G x) xs ys

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
            {D₁ : γ , ts ⇓ v [ R ]} {D₂ : γ , tt ⇓ u [ S ]} where

  record Phase₁ (G : Graph (⇓-pair D₁ D₂)) (H : Graph D₁) : Set ℓ where
    field
      env-left    : ∀ q → G env (at (pair₁ q)) M.≈ₘ H env (at q)
      left-left   : ∀ p q → G (at (pair₁ p)) (at (pair₁ q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (M.in₁ M.∘ H env (at ε))
      left-root   : ∀ p → is-ε p ≡ Bool.false →
                    G (at (pair₁ p)) (at ε) M.≈ₘ (M.in₁ M.∘ H (at p) (at ε))
      env-right   : ∀ q → G env (at (pair₂ q)) M.≈ₘ graph D₂ env (at q)
      right-right : ∀ p q → G (at (pair₂ p)) (at (pair₂ q)) M.≈ₘ graph D₂ (at p) (at q)
      right-root  : ∀ p → G (at (pair₂ p)) (at ε) M.≈ₘ edge M.in₂ p
      left-right  : ∀ p q → G (at (pair₁ p)) (at (pair₂ q)) M.≈ₘ M.εₘ
      right-left  : ∀ p q → G (at (pair₂ p)) (at (pair₁ q)) M.≈ₘ M.εₘ

  open Phase₁

  stepₗ : ∀ {G H} (w : Path D₁) → is-ε w ≡ Bool.false →
          Phase₁ G H → Phase₁ (hide G (at (pair₁ w))) (hide H (at w))
  stepₗ w nw r .env-left q  = +ₘ-cong (r .env-left q) (∘-cong (r .left-left w q) (r .env-left w))
  stepₗ w nw r .left-left p q = +ₘ-cong (r .left-left p q) (∘-cong (r .left-left w q) (r .left-left p w))
  stepₗ w nw r .env-root = root-step {P = M.in₁ {width v} {width u}} (r .env-root) (r .left-root w nw) (r .env-left w)
  stepₗ w nw r .left-root p np = root-step {P = M.in₁ {width v} {width u}} (r .left-root p np) (r .left-root w nw) (r .left-left p w)
  stepₗ {G} w nw r .env-right q =
    ≈-trans (+ₘ-cong (r .env-right q) (∘-cong₁ (r .left-right w q)))
            (absorb (graph D₂ env (at q)) (G env (at (pair₁ w))))
  stepₗ {G} w nw r .right-right p q =
    ≈-trans (+ₘ-cong (r .right-right p q) (∘-cong₁ (r .left-right w q)))
            (absorb (graph D₂ (at p) (at q)) (G (at (pair₂ p)) (at (pair₁ w))))
  stepₗ {G} w nw r .right-root p =
    ≈-trans (+ₘ-cong (r .right-root p) (∘-cong₂ (r .right-left p w)))
            (absorb-r (edge M.in₂ p) (G (at (pair₁ w)) (at ε)))
  stepₗ {G} w nw r .left-right p q =
    ≈-trans (+ₘ-cong (r .left-right p q) (∘-cong₁ (r .left-right w q)))
            (absorb M.εₘ (G (at (pair₁ p)) (at (pair₁ w))))
  stepₗ {G} w nw r .right-left p q =
    ≈-trans (+ₘ-cong (r .right-left p q) (∘-cong₂ (r .right-left p w)))
            (absorb-r M.εₘ (G (at (pair₁ w)) (at (pair₁ q))))

  foldₗ : ∀ {G H} (ws : List (Path D₁)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₁ G H → Phase₁ (hide-all G (map at (map pair₁ ws))) (hide-all H (map at ws))
  foldₗ []       []         r = r
  foldₗ (w ∷ ws) (nw ∷ nws) r = foldₗ ws nws (stepₗ w nw r)

  private
    hh : ∀ x y → hide (hide (graph (⇓-pair D₁ D₂)) (at ε)) (at (pair₁ ε)) x y
         M.≈ₘ (graph (⇓-pair D₁ D₂) x y
               M.+ₘ (graph (⇓-pair D₁ D₂) (at (pair₁ ε)) y M.∘ graph (⇓-pair D₁ D₂) x (at (pair₁ ε))))
    hh = hide-hide-root (⇓-pair D₁ D₂) (at (pair₁ ε))

    base₁ : Phase₁ (hide (hide (graph (⇓-pair D₁ D₂)) (at ε)) (at (pair₁ ε)))
                   (hide (graph D₁) (at ε))
    base₁ .env-left q  = hh env (at (pair₁ q))
    base₁ .left-left p q = hh (at (pair₁ p)) (at (pair₁ q))
    base₁ .env-root = ≈-trans (hh env (at ε)) (into-hidden D₁ M.in₁ env)
    base₁ .left-root p np =
      ≈-trans (hh (at (pair₁ p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off M.in₁ p np) ≈-refl) (into-hidden D₁ M.in₁ (at p)))
    base₁ .env-right q = ≈-trans (hh env (at (pair₂ q))) (absorb (graph D₂ env (at q)) (graph D₁ env (at ε)))
    base₁ .right-right p q =
      ≈-trans (hh (at (pair₂ p)) (at (pair₂ q)))
              (absorb (graph D₂ (at p) (at q)) (graph (⇓-pair D₁ D₂) (at (pair₂ p)) (at (pair₁ ε))))
    base₁ .right-root p =
      ≈-trans (hh (at (pair₂ p)) (at ε))
              (absorb-r (edge M.in₂ p) (graph (⇓-pair D₁ D₂) (at (pair₁ ε)) (at ε)))
    base₁ .left-right p q =
      ≈-trans (hh (at (pair₁ p)) (at (pair₂ q))) (absorb M.εₘ (graph D₁ (at p) (at ε)))
    base₁ .right-left p q =
      ≈-trans (hh (at (pair₂ p)) (at (pair₁ q))) (absorb-r M.εₘ (graph D₁ (at ε) (at q)))

  record Phase₂ (G : Graph (⇓-pair D₁ D₂)) (H : Graph D₂)
                (K : M.Matrix (width (pair v u)) (width-env γ)) : Set ℓ where
    field
      env-right   : ∀ q → G env (at (pair₂ q)) M.≈ₘ H env (at q)
      right-right : ∀ p q → G (at (pair₂ p)) (at (pair₂ q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (K M.+ₘ (M.in₂ M.∘ H env (at ε)))
      right-root  : ∀ p → is-ε p ≡ Bool.false →
                    G (at (pair₂ p)) (at ε) M.≈ₘ (M.in₂ M.∘ H (at p) (at ε))

  open Phase₂

  stepᵣ : ∀ {G H K} (w : Path D₂) → is-ε w ≡ Bool.false →
          Phase₂ G H K → Phase₂ (hide G (at (pair₂ w))) (hide H (at w)) K
  stepᵣ w nw r .env-right q  = +ₘ-cong (r .env-right q) (∘-cong (r .right-right w q) (r .env-right w))
  stepᵣ w nw r .right-right p q = +ₘ-cong (r .right-right p q) (∘-cong (r .right-right w q) (r .right-right p w))
  stepᵣ w nw r .env-root = offset-step {P = M.in₂ {width v} {width u}} (r .env-root) (r .right-root w nw) (r .env-right w)
  stepᵣ w nw r .right-root p np = root-step {P = M.in₂ {width v} {width u}} (r .right-root p np) (r .right-root w nw) (r .right-right p w)

  foldᵣ : ∀ {G H K} (ws : List (Path D₂)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₂ G H K → Phase₂ (hide-all G (map at (map pair₂ ws))) (hide-all H (map at ws)) K
  foldᵣ []       []         r = r
  foldᵣ (w ∷ ws) (nw ∷ nws) r = foldᵣ ws nws (stepᵣ w nw r)

  private
    r1 : Phase₁ (hide-all (hide (hide (graph (⇓-pair D₁ D₂)) (at ε)) (at (pair₁ ε)))
                          (map at (map pair₁ (interior D₁))))
                (hide-all (hide (graph D₁) (at ε)) (map at (interior D₁)))
    r1 = foldₗ (interior D₁) (interior-not-root D₁) base₁

    base₂ : Phase₂ (hide (hide-all (hide (hide (graph (⇓-pair D₁ D₂)) (at ε)) (at (pair₁ ε)))
                                   (map at (map pair₁ (interior D₁))))
                         (at (pair₂ ε)))
                   (hide (graph D₂) (at ε))
                   (M.in₁ M.∘ collapse D₁)
    base₂ .env-right q = +ₘ-cong (r1 .env-right q) (∘-cong (r1 .right-right ε q) (r1 .env-right ε))
    base₂ .right-right p q = +ₘ-cong (r1 .right-right p q) (∘-cong (r1 .right-right ε q) (r1 .right-right p ε))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (r1 .env-root) (∘-cong (r1 .right-root ε) (r1 .env-right ε)))
              (+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (hide-root D₂ env (at ε)))))
    base₂ .right-root p np =
      ≈-trans (+ₘ-cong (r1 .right-root p) (∘-cong (r1 .right-root ε) (r1 .right-right p ε)))
      (≈-trans (+ₘ-cong (edge-off M.in₂ p np) ≈-refl) (into-hidden D₂ M.in₂ (at p)))

  -- Collapsing a pair derivation pairs its premises' collapses.
  agree-pair : collapse (⇓-pair D₁ D₂)
               M.≈ₘ ((M.in₁ M.∘ collapse D₁) M.+ₘ (M.in₂ M.∘ collapse D₂))
  agree-pair =
    ≈-trans (≈-of-≡ plumb) (foldᵣ (interior D₂) (interior-not-root D₂) base₂ .env-root)
    where
      plumb : hide-all (hide (graph (⇓-pair D₁ D₂)) (at ε))
                       (map at (map pair₁ (paths D₁) ++ map pair₂ (paths D₂))) env (at ε)
              ≡ hide-all (hide-all (hide (graph (⇓-pair D₁ D₂)) (at ε))
                                   (map at (map pair₁ (paths D₁))))
                         (map at (map pair₂ (paths D₂))) env (at ε)
      plumb =
        ≡-trans (≡-cong (λ L → hide-all (hide (graph (⇓-pair D₁ D₂)) (at ε)) L env (at ε))
                        (map-++ at (map pair₁ (paths D₁)) (map pair₂ (paths D₂))))
                (≡-cong (λ Gg → Gg env (at ε))
                        (hide-all-++ (hide (graph (⇓-pair D₁ D₂)) (at ε))
                                     (map at (map pair₁ (paths D₁)))
                                     (map at (map pair₂ (paths D₂)))))

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
            {D₁ : γ , ts ⇓ inl v [ R ]} {D₂ : γ · v , t₁ ⇓ u [ S ]} where

  iₗ : M.Matrix (width-env (γ · v)) (width-env γ)
  iₗ = M.in₁ {width-env γ} {width v}

  iᵣ : M.Matrix (width-env (γ · v)) (width v)
  iᵣ = M.in₂ {width-env γ} {width v}

  B : (q : Path D₂) → M.Matrix (width-at q) (width-env (γ · v))
  B q = graph D₂ env (at q)

  W : M.Matrix (width-env (γ · v)) (width-env γ)
  W = iₗ M.+ₘ (iᵣ M.∘ collapse D₁)

  record Phase₁ (G : Graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (H : Graph D₁) : Set ℓ where
    field
      env-scrut    : ∀ q → G env (at (case-l₁ q)) M.≈ₘ H env (at q)
      scrut-scrut  : ∀ p q → G (at (case-l₁ p)) (at (case-l₁ q)) M.≈ₘ H (at p) (at q)
      env-branch   : ∀ q → G env (at (case-l₂ q))
                     M.≈ₘ ((B q M.∘ iₗ) M.+ₘ ((B q M.∘ iᵣ) M.∘ H env (at ε)))
      scrut-branch : ∀ p → is-ε p ≡ Bool.false → ∀ q →
                     G (at (case-l₁ p)) (at (case-l₂ q)) M.≈ₘ ((B q M.∘ iᵣ) M.∘ H (at p) (at ε))
      branch-branch : ∀ p q → G (at (case-l₂ p)) (at (case-l₂ q)) M.≈ₘ graph D₂ (at p) (at q)
      branch-scrut  : ∀ p q → G (at (case-l₂ p)) (at (case-l₁ q)) M.≈ₘ M.εₘ
      env-root      : G env (at ε) M.≈ₘ M.εₘ
      scrut-root    : ∀ p → G (at (case-l₁ p)) (at ε) M.≈ₘ M.εₘ
      branch-root   : ∀ p → G (at (case-l₂ p)) (at ε) M.≈ₘ edge M.I p

  open Phase₁

  stepₛ : ∀ {G H} (w : Path D₁) → is-ε w ≡ Bool.false →
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
            (absorb-r (graph D₂ (at p) (at q)) (G (at (case-l₁ w)) (at (case-l₂ q))))
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

  foldₛ : ∀ {G H} (ws : List (Path D₁)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₁ G H → Phase₁ (hide-all G (map at (map case-l₁ ws))) (hide-all H (map at ws))
  foldₛ []       []         r = r
  foldₛ (w ∷ ws) (nw ∷ nws) r = foldₛ ws nws (stepₛ w nw r)

  private
    hh : ∀ x y → hide (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε)) (at (case-l₁ ε)) x y
         M.≈ₘ (graph (⇓-case-l {t₂ = t₂} D₁ D₂) x y
               M.+ₘ (graph (⇓-case-l {t₂ = t₂} D₁ D₂) (at (case-l₁ ε)) y M.∘ graph (⇓-case-l {t₂ = t₂} D₁ D₂) x (at (case-l₁ ε))))
    hh = hide-hide-root (⇓-case-l {t₂ = t₂} D₁ D₂) (at (case-l₁ ε))

    base₁ : Phase₁ (hide (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε)) (at (case-l₁ ε))) (hide (graph D₁) (at ε))
    base₁ .env-scrut q  = hh env (at (case-l₁ q))
    base₁ .scrut-scrut p q = hh (at (case-l₁ p)) (at (case-l₁ q))
    base₁ .env-branch q =
      ≈-trans (hh env (at (case-l₂ q)))
              (+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (hide-root D₁ env (at ε)))))
    base₁ .scrut-branch p np q =
      ≈-trans (hh (at (case-l₁ p)) (at (case-l₂ q)))
      (≈-trans (+ₘ-cong (edge-off (B q M.∘ iᵣ) p np) ≈-refl)
               (into-hidden D₁ (B q M.∘ iᵣ) (at p)))
    base₁ .branch-branch p q =
      ≈-trans (hh (at (case-l₂ p)) (at (case-l₂ q))) (absorb-r (graph D₂ (at p) (at q)) (B q M.∘ iᵣ))
    base₁ .branch-scrut p q =
      ≈-trans (hh (at (case-l₂ p)) (at (case-l₁ q))) (absorb-r M.εₘ (graph D₁ (at ε) (at q)))
    base₁ .env-root = ≈-trans (hh env (at ε)) (absorb M.εₘ (graph D₁ env (at ε)))
    base₁ .scrut-root p = ≈-trans (hh (at (case-l₁ p)) (at ε)) (absorb M.εₘ (graph D₁ (at p) (at ε)))
    base₁ .branch-root p =
      ≈-trans (hh (at (case-l₂ p)) (at ε))
              (absorb (edge M.I p) (graph (⇓-case-l {t₂ = t₂} D₁ D₂) (at (case-l₂ p)) (at (case-l₁ ε))))

  record Phase₂ (G : Graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (H : Graph D₂) : Set ℓ where
    field
      env-branch    : ∀ q → G env (at (case-l₂ q)) M.≈ₘ (H env (at q) M.∘ W)
      branch-branch : ∀ p q → G (at (case-l₂ p)) (at (case-l₂ q)) M.≈ₘ H (at p) (at q)
      env-root      : G env (at ε) M.≈ₘ (H env (at ε) M.∘ W)
      branch-root   : ∀ p → is-ε p ≡ Bool.false → G (at (case-l₂ p)) (at ε) M.≈ₘ H (at p) (at ε)

  open Phase₂

  stepᵦ : ∀ {G H} (w : Path D₂) → is-ε w ≡ Bool.false →
          Phase₂ G H → Phase₂ (hide G (at (case-l₂ w))) (hide H (at w))
  stepᵦ w nw r .env-branch q =
    step-under {W = W} (r .env-branch q) (r .branch-branch w q) (r .env-branch w)
  stepᵦ w nw r .branch-branch p q = +ₘ-cong (r .branch-branch p q) (∘-cong (r .branch-branch w q) (r .branch-branch p w))
  stepᵦ w nw r .env-root =
    step-under {W = W} (r .env-root) (r .branch-root w nw) (r .env-branch w)
  stepᵦ w nw r .branch-root p np = +ₘ-cong (r .branch-root p np) (∘-cong (r .branch-root w nw) (r .branch-branch p w))

  foldᵦ : ∀ {G H} (ws : List (Path D₂)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₂ G H → Phase₂ (hide-all G (map at (map case-l₂ ws))) (hide-all H (map at ws))
  foldᵦ []       []         r = r
  foldᵦ (w ∷ ws) (nw ∷ nws) r = foldᵦ ws nws (stepᵦ w nw r)

  private
    r1 : Phase₁ (hide-all (hide (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε)) (at (case-l₁ ε)))
                          (map at (map case-l₁ (interior D₁))))
                (hide-all (hide (graph D₁) (at ε)) (map at (interior D₁)))
    r1 = foldₛ (interior D₁) (interior-not-root D₁) base₁

    base₂ : Phase₂ (hide (hide-all (hide (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε)) (at (case-l₁ ε)))
                                   (map at (map case-l₁ (interior D₁))))
                         (at (case-l₂ ε)))
                   (hide (graph D₂) (at ε))
    base₂ .env-branch q =
      ≈-trans (+ₘ-cong (≈-trans (r1 .env-branch q) (factor (B q) (collapse D₁)))
                       (∘-cong₁ (≈-trans (r1 .branch-branch ε q) (root-sink D₂ (at q)))))
      (≈-trans (absorb (B q M.∘ W) (graph (⇓-case-l {t₂ = t₂} D₁ D₂) env (at (case-l₂ ε))))
               (≈-sym (∘-cong₁ (hide-root D₂ env (at q)))))
    base₂ .branch-branch p q =
      +ₘ-cong (r1 .branch-branch p q) (∘-cong (r1 .branch-branch ε q) (r1 .branch-branch p ε))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (r1 .env-root)
                       (∘-cong (r1 .branch-root ε) (≈-trans (r1 .env-branch ε) (factor (B ε) (collapse D₁)))))
      (≈-trans (+ₘ-lunit (M.I M.∘ (B ε M.∘ W)))
      (≈-trans id-left (≈-sym (∘-cong₁ (hide-root D₂ env (at ε))))))
    base₂ .branch-root p np =
      ≈-trans (+ₘ-cong (≈-trans (r1 .branch-root p) (edge-off M.I p np))
                       (∘-cong (r1 .branch-root ε) (r1 .branch-branch p ε)))
      (≈-trans (into-hidden D₂ M.I (at p)) id-left)

  -- Collapsing a agree-case-l-branch derivation composes the branch collapse with the substitution.
  agree-case-l : collapse (⇓-case-l {t₂ = t₂} D₁ D₂)
             M.≈ₘ (collapse D₂ M.∘ W)
  agree-case-l =
    ≈-trans (≈-of-≡ plumb) (foldᵦ (interior D₂) (interior-not-root D₂) base₂ .env-root)
    where
      plumb : hide-all (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε))
                       (map at (map case-l₁ (paths D₁) ++ map case-l₂ (paths D₂))) env (at ε)
              ≡ hide-all (hide-all (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε)) (map at (map case-l₁ (paths D₁))))
                         (map at (map case-l₂ (paths D₂))) env (at ε)
      plumb =
        ≡-trans (≡-cong (λ L → hide-all (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε)) L env (at ε))
                        (map-++ at (map case-l₁ (paths D₁)) (map case-l₂ (paths D₂))))
                (≡-cong (λ Gg → Gg env (at ε))
                        (hide-all-++ (hide (graph (⇓-case-l {t₂ = t₂} D₁ D₂)) (at ε))
                                     (map at (map case-l₁ (paths D₁)))
                                     (map at (map case-l₂ (paths D₂)))))

-- Right case branch, evaluated under the extended environment. Phase one folds the scrutinee: the branch's rewired columns carry the env slice
-- plus the routed slice through the evolving scrutinee collapse. Phase two folds the branch with
-- its env columns composed with the substitution W.
module CaseR {Γ τ₁ τ₂ τ} {γ : Env Γ} {ts : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
            {v : Val τ₂} {u : Val τ}
            {R : width-env γ ⇒ width v} {S : width-env (γ · v) ⇒ width u}
            {D₁ : γ , ts ⇓ inr v [ R ]} {D₂ : γ · v , t₂ ⇓ u [ S ]} where

  iₗ : M.Matrix (width-env (γ · v)) (width-env γ)
  iₗ = M.in₁ {width-env γ} {width v}

  iᵣ : M.Matrix (width-env (γ · v)) (width v)
  iᵣ = M.in₂ {width-env γ} {width v}

  B : (q : Path D₂) → M.Matrix (width-at q) (width-env (γ · v))
  B q = graph D₂ env (at q)

  W : M.Matrix (width-env (γ · v)) (width-env γ)
  W = iₗ M.+ₘ (iᵣ M.∘ collapse D₁)

  record Phase₁ (G : Graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (H : Graph D₁) : Set ℓ where
    field
      env-scrut    : ∀ q → G env (at (case-r₁ q)) M.≈ₘ H env (at q)
      scrut-scrut  : ∀ p q → G (at (case-r₁ p)) (at (case-r₁ q)) M.≈ₘ H (at p) (at q)
      env-branch   : ∀ q → G env (at (case-r₂ q))
                     M.≈ₘ ((B q M.∘ iₗ) M.+ₘ ((B q M.∘ iᵣ) M.∘ H env (at ε)))
      scrut-branch : ∀ p → is-ε p ≡ Bool.false → ∀ q →
                     G (at (case-r₁ p)) (at (case-r₂ q)) M.≈ₘ ((B q M.∘ iᵣ) M.∘ H (at p) (at ε))
      branch-branch : ∀ p q → G (at (case-r₂ p)) (at (case-r₂ q)) M.≈ₘ graph D₂ (at p) (at q)
      branch-scrut  : ∀ p q → G (at (case-r₂ p)) (at (case-r₁ q)) M.≈ₘ M.εₘ
      env-root      : G env (at ε) M.≈ₘ M.εₘ
      scrut-root    : ∀ p → G (at (case-r₁ p)) (at ε) M.≈ₘ M.εₘ
      branch-root   : ∀ p → G (at (case-r₂ p)) (at ε) M.≈ₘ edge M.I p

  open Phase₁

  stepₛ : ∀ {G H} (w : Path D₁) → is-ε w ≡ Bool.false →
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
            (absorb-r (graph D₂ (at p) (at q)) (G (at (case-r₁ w)) (at (case-r₂ q))))
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

  foldₛ : ∀ {G H} (ws : List (Path D₁)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₁ G H → Phase₁ (hide-all G (map at (map case-r₁ ws))) (hide-all H (map at ws))
  foldₛ []       []         r = r
  foldₛ (w ∷ ws) (nw ∷ nws) r = foldₛ ws nws (stepₛ w nw r)

  private
    hh : ∀ x y → hide (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε)) (at (case-r₁ ε)) x y
         M.≈ₘ (graph (⇓-case-r {t₁ = t₁} D₁ D₂) x y
               M.+ₘ (graph (⇓-case-r {t₁ = t₁} D₁ D₂) (at (case-r₁ ε)) y M.∘ graph (⇓-case-r {t₁ = t₁} D₁ D₂) x (at (case-r₁ ε))))
    hh = hide-hide-root (⇓-case-r {t₁ = t₁} D₁ D₂) (at (case-r₁ ε))

    base₁ : Phase₁ (hide (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε)) (at (case-r₁ ε))) (hide (graph D₁) (at ε))
    base₁ .env-scrut q  = hh env (at (case-r₁ q))
    base₁ .scrut-scrut p q = hh (at (case-r₁ p)) (at (case-r₁ q))
    base₁ .env-branch q =
      ≈-trans (hh env (at (case-r₂ q)))
              (+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (hide-root D₁ env (at ε)))))
    base₁ .scrut-branch p np q =
      ≈-trans (hh (at (case-r₁ p)) (at (case-r₂ q)))
      (≈-trans (+ₘ-cong (edge-off (B q M.∘ iᵣ) p np) ≈-refl)
               (into-hidden D₁ (B q M.∘ iᵣ) (at p)))
    base₁ .branch-branch p q =
      ≈-trans (hh (at (case-r₂ p)) (at (case-r₂ q))) (absorb-r (graph D₂ (at p) (at q)) (B q M.∘ iᵣ))
    base₁ .branch-scrut p q =
      ≈-trans (hh (at (case-r₂ p)) (at (case-r₁ q))) (absorb-r M.εₘ (graph D₁ (at ε) (at q)))
    base₁ .env-root = ≈-trans (hh env (at ε)) (absorb M.εₘ (graph D₁ env (at ε)))
    base₁ .scrut-root p = ≈-trans (hh (at (case-r₁ p)) (at ε)) (absorb M.εₘ (graph D₁ (at p) (at ε)))
    base₁ .branch-root p =
      ≈-trans (hh (at (case-r₂ p)) (at ε))
              (absorb (edge M.I p) (graph (⇓-case-r {t₁ = t₁} D₁ D₂) (at (case-r₂ p)) (at (case-r₁ ε))))

  record Phase₂ (G : Graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (H : Graph D₂) : Set ℓ where
    field
      env-branch    : ∀ q → G env (at (case-r₂ q)) M.≈ₘ (H env (at q) M.∘ W)
      branch-branch : ∀ p q → G (at (case-r₂ p)) (at (case-r₂ q)) M.≈ₘ H (at p) (at q)
      env-root      : G env (at ε) M.≈ₘ (H env (at ε) M.∘ W)
      branch-root   : ∀ p → is-ε p ≡ Bool.false → G (at (case-r₂ p)) (at ε) M.≈ₘ H (at p) (at ε)

  open Phase₂

  stepᵦ : ∀ {G H} (w : Path D₂) → is-ε w ≡ Bool.false →
          Phase₂ G H → Phase₂ (hide G (at (case-r₂ w))) (hide H (at w))
  stepᵦ w nw r .env-branch q =
    step-under {W = W} (r .env-branch q) (r .branch-branch w q) (r .env-branch w)
  stepᵦ w nw r .branch-branch p q = +ₘ-cong (r .branch-branch p q) (∘-cong (r .branch-branch w q) (r .branch-branch p w))
  stepᵦ w nw r .env-root =
    step-under {W = W} (r .env-root) (r .branch-root w nw) (r .env-branch w)
  stepᵦ w nw r .branch-root p np = +ₘ-cong (r .branch-root p np) (∘-cong (r .branch-root w nw) (r .branch-branch p w))

  foldᵦ : ∀ {G H} (ws : List (Path D₂)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₂ G H → Phase₂ (hide-all G (map at (map case-r₂ ws))) (hide-all H (map at ws))
  foldᵦ []       []         r = r
  foldᵦ (w ∷ ws) (nw ∷ nws) r = foldᵦ ws nws (stepᵦ w nw r)

  private
    r1 : Phase₁ (hide-all (hide (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε)) (at (case-r₁ ε)))
                          (map at (map case-r₁ (interior D₁))))
                (hide-all (hide (graph D₁) (at ε)) (map at (interior D₁)))
    r1 = foldₛ (interior D₁) (interior-not-root D₁) base₁

    base₂ : Phase₂ (hide (hide-all (hide (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε)) (at (case-r₁ ε)))
                                   (map at (map case-r₁ (interior D₁))))
                         (at (case-r₂ ε)))
                   (hide (graph D₂) (at ε))
    base₂ .env-branch q =
      ≈-trans (+ₘ-cong (≈-trans (r1 .env-branch q) (factor (B q) (collapse D₁)))
                       (∘-cong₁ (≈-trans (r1 .branch-branch ε q) (root-sink D₂ (at q)))))
      (≈-trans (absorb (B q M.∘ W) (graph (⇓-case-r {t₁ = t₁} D₁ D₂) env (at (case-r₂ ε))))
               (≈-sym (∘-cong₁ (hide-root D₂ env (at q)))))
    base₂ .branch-branch p q =
      +ₘ-cong (r1 .branch-branch p q) (∘-cong (r1 .branch-branch ε q) (r1 .branch-branch p ε))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (r1 .env-root)
                       (∘-cong (r1 .branch-root ε) (≈-trans (r1 .env-branch ε) (factor (B ε) (collapse D₁)))))
      (≈-trans (+ₘ-lunit (M.I M.∘ (B ε M.∘ W)))
      (≈-trans id-left (≈-sym (∘-cong₁ (hide-root D₂ env (at ε))))))
    base₂ .branch-root p np =
      ≈-trans (+ₘ-cong (≈-trans (r1 .branch-root p) (edge-off M.I p np))
                       (∘-cong (r1 .branch-root ε) (r1 .branch-branch p ε)))
      (≈-trans (into-hidden D₂ M.I (at p)) id-left)

  -- Collapsing a agree-case-r-branch derivation composes the branch collapse with the substitution.
  agree-case-r : collapse (⇓-case-r {t₁ = t₁} D₁ D₂)
             M.≈ₘ (collapse D₂ M.∘ W)
  agree-case-r =
    ≈-trans (≈-of-≡ plumb) (foldᵦ (interior D₂) (interior-not-root D₂) base₂ .env-root)
    where
      plumb : hide-all (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε))
                       (map at (map case-r₁ (paths D₁) ++ map case-r₂ (paths D₂))) env (at ε)
              ≡ hide-all (hide-all (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε)) (map at (map case-r₁ (paths D₁))))
                         (map at (map case-r₂ (paths D₂))) env (at ε)
      plumb =
        ≡-trans (≡-cong (λ L → hide-all (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε)) L env (at ε))
                        (map-++ at (map case-r₁ (paths D₁)) (map case-r₂ (paths D₂))))
                (≡-cong (λ Gg → Gg env (at ε))
                        (hide-all-++ (hide (graph (⇓-case-r {t₁ = t₁} D₁ D₂)) (at ε))
                                     (map at (map case-r₁ (paths D₁)))
                                     (map at (map case-r₂ (paths D₂)))))

-- Regroup a fully rewired column: both slices factor through the assembled substitution.
factor₂ : ∀ {m g wγ wv} (B : M.Matrix m (wγ Data.Nat.+ wv))
          (C₁ : M.Matrix wγ g) (C₂ : M.Matrix wv g) →
          (((B M.∘ M.in₁) M.∘ C₁) M.+ₘ ((B M.∘ M.in₂) M.∘ C₂))
          M.≈ₘ (B M.∘ ((M.in₁ M.∘ C₁) M.+ₘ (M.in₂ M.∘ C₂)))
factor₂ B C₁ C₂ =
  ≈-trans (+ₘ-cong (assoc B M.in₁ C₁) (assoc B M.in₂ C₂))
          (≈-sym (M.comp-bilinear₂ B (M.in₁ M.∘ C₁) (M.in₂ M.∘ C₂)))

-- Application: the function and argument premises fold in turn, the body's rewired columns
-- accumulating each collapse through its slice; the body then folds under the substitution W.
module App {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {ts : Γ ⊢ σ [→] τ} {tt : Γ ⊢ σ}
           {tb : Γ' ▸ σ ⊢ τ} {v : Val σ} {u : Val τ}
           {R : width-env γ ⇒ width-env γ'} {S : width-env γ ⇒ width v}
           {T : width-env (γ' · v) ⇒ width u}
           {D₁ : γ , ts ⇓ clo γ' tb [ R ]} {D₂ : γ , tt ⇓ v [ S ]}
           {D₃ : γ' · v , tb ⇓ u [ T ]} where

  iₗ : M.Matrix (width-env (γ' · v)) (width-env γ')
  iₗ = M.in₁ {width-env γ'} {width v}

  iᵣ : M.Matrix (width-env (γ' · v)) (width v)
  iᵣ = M.in₂ {width-env γ'} {width v}

  B : (q : Path D₃) → M.Matrix (width-at q) (width-env (γ' · v))
  B q = graph D₃ env (at q)

  W : M.Matrix (width-env (γ' · v)) (width-env γ)
  W = (iₗ M.∘ collapse D₁) M.+ₘ (iᵣ M.∘ collapse D₂)

  record Phase₁ (G : Graph (⇓-app D₁ D₂ D₃)) (H : Graph D₁) : Set ℓ where
    field
      env-fun   : ∀ q → G env (at (app₁ q)) M.≈ₘ H env (at q)
      fun-fun   : ∀ p q → G (at (app₁ p)) (at (app₁ q)) M.≈ₘ H (at p) (at q)
      env-arg   : ∀ q → G env (at (app₂ q)) M.≈ₘ graph D₂ env (at q)
      arg-arg   : ∀ p q → G (at (app₂ p)) (at (app₂ q)) M.≈ₘ graph D₂ (at p) (at q)
      fun-arg   : ∀ p q → G (at (app₁ p)) (at (app₂ q)) M.≈ₘ M.εₘ
      arg-fun   : ∀ p q → G (at (app₂ p)) (at (app₁ q)) M.≈ₘ M.εₘ
      env-body  : ∀ q → G env (at (app₃ q)) M.≈ₘ ((B q M.∘ iₗ) M.∘ H env (at ε))
      fun-body  : ∀ p → is-ε p ≡ Bool.false → ∀ q →
                  G (at (app₁ p)) (at (app₃ q)) M.≈ₘ ((B q M.∘ iₗ) M.∘ H (at p) (at ε))
      arg-body  : ∀ p q → G (at (app₂ p)) (at (app₃ q)) M.≈ₘ edge (B q M.∘ iᵣ) p
      body-body : ∀ p q → G (at (app₃ p)) (at (app₃ q)) M.≈ₘ graph D₃ (at p) (at q)
      body-fun  : ∀ p q → G (at (app₃ p)) (at (app₁ q)) M.≈ₘ M.εₘ
      body-arg  : ∀ p q → G (at (app₃ p)) (at (app₂ q)) M.≈ₘ M.εₘ
      env-root  : G env (at ε) M.≈ₘ M.εₘ
      fun-root  : ∀ p → G (at (app₁ p)) (at ε) M.≈ₘ M.εₘ
      arg-root  : ∀ p → G (at (app₂ p)) (at ε) M.≈ₘ M.εₘ
      body-root : ∀ p → G (at (app₃ p)) (at ε) M.≈ₘ edge M.I p

  open Phase₁

  stepf : ∀ {G H} (w : Path D₁) → is-ε w ≡ Bool.false →
          Phase₁ G H → Phase₁ (hide G (at (app₁ w))) (hide H (at w))
  stepf w nw r .env-fun q  = +ₘ-cong (r .env-fun q) (∘-cong (r .fun-fun w q) (r .env-fun w))
  stepf w nw r .fun-fun p q = +ₘ-cong (r .fun-fun p q) (∘-cong (r .fun-fun w q) (r .fun-fun p w))
  stepf {G} w nw r .env-arg q =
    ≈-trans (+ₘ-cong (r .env-arg q) (∘-cong₁ (r .fun-arg w q)))
            (absorb (graph D₂ env (at q)) (G env (at (app₁ w))))
  stepf {G} w nw r .arg-arg p q =
    ≈-trans (+ₘ-cong (r .arg-arg p q) (∘-cong₁ (r .fun-arg w q)))
            (absorb (graph D₂ (at p) (at q)) (G (at (app₂ p)) (at (app₁ w))))
  stepf {G} w nw r .fun-arg p q =
    ≈-trans (+ₘ-cong (r .fun-arg p q) (∘-cong₁ (r .fun-arg w q)))
            (absorb M.εₘ (G (at (app₁ p)) (at (app₁ w))))
  stepf {G} w nw r .arg-fun p q =
    ≈-trans (+ₘ-cong (r .arg-fun p q) (∘-cong₂ (r .arg-fun p w)))
            (absorb-r M.εₘ (G (at (app₁ w)) (at (app₁ q))))
  stepf w nw r .env-body q =
    root-step {P = B q M.∘ iₗ} (r .env-body q) (r .fun-body w nw q) (r .env-fun w)
  stepf w nw r .fun-body p np q =
    root-step {P = B q M.∘ iₗ} (r .fun-body p np q) (r .fun-body w nw q) (r .fun-fun p w)
  stepf {G} w nw r .arg-body p q =
    ≈-trans (+ₘ-cong (r .arg-body p q) (∘-cong₂ (r .arg-fun p w)))
            (absorb-r (edge (B q M.∘ iᵣ) p) (G (at (app₁ w)) (at (app₃ q))))
  stepf {G} w nw r .body-body p q =
    ≈-trans (+ₘ-cong (r .body-body p q) (∘-cong₂ (r .body-fun p w)))
            (absorb-r (graph D₃ (at p) (at q)) (G (at (app₁ w)) (at (app₃ q))))
  stepf {G} w nw r .body-fun p q =
    ≈-trans (+ₘ-cong (r .body-fun p q) (∘-cong₂ (r .body-fun p w)))
            (absorb-r M.εₘ (G (at (app₁ w)) (at (app₁ q))))
  stepf {G} w nw r .body-arg p q =
    ≈-trans (+ₘ-cong (r .body-arg p q) (∘-cong₁ (r .fun-arg w q)))
            (absorb M.εₘ (G (at (app₃ p)) (at (app₁ w))))
  stepf {G} w nw r .env-root =
    ≈-trans (+ₘ-cong (r .env-root) (∘-cong₁ (r .fun-root w))) (absorb M.εₘ (G env (at (app₁ w))))
  stepf {G} w nw r .fun-root p =
    ≈-trans (+ₘ-cong (r .fun-root p) (∘-cong₁ (r .fun-root w)))
            (absorb M.εₘ (G (at (app₁ p)) (at (app₁ w))))
  stepf {G} w nw r .arg-root p =
    ≈-trans (+ₘ-cong (r .arg-root p) (∘-cong₁ (r .fun-root w)))
            (absorb M.εₘ (G (at (app₂ p)) (at (app₁ w))))
  stepf {G} w nw r .body-root p =
    ≈-trans (+ₘ-cong (r .body-root p) (∘-cong₁ (r .fun-root w)))
            (absorb (edge M.I p) (G (at (app₃ p)) (at (app₁ w))))

  foldf : ∀ {G H} (ws : List (Path D₁)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₁ G H → Phase₁ (hide-all G (map at (map app₁ ws))) (hide-all H (map at ws))
  foldf []       []         r = r
  foldf (w ∷ ws) (nw ∷ nws) r = foldf ws nws (stepf w nw r)

  private
    hh : ∀ x y → hide (hide (graph (⇓-app D₁ D₂ D₃)) (at ε)) (at (app₁ ε)) x y
         M.≈ₘ (graph (⇓-app D₁ D₂ D₃) x y
               M.+ₘ (graph (⇓-app D₁ D₂ D₃) (at (app₁ ε)) y
                     M.∘ graph (⇓-app D₁ D₂ D₃) x (at (app₁ ε))))
    hh = hide-hide-root (⇓-app D₁ D₂ D₃) (at (app₁ ε))

    base₁ : Phase₁ (hide (hide (graph (⇓-app D₁ D₂ D₃)) (at ε)) (at (app₁ ε)))
                   (hide (graph D₁) (at ε))
    base₁ .env-fun q  = hh env (at (app₁ q))
    base₁ .fun-fun p q = hh (at (app₁ p)) (at (app₁ q))
    base₁ .env-arg q =
      ≈-trans (hh env (at (app₂ q))) (absorb (graph D₂ env (at q)) (graph D₁ env (at ε)))
    base₁ .arg-arg p q =
      ≈-trans (hh (at (app₂ p)) (at (app₂ q)))
              (absorb (graph D₂ (at p) (at q))
                      (graph (⇓-app D₁ D₂ D₃) (at (app₂ p)) (at (app₁ ε))))
    base₁ .fun-arg p q =
      ≈-trans (hh (at (app₁ p)) (at (app₂ q))) (absorb M.εₘ (graph D₁ (at p) (at ε)))
    base₁ .arg-fun p q =
      ≈-trans (hh (at (app₂ p)) (at (app₁ q))) (absorb-r M.εₘ (graph D₁ (at ε) (at q)))
    base₁ .env-body q =
      ≈-trans (hh env (at (app₃ q))) (into-hidden D₁ (B q M.∘ iₗ) env)
    base₁ .fun-body p np q =
      ≈-trans (hh (at (app₁ p)) (at (app₃ q)))
      (≈-trans (+ₘ-cong (edge-off (B q M.∘ iₗ) p np) ≈-refl)
               (into-hidden D₁ (B q M.∘ iₗ) (at p)))
    base₁ .arg-body p q =
      ≈-trans (hh (at (app₂ p)) (at (app₃ q)))
              (absorb-r (edge (B q M.∘ iᵣ) p) (B q M.∘ iₗ))
    base₁ .body-body p q =
      ≈-trans (hh (at (app₃ p)) (at (app₃ q)))
              (absorb-r (graph D₃ (at p) (at q)) (B q M.∘ iₗ))
    base₁ .body-fun p q =
      ≈-trans (hh (at (app₃ p)) (at (app₁ q))) (absorb-r M.εₘ (graph D₁ (at ε) (at q)))
    base₁ .body-arg p q =
      ≈-trans (hh (at (app₃ p)) (at (app₂ q)))
              (absorb M.εₘ (graph (⇓-app D₁ D₂ D₃) (at (app₃ p)) (at (app₁ ε))))
    base₁ .env-root = ≈-trans (hh env (at ε)) (absorb M.εₘ (graph D₁ env (at ε)))
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
    rA = foldf (interior D₁) (interior-not-root D₁) base₁

  record Phase₂ (G : Graph (⇓-app D₁ D₂ D₃)) (H : Graph D₂) : Set ℓ where
    field
      env-arg   : ∀ q → G env (at (app₂ q)) M.≈ₘ H env (at q)
      arg-arg   : ∀ p q → G (at (app₂ p)) (at (app₂ q)) M.≈ₘ H (at p) (at q)
      env-body  : ∀ q → G env (at (app₃ q))
                  M.≈ₘ (((B q M.∘ iₗ) M.∘ collapse D₁) M.+ₘ ((B q M.∘ iᵣ) M.∘ H env (at ε)))
      arg-body  : ∀ p → is-ε p ≡ Bool.false → ∀ q →
                  G (at (app₂ p)) (at (app₃ q)) M.≈ₘ ((B q M.∘ iᵣ) M.∘ H (at p) (at ε))
      body-body : ∀ p q → G (at (app₃ p)) (at (app₃ q)) M.≈ₘ graph D₃ (at p) (at q)
      body-arg  : ∀ p q → G (at (app₃ p)) (at (app₂ q)) M.≈ₘ M.εₘ
      env-root  : G env (at ε) M.≈ₘ M.εₘ
      arg-root  : ∀ p → G (at (app₂ p)) (at ε) M.≈ₘ M.εₘ
      body-root : ∀ p → G (at (app₃ p)) (at ε) M.≈ₘ edge M.I p

  open Phase₂

  step₂ : ∀ {G H} (w : Path D₂) → is-ε w ≡ Bool.false →
          Phase₂ G H → Phase₂ (hide G (at (app₂ w))) (hide H (at w))
  step₂ w nw r .env-arg q  = +ₘ-cong (r .env-arg q) (∘-cong (r .arg-arg w q) (r .env-arg w))
  step₂ w nw r .arg-arg p q = +ₘ-cong (r .arg-arg p q) (∘-cong (r .arg-arg w q) (r .arg-arg p w))
  step₂ w nw r .env-body q =
    offset-step {K = (B q M.∘ iₗ) M.∘ collapse D₁} {P = B q M.∘ iᵣ}
                (r .env-body q) (r .arg-body w nw q) (r .env-arg w)
  step₂ w nw r .arg-body p np q =
    root-step {P = B q M.∘ iᵣ} (r .arg-body p np q) (r .arg-body w nw q) (r .arg-arg p w)
  step₂ {G} w nw r .body-body p q =
    ≈-trans (+ₘ-cong (r .body-body p q) (∘-cong₂ (r .body-arg p w)))
            (absorb-r (graph D₃ (at p) (at q)) (G (at (app₂ w)) (at (app₃ q))))
  step₂ {G} w nw r .body-arg p q =
    ≈-trans (+ₘ-cong (r .body-arg p q) (∘-cong₂ (r .body-arg p w)))
            (absorb-r M.εₘ (G (at (app₂ w)) (at (app₂ q))))
  step₂ {G} w nw r .env-root =
    ≈-trans (+ₘ-cong (r .env-root) (∘-cong₁ (r .arg-root w))) (absorb M.εₘ (G env (at (app₂ w))))
  step₂ {G} w nw r .arg-root p =
    ≈-trans (+ₘ-cong (r .arg-root p) (∘-cong₁ (r .arg-root w)))
            (absorb M.εₘ (G (at (app₂ p)) (at (app₂ w))))
  step₂ {G} w nw r .body-root p =
    ≈-trans (+ₘ-cong (r .body-root p) (∘-cong₁ (r .arg-root w)))
            (absorb (edge M.I p) (G (at (app₃ p)) (at (app₂ w))))

  fold₂' : ∀ {G H} (ws : List (Path D₂)) → All (λ w → is-ε w ≡ Bool.false) ws →
           Phase₂ G H → Phase₂ (hide-all G (map at (map app₂ ws))) (hide-all H (map at ws))
  fold₂' []       []         r = r
  fold₂' (w ∷ ws) (nw ∷ nws) r = fold₂' ws nws (step₂ w nw r)

  private
    base₂ : Phase₂ (hide PA (at (app₂ ε))) (hide (graph D₂) (at ε))
    base₂ .env-arg q = +ₘ-cong (rA .env-arg q) (∘-cong (rA .arg-arg ε q) (rA .env-arg ε))
    base₂ .arg-arg p q = +ₘ-cong (rA .arg-arg p q) (∘-cong (rA .arg-arg ε q) (rA .arg-arg p ε))
    base₂ .env-body q =
      ≈-trans (+ₘ-cong (rA .env-body q) (∘-cong (rA .arg-body ε q) (rA .env-arg ε)))
              (+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (hide-root D₂ env (at ε)))))
    base₂ .arg-body p np q =
      ≈-trans (+ₘ-cong (≈-trans (rA .arg-body p q) (edge-off (B q M.∘ iᵣ) p np))
                       (∘-cong (rA .arg-body ε q) (rA .arg-arg p ε)))
              (into-hidden D₂ (B q M.∘ iᵣ) (at p))
    base₂ .body-body p q =
      ≈-trans (+ₘ-cong (rA .body-body p q) (∘-cong (rA .arg-body ε q) (rA .body-arg p ε)))
              (absorb-r (graph D₃ (at p) (at q)) (B q M.∘ iᵣ))
    base₂ .body-arg p q =
      ≈-trans (+ₘ-cong (rA .body-arg p q) (∘-cong (rA .arg-arg ε q) (rA .body-arg p ε)))
              (absorb-r M.εₘ (graph D₂ (at ε) (at q)))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (rA .env-root) (∘-cong₁ (rA .arg-root ε)))
              (absorb M.εₘ (PA env (at (app₂ ε))))
    base₂ .arg-root p =
      ≈-trans (+ₘ-cong (rA .arg-root p) (∘-cong₁ (rA .arg-root ε)))
              (absorb M.εₘ (PA (at (app₂ p)) (at (app₂ ε))))
    base₂ .body-root p =
      ≈-trans (+ₘ-cong (rA .body-root p) (∘-cong₁ (rA .arg-root ε)))
              (absorb (edge M.I p) (PA (at (app₃ p)) (at (app₂ ε))))

    PB : Graph (⇓-app D₁ D₂ D₃)
    PB = hide-all (hide PA (at (app₂ ε))) (map at (map app₂ (interior D₂)))

    rB : Phase₂ PB (hide-all (hide (graph D₂) (at ε)) (map at (interior D₂)))
    rB = fold₂' (interior D₂) (interior-not-root D₂) base₂

  record Phase₃ (G : Graph (⇓-app D₁ D₂ D₃)) (H : Graph D₃) : Set ℓ where
    field
      env-body  : ∀ q → G env (at (app₃ q)) M.≈ₘ (H env (at q) M.∘ W)
      body-body : ∀ p q → G (at (app₃ p)) (at (app₃ q)) M.≈ₘ H (at p) (at q)
      env-root  : G env (at ε) M.≈ₘ (H env (at ε) M.∘ W)
      body-root : ∀ p → is-ε p ≡ Bool.false → G (at (app₃ p)) (at ε) M.≈ₘ H (at p) (at ε)

  open Phase₃

  step₃ : ∀ {G H} (w : Path D₃) → is-ε w ≡ Bool.false →
          Phase₃ G H → Phase₃ (hide G (at (app₃ w))) (hide H (at w))
  step₃ w nw r .env-body q =
    step-under {W = W} (r .env-body q) (r .body-body w q) (r .env-body w)
  step₃ w nw r .body-body p q = +ₘ-cong (r .body-body p q) (∘-cong (r .body-body w q) (r .body-body p w))
  step₃ w nw r .env-root = step-under {W = W} (r .env-root) (r .body-root w nw) (r .env-body w)
  step₃ w nw r .body-root p np = +ₘ-cong (r .body-root p np) (∘-cong (r .body-root w nw) (r .body-body p w))

  fold₃ : ∀ {G H} (ws : List (Path D₃)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₃ G H → Phase₃ (hide-all G (map at (map app₃ ws))) (hide-all H (map at ws))
  fold₃ []       []         r = r
  fold₃ (w ∷ ws) (nw ∷ nws) r = fold₃ ws nws (step₃ w nw r)

  private
    base₃ : Phase₃ (hide PB (at (app₃ ε))) (hide (graph D₃) (at ε))
    base₃ .env-body q =
      ≈-trans (+ₘ-cong (≈-trans (rB .env-body q) (factor₂ (B q) (collapse D₁) (collapse D₂)))
                       (∘-cong₁ (≈-trans (rB .body-body ε q) (root-sink D₃ (at q)))))
      (≈-trans (absorb (B q M.∘ W) (PB env (at (app₃ ε))))
               (≈-sym (∘-cong₁ (hide-root D₃ env (at q)))))
    base₃ .body-body p q =
      +ₘ-cong (rB .body-body p q) (∘-cong (rB .body-body ε q) (rB .body-body p ε))
    base₃ .env-root =
      ≈-trans (+ₘ-cong (rB .env-root)
                       (∘-cong (rB .body-root ε)
                               (≈-trans (rB .env-body ε) (factor₂ (B ε) (collapse D₁) (collapse D₂)))))
      (≈-trans (+ₘ-lunit (M.I M.∘ (B ε M.∘ W)))
      (≈-trans id-left (≈-sym (∘-cong₁ (hide-root D₃ env (at ε))))))
    base₃ .body-root p np =
      ≈-trans (+ₘ-cong (≈-trans (rB .body-root p) (edge-off M.I p np))
                       (∘-cong (rB .body-root ε) (rB .body-body p ε)))
      (≈-trans (into-hidden D₃ M.I (at p)) id-left)

  -- Collapsing an application composes the body's collapse with the assembled substitution.
  agree-app : collapse (⇓-app D₁ D₂ D₃) M.≈ₘ (collapse D₃ M.∘ W)
  agree-app =
    ≈-trans (≈-of-≡ plumb) (fold₃ (interior D₃) (interior-not-root D₃) base₃ .env-root)
    where
      A₁ = hide (graph (⇓-app D₁ D₂ D₃)) (at ε)
      L₁ = map app₁ (paths D₁)
      L₂ = map app₂ (paths D₂)
      L₃ = map app₃ (paths D₃)
      plumb : hide-all A₁ (map at (L₁ ++ L₂ ++ L₃)) env (at ε)
              ≡ hide-all (hide-all (hide-all A₁ (map at L₁)) (map at L₂)) (map at L₃) env (at ε)
      plumb =
        ≡-trans (≡-cong (λ L → hide-all A₁ L env (at ε))
                        (≡-trans (map-++ at L₁ (L₂ ++ L₃))
                                 (≡-cong (λ z → map at L₁ ++ z) (map-++ at L₂ L₃))))
        (≡-trans (≡-cong (λ Gg → Gg env (at ε))
                         (hide-all-++ A₁ (map at L₁) (map at L₂ ++ map at L₃)))
                 (≡-cong (λ Gg → Gg env (at ε))
                         (hide-all-++ (hide-all A₁ (map at L₁)) (map at L₂) (map at L₃))))

-- Operand lists: the S-family analogues of the root and edge lemmas.
root-sink-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
              (D₁ : γ , Ms ⇓s vs [ R ]) (y : VertexS D₁) → graphS D₁ (at ε) y M.≈ₘ M.εₘ
root-sink-s []       env    i j = refl {x = two.O}
root-sink-s []       (at ε) i j = refl {x = two.O}
root-sink-s (D ∷ D₁) env    i j = refl {x = two.O}
root-sink-s (D ∷ D₁) (at ε) i j = refl {x = two.O}
root-sink-s (D ∷ D₁) (at (hd q)) i j = refl {x = two.O}
root-sink-s (D ∷ D₁) (at (tl q)) i j = refl {x = two.O}

hide-root-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
              (D₁ : γ , Ms ⇓s vs [ R ]) (x y : VertexS D₁) →
              hide-s (graphS D₁) (at ε) x y M.≈ₘ graphS D₁ x y
hide-root-s D₁ x y =
  ≈-trans (+ₘ-cong ≈-refl (∘-cong₁ (root-sink-s D₁ y)))
          (absorb (graphS D₁ x y) (graphS D₁ x (at ε)))

hide-hide-root-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
                   (D₁ : γ , Ms ⇓s vs [ R ]) (r x y : VertexS D₁) →
                   hide-s (hide-s (graphS D₁) (at ε)) r x y
                   M.≈ₘ (graphS D₁ x y M.+ₘ (graphS D₁ r y M.∘ graphS D₁ x r))
hide-hide-root-s D₁ r x y =
  +ₘ-cong (hide-root-s D₁ x y) (∘-cong (hide-root-s D₁ r y) (hide-root-s D₁ x r))

edge-off-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
             {D₁ : γ , Ms ⇓s vs [ R ]} {m}
             (S : M.Matrix m (bases-width is)) (p : PathS D₁) → is-ε-s p ≡ Bool.false →
             edge-s S p M.≈ₘ M.εₘ
edge-off-s S ε ()
edge-off-s S (hd p) np i j = refl {x = two.O}
edge-off-s S (tl p) np i j = refl {x = two.O}

into-hidden-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
                (D₁ : γ , Ms ⇓s vs [ R ]) {m}
                (P : M.Matrix m (bases-width is)) (x : VertexS D₁) →
                (M.εₘ M.+ₘ (P M.∘ graphS D₁ x (at ε)))
                M.≈ₘ (P M.∘ hide-s (graphS D₁) (at ε) x (at ε))
into-hidden-s D₁ P x =
  ≈-trans (+ₘ-lunit (P M.∘ graphS D₁ x (at ε))) (∘-cong₂ (≈-sym (hide-root-s D₁ x (at ε))))

interior-not-root-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
                      (D₁ : γ , Ms ⇓s vs [ R ]) →
                      All (λ p → is-ε-s p ≡ Bool.false) (interior-s D₁)
interior-not-root-s []       = []
interior-not-root-s (D ∷ D₁) =
  ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths D))) (map⁺ (universal (λ _ → ≡-refl) (paths-s D₁)))

-- An operand cons: head premise then tail premise, as for pair but with the tail in the S family.
module SCons {Γ i is} {γ : Env Γ} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is}
             {v : sort-val i} {vs : sort-vals is}
             {R : width-env γ ⇒ width (const {s = i} v)} {Rs : width-env γ ⇒ bases-width is}
             {D₁ : γ , M ⇓ const v [ R ]} {D₂ : γ , Ms ⇓s vs [ Rs ]} where

  record Phase₁ (G : GraphS (D₁ ∷ D₂)) (H : Graph D₁) : Set ℓ where
    field
      env-left    : ∀ q → G env (at (hd q)) M.≈ₘ H env (at q)
      left-left   : ∀ p q → G (at (hd p)) (at (hd q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (M.in₁ M.∘ H env (at ε))
      left-root   : ∀ p → is-ε p ≡ Bool.false →
                    G (at (hd p)) (at ε) M.≈ₘ (M.in₁ M.∘ H (at p) (at ε))
      env-right   : ∀ q → G env (at (tl q)) M.≈ₘ graphS D₂ env (at q)
      right-right : ∀ p q → G (at (tl p)) (at (tl q)) M.≈ₘ graphS D₂ (at p) (at q)
      right-root  : ∀ p → G (at (tl p)) (at ε) M.≈ₘ edge-s M.in₂ p
      left-right  : ∀ p q → G (at (hd p)) (at (tl q)) M.≈ₘ M.εₘ
      right-left  : ∀ p q → G (at (tl p)) (at (hd q)) M.≈ₘ M.εₘ

  open Phase₁

  stepₗ : ∀ {G H} (w : Path D₁) → is-ε w ≡ Bool.false →
          Phase₁ G H → Phase₁ (hide-s G (at (hd w))) (hide H (at w))
  stepₗ w nw r .env-left q  = +ₘ-cong (r .env-left q) (∘-cong (r .left-left w q) (r .env-left w))
  stepₗ w nw r .left-left p q = +ₘ-cong (r .left-left p q) (∘-cong (r .left-left w q) (r .left-left p w))
  stepₗ w nw r .env-root = root-step {P = M.in₁ {sort-width i} {bases-width is}} (r .env-root) (r .left-root w nw) (r .env-left w)
  stepₗ w nw r .left-root p np = root-step {P = M.in₁ {sort-width i} {bases-width is}} (r .left-root p np) (r .left-root w nw) (r .left-left p w)
  stepₗ {G} w nw r .env-right q =
    ≈-trans (+ₘ-cong (r .env-right q) (∘-cong₁ (r .left-right w q)))
            (absorb (graphS D₂ env (at q)) (G env (at (hd w))))
  stepₗ {G} w nw r .right-right p q =
    ≈-trans (+ₘ-cong (r .right-right p q) (∘-cong₁ (r .left-right w q)))
            (absorb (graphS D₂ (at p) (at q)) (G (at (tl p)) (at (hd w))))
  stepₗ {G} w nw r .right-root p =
    ≈-trans (+ₘ-cong (r .right-root p) (∘-cong₂ (r .right-left p w)))
            (absorb-r (edge-s M.in₂ p) (G (at (hd w)) (at ε)))
  stepₗ {G} w nw r .left-right p q =
    ≈-trans (+ₘ-cong (r .left-right p q) (∘-cong₁ (r .left-right w q)))
            (absorb M.εₘ (G (at (hd p)) (at (hd w))))
  stepₗ {G} w nw r .right-left p q =
    ≈-trans (+ₘ-cong (r .right-left p q) (∘-cong₂ (r .right-left p w)))
            (absorb-r M.εₘ (G (at (hd w)) (at (hd q))))

  foldₗ' : ∀ {G H} (ws : List (Path D₁)) → All (λ w → is-ε w ≡ Bool.false) ws →
           Phase₁ G H → Phase₁ (hide-all-s G (map at (map hd ws))) (hide-all H (map at ws))
  foldₗ' []       []         r = r
  foldₗ' (w ∷ ws) (nw ∷ nws) r = foldₗ' ws nws (stepₗ w nw r)

  private
    hh : ∀ x y → hide-s (hide-s (graphS (D₁ ∷ D₂)) (at ε)) (at (hd ε)) x y
         M.≈ₘ (graphS (D₁ ∷ D₂) x y
               M.+ₘ (graphS (D₁ ∷ D₂) (at (hd ε)) y M.∘ graphS (D₁ ∷ D₂) x (at (hd ε))))
    hh = hide-hide-root-s (D₁ ∷ D₂) (at (hd ε))

    base₁ : Phase₁ (hide-s (hide-s (graphS (D₁ ∷ D₂)) (at ε)) (at (hd ε))) (hide (graph D₁) (at ε))
    base₁ .env-left q  = hh env (at (hd q))
    base₁ .left-left p q = hh (at (hd p)) (at (hd q))
    base₁ .env-root = ≈-trans (hh env (at ε)) (into-hidden D₁ M.in₁ env)
    base₁ .left-root p np =
      ≈-trans (hh (at (hd p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off M.in₁ p np) ≈-refl) (into-hidden D₁ M.in₁ (at p)))
    base₁ .env-right q =
      ≈-trans (hh env (at (tl q))) (absorb (graphS D₂ env (at q)) (graph D₁ env (at ε)))
    base₁ .right-right p q =
      ≈-trans (hh (at (tl p)) (at (tl q)))
              (absorb (graphS D₂ (at p) (at q)) (graphS (D₁ ∷ D₂) (at (tl p)) (at (hd ε))))
    base₁ .right-root p =
      ≈-trans (hh (at (tl p)) (at ε))
              (absorb-r (edge-s M.in₂ p) (graphS (D₁ ∷ D₂) (at (hd ε)) (at ε)))
    base₁ .left-right p q =
      ≈-trans (hh (at (hd p)) (at (tl q))) (absorb M.εₘ (graph D₁ (at p) (at ε)))
    base₁ .right-left p q =
      ≈-trans (hh (at (tl p)) (at (hd q))) (absorb-r M.εₘ (graph D₁ (at ε) (at q)))

  record Phase₂ (G : GraphS (D₁ ∷ D₂)) (H : GraphS D₂)
                (K : M.Matrix (bases-width (i ∷ is)) (width-env γ)) : Set ℓ where
    field
      env-right   : ∀ q → G env (at (tl q)) M.≈ₘ H env (at q)
      right-right : ∀ p q → G (at (tl p)) (at (tl q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (K M.+ₘ (M.in₂ M.∘ H env (at ε)))
      right-root  : ∀ p → is-ε-s p ≡ Bool.false →
                    G (at (tl p)) (at ε) M.≈ₘ (M.in₂ M.∘ H (at p) (at ε))

  open Phase₂

  stepᵣ : ∀ {G H K} (w : PathS D₂) → is-ε-s w ≡ Bool.false →
          Phase₂ G H K → Phase₂ (hide-s G (at (tl w))) (hide-s H (at w)) K
  stepᵣ w nw r .env-right q  = +ₘ-cong (r .env-right q) (∘-cong (r .right-right w q) (r .env-right w))
  stepᵣ w nw r .right-right p q = +ₘ-cong (r .right-right p q) (∘-cong (r .right-right w q) (r .right-right p w))
  stepᵣ w nw r .env-root =
    offset-step {P = M.in₂ {sort-width i} {bases-width is}} (r .env-root) (r .right-root w nw) (r .env-right w)
  stepᵣ w nw r .right-root p np =
    root-step {P = M.in₂ {sort-width i} {bases-width is}} (r .right-root p np) (r .right-root w nw) (r .right-right p w)

  foldᵣ' : ∀ {G H K} (ws : List (PathS D₂)) → All (λ w → is-ε-s w ≡ Bool.false) ws →
           Phase₂ G H K → Phase₂ (hide-all-s G (map at (map tl ws))) (hide-all-s H (map at ws)) K
  foldᵣ' []       []         r = r
  foldᵣ' (w ∷ ws) (nw ∷ nws) r = foldᵣ' ws nws (stepᵣ w nw r)

  private
    r1 : Phase₁ (hide-all-s (hide-s (hide-s (graphS (D₁ ∷ D₂)) (at ε)) (at (hd ε)))
                            (map at (map hd (interior D₁))))
                (hide-all (hide (graph D₁) (at ε)) (map at (interior D₁)))
    r1 = foldₗ' (interior D₁) (interior-not-root D₁) base₁

    base₂ : Phase₂ (hide-s (hide-all-s (hide-s (hide-s (graphS (D₁ ∷ D₂)) (at ε)) (at (hd ε)))
                                       (map at (map hd (interior D₁))))
                           (at (tl ε)))
                   (hide-s (graphS D₂) (at ε))
                   (M.in₁ M.∘ collapse D₁)
    base₂ .env-right q = +ₘ-cong (r1 .env-right q) (∘-cong (r1 .right-right ε q) (r1 .env-right ε))
    base₂ .right-right p q = +ₘ-cong (r1 .right-right p q) (∘-cong (r1 .right-right ε q) (r1 .right-right p ε))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (r1 .env-root) (∘-cong (r1 .right-root ε) (r1 .env-right ε)))
              (+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (hide-root-s D₂ env (at ε)))))
    base₂ .right-root p np =
      ≈-trans (+ₘ-cong (≈-trans (r1 .right-root p) (edge-off-s M.in₂ p np))
                       (∘-cong (r1 .right-root ε) (r1 .right-right p ε)))
              (into-hidden-s D₂ M.in₂ (at p))

  -- Collapsing an operand cons pairs the head and tail collapses.
  agree-s-cons : collapse-s (D₁ ∷ D₂)
                 M.≈ₘ ((M.in₁ M.∘ collapse D₁) M.+ₘ (M.in₂ M.∘ collapse-s D₂))
  agree-s-cons =
    ≈-trans (≈-of-≡ plumb) (foldᵣ' (interior-s D₂) (interior-not-root-s D₂) base₂ .env-root)
    where
      plumb : hide-all-s (hide-s (graphS (D₁ ∷ D₂)) (at ε))
                         (map at (map hd (paths D₁) ++ map tl (paths-s D₂))) env (at ε)
              ≡ hide-all-s (hide-all-s (hide-s (graphS (D₁ ∷ D₂)) (at ε))
                                       (map at (map hd (paths D₁))))
                           (map at (map tl (paths-s D₂))) env (at ε)
      plumb =
        ≡-trans (≡-cong (λ L → hide-all-s (hide-s (graphS (D₁ ∷ D₂)) (at ε)) L env (at ε))
                        (map-++ at (map hd (paths D₁)) (map tl (paths-s D₂))))
                (≡-cong (λ Gg → Gg env (at ε))
                        (hide-all-s-++ (hide-s (graphS (D₁ ∷ D₂)) (at ε))
                                       (map at (map hd (paths D₁)))
                                       (map at (map tl (paths-s D₂)))))

-- A primitive operation: one operand-list premise, with the operator's derivative as root edge.
module Bop {Γ is o'} {γ : Env Γ} {ω : op is o'} {Ms : Every (λ s → Γ ⊢ base s) is}
           {vs : sort-vals is} {Rs : width-env γ ⇒ bases-width is}
           {D : γ , Ms ⇓s vs [ Rs ]} where

  record Embeds (G : Graph (⇓-bop {ω = ω} D)) (H : GraphS D)
                (P : M.Matrix (sort-width o') (bases-width is)) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (bop q)) M.≈ₘ H env (at q)
      embed-embed : ∀ p q → G (at (bop p)) (at (bop q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      embed-root  : ∀ p → is-ε-s p ≡ Bool.false →
                    G (at (bop p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : PathS D) → is-ε-s w ≡ Bool.false →
                Embeds G H P → Embeds (hide G (at (bop w))) (hide-s H (at w)) P
  embeds-hide w nw s .env-embed q   = +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .embed-embed p q = +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {P = P} w nw s .env-root = root-step {P = P} (s .env-root) (s .embed-root w nw) (s .env-embed w)
  embeds-hide {P = P} w nw s .embed-root p np =
    root-step {P = P} (s .embed-root p np) (s .embed-root w nw) (s .embed-embed p w)

  embeds-hide-all : ∀ {G H P} (ws : List (PathS D)) → All (λ w → is-ε-s w ≡ Bool.false) ws →
                    Embeds G H P →
                    Embeds (hide-all G (map at (map bop ws))) (hide-all-s H (map at ws)) P
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    embeds₀ : Embeds (hide (hide (graph (⇓-bop {ω = ω} D)) (at ε)) (at (bop ε)))
                     (hide-s (graphS D) (at ε)) (op-deps ω .func vs)
    embeds₀ .env-embed q   = hide-hide-root (⇓-bop {ω = ω} D) (at (bop ε)) env (at (bop q))
    embeds₀ .embed-embed p q = hide-hide-root (⇓-bop {ω = ω} D) (at (bop ε)) (at (bop p)) (at (bop q))
    embeds₀ .env-root =
      ≈-trans (hide-hide-root (⇓-bop {ω = ω} D) (at (bop ε)) env (at ε))
              (into-hidden-s D (op-deps ω .func vs) env)
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root (⇓-bop {ω = ω} D) (at (bop ε)) (at (bop p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off-s (op-deps ω .func vs) p np) ≈-refl)
               (into-hidden-s D (op-deps ω .func vs) (at p)))

  -- Collapsing an operation composes the derivative with the operands' collapse.
  agree-bop : collapse (⇓-bop {ω = ω} D) M.≈ₘ ((op-deps ω .func vs) M.∘ collapse-s D)
  agree-bop = embeds-hide-all (interior-s D) (interior-not-root-s D) embeds₀ .env-root

-- A primitive relation: the result has no positions, so any two matrices agree.
rows-zero : ∀ {n g} → n ≡ 0 → (X Y : M.Matrix n g) → X M.≈ₘ Y
rows-zero ≡-refl X Y ()

sum-width : ∀ (b : ⊤' {Level.0ℓ} ⊎' ⊤' {Level.0ℓ}) → width (bool→val b) ≡ 0
sum-width (inj₁ _) = ≡-refl
sum-width (inj₂ _) = ≡-refl

agree-brel : ∀ {Γ is} {γ : Env Γ} {ω : rel is} {Ms : Every (λ s → Γ ⊢ base s) is}
             {vs : sort-vals is} {Rs : width-env γ ⇒ bases-width is}
             {D : γ , Ms ⇓s vs [ Rs ]} →
             collapse (⇓-brel {ω = ω} D) M.≈ₘ brel-mat γ (rel-pred ω .func vs)
agree-brel {γ = γ} {ω = ω} {vs = vs} {D = D} =
  rows-zero (sum-width (rel-pred ω .func vs)) (collapse (⇓-brel {ω = ω} D))
            (brel-mat γ (rel-pred ω .func vs))

-- One summand survives because a factor of the other is zero.
keep-l : ∀ {m n k} {G₁ C : M.Matrix m n} {G₂ : M.Matrix m k} {G₃ : M.Matrix k n} →
         G₁ M.≈ₘ C → G₂ M.≈ₘ M.εₘ → (G₁ M.+ₘ (G₂ M.∘ G₃)) M.≈ₘ C
keep-l {C = C} {G₃ = G₃} a b = ≈-trans (+ₘ-cong a (∘-cong₁ b)) (absorb C G₃)

keep-r : ∀ {m n k} {G₁ C : M.Matrix m n} {G₂ : M.Matrix m k} {G₃ : M.Matrix k n} →
         G₁ M.≈ₘ C → G₃ M.≈ₘ M.εₘ → (G₁ M.+ₘ (G₂ M.∘ G₃)) M.≈ₘ C
keep-r {C = C} {G₂ = G₂} a c = ≈-trans (+ₘ-cong a (∘-cong₂ c)) (absorb-r C G₂)

-- The fold-action family: mirrors of the root and edge lemmas.
root-sink-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
    {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
    {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
              (Dm : Map γ s σ' v R v' R') (y : VertexM Dm) → graphM Dm (at ε) y M.≈ₘ M.εₘ
root-sink-m (m-rec Dm De) env i j = refl {x = two.O}
root-sink-m (m-rec Dm De) input i j = refl {x = two.O}
root-sink-m (m-rec Dm De) (at ε) i j = refl {x = two.O}
root-sink-m (m-rec Dm De) (at (m-rec₁ q)) i j = refl {x = two.O}
root-sink-m (m-rec Dm De) (at (m-rec₂ q)) i j = refl {x = two.O}
root-sink-m m-unit env i j = refl {x = two.O}
root-sink-m m-unit input i j = refl {x = two.O}
root-sink-m m-unit (at ε) i j = refl {x = two.O}
root-sink-m m-base env i j = refl {x = two.O}
root-sink-m m-base input i j = refl {x = two.O}
root-sink-m m-base (at ε) i j = refl {x = two.O}
root-sink-m m-arrow env i j = refl {x = two.O}
root-sink-m m-arrow input i j = refl {x = two.O}
root-sink-m m-arrow (at ε) i j = refl {x = two.O}
root-sink-m (m-inl Dm) env i j = refl {x = two.O}
root-sink-m (m-inl Dm) input i j = refl {x = two.O}
root-sink-m (m-inl Dm) (at ε) i j = refl {x = two.O}
root-sink-m (m-inl Dm) (at (m-inl q)) i j = refl {x = two.O}
root-sink-m (m-inr Dm) env i j = refl {x = two.O}
root-sink-m (m-inr Dm) input i j = refl {x = two.O}
root-sink-m (m-inr Dm) (at ε) i j = refl {x = two.O}
root-sink-m (m-inr Dm) (at (m-inr q)) i j = refl {x = two.O}
root-sink-m (m-pair Dm Dm') env i j = refl {x = two.O}
root-sink-m (m-pair Dm Dm') input i j = refl {x = two.O}
root-sink-m (m-pair Dm Dm') (at ε) i j = refl {x = two.O}
root-sink-m (m-pair Dm Dm') (at (m-pair₁ q)) i j = refl {x = two.O}
root-sink-m (m-pair Dm Dm') (at (m-pair₂ q)) i j = refl {x = two.O}
root-sink-m (m-mu Dm) env i j = refl {x = two.O}
root-sink-m (m-mu Dm) input i j = refl {x = two.O}
root-sink-m (m-mu Dm) (at ε) i j = refl {x = two.O}
root-sink-m (m-mu Dm) (at (m-mu q)) i j = refl {x = two.O}

hide-root-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
    {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
    {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
              (Dm : Map γ s σ' v R v' R') (x y : VertexM Dm) →
              hide-m (graphM Dm) (at ε) x y M.≈ₘ graphM Dm x y
hide-root-m Dm x y =
  ≈-trans (+ₘ-cong ≈-refl (∘-cong₁ (root-sink-m Dm y)))
          (absorb (graphM Dm x y) (graphM Dm x (at ε)))

hide-hide-root-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
    {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
    {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
                   (Dm : Map γ s σ' v R v' R') (r x y : VertexM Dm) →
                   hide-m (hide-m (graphM Dm) (at ε)) r x y
                   M.≈ₘ (graphM Dm x y M.+ₘ (graphM Dm r y M.∘ graphM Dm x r))
hide-hide-root-m Dm r x y =
  +ₘ-cong (hide-root-m Dm x y) (∘-cong (hide-root-m Dm r y) (hide-root-m Dm x r))

edge-off-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
    {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
    {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'} {Dm : Map γ s σ' v R v' R'} {m}
             (S : M.Matrix m (width v')) (p : PathM Dm) → is-ε-m p ≡ Bool.false →
             edge-m S p M.≈ₘ M.εₘ
edge-off-m S ε ()
edge-off-m S (m-rec₁ p) np i j = refl {x = two.O}
edge-off-m S (m-rec₂ p) np i j = refl {x = two.O}
edge-off-m S (m-inl p) np i j = refl {x = two.O}
edge-off-m S (m-inr p) np i j = refl {x = two.O}
edge-off-m S (m-pair₁ p) np i j = refl {x = two.O}
edge-off-m S (m-pair₂ p) np i j = refl {x = two.O}
edge-off-m S (m-mu p) np i j = refl {x = two.O}

into-hidden-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
    {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
    {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
                (Dm : Map γ s σ' v R v' R') {m}
                (P : M.Matrix m (width v')) (x : VertexM Dm) →
                (M.εₘ M.+ₘ (P M.∘ graphM Dm x (at ε)))
                M.≈ₘ (P M.∘ hide-m (graphM Dm) (at ε) x (at ε))
into-hidden-m Dm P x =
  ≈-trans (+ₘ-lunit (P M.∘ graphM Dm x (at ε))) (∘-cong₂ (≈-sym (hide-root-m Dm x (at ε))))

interior-not-root-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
    {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
    {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
                      (Dm : Map γ s σ' v R v' R') →
                      All (λ p → is-ε-m p ≡ Bool.false) (interior-m Dm)
interior-not-root-m (m-rec Dm De)   = ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths-m Dm))) (map⁺ (universal (λ _ → ≡-refl) (paths De)))
interior-not-root-m m-unit          = []
interior-not-root-m m-base          = []
interior-not-root-m m-arrow         = []
interior-not-root-m (m-inl Dm)      = map⁺ (universal (λ _ → ≡-refl) (paths-m Dm))
interior-not-root-m (m-inr Dm)      = map⁺ (universal (λ _ → ≡-refl) (paths-m Dm))
interior-not-root-m (m-pair Dm Dm') = ++⁺ (map⁺ (universal (λ _ → ≡-refl) (paths-m Dm))) (map⁺ (universal (λ _ → ≡-refl) (paths-m Dm')))
interior-not-root-m (m-mu Dm)       = map⁺ (universal (λ _ → ≡-refl) (paths-m Dm))

-- Casts along width equalities, and their interaction with the matrix algebra. Each is proved by
-- matching the equality, so they apply at neutral width proofs.
ccast-∘ : ∀ {m k n n'} (e : n ≡ n') (X : M.Matrix m k) (Y : M.Matrix k n) →
          (X M.∘ ccast e Y) M.≈ₘ ccast e (X M.∘ Y)
ccast-∘ ≡-refl X Y = ≈-refl

+ₘ-ccast : ∀ {m n n'} (e : n ≡ n') (X Y : M.Matrix m n) →
           (ccast e X M.+ₘ ccast e Y) M.≈ₘ ccast e (X M.+ₘ Y)
+ₘ-ccast ≡-refl X Y = ≈-refl

rcast-∘ : ∀ {m m' k n} (e : m ≡ m') (X : M.Matrix m k) (Y : M.Matrix k n) →
          (rcast e X M.∘ Y) M.≈ₘ rcast e (X M.∘ Y)
rcast-∘ ≡-refl X Y = ≈-refl

ccast-rcast-∘ : ∀ {m n n' k} (e : n ≡ n') (X : M.Matrix m n) (Y : M.Matrix n k) →
                (ccast e X M.∘ rcast e Y) M.≈ₘ (X M.∘ Y)
ccast-rcast-∘ ≡-refl X Y = ≈-refl

rcast-cong : ∀ {m m' n} (e : m ≡ m') {X Y : M.Matrix m n} → X M.≈ₘ Y → rcast e X M.≈ₘ rcast e Y
rcast-cong ≡-refl h = h

+ₘ-rcast : ∀ {m m' n} (e : m ≡ m') (X Y : M.Matrix m n) →
           (rcast e X M.+ₘ rcast e Y) M.≈ₘ rcast e (X M.+ₘ Y)
+ₘ-rcast ≡-refl X Y = ≈-refl

ccast-step : ∀ {m k n n'} (e : n ≡ n') {G₁ : M.Matrix m n'} {X : M.Matrix m n}
             {G₂ Y : M.Matrix m k} {G₃ : M.Matrix k n'} {Z : M.Matrix k n} →
             G₁ M.≈ₘ ccast e X → G₂ M.≈ₘ Y → G₃ M.≈ₘ ccast e Z →
             (G₁ M.+ₘ (G₂ M.∘ G₃)) M.≈ₘ ccast e (X M.+ₘ (Y M.∘ Z))
ccast-step e {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (≈-trans (∘-cong b c) (ccast-∘ e Y Z))) (+ₘ-ccast e X (Y M.∘ Z))


ccast-cong : ∀ {m n n'} (e : n ≡ n') {X Y : M.Matrix m n} → X M.≈ₘ Y → ccast e X M.≈ₘ ccast e Y
ccast-cong ≡-refl h = h

root-step-cast : ∀ {m l g n n'} (e : n ≡ n') (P : M.Matrix m l)
                 {G₁ : M.Matrix m n'} {X : M.Matrix l n} {G₂ : M.Matrix m g} {Y : M.Matrix l g}
                 {G₃ : M.Matrix g n'} {Z : M.Matrix g n} →
                 G₁ M.≈ₘ (P M.∘ ccast e X) → G₂ M.≈ₘ (P M.∘ Y) → G₃ M.≈ₘ ccast e Z →
                 (G₁ M.+ₘ (G₂ M.∘ G₃)) M.≈ₘ (P M.∘ ccast e (X M.+ₘ (Y M.∘ Z)))
root-step-cast e P {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c))
  (≈-trans (+ₘ-cong ≈-refl (≈-trans (assoc P Y (ccast e Z)) (∘-cong₂ (ccast-∘ e Y Z))))
  (≈-trans (≈-sym (M.comp-bilinear₂ P (ccast e X) (ccast e (Y M.∘ Z))))
           (∘-cong₂ (+ₘ-ccast e X (Y M.∘ Z)))))


+ₘ-interchange : ∀ {m n} (A B C D : M.Matrix m n) →
                 ((A M.+ₘ B) M.+ₘ (C M.+ₘ D)) M.≈ₘ ((A M.+ₘ C) M.+ₘ (B M.+ₘ D))
+ₘ-interchange A B C D i j = +-interchange {w = A i j} {x = B i j} {y = C i j} {z = D i j}

hide-all-m-++ : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : width-env γ ⇒ width v}
                {v' : Val (σ' [ σr ])} {R' : width-env γ ⇒ width v'}
                {Dm : Map γ s σ' v R v' R'}
                (G : GraphM Dm) (xs ys : List (VertexM Dm)) →
                hide-all-m G (xs ++ ys) ≡ hide-all-m (hide-all-m G xs) ys
hide-all-m-++ G []       ys = ≡-refl
hide-all-m-++ G (x ∷ xs) ys = hide-all-m-++ (hide-m G x) xs ys

-- One hide step where the root columns carry both a pre-composition P and a post-composition W.
root-under : ∀ {m l g g' n} (P : M.Matrix m l) {W : M.Matrix g g'}
             {G₁ : M.Matrix m g'} {X : M.Matrix l g} {G₂ : M.Matrix m n} {Y : M.Matrix l n}
             {G₃ : M.Matrix n g'} {Z : M.Matrix n g} →
             G₁ M.≈ₘ ((P M.∘ X) M.∘ W) → G₂ M.≈ₘ (P M.∘ Y) → G₃ M.≈ₘ (Z M.∘ W) →
             (G₁ M.+ₘ (G₂ M.∘ G₃)) M.≈ₘ ((P M.∘ (X M.+ₘ (Y M.∘ Z))) M.∘ W)
root-under P {W} {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c))
  (≈-trans (+ₘ-cong (≈-refl {f = (P M.∘ X) M.∘ W}) (≈-sym (assoc (P M.∘ Y) Z W)))
  (≈-trans (≈-sym (M.comp-bilinear₁ (P M.∘ X) ((P M.∘ Y) M.∘ Z) W))
           (∘-cong₁ (distrib-root P X Y Z))))

offset-under : ∀ {m l g g' n} (P : M.Matrix m l) {W : M.Matrix g g'} {K : M.Matrix m g'}
               {G₁ : M.Matrix m g'} {X : M.Matrix l g} {G₂ : M.Matrix m n} {Y : M.Matrix l n}
               {G₃ : M.Matrix n g'} {Z : M.Matrix n g} →
               G₁ M.≈ₘ (K M.+ₘ ((P M.∘ X) M.∘ W)) → G₂ M.≈ₘ (P M.∘ Y) → G₃ M.≈ₘ (Z M.∘ W) →
               (G₁ M.+ₘ (G₂ M.∘ G₃)) M.≈ₘ (K M.+ₘ ((P M.∘ (X M.+ₘ (Y M.∘ Z))) M.∘ W))
offset-under P {W} {K} {X = X} {Y = Y} {Z = Z} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c))
  (≈-trans (+ₘ-assoc K ((P M.∘ X) M.∘ W) ((P M.∘ Y) M.∘ (Z M.∘ W)))
           (+ₘ-cong (≈-refl {f = K})
                    (root-under P {W} {X = X} {Y = Y} {Z = Z}
                                (≈-refl {f = (P M.∘ X) M.∘ W}) (≈-refl {f = P M.∘ Y})
                                (≈-refl {f = Z M.∘ W}))))

-- One hide step on entries carrying an env part and an input part resolved through W.
pair-source-step : ∀ {m n g g'} {W : M.Matrix g g'}
                   {G₁ X : M.Matrix m g'} {X' : M.Matrix m g} {G₂ Y : M.Matrix m n}
                   {G₃ Z : M.Matrix n g'} {Z' : M.Matrix n g} →
                   G₁ M.≈ₘ (X M.+ₘ (X' M.∘ W)) → G₂ M.≈ₘ Y → G₃ M.≈ₘ (Z M.+ₘ (Z' M.∘ W)) →
                   (G₁ M.+ₘ (G₂ M.∘ G₃))
                   M.≈ₘ ((X M.+ₘ (Y M.∘ Z)) M.+ₘ ((X' M.+ₘ (Y M.∘ Z')) M.∘ W))
pair-source-step {W = W} {X = X} {X' = X'} {Y = Y} {Z = Z} {Z' = Z'} a b c =
  ≈-trans (+ₘ-cong a (∘-cong b c))
  (≈-trans (+ₘ-cong (≈-refl {f = X M.+ₘ (X' M.∘ W)}) (M.comp-bilinear₂ Y Z (Z' M.∘ W)))
  (≈-trans (+ₘ-interchange X (X' M.∘ W) (Y M.∘ Z) (Y M.∘ (Z' M.∘ W)))
  (≈-trans (+ₘ-cong (≈-refl {f = X M.+ₘ (Y M.∘ Z)})
                    (+ₘ-cong (≈-refl {f = X' M.∘ W}) (≈-sym (assoc Y Z' W))))
           (+ₘ-cong (≈-refl {f = X M.+ₘ (Y M.∘ Z)})
                    (≈-sym (M.comp-bilinear₁ X' (Y M.∘ Z') W))))))

-- Leaf fold actions: the output is the input, so the collapse pair is (zero, identity).
agree-m-unit : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
               {v : Val (unit [ μ τ₀ ])} {R : width-env γ ⇒ width v} →
               (collapse-m-env (m-unit {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R})
                M.+ₘ (collapse-m-in (m-unit {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R}) M.∘ R)) M.≈ₘ R
agree-m-unit {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R} =
  ≈-trans (+ₘ-cong (absorb M.εₘ (graphM (m-unit {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R}) env (at ε)))
                   (∘-cong₁ (absorb M.I (graphM (m-unit {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R}) input (at ε)))))
  (≈-trans (+ₘ-lunit (M.I M.∘ R)) id-left)

agree-m-base : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
               {b} {v : Val (base b [ μ τ₀ ])} {R : width-env γ ⇒ width v} →
               (collapse-m-env (m-base {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R})
                M.+ₘ (collapse-m-in (m-base {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R}) M.∘ R)) M.≈ₘ R
agree-m-base {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R} =
  ≈-trans (+ₘ-cong (absorb M.εₘ (graphM (m-base {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R}) env (at ε)))
                   (∘-cong₁ (absorb M.I (graphM (m-base {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R}) input (at ε)))))
  (≈-trans (+ₘ-lunit (M.I M.∘ R)) id-left)

agree-m-arrow : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                {σ₁ σ₂ : type 0} {v : Val ((σ₁ [→] σ₂) [ μ τ₀ ])} {R : width-env γ ⇒ width v} →
                (collapse-m-env (m-arrow {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R})
                 M.+ₘ (collapse-m-in (m-arrow {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R}) M.∘ R)) M.≈ₘ R
agree-m-arrow {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R} =
  ≈-trans (+ₘ-cong (absorb M.εₘ (graphM (m-arrow {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R}) env (at ε)))
                   (∘-cong₁ (absorb M.I (graphM (m-arrow {γ = γ} {τ₀ = τ₀} {s = s} {v = v} {R = R}) input (at ε)))))
  (≈-trans (+ₘ-lunit (M.I M.∘ R)) id-left)

-- The m-inl action: one premise, both source rows embedding unchanged.
module MInl {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ₁ σ₂ : type 1} {v : Val (σ₁ [ μ τ₀ ])} {R : width-env γ ⇒ width v}
            {v' : Val (σ₁ [ σr ])} {R' : width-env γ ⇒ width v'}
            {Dm : Map γ s σ₁ v R v' R'} where

  private
    C : Map γ s (σ₁ [+] σ₂) _ R _ R'
    C = m-inl {σ₁ = σ₁} {σ₂ = σ₂} Dm

  record Embeds (G : GraphM C) (H : GraphM Dm)
                (P : M.Matrix (width v') (width v')) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (m-inl q)) M.≈ₘ H env (at q)
      input-embed : ∀ q → G input (at (m-inl q)) M.≈ₘ H input (at q)
      embed-embed : ∀ p q → G (at (m-inl p)) (at (m-inl q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      input-root  : G input (at ε) M.≈ₘ (P M.∘ H input (at ε))
      embed-root  : ∀ p → is-ε-m p ≡ Bool.false →
                    G (at (m-inl p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : PathM Dm) → is-ε-m w ≡ Bool.false →
                Embeds G H P → Embeds (hide-m G (at (m-inl w))) (hide-m H (at w)) P
  embeds-hide w nw r .env-embed q   = +ₘ-cong (r .env-embed q) (∘-cong (r .embed-embed w q) (r .env-embed w))
  embeds-hide w nw r .input-embed q = +ₘ-cong (r .input-embed q) (∘-cong (r .embed-embed w q) (r .input-embed w))
  embeds-hide w nw r .embed-embed p q = +ₘ-cong (r .embed-embed p q) (∘-cong (r .embed-embed w q) (r .embed-embed p w))
  embeds-hide {P = P} w nw r .env-root = root-step {P = P} (r .env-root) (r .embed-root w nw) (r .env-embed w)
  embeds-hide {P = P} w nw r .input-root = root-step {P = P} (r .input-root) (r .embed-root w nw) (r .input-embed w)
  embeds-hide {P = P} w nw r .embed-root p np =
    root-step {P = P} (r .embed-root p np) (r .embed-root w nw) (r .embed-embed p w)

  embeds-hide-all : ∀ {G H P} (ws : List (PathM Dm)) → All (λ w → is-ε-m w ≡ Bool.false) ws →
                    Embeds G H P →
                    Embeds (hide-all-m G (map at (map m-inl ws))) (hide-all-m H (map at ws)) P
  embeds-hide-all []       []         r = r
  embeds-hide-all (w ∷ ws) (nw ∷ nws) r = embeds-hide-all ws nws (embeds-hide w nw r)

  private
    embeds₀ : Embeds (hide-m (hide-m (graphM C) (at ε)) (at (m-inl ε)))
                     (hide-m (graphM Dm) (at ε)) M.I
    embeds₀ .env-embed q   = hide-hide-root-m C (at (m-inl ε)) env (at (m-inl q))
    embeds₀ .input-embed q = hide-hide-root-m C (at (m-inl ε)) input (at (m-inl q))
    embeds₀ .embed-embed p q = hide-hide-root-m C (at (m-inl ε)) (at (m-inl p)) (at (m-inl q))
    embeds₀ .env-root   = ≈-trans (hide-hide-root-m C (at (m-inl ε)) env (at ε)) (into-hidden-m Dm M.I env)
    embeds₀ .input-root = ≈-trans (hide-hide-root-m C (at (m-inl ε)) input (at ε)) (into-hidden-m Dm M.I input)
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root-m C (at (m-inl ε)) (at (m-inl p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off-m M.I p np) ≈-refl) (into-hidden-m Dm M.I (at p)))

    rfin = embeds-hide-all (interior-m Dm) (interior-not-root-m Dm) embeds₀

  agree-MInl-env : collapse-m-env C M.≈ₘ collapse-m-env Dm
  agree-MInl-env = ≈-trans (rfin .env-root) id-left

  agree-MInl-in : collapse-m-in C M.≈ₘ collapse-m-in Dm
  agree-MInl-in = ≈-trans (rfin .input-root) id-left

-- The m-inr action: one premise, both source rows embedding unchanged.
module MInr {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ₁ σ₂ : type 1} {v : Val (σ₂ [ μ τ₀ ])} {R : width-env γ ⇒ width v}
            {v' : Val (σ₂ [ σr ])} {R' : width-env γ ⇒ width v'}
            {Dm : Map γ s σ₂ v R v' R'} where

  private
    C : Map γ s (σ₁ [+] σ₂) _ R _ R'
    C = m-inr {σ₁ = σ₁} {σ₂ = σ₂} Dm

  record Embeds (G : GraphM C) (H : GraphM Dm)
                (P : M.Matrix (width v') (width v')) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (m-inr q)) M.≈ₘ H env (at q)
      input-embed : ∀ q → G input (at (m-inr q)) M.≈ₘ H input (at q)
      embed-embed : ∀ p q → G (at (m-inr p)) (at (m-inr q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      input-root  : G input (at ε) M.≈ₘ (P M.∘ H input (at ε))
      embed-root  : ∀ p → is-ε-m p ≡ Bool.false →
                    G (at (m-inr p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : PathM Dm) → is-ε-m w ≡ Bool.false →
                Embeds G H P → Embeds (hide-m G (at (m-inr w))) (hide-m H (at w)) P
  embeds-hide w nw r .env-embed q   = +ₘ-cong (r .env-embed q) (∘-cong (r .embed-embed w q) (r .env-embed w))
  embeds-hide w nw r .input-embed q = +ₘ-cong (r .input-embed q) (∘-cong (r .embed-embed w q) (r .input-embed w))
  embeds-hide w nw r .embed-embed p q = +ₘ-cong (r .embed-embed p q) (∘-cong (r .embed-embed w q) (r .embed-embed p w))
  embeds-hide {P = P} w nw r .env-root = root-step {P = P} (r .env-root) (r .embed-root w nw) (r .env-embed w)
  embeds-hide {P = P} w nw r .input-root = root-step {P = P} (r .input-root) (r .embed-root w nw) (r .input-embed w)
  embeds-hide {P = P} w nw r .embed-root p np =
    root-step {P = P} (r .embed-root p np) (r .embed-root w nw) (r .embed-embed p w)

  embeds-hide-all : ∀ {G H P} (ws : List (PathM Dm)) → All (λ w → is-ε-m w ≡ Bool.false) ws →
                    Embeds G H P →
                    Embeds (hide-all-m G (map at (map m-inr ws))) (hide-all-m H (map at ws)) P
  embeds-hide-all []       []         r = r
  embeds-hide-all (w ∷ ws) (nw ∷ nws) r = embeds-hide-all ws nws (embeds-hide w nw r)

  private
    embeds₀ : Embeds (hide-m (hide-m (graphM C) (at ε)) (at (m-inr ε)))
                     (hide-m (graphM Dm) (at ε)) M.I
    embeds₀ .env-embed q   = hide-hide-root-m C (at (m-inr ε)) env (at (m-inr q))
    embeds₀ .input-embed q = hide-hide-root-m C (at (m-inr ε)) input (at (m-inr q))
    embeds₀ .embed-embed p q = hide-hide-root-m C (at (m-inr ε)) (at (m-inr p)) (at (m-inr q))
    embeds₀ .env-root   = ≈-trans (hide-hide-root-m C (at (m-inr ε)) env (at ε)) (into-hidden-m Dm M.I env)
    embeds₀ .input-root = ≈-trans (hide-hide-root-m C (at (m-inr ε)) input (at ε)) (into-hidden-m Dm M.I input)
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root-m C (at (m-inr ε)) (at (m-inr p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off-m M.I p np) ≈-refl) (into-hidden-m Dm M.I (at p)))

    rfin = embeds-hide-all (interior-m Dm) (interior-not-root-m Dm) embeds₀

  agree-MInr-env : collapse-m-env C M.≈ₘ collapse-m-env Dm
  agree-MInr-env = ≈-trans (rfin .env-root) id-left

  agree-MInr-in : collapse-m-in C M.≈ₘ collapse-m-in Dm
  agree-MInr-in = ≈-trans (rfin .input-root) id-left

-- The mu action: one premise at the unfolded type, with width casts on the input row and the
-- root edge.
module MMu {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
           {τ' : type 2} {w : Val (unfold₁ τ' [ μ τ₀ ])} {R : width-env γ ⇒ width w}
           {w' : Val (unfold₁ τ' [ σr ])} {R' : width-env γ ⇒ width w'}
           {Dm : Map γ s (unfold₁ τ') w R w' R'} where

  private
    C = m-mu {τ' = τ'} Dm

    eᵥ : width w ≡ width (subst Val (unfold₁-inst τ' (μ τ₀)) w)
    eᵥ = ≡-sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)

    e' : width w' ≡ width (subst Val (unfold₁-inst τ' σr) w')
    e' = ≡-sym (width-subst (unfold₁-inst τ' σr) w')

    P : M.Matrix (width (subst Val (unfold₁-inst τ' σr) w')) (width w')
    P = rcast e' M.I

  record Embeds (G : GraphM C) (H : GraphM Dm) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (m-mu q)) M.≈ₘ H env (at q)
      input-embed : ∀ q → G input (at (m-mu q)) M.≈ₘ ccast eᵥ (H input (at q))
      embed-embed : ∀ p q → G (at (m-mu p)) (at (m-mu q)) M.≈ₘ H (at p) (at q)
      env-root    : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      input-root  : G input (at ε) M.≈ₘ (P M.∘ ccast eᵥ (H input (at ε)))
      embed-root  : ∀ p → is-ε-m p ≡ Bool.false →
                    G (at (m-mu p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H} (v : PathM Dm) → is-ε-m v ≡ Bool.false →
                Embeds G H → Embeds (hide-m G (at (m-mu v))) (hide-m H (at v))
  embeds-hide v nw r .env-embed q   = +ₘ-cong (r .env-embed q) (∘-cong (r .embed-embed v q) (r .env-embed v))
  embeds-hide v nw r .input-embed q =
    ccast-step eᵥ (r .input-embed q) (r .embed-embed v q) (r .input-embed v)
  embeds-hide v nw r .embed-embed p q = +ₘ-cong (r .embed-embed p q) (∘-cong (r .embed-embed v q) (r .embed-embed p v))
  embeds-hide v nw r .env-root = root-step {P = P} (r .env-root) (r .embed-root v nw) (r .env-embed v)
  embeds-hide v nw r .input-root =
    root-step-cast eᵥ P (r .input-root) (r .embed-root v nw) (r .input-embed v)
  embeds-hide v nw r .embed-root p np =
    root-step {P = P} (r .embed-root p np) (r .embed-root v nw) (r .embed-embed p v)

  embeds-hide-all : ∀ {G H} (ws : List (PathM Dm)) → All (λ v → is-ε-m v ≡ Bool.false) ws →
                    Embeds G H →
                    Embeds (hide-all-m G (map at (map m-mu ws))) (hide-all-m H (map at ws))
  embeds-hide-all []       []         r = r
  embeds-hide-all (v ∷ ws) (nw ∷ nws) r = embeds-hide-all ws nws (embeds-hide v nw r)

  private
    embeds₀ : Embeds (hide-m (hide-m (graphM C) (at ε)) (at (m-mu ε)))
                     (hide-m (graphM Dm) (at ε))
    embeds₀ .env-embed q   = hide-hide-root-m C (at (m-mu ε)) env (at (m-mu q))
    embeds₀ .input-embed q =
      ≈-trans (hide-hide-root-m C (at (m-mu ε)) input (at (m-mu q)))
              (ccast-step eᵥ {X = graphM Dm input (at q)} {Z = graphM Dm input (at ε)}
                          ≈-refl ≈-refl ≈-refl)
    embeds₀ .embed-embed p q = hide-hide-root-m C (at (m-mu ε)) (at (m-mu p)) (at (m-mu q))
    embeds₀ .env-root =
      ≈-trans (hide-hide-root-m C (at (m-mu ε)) env (at ε)) (into-hidden-m Dm P env)
    embeds₀ .input-root =
      ≈-trans (hide-hide-root-m C (at (m-mu ε)) input (at ε))
      (≈-trans (+ₘ-lunit (P M.∘ ccast eᵥ (graphM Dm input (at ε))))
               (∘-cong₂ (ccast-cong eᵥ (≈-sym (hide-root-m Dm input (at ε))))))
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root-m C (at (m-mu ε)) (at (m-mu p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off-m P p np) ≈-refl) (into-hidden-m Dm P (at p)))

    rfin = embeds-hide-all (interior-m Dm) (interior-not-root-m Dm) embeds₀

  agree-mu-env : collapse-m-env C M.≈ₘ rcast e' (collapse-m-env Dm)
  agree-mu-env =
    ≈-trans (rfin .env-root)
    (≈-trans (rcast-∘ e' M.I (collapse-m-env Dm)) (rcast-cong e' id-left))

  agree-mu-in : collapse-m-in C M.≈ₘ rcast e' (ccast eᵥ (collapse-m-in Dm))
  agree-mu-in =
    ≈-trans (rfin .input-root)
    (≈-trans (rcast-∘ e' M.I (ccast eᵥ (collapse-m-in Dm))) (rcast-cong e' id-left))
