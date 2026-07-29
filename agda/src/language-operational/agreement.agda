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

open CommutativeSemiring two.semiring using (+-comm; +-cong; +-lunit; refl; trans)
import Data.Bool as Bool
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Relation.Unary.All.Properties using (map⁺; ++⁺)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; HasTerminal)
open Category M.cat using (_⇒_; ∘-cong; assoc; id-left; ≈-refl; ≈-sym; ≈-trans; isEquiv) renaming (id to idm)
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

distrib-root : ∀ {m n k l} (P : M.Matrix m n) (X : M.Matrix n k)
               (Y : M.Matrix n l) (Z : M.Matrix l k) →
               ((P M.∘ X) M.+ₘ ((P M.∘ Y) M.∘ Z)) M.≈ₘ (P M.∘ (X M.+ₘ (Y M.∘ Z)))
distrib-root P X Y Z =
  ≈-trans (+ₘ-cong ≈-refl (assoc P Y Z)) (≈-sym (M.comp-bilinear₂ P X (Y M.∘ Z)))


-- Collapsing an inl derivation collapses its premise.
module Inl {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁} {v : Val τ₁} {R : width-env γ ⇒ width v}
           {D : γ , t ⇓ v [ R ]} where

  record Embeds (G : Graph (⇓-inl {τ₂ = τ₂} D)) (H : Graph D)
                (P : M.Matrix (width v) (width v)) : Set ℓ where
    field
      env-embed  : ∀ q → G env (at (inl q)) M.≈ₘ H env (at q)
      embed-embed : ∀ p q → G (at (inl p)) (at (inl q)) M.≈ₘ H (at p) (at q)
      env-root : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      embed-root : ∀ p → is-ε p ≡ Bool.false →
               G (at (inl p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : Path D) → is-ε w ≡ Bool.false →
             Embeds G H P → Embeds (hide G (at (inl w))) (hide H (at w)) P
  embeds-hide w nw s .env-embed q  = +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .embed-embed p q = +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {H = H} {P} w nw s .env-root =
    ≈-trans (+ₘ-cong (s .env-root) (∘-cong (s .embed-root w nw) (s .env-embed w)))
            (distrib-root P (H env (at ε)) (H (at w) (at ε)) (H env (at w)))
  embeds-hide {H = H} {P} w nw s .embed-root p np =
    ≈-trans (+ₘ-cong (s .embed-root p np) (∘-cong (s .embed-root w nw) (s .embed-embed p w)))
            (distrib-root P (H (at p) (at ε)) (H (at w) (at ε)) (H (at p) (at w)))

  embeds-hide-all : ∀ {G H P} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
             Embeds G H P →
             Embeds (hide-all G (map at (map inl ws))) (hide-all H (map at ws)) P
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    root-noop : ∀ x y → hide (graph (⇓-inl {τ₂ = τ₂} D)) (at ε) x y M.≈ₘ graph (⇓-inl {τ₂ = τ₂} D) x y
    root-noop = hide-root (⇓-inl {τ₂ = τ₂} D)

    embeds₀ : Embeds (hide (hide (graph (⇓-inl {τ₂ = τ₂} D)) (at ε)) (at (inl ε)))
                     (hide (graph D) (at ε)) M.I
    embeds₀ .env-embed q =
      +ₘ-cong (root-noop env (at (inl q)))
              (∘-cong (root-noop (at (inl ε)) (at (inl q))) (root-noop env (at (inl ε))))
    embeds₀ .embed-embed p q =
      +ₘ-cong (root-noop (at (inl p)) (at (inl q)))
              (∘-cong (root-noop (at (inl ε)) (at (inl q))) (root-noop (at (inl p)) (at (inl ε))))
    embeds₀ .env-root =
      ≈-trans (+ₘ-cong (root-noop env (at ε))
                       (∘-cong (root-noop (at (inl ε)) (at ε)) (root-noop env (at (inl ε)))))
      (≈-trans (+ₘ-lunit (M.I M.∘ graph D env (at ε)))
               (∘-cong ≈-refl (≈-sym (hide-root D env (at ε)))))
    embeds₀ .embed-root p np =
      ≈-trans (+ₘ-cong (root-noop (at (inl p)) (at ε))
                       (∘-cong (root-noop (at (inl ε)) (at ε)) (root-noop (at (inl p)) (at (inl ε)))))
      (≈-trans (+ₘ-cong (edge-off M.I p np) ≈-refl)
      (≈-trans (+ₘ-lunit (M.I M.∘ graph D (at p) (at ε)))
               (∘-cong ≈-refl (≈-sym (hide-root D (at p) (at ε))))))

  agree-inl : collapse (⇓-inl {τ₂ = τ₂} D) M.≈ₘ collapse D
  agree-inl = ≈-trans (embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root) id-left


-- Collapsing an inr derivation collapses its premise.
module Inr {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₂} {v : Val τ₂} {R : width-env γ ⇒ width v}
           {D : γ , t ⇓ v [ R ]} where

  record Embeds (G : Graph (⇓-inr {τ₁ = τ₁} D)) (H : Graph D)
                (P : M.Matrix (width v) (width v)) : Set ℓ where
    field
      env-embed  : ∀ q → G env (at (inr q)) M.≈ₘ H env (at q)
      embed-embed : ∀ p q → G (at (inr p)) (at (inr q)) M.≈ₘ H (at p) (at q)
      env-root : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      embed-root : ∀ p → is-ε p ≡ Bool.false →
               G (at (inr p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : Path D) → is-ε w ≡ Bool.false →
             Embeds G H P → Embeds (hide G (at (inr w))) (hide H (at w)) P
  embeds-hide w nw s .env-embed q  = +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .embed-embed p q = +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {H = H} {P} w nw s .env-root =
    ≈-trans (+ₘ-cong (s .env-root) (∘-cong (s .embed-root w nw) (s .env-embed w)))
            (distrib-root P (H env (at ε)) (H (at w) (at ε)) (H env (at w)))
  embeds-hide {H = H} {P} w nw s .embed-root p np =
    ≈-trans (+ₘ-cong (s .embed-root p np) (∘-cong (s .embed-root w nw) (s .embed-embed p w)))
            (distrib-root P (H (at p) (at ε)) (H (at w) (at ε)) (H (at p) (at w)))

  embeds-hide-all : ∀ {G H P} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
             Embeds G H P →
             Embeds (hide-all G (map at (map inr ws))) (hide-all H (map at ws)) P
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    root-noop : ∀ x y → hide (graph (⇓-inr {τ₁ = τ₁} D)) (at ε) x y M.≈ₘ graph (⇓-inr {τ₁ = τ₁} D) x y
    root-noop = hide-root (⇓-inr {τ₁ = τ₁} D)

    embeds₀ : Embeds (hide (hide (graph (⇓-inr {τ₁ = τ₁} D)) (at ε)) (at (inr ε)))
                     (hide (graph D) (at ε)) M.I
    embeds₀ .env-embed q =
      +ₘ-cong (root-noop env (at (inr q)))
              (∘-cong (root-noop (at (inr ε)) (at (inr q))) (root-noop env (at (inr ε))))
    embeds₀ .embed-embed p q =
      +ₘ-cong (root-noop (at (inr p)) (at (inr q)))
              (∘-cong (root-noop (at (inr ε)) (at (inr q))) (root-noop (at (inr p)) (at (inr ε))))
    embeds₀ .env-root =
      ≈-trans (+ₘ-cong (root-noop env (at ε))
                       (∘-cong (root-noop (at (inr ε)) (at ε)) (root-noop env (at (inr ε)))))
      (≈-trans (+ₘ-lunit (M.I M.∘ graph D env (at ε)))
               (∘-cong ≈-refl (≈-sym (hide-root D env (at ε)))))
    embeds₀ .embed-root p np =
      ≈-trans (+ₘ-cong (root-noop (at (inr p)) (at ε))
                       (∘-cong (root-noop (at (inr ε)) (at ε)) (root-noop (at (inr p)) (at (inr ε)))))
      (≈-trans (+ₘ-cong (edge-off M.I p np) ≈-refl)
      (≈-trans (+ₘ-lunit (M.I M.∘ graph D (at p) (at ε)))
               (∘-cong ≈-refl (≈-sym (hide-root D (at p) (at ε))))))

  agree-inr : collapse (⇓-inr {τ₁ = τ₁} D) M.≈ₘ collapse D
  agree-inr = ≈-trans (embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root) id-left


-- Collapsing a fst derivation projects its premise's collapse.
module Fst {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v : Val τ₁} {u : Val τ₂}
           {R : width-env γ ⇒ width (pair v u)} {D : γ , t ⇓ pair v u [ R ]} where

  record Embeds (G : Graph (⇓-fst D)) (H : Graph D)
                (P : M.Matrix (width v) (width (pair v u))) : Set ℓ where
    field
      env-embed  : ∀ q → G env (at (fst q)) M.≈ₘ H env (at q)
      embed-embed : ∀ p q → G (at (fst p)) (at (fst q)) M.≈ₘ H (at p) (at q)
      env-root : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      embed-root : ∀ p → is-ε p ≡ Bool.false →
               G (at (fst p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : Path D) → is-ε w ≡ Bool.false →
             Embeds G H P → Embeds (hide G (at (fst w))) (hide H (at w)) P
  embeds-hide w nw s .env-embed q  = +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .embed-embed p q = +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {H = H} {P} w nw s .env-root =
    ≈-trans (+ₘ-cong (s .env-root) (∘-cong (s .embed-root w nw) (s .env-embed w)))
            (distrib-root P (H env (at ε)) (H (at w) (at ε)) (H env (at w)))
  embeds-hide {H = H} {P} w nw s .embed-root p np =
    ≈-trans (+ₘ-cong (s .embed-root p np) (∘-cong (s .embed-root w nw) (s .embed-embed p w)))
            (distrib-root P (H (at p) (at ε)) (H (at w) (at ε)) (H (at p) (at w)))

  embeds-hide-all : ∀ {G H P} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
             Embeds G H P →
             Embeds (hide-all G (map at (map fst ws))) (hide-all H (map at ws)) P
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    root-noop : ∀ x y → hide (graph (⇓-fst D)) (at ε) x y M.≈ₘ graph (⇓-fst D) x y
    root-noop = hide-root (⇓-fst D)

    embeds₀ : Embeds (hide (hide (graph (⇓-fst D)) (at ε)) (at (fst ε)))
                     (hide (graph D) (at ε)) M.p₁
    embeds₀ .env-embed q =
      +ₘ-cong (root-noop env (at (fst q)))
              (∘-cong (root-noop (at (fst ε)) (at (fst q))) (root-noop env (at (fst ε))))
    embeds₀ .embed-embed p q =
      +ₘ-cong (root-noop (at (fst p)) (at (fst q)))
              (∘-cong (root-noop (at (fst ε)) (at (fst q))) (root-noop (at (fst p)) (at (fst ε))))
    embeds₀ .env-root =
      ≈-trans (+ₘ-cong (root-noop env (at ε))
                       (∘-cong (root-noop (at (fst ε)) (at ε)) (root-noop env (at (fst ε)))))
      (≈-trans (+ₘ-lunit (M.p₁ M.∘ graph D env (at ε)))
               (∘-cong ≈-refl (≈-sym (hide-root D env (at ε)))))
    embeds₀ .embed-root p np =
      ≈-trans (+ₘ-cong (root-noop (at (fst p)) (at ε))
                       (∘-cong (root-noop (at (fst ε)) (at ε)) (root-noop (at (fst p)) (at (fst ε)))))
      (≈-trans (+ₘ-cong (edge-off M.p₁ p np) ≈-refl)
      (≈-trans (+ₘ-lunit (M.p₁ M.∘ graph D (at p) (at ε)))
               (∘-cong ≈-refl (≈-sym (hide-root D (at p) (at ε))))))

  agree-fst : collapse (⇓-fst D) M.≈ₘ (M.p₁ M.∘ collapse D)
  agree-fst = embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root


-- Collapsing a snd derivation projects its premise's collapse.
module Snd {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v : Val τ₁} {u : Val τ₂}
           {R : width-env γ ⇒ width (pair v u)} {D : γ , t ⇓ pair v u [ R ]} where

  record Embeds (G : Graph (⇓-snd D)) (H : Graph D)
                (P : M.Matrix (width u) (width (pair v u))) : Set ℓ where
    field
      env-embed  : ∀ q → G env (at (snd q)) M.≈ₘ H env (at q)
      embed-embed : ∀ p q → G (at (snd p)) (at (snd q)) M.≈ₘ H (at p) (at q)
      env-root : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      embed-root : ∀ p → is-ε p ≡ Bool.false →
               G (at (snd p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : Path D) → is-ε w ≡ Bool.false →
             Embeds G H P → Embeds (hide G (at (snd w))) (hide H (at w)) P
  embeds-hide w nw s .env-embed q  = +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .embed-embed p q = +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {H = H} {P} w nw s .env-root =
    ≈-trans (+ₘ-cong (s .env-root) (∘-cong (s .embed-root w nw) (s .env-embed w)))
            (distrib-root P (H env (at ε)) (H (at w) (at ε)) (H env (at w)))
  embeds-hide {H = H} {P} w nw s .embed-root p np =
    ≈-trans (+ₘ-cong (s .embed-root p np) (∘-cong (s .embed-root w nw) (s .embed-embed p w)))
            (distrib-root P (H (at p) (at ε)) (H (at w) (at ε)) (H (at p) (at w)))

  embeds-hide-all : ∀ {G H P} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
             Embeds G H P →
             Embeds (hide-all G (map at (map snd ws))) (hide-all H (map at ws)) P
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    root-noop : ∀ x y → hide (graph (⇓-snd D)) (at ε) x y M.≈ₘ graph (⇓-snd D) x y
    root-noop = hide-root (⇓-snd D)

    embeds₀ : Embeds (hide (hide (graph (⇓-snd D)) (at ε)) (at (snd ε)))
                     (hide (graph D) (at ε)) M.p₂
    embeds₀ .env-embed q =
      +ₘ-cong (root-noop env (at (snd q)))
              (∘-cong (root-noop (at (snd ε)) (at (snd q))) (root-noop env (at (snd ε))))
    embeds₀ .embed-embed p q =
      +ₘ-cong (root-noop (at (snd p)) (at (snd q)))
              (∘-cong (root-noop (at (snd ε)) (at (snd q))) (root-noop (at (snd p)) (at (snd ε))))
    embeds₀ .env-root =
      ≈-trans (+ₘ-cong (root-noop env (at ε))
                       (∘-cong (root-noop (at (snd ε)) (at ε)) (root-noop env (at (snd ε)))))
      (≈-trans (+ₘ-lunit (M.p₂ M.∘ graph D env (at ε)))
               (∘-cong ≈-refl (≈-sym (hide-root D env (at ε)))))
    embeds₀ .embed-root p np =
      ≈-trans (+ₘ-cong (root-noop (at (snd p)) (at ε))
                       (∘-cong (root-noop (at (snd ε)) (at ε)) (root-noop (at (snd p)) (at (snd ε)))))
      (≈-trans (+ₘ-cong (edge-off M.p₂ p np) ≈-refl)
      (≈-trans (+ₘ-lunit (M.p₂ M.∘ graph D (at p) (at ε)))
               (∘-cong ≈-refl (≈-sym (hide-root D (at p) (at ε))))))

  agree-snd : collapse (⇓-snd D) M.≈ₘ (M.p₂ M.∘ collapse D)
  agree-snd = embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root


-- Collapsing a roll derivation collapses its premise.
module Roll {Γ} {τ : type 1} {γ : Env Γ} {t : Γ ⊢ τ [ μ τ ]} {v : Val (τ [ μ τ ])}
           {R : width-env γ ⇒ width v} {D : γ , t ⇓ v [ R ]} where

  record Embeds (G : Graph (⇓-roll {τ = τ} D)) (H : Graph D)
                (P : M.Matrix (width v) (width v)) : Set ℓ where
    field
      env-embed  : ∀ q → G env (at (roll q)) M.≈ₘ H env (at q)
      embed-embed : ∀ p q → G (at (roll p)) (at (roll q)) M.≈ₘ H (at p) (at q)
      env-root : G env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      embed-root : ∀ p → is-ε p ≡ Bool.false →
               G (at (roll p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H P} (w : Path D) → is-ε w ≡ Bool.false →
             Embeds G H P → Embeds (hide G (at (roll w))) (hide H (at w)) P
  embeds-hide w nw s .env-embed q  = +ₘ-cong (s .env-embed q) (∘-cong (s .embed-embed w q) (s .env-embed w))
  embeds-hide w nw s .embed-embed p q = +ₘ-cong (s .embed-embed p q) (∘-cong (s .embed-embed w q) (s .embed-embed p w))
  embeds-hide {H = H} {P} w nw s .env-root =
    ≈-trans (+ₘ-cong (s .env-root) (∘-cong (s .embed-root w nw) (s .env-embed w)))
            (distrib-root P (H env (at ε)) (H (at w) (at ε)) (H env (at w)))
  embeds-hide {H = H} {P} w nw s .embed-root p np =
    ≈-trans (+ₘ-cong (s .embed-root p np) (∘-cong (s .embed-root w nw) (s .embed-embed p w)))
            (distrib-root P (H (at p) (at ε)) (H (at w) (at ε)) (H (at p) (at w)))

  embeds-hide-all : ∀ {G H P} (ws : List (Path D)) → All (λ w → is-ε w ≡ Bool.false) ws →
             Embeds G H P →
             Embeds (hide-all G (map at (map roll ws))) (hide-all H (map at ws)) P
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    root-noop : ∀ x y → hide (graph (⇓-roll {τ = τ} D)) (at ε) x y M.≈ₘ graph (⇓-roll {τ = τ} D) x y
    root-noop = hide-root (⇓-roll {τ = τ} D)

    embeds₀ : Embeds (hide (hide (graph (⇓-roll {τ = τ} D)) (at ε)) (at (roll ε)))
                     (hide (graph D) (at ε)) M.I
    embeds₀ .env-embed q =
      +ₘ-cong (root-noop env (at (roll q)))
              (∘-cong (root-noop (at (roll ε)) (at (roll q))) (root-noop env (at (roll ε))))
    embeds₀ .embed-embed p q =
      +ₘ-cong (root-noop (at (roll p)) (at (roll q)))
              (∘-cong (root-noop (at (roll ε)) (at (roll q))) (root-noop (at (roll p)) (at (roll ε))))
    embeds₀ .env-root =
      ≈-trans (+ₘ-cong (root-noop env (at ε))
                       (∘-cong (root-noop (at (roll ε)) (at ε)) (root-noop env (at (roll ε)))))
      (≈-trans (+ₘ-lunit (M.I M.∘ graph D env (at ε)))
               (∘-cong ≈-refl (≈-sym (hide-root D env (at ε)))))
    embeds₀ .embed-root p np =
      ≈-trans (+ₘ-cong (root-noop (at (roll p)) (at ε))
                       (∘-cong (root-noop (at (roll ε)) (at ε)) (root-noop (at (roll p)) (at (roll ε)))))
      (≈-trans (+ₘ-cong (edge-off M.I p np) ≈-refl)
      (≈-trans (+ₘ-lunit (M.I M.∘ graph D (at p) (at ε)))
               (∘-cong ≈-refl (≈-sym (hide-root D (at p) (at ε))))))

  agree-roll : collapse (⇓-roll {τ = τ} D) M.≈ₘ collapse D
  agree-roll = ≈-trans (embeds-hide-all (interior D) (interior-not-root D) embeds₀ .env-root) id-left
