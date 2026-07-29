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
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Relation.Unary.All.Properties using (map⁺; ++⁺)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; cong to ≡-cong; trans to ≡-trans)
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
  stepₗ {G} {H} w nw r .env-root =
    ≈-trans (+ₘ-cong (r .env-root) (∘-cong (r .left-root w nw) (r .env-left w)))
            (distrib-root M.in₁ (H env (at ε)) (H (at w) (at ε)) (H env (at w)))
  stepₗ {G} {H} w nw r .left-root p np =
    ≈-trans (+ₘ-cong (r .left-root p np) (∘-cong (r .left-root w nw) (r .left-left p w)))
            (distrib-root M.in₁ (H (at p) (at ε)) (H (at w) (at ε)) (H (at p) (at w)))
  stepₗ {G} {H} w nw r .env-right q =
    ≈-trans (+ₘ-cong (r .env-right q)
                     (∘-cong (r .left-right w q) (≈-refl {f = G env (at (pair₁ w))})))
            (absorb (graph Dt env (at q)) (G env (at (pair₁ w))))
  stepₗ {G} {H} w nw r .right-right p q =
    ≈-trans (+ₘ-cong (r .right-right p q)
                     (∘-cong (r .left-right w q) (≈-refl {f = G (at (pair₂ p)) (at (pair₁ w))})))
            (absorb (graph Dt (at p) (at q)) (G (at (pair₂ p)) (at (pair₁ w))))
  stepₗ {G} {H} w nw r .right-root p =
    ≈-trans (+ₘ-cong (r .right-root p)
                     (∘-cong (≈-refl {f = G (at (pair₁ w)) (at ε)}) (r .right-left p w)))
            (absorb-r (edge M.in₂ p) (G (at (pair₁ w)) (at ε)))
  stepₗ {G} {H} w nw r .left-right p q =
    ≈-trans (+ₘ-cong (r .left-right p q)
                     (∘-cong (r .left-right w q) (≈-refl {f = G (at (pair₁ p)) (at (pair₁ w))})))
            (absorb M.εₘ (G (at (pair₁ p)) (at (pair₁ w))))
  stepₗ {G} {H} w nw r .right-left p q =
    ≈-trans (+ₘ-cong (r .right-left p q)
                     (∘-cong (≈-refl {f = G (at (pair₁ w)) (at (pair₁ q))}) (r .right-left p w)))
            (absorb-r M.εₘ (G (at (pair₁ w)) (at (pair₁ q))))

  foldₗ : ∀ {G H} (ws : List (Path Ds)) → All (λ w → is-ε w ≡ Bool.false) ws →
          Phase₁ G H → Phase₁ (hide-all G (map at (map pair₁ ws))) (hide-all H (map at ws))
  foldₗ []       []         r = r
  foldₗ (w ∷ ws) (nw ∷ nws) r = foldₗ ws nws (stepₗ w nw r)

  private
    rn : ∀ x y → hide (graph (⇓-pair Ds Dt)) (at ε) x y M.≈ₘ graph (⇓-pair Ds Dt) x y
    rn = hide-root (⇓-pair Ds Dt)

    base₁ : Phase₁ (hide (hide (graph (⇓-pair Ds Dt)) (at ε)) (at (pair₁ ε)))
                   (hide (graph Ds) (at ε))
    base₁ .env-left q =
      +ₘ-cong (rn env (at (pair₁ q)))
              (∘-cong (rn (at (pair₁ ε)) (at (pair₁ q))) (rn env (at (pair₁ ε))))
    base₁ .left-left p q =
      +ₘ-cong (rn (at (pair₁ p)) (at (pair₁ q)))
              (∘-cong (rn (at (pair₁ ε)) (at (pair₁ q))) (rn (at (pair₁ p)) (at (pair₁ ε))))
    base₁ .env-root =
      ≈-trans (+ₘ-cong (rn env (at ε)) (∘-cong (rn (at (pair₁ ε)) (at ε)) (rn env (at (pair₁ ε)))))
      (≈-trans (+ₘ-lunit (M.in₁ M.∘ graph Ds env (at ε)))
               (∘-cong ≈-refl (≈-sym (hide-root Ds env (at ε)))))
    base₁ .left-root p np =
      ≈-trans (+ₘ-cong (rn (at (pair₁ p)) (at ε))
                       (∘-cong (rn (at (pair₁ ε)) (at ε)) (rn (at (pair₁ p)) (at (pair₁ ε)))))
      (≈-trans (+ₘ-cong (edge-off M.in₁ p np) ≈-refl)
      (≈-trans (+ₘ-lunit (M.in₁ M.∘ graph Ds (at p) (at ε)))
               (∘-cong ≈-refl (≈-sym (hide-root Ds (at p) (at ε))))))
    base₁ .env-right q =
      ≈-trans (+ₘ-cong (rn env (at (pair₂ q)))
                       (∘-cong (rn (at (pair₁ ε)) (at (pair₂ q))) (rn env (at (pair₁ ε)))))
              (absorb (graph Dt env (at q)) (graph Ds env (at ε)))
    base₁ .right-right p q =
      ≈-trans (+ₘ-cong (rn (at (pair₂ p)) (at (pair₂ q)))
                       (∘-cong (rn (at (pair₁ ε)) (at (pair₂ q))) (rn (at (pair₂ p)) (at (pair₁ ε)))))
              (absorb (graph Dt (at p) (at q)) (graph (⇓-pair Ds Dt) (at (pair₂ p)) (at (pair₁ ε))))
    base₁ .right-root p =
      ≈-trans (+ₘ-cong (rn (at (pair₂ p)) (at ε))
                       (∘-cong (rn (at (pair₁ ε)) (at ε)) (rn (at (pair₂ p)) (at (pair₁ ε)))))
              (absorb-r (edge M.in₂ p) (graph (⇓-pair Ds Dt) (at (pair₁ ε)) (at ε)))
    base₁ .left-right p q =
      ≈-trans (+ₘ-cong (rn (at (pair₁ p)) (at (pair₂ q)))
                       (∘-cong (rn (at (pair₁ ε)) (at (pair₂ q))) (rn (at (pair₁ p)) (at (pair₁ ε)))))
              (absorb M.εₘ (graph Ds (at p) (at ε)))
    base₁ .right-left p q =
      ≈-trans (+ₘ-cong (rn (at (pair₂ p)) (at (pair₁ q)))
                       (∘-cong (rn (at (pair₁ ε)) (at (pair₁ q))) (rn (at (pair₂ p)) (at (pair₁ ε)))))
              (absorb-r M.εₘ (graph Ds (at ε) (at q)))

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
  stepᵣ {G} {H} {K} w nw r .env-root =
    ≈-trans (+ₘ-cong (r .env-root) (∘-cong (r .right-root w nw) (r .env-right w)))
            (offset-distrib K M.in₂ (H env (at ε)) (H (at w) (at ε)) (H env (at w)))
  stepᵣ {G} {H} {K} w nw r .right-root p np =
    ≈-trans (+ₘ-cong (r .right-root p np) (∘-cong (r .right-root w nw) (r .right-right p w)))
            (distrib-root M.in₂ (H (at p) (at ε)) (H (at w) (at ε)) (H (at p) (at w)))

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
    base₂ .env-right q =
      +ₘ-cong (r1 .env-right q) (∘-cong (r1 .right-right ε q) (r1 .env-right ε))
    base₂ .right-right p q =
      +ₘ-cong (r1 .right-right p q) (∘-cong (r1 .right-right ε q) (r1 .right-right p ε))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (r1 .env-root) (∘-cong (r1 .right-root ε) (r1 .env-right ε)))
              (+ₘ-cong ≈-refl (∘-cong ≈-refl (≈-sym (hide-root Dt env (at ε)))))
    base₂ .right-root p np =
      ≈-trans (+ₘ-cong (r1 .right-root p) (∘-cong (r1 .right-root ε) (r1 .right-right p ε)))
      (≈-trans (+ₘ-cong (edge-off M.in₂ p np) ≈-refl)
      (≈-trans (+ₘ-lunit (M.in₂ M.∘ graph Dt (at p) (at ε)))
               (∘-cong ≈-refl (≈-sym (hide-root Dt (at p) (at ε))))))

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
