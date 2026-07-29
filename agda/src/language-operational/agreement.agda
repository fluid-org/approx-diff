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
import Data.Bool
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
           (S : M.Matrix m (width v)) (p : Path D) → is-ε p ≡ Data.Bool.false →
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
                    All (λ p → is-ε p ≡ Data.Bool.false) (interior D)
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

-- A embeds H when A's entries at inl-embedded vertices are H's, and A's root column is H's root
-- column through the root edge P. Hiding corresponding paths on both sides preserves this; the
-- root-column claim excludes the premise root, whose entry is stale once hidden.
module _ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁} {v : Val τ₁} {R : width-env γ ⇒ width v}
         {D : γ , t ⇓ v [ R ]} where

  record Embeds (A : Graph (⇓-inl {τ₂ = τ₂} D)) (H : Graph D)
                (P : M.Matrix (width v) (width v)) : Set ℓ where
    field
      s-env  : ∀ q → A env (at (inl q)) M.≈ₘ H env (at q)
      s-emb  : ∀ p q → A (at (inl p)) (at (inl q)) M.≈ₘ H (at p) (at q)
      s-envr : A env (at ε) M.≈ₘ (P M.∘ H env (at ε))
      s-embr : ∀ p → is-ε p ≡ Data.Bool.false →
               A (at (inl p)) (at ε) M.≈ₘ (P M.∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {A H P} (w : Path D) → is-ε w ≡ Data.Bool.false →
             Embeds A H P → Embeds (hide A (at (inl w))) (hide H (at w)) P
  embeds-hide w nw s .s-env q  = +ₘ-cong (s .s-env q) (∘-cong (s .s-emb w q) (s .s-env w))
  embeds-hide w nw s .s-emb p q = +ₘ-cong (s .s-emb p q) (∘-cong (s .s-emb w q) (s .s-emb p w))
  embeds-hide {A} {H} {P} w nw s .s-envr =
    begin
      A env (at ε) M.+ₘ (A (at (inl w)) (at ε) M.∘ A env (at (inl w)))
        ≈⟨ +ₘ-cong (s .s-envr) (∘-cong (s .s-embr w nw) (s .s-env w)) ⟩
      (P M.∘ H env (at ε)) M.+ₘ ((P M.∘ H (at w) (at ε)) M.∘ H env (at w))
        ≈⟨ +ₘ-cong ≈-refl (assoc P (H (at w) (at ε)) (H env (at w))) ⟩
      (P M.∘ H env (at ε)) M.+ₘ (P M.∘ (H (at w) (at ε) M.∘ H env (at w)))
        ≈⟨ ≈-sym (M.comp-bilinear₂ P (H env (at ε)) (H (at w) (at ε) M.∘ H env (at w))) ⟩
      P M.∘ (H env (at ε) M.+ₘ (H (at w) (at ε) M.∘ H env (at w)))
    ∎
    where open ≈-Reasoning isEquiv
  embeds-hide {A} {H} {P} w nw s .s-embr p np =
    begin
      A (at (inl p)) (at ε) M.+ₘ (A (at (inl w)) (at ε) M.∘ A (at (inl p)) (at (inl w)))
        ≈⟨ +ₘ-cong (s .s-embr p np) (∘-cong (s .s-embr w nw) (s .s-emb p w)) ⟩
      (P M.∘ H (at p) (at ε)) M.+ₘ ((P M.∘ H (at w) (at ε)) M.∘ H (at p) (at w))
        ≈⟨ +ₘ-cong ≈-refl (assoc P (H (at w) (at ε)) (H (at p) (at w))) ⟩
      (P M.∘ H (at p) (at ε)) M.+ₘ (P M.∘ (H (at w) (at ε) M.∘ H (at p) (at w)))
        ≈⟨ ≈-sym (M.comp-bilinear₂ P (H (at p) (at ε)) (H (at w) (at ε) M.∘ H (at p) (at w))) ⟩
      P M.∘ (H (at p) (at ε) M.+ₘ (H (at w) (at ε) M.∘ H (at p) (at w)))
    ∎
    where open ≈-Reasoning isEquiv

  embeds-hide-all : ∀ {A H P} (ws : List (Path D)) → All (λ w → is-ε w ≡ Data.Bool.false) ws →
             Embeds A H P →
             Embeds (hide-all A (map at (map inl ws))) (hide-all H (map at ws)) P
  embeds-hide-all []       []         s = s
  embeds-hide-all (w ∷ ws) (nw ∷ nws) s = embeds-hide-all ws nws (embeds-hide w nw s)

  private
    G₀ : Graph (⇓-inl {τ₂ = τ₂} D)
    G₀ = graph (⇓-inl D)

    A₂ : Graph (⇓-inl {τ₂ = τ₂} D)
    A₂ = hide (hide G₀ (at ε)) (at (inl ε))

    H₁ : Graph D
    H₁ = hide (graph D) (at ε)

    A₁-entry : ∀ x y → hide G₀ (at ε) x y M.≈ₘ G₀ x y
    A₁-entry = hide-root (⇓-inl D)

    embeds₀ : Embeds A₂ H₁ M.I
    embeds₀ .Embeds.s-env q =
      +ₘ-cong (A₁-entry env (at (inl q)))
              (∘-cong (A₁-entry (at (inl ε)) (at (inl q))) (A₁-entry env (at (inl ε))))
    embeds₀ .Embeds.s-emb p q =
      +ₘ-cong (A₁-entry (at (inl p)) (at (inl q)))
              (∘-cong (A₁-entry (at (inl ε)) (at (inl q))) (A₁-entry (at (inl p)) (at (inl ε))))
    embeds₀ .Embeds.s-envr =
      begin
        hide G₀ (at ε) env (at ε) M.+ₘ
          (hide G₀ (at ε) (at (inl ε)) (at ε) M.∘ hide G₀ (at ε) env (at (inl ε)))
          ≈⟨ +ₘ-cong (A₁-entry env (at ε))
                     (∘-cong (A₁-entry (at (inl ε)) (at ε)) (A₁-entry env (at (inl ε)))) ⟩
        M.εₘ M.+ₘ (M.I M.∘ graph D env (at ε))
          ≈⟨ +ₘ-lunit (M.I M.∘ graph D env (at ε)) ⟩
        M.I M.∘ graph D env (at ε)
          ≈⟨ ∘-cong ≈-refl (≈-sym (hide-root D env (at ε))) ⟩
        M.I M.∘ H₁ env (at ε)
      ∎
      where open ≈-Reasoning isEquiv
    embeds₀ .Embeds.s-embr p np =
      begin
        hide G₀ (at ε) (at (inl p)) (at ε) M.+ₘ
          (hide G₀ (at ε) (at (inl ε)) (at ε) M.∘ hide G₀ (at ε) (at (inl p)) (at (inl ε)))
          ≈⟨ +ₘ-cong (A₁-entry (at (inl p)) (at ε))
                     (∘-cong (A₁-entry (at (inl ε)) (at ε)) (A₁-entry (at (inl p)) (at (inl ε)))) ⟩
        edge M.I p M.+ₘ (M.I M.∘ graph D (at p) (at ε))
          ≈⟨ +ₘ-cong (edge-off M.I p np) ≈-refl ⟩
        M.εₘ M.+ₘ (M.I M.∘ graph D (at p) (at ε))
          ≈⟨ +ₘ-lunit (M.I M.∘ graph D (at p) (at ε)) ⟩
        M.I M.∘ graph D (at p) (at ε)
          ≈⟨ ∘-cong ≈-refl (≈-sym (hide-root D (at p) (at ε))) ⟩
        M.I M.∘ H₁ (at p) (at ε)
      ∎
      where open ≈-Reasoning isEquiv

  -- Collapsing an inl derivation collapses its premise.
  agree-inl : collapse (⇓-inl {τ₂ = τ₂} D) M.≈ₘ collapse D
  agree-inl =
    ≈-trans (embeds-hide-all (interior D) (interior-not-root D) embeds₀ .Embeds.s-envr) id-left
