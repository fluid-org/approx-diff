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
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤'; tt to tt')
open import Level using (0ℓ)
open import categories using (Category; HasTerminal)
open Category M.cat
  using (_⇒_; _∘_; _≈_; ∘-cong; ∘-cong₁; ∘-cong₂; assoc; id-left; id-right;
         ≈-refl; ≈-sym; ≈-trans; isEquiv)
  renaming (id to idm)
open HasTerminal M.terminal using (to-terminal)
open import interaction.control-agreement-algebra Sig 𝒫
open import interaction.control-simulation Sig 𝒫

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

  P₀ : M.Matrix (width v) (width (pair v u))
  P₀ = (M.p₁ {width v} {width u} ∘ M.p₂ {1} {width v Nat.+ width u}) M.+ₘ (ctrl-row ∘ M.p₁ {1})

  K₀ : (i : Input) → M.Matrix (width v) (input-width γ i)
  K₀ environment = M.εₘ
  K₀ source      = ctrl-row ∘ ctrl-row {1}

  open Single (⇓-fst D) (fst {D = D}) is-ε ε (λ (_ : Root) → ε) (λ _ → P₀) (λ _ → K₀)
  open Premise
  open Agrees
  open Entries

  private
    premise-of : Graph D → Premise
    premise-of G .input-entry i q = G (inp i) (at q)
    premise-of G .path-entry p q = G (at p) (at q)

    folds′ : (ws : List (Path D)) (G : Graph D) →
             steps (premise-of G) ws ≡ premise-of (hide-all G (map at ws))
    folds′ = folds premise-of at hide (λ G w → ≡-refl)

    entries : Entries (graph (⇓-fst D)) (premise-of (graph D))
    entries .inputs environment q = ≈-refl
    entries .inputs source q = ≈-refl
    entries .block p q = ≈-refl
    entries .offset _ environment = ≈-refl {f = K₀ environment}
    entries .offset _ source = ≈-refl {f = K₀ source}
    entries .root-edge _ = ≈-refl {f = P₀}
    entries .off-edge _ p np = edge-off P₀ p np
    entries .sink q = root-sink D (at q)

    start : Agrees (hide (hide (graph (⇓-fst D)) (at ε)) (at (fst ε)))
                   (premise-of (hide (graph D) (at ε)))
    start = agrees-base entries

  agree : ∀ i → collapse-at (⇓-fst D) i ≈ (K₀ i M.+ₘ (P₀ ∘ collapse-at D i))
  agree i =
    ≈-trans (agrees-hide-all (interior D) (interior-not-root D) start .root-agrees root i)
            (root-cong root i (≈-of-≡ (≡-cong (λ H → H .input-entry i ε)
                                           (folds′ (interior D) (hide (graph D) (at ε))))))

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

module Pair {Γ τ₁ τ₂} {γ : Env Γ} {ts : Γ ⊢ τ₁} {tt : Γ ⊢ τ₂} {v : Val τ₁} {u : Val τ₂}
            {R : Nat.suc (width-env γ) ⇒ width v} {S : Nat.suc (width-env γ) ⇒ width u}
            {D₁ : γ , ts ⇓ v [ R ]} {D₂ : γ , tt ⇓ u [ S ]} where

  private
    E = ⇓-pair D₁ D₂

  P₁ : M.Matrix (width (pair v u)) (width v)
  P₁ = M.in₂ {1} {width v Nat.+ width u} ∘ M.in₁ {width v} {width u}

  P₂ : M.Matrix (width (pair v u)) (width u)
  P₂ = M.in₂ {1} {width v Nat.+ width u} ∘ M.in₂ {width v} {width u}

  K₁ : (i : Input) → M.Matrix (width (pair v u)) (input-width γ i)
  K₁ environment = M.εₘ
  K₁ source      = src-root

  K₂ : (i : Input) → M.Matrix (width (pair v u)) (input-width γ i)
  K₂ i = K₁ i M.+ₘ (P₁ ∘ collapse-at D₁ i)

  private
    module S₁ = Single E (pair₁ {D₁ = D₁} {D₂ = D₂}) is-ε ε (λ (_ : Root) → ε) (λ _ → P₁) (λ _ → K₁)
    module S₂ = Single E (pair₂ {D₁ = D₁} {D₂ = D₂}) is-ε ε (λ (_ : Root) → ε) (λ _ → P₂) (λ _ → K₂)
    module Bh = Behind E (pair₁ {D₁ = D₁} {D₂ = D₂}) (pair₂ {D₁ = D₁} {D₂ = D₂})
                       (λ (_ : Root) → ε)
                       (λ p q → graph D₂ (at p) (at q))
                       (λ _ p → edge P₂ p)
    module Fr = Frozen E (pair₁ {D₁ = D₁} {D₂ = D₂}) (pair₂ {D₁ = D₁} {D₂ = D₂})
                       (λ i q → graph D₂ (inp i) (at q))

  open S₁.Premise
  open S₂.Premise
  open S₁.Agrees
  open S₂.Agrees
  open S₁.Entries
  open S₂.Entries
  open Bh.Keeps
  open Fr.Keeps

  private

    prem₁ : Graph D₁ → S₁.Premise
    prem₁ G .input-entry i q = G (inp i) (at q)
    prem₁ G .path-entry p q = G (at p) (at q)

    folds₁ : (ws : List (Path D₁)) (G : Graph D₁) →
             S₁.steps (prem₁ G) ws ≡ prem₁ (hide-all G (map at ws))
    folds₁ = S₁.folds prem₁ at hide (λ G w → ≡-refl)

    prem₂ : Graph D₂ → S₂.Premise
    prem₂ G .input-entry i q = G (inp i) (at q)
    prem₂ G .path-entry p q = G (at p) (at q)

    folds₂ : (ws : List (Path D₂)) (G : Graph D₂) →
             S₂.steps (prem₂ G) ws ≡ prem₂ (hide-all G (map at ws))
    folds₂ = S₂.folds prem₂ at hide (λ G w → ≡-refl)

    G₁ : Graph E
    G₁ = hide-all (hide (hide (graph E) (at ε)) (at (pair₁ ε))) (map at (map pair₁ (interior D₁)))

    entries₁ : S₁.Entries (graph E) (prem₁ (graph D₁))
    entries₁ .inputs environment q = ≈-refl
    entries₁ .inputs source q = ≈-refl
    entries₁ .block p q = ≈-refl
    entries₁ .offset _ environment = ≈-refl {f = K₁ environment}
    entries₁ .offset _ source = ≈-refl {f = K₁ source}
    entries₁ .root-edge _ = ≈-refl {f = P₁}
    entries₁ .off-edge _ p np = edge-off P₁ p np
    entries₁ .sink q = root-sink D₁ (at q)

    start₁ : S₁.Agrees (hide (hide (graph E) (at ε)) (at (pair₁ ε)))
                       (prem₁ (hide (graph D₁) (at ε)))
    start₁ = S₁.agrees-base entries₁

    done₁ : S₁.Agrees G₁ (S₁.steps (prem₁ (hide (graph D₁) (at ε))) (interior D₁))
    done₁ = S₁.agrees-hide-all (interior D₁) (interior-not-root D₁) start₁

    behind₀ : Bh.Keeps (graph E)
    behind₀ .path-keeps p q = ≈-refl
    behind₀ .root-keeps _ p = ≈-refl {f = edge P₂ p}
    behind₀ .two-one p q = ≈-refl {f = M.εₘ}

    frozen₀ : Fr.Keeps (graph E)
    frozen₀ .input-keeps environment q = ≈-refl
    frozen₀ .input-keeps source q = ≈-refl
    frozen₀ .one-two p q = ≈-refl {f = M.εₘ}

    behind₁ : Bh.Keeps G₁
    behind₁ = Bh.keeps-hide-all (λ w → w) (interior D₁)
                (Bh.keeps-hide ε (Bh.keeps-sink (at ε) (root-sink E) behind₀))

    frozen₁ : Fr.Keeps G₁
    frozen₁ = Fr.keeps-hide-all (λ w → w) (interior D₁)
                (Fr.keeps-hide ε (Fr.keeps-sink (at ε) (root-sink E) frozen₀))

    kin₂ : ∀ i → G₁ (inp i) (at ε) ≈ K₂ i
    kin₂ i =
      ≈-trans (done₁ .root-agrees root i)
              (S₁.root-cong root i
                (≈-of-≡ (≡-cong (λ (H : S₁.Premise) → H .input-entry i ε)
                                (folds₁ (interior D₁) (hide (graph D₁) (at ε))))))

    entries₂ : S₂.Entries G₁ (prem₂ (graph D₂))
    entries₂ .inputs i q = frozen₁ .input-keeps i q
    entries₂ .block p q = behind₁ .path-keeps p q
    entries₂ .offset _ i = kin₂ i
    entries₂ .root-edge _ = behind₁ .root-keeps root ε
    entries₂ .off-edge _ p np = ≈-trans (behind₁ .root-keeps root p) (edge-off P₂ p np)
    entries₂ .sink q = root-sink D₂ (at q)

    start₂ : S₂.Agrees (hide G₁ (at (pair₂ ε))) (prem₂ (hide (graph D₂) (at ε)))
    start₂ = S₂.agrees-from entries₂

    done₂ : S₂.Agrees (hide-all (hide G₁ (at (pair₂ ε))) (map at (map pair₂ (interior D₂))))
                      (S₂.steps (prem₂ (hide (graph D₂) (at ε))) (interior D₂))
    done₂ = S₂.agrees-hide-all (interior D₂) (interior-not-root D₂) start₂

    plumb : hide-all (graph E) (map at (paths E))
            ≡ hide-all (hide G₁ (at (pair₂ ε))) (map at (map pair₂ (interior D₂)))
    plumb =
      ≡-trans (≡-cong (hide-all (hide (graph E) (at ε)))
                      (map-++ at (map pair₁ (paths D₁)) (map pair₂ (paths D₂))))
              (hide-all-++ (hide (graph E) (at ε))
                           (map at (map pair₁ (paths D₁)))
                           (map at (map pair₂ (paths D₂))))

  agree : ∀ i → collapse-at E i ≈ (K₂ i M.+ₘ (P₂ ∘ collapse-at D₂ i))
  agree i =
    ≈-trans (≈-of-≡ (≡-cong (λ G → G (inp i) (at ε)) plumb))
    (≈-trans (done₂ .root-agrees root i)
             (S₂.root-cong root i
               (≈-of-≡ (≡-cong (λ (H : S₂.Premise) → H .input-entry i ε)
                               (folds₂ (interior D₂) (hide (graph D₂) (at ε)))))))

module CaseL {Γ τ₁ τ₂ τ} {γ : Env Γ} {ts : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
             {v : Val τ₁} {u : Val τ}
             {R : Nat.suc (width-env γ) ⇒ Nat.suc (width v)}
             {S : Nat.suc (width-env (γ · v)) ⇒ width u}
             {D₁ : γ , ts ⇓ inl v [ R ]} {D₂ : γ · v , t₁ ⇓ u [ S ]} where

  private
    E = ⇓-case-l {t₂ = t₂} D₁ D₂

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

  Rt : (q : Path D₂) → M.Matrix (width-at q) (Nat.suc (width v))
  Rt q = ((B q ∘ iᵣ) ∘ p2) M.+ₘ (Bₛ q ∘ p1)

  Wsub : (i i' : Input) → M.Matrix (input-width (γ · v) i') (input-width γ i)
  Wsub environment environment = iₗ M.+ₘ ((iᵣ ∘ p2) ∘ collapse D₁)
  Wsub environment source      = p1 ∘ collapse D₁
  Wsub source      environment = (iᵣ ∘ p2) ∘ collapse-src D₁
  Wsub source      source      = ctrl-row {1} M.+ₘ (p1 ∘ collapse-src D₁)

  private
    Targets : Set ℓ
    Targets = Path D₂ ⊎ Root

    tgt : Targets → Path E
    tgt (inj₁ q) = case-l₂ q
    tgt (inj₂ _) = ε

    P₁ : (n : Targets) → M.Matrix (width-at (tgt n)) (Nat.suc (width v))
    P₁ (inj₁ q) = Rt q
    P₁ (inj₂ _) = M.εₘ

    K₁ : (n : Targets) (i : Input) → M.Matrix (width-at (tgt n)) (input-width γ i)
    K₁ (inj₁ q) environment = B q ∘ iₗ
    K₁ (inj₁ q) source      = Bₛ q ∘ ctrl-row {1}
    K₁ (inj₂ _) _           = M.εₘ

    P₂ : (n : Root) → M.Matrix (width u) (width-at (ε {D = D₂}))
    P₂ _ = M.I

    K₂ : (n : Root) (i : Input) → M.Matrix (width u) (input-width γ i)
    K₂ _ _ = M.εₘ

    module Sc = Single E (case-l₁ {t₂ = t₂} {D₁ = D₁} {D₂ = D₂}) is-ε ε tgt P₁ K₁
    module Br = Under E (γ · v) (case-l₂ {t₂ = t₂} {D₁ = D₁} {D₂ = D₂}) is-ε ε
                      (λ (_ : Root) → ε) Wsub P₂ K₂
    module Bh = Behind E (case-l₁ {t₂ = t₂} {D₁ = D₁} {D₂ = D₂})
                       (case-l₂ {t₂ = t₂} {D₁ = D₁} {D₂ = D₂})
                       (λ (_ : Root) → ε)
                       (λ p q → graph D₂ (at p) (at q))
                       (λ _ p → edge M.I p)

  open Sc.Premise
  open Br.Premise
  open Sc.Agrees
  open Br.Agrees
  open Sc.Entries
  open Br.Entries
  open Bh.Keeps

  private
    prem₁ : Graph D₁ → Sc.Premise
    prem₁ G .input-entry i q = G (inp i) (at q)
    prem₁ G .path-entry p q = G (at p) (at q)

    folds₁ : (ws : List (Path D₁)) (G : Graph D₁) →
             Sc.steps (prem₁ G) ws ≡ prem₁ (hide-all G (map at ws))
    folds₁ = Sc.folds prem₁ at hide (λ G w → ≡-refl)

    prem₂ : Graph D₂ → Br.Premise
    prem₂ G .input-entry i q = G (inp i) (at q)
    prem₂ G .path-entry p q = G (at p) (at q)

    folds₂ : (ws : List (Path D₂)) (G : Graph D₂) →
             Br.steps (prem₂ G) ws ≡ prem₂ (hide-all G (map at ws))
    folds₂ = Br.folds prem₂ at hide (λ G w → ≡-refl)

    G₁ : Graph E
    G₁ = hide-all (hide (hide (graph E) (at ε)) (at (case-l₁ ε)))
                  (map at (map case-l₁ (interior D₁)))

    entries₁ : Sc.Entries (graph E) (prem₁ (graph D₁))
    entries₁ .inputs environment q = ≈-refl
    entries₁ .inputs source q = ≈-refl
    entries₁ .block p q = ≈-refl
    entries₁ .offset (inj₁ q) environment = ≈-refl {f = K₁ (inj₁ q) environment}
    entries₁ .offset (inj₁ q) source = ≈-refl {f = K₁ (inj₁ q) source}
    entries₁ .offset (inj₂ _) environment = ≈-refl {f = M.εₘ}
    entries₁ .offset (inj₂ _) source = ≈-refl {f = M.εₘ}
    entries₁ .root-edge (inj₁ q) = ≈-refl {f = Rt q}
    entries₁ .root-edge (inj₂ _) = ≈-refl {f = M.εₘ}
    entries₁ .off-edge (inj₁ q) p np = edge-off (Rt q) p np
    entries₁ .off-edge (inj₂ _) p np = ≈-refl {f = M.εₘ}
    entries₁ .sink q = root-sink D₁ (at q)

    done₁ : Sc.Agrees G₁ (Sc.steps (prem₁ (hide (graph D₁) (at ε))) (interior D₁))
    done₁ = Sc.agrees-hide-all (interior D₁) (interior-not-root D₁) (Sc.agrees-base entries₁)

    behind₀ : Bh.Keeps (graph E)
    behind₀ .path-keeps p q = ≈-refl
    behind₀ .root-keeps _ p = ≈-refl {f = edge M.I p}
    behind₀ .two-one p q = ≈-refl {f = M.εₘ}

    behind₁ : Bh.Keeps G₁
    behind₁ = Bh.keeps-hide-all (λ w → w) (interior D₁)
                (Bh.keeps-hide ε (Bh.keeps-sink (at ε) (root-sink E) behind₀))

    collapsed₁ : ∀ i → Sc.steps (prem₁ (hide (graph D₁) (at ε))) (interior D₁) .input-entry i ε
                       ≈ collapse-at D₁ i
    collapsed₁ i = ≈-of-≡ (≡-cong (λ (H : Sc.Premise) → H .input-entry i ε)
                                  (folds₁ (interior D₁) (hide (graph D₁) (at ε))))

    route-env : ∀ (q : Path D₂) →
                ((B q ∘ iₗ) M.+ₘ (Rt q ∘ collapse D₁))
                ≈ ((B q ∘ Wsub environment environment) M.+ₘ (Bₛ q ∘ Wsub environment source))
    route-env q =
      ≈-trans (+ₘ-cong (≈-refl {f = B q ∘ iₗ})
                       (M.comp-bilinear₁ ((B q ∘ iᵣ) ∘ p2) (Bₛ q ∘ p1) (collapse D₁)))
      (≈-trans (≈-sym (+ₘ-assoc (B q ∘ iₗ) (((B q ∘ iᵣ) ∘ p2) ∘ collapse D₁)
                                ((Bₛ q ∘ p1) ∘ collapse D₁)))
               (+ₘ-cong (≈-trans (+ₘ-cong (≈-refl {f = B q ∘ iₗ})
                                   (≈-trans (∘-cong₁ {g = collapse D₁} (assoc (B q) iᵣ p2))
                                            (assoc (B q) (iᵣ ∘ p2) (collapse D₁))))
                                 (≈-sym (M.comp-bilinear₂ (B q) iₗ ((iᵣ ∘ p2) ∘ collapse D₁))))
                        (assoc (Bₛ q) p1 (collapse D₁))))

    route-src : ∀ (q : Path D₂) →
                ((Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ collapse-src D₁))
                ≈ ((B q ∘ Wsub source environment) M.+ₘ (Bₛ q ∘ Wsub source source))
    route-src q =
      ≈-trans (+ₘ-cong (≈-refl {f = Bₛ q ∘ ctrl-row {1}})
                       (M.comp-bilinear₁ ((B q ∘ iᵣ) ∘ p2) (Bₛ q ∘ p1) (collapse-src D₁)))
      (≈-trans (+ₘ-swap-mid (Bₛ q ∘ ctrl-row {1}) (((B q ∘ iᵣ) ∘ p2) ∘ collapse-src D₁)
                            ((Bₛ q ∘ p1) ∘ collapse-src D₁))
               (+ₘ-cong (≈-trans (∘-cong₁ {g = collapse-src D₁} (assoc (B q) iᵣ p2))
                                 (assoc (B q) (iᵣ ∘ p2) (collapse-src D₁)))
                        (≈-trans (+ₘ-cong (≈-refl {f = Bₛ q ∘ ctrl-row {1}})
                                          (assoc (Bₛ q) p1 (collapse-src D₁)))
                                 (≈-sym (M.comp-bilinear₂ (Bₛ q) (ctrl-row {1})
                                                          (p1 ∘ collapse-src D₁))))))

    branch-rows : ∀ i q → G₁ (inp i) (at (case-l₂ q)) ≈ Br.input-sub (prem₂ (graph D₂)) i q
    branch-rows environment q =
      ≈-trans (done₁ .root-agrees (inj₁ q) environment)
      (≈-trans (Sc.root-cong (inj₁ q) environment (collapsed₁ environment)) (route-env q))
    branch-rows source q =
      ≈-trans (done₁ .root-agrees (inj₁ q) source)
      (≈-trans (Sc.root-cong (inj₁ q) source (collapsed₁ source)) (route-src q))

    scrut-col : ∀ i → M.Matrix (Nat.suc (width v)) (input-width γ i)
    scrut-col i = Sc.steps (prem₁ (hide (graph D₁) (at ε))) (interior D₁) .input-entry i ε

    branch-col : ∀ i → M.Matrix (width u) (input-width γ i)
    branch-col i = Br.input-sub (Br.steps (prem₂ (hide (graph D₂) (at ε))) (interior D₂)) i ε

    zero-root : ∀ i → G₁ (inp i) (at ε) ≈ M.εₘ
    zero-root i = ≈-trans (done₁ .root-agrees (inj₂ root) i) (absorb M.εₘ (scrut-col i))

    entries₂ : Br.Entries G₁ (prem₂ (graph D₂))
    entries₂ .inputs i q = branch-rows i q
    entries₂ .block p q = behind₁ .path-keeps p q
    entries₂ .offset _ i = zero-root i
    entries₂ .root-edge _ = behind₁ .root-keeps root ε
    entries₂ .off-edge _ p np = ≈-trans (behind₁ .root-keeps root p) (edge-off M.I p np)
    entries₂ .sink q = root-sink D₂ (at q)

    done₂ : Br.Agrees (hide-all (hide G₁ (at (case-l₂ ε))) (map at (map case-l₂ (interior D₂))))
                      (Br.steps (prem₂ (hide (graph D₂) (at ε))) (interior D₂))
    done₂ = Br.agrees-hide-all (interior D₂) (interior-not-root D₂) (Br.agrees-from entries₂)

    plumb : hide-all (graph E) (map at (paths E))
            ≡ hide-all (hide G₁ (at (case-l₂ ε))) (map at (map case-l₂ (interior D₂)))
    plumb =
      ≡-trans (≡-cong (hide-all (hide (graph E) (at ε)))
                      (map-++ at (map case-l₁ (paths D₁)) (map case-l₂ (paths D₂))))
              (hide-all-++ (hide (graph E) (at ε))
                           (map at (map case-l₁ (paths D₁)))
                           (map at (map case-l₂ (paths D₂))))

    collapsed₂ : ∀ i → Br.steps (prem₂ (hide (graph D₂) (at ε))) (interior D₂) .input-entry i ε
                       ≈ collapse-at D₂ i
    collapsed₂ i = ≈-of-≡ (≡-cong (λ (H : Br.Premise) → H .input-entry i ε)
                                  (folds₂ (interior D₂) (hide (graph D₂) (at ε))))

  agree : ∀ i → collapse-at E i
                ≈ ((collapse-at D₂ environment ∘ Wsub i environment)
                     M.+ₘ (collapse-at D₂ source ∘ Wsub i source))
  agree i =
    ≈-trans (≈-of-≡ (≡-cong (λ G → G (inp i) (at ε)) plumb))
    (≈-trans (done₂ .root-agrees root i)
    (≈-trans (+ₘ-lunit (M.I ∘ branch-col i))
    (≈-trans (id-left {f = branch-col i})
             (+ₘ-cong (∘-cong₁ {g = Wsub i environment} (collapsed₂ environment))
                      (∘-cong₁ {g = Wsub i source} (collapsed₂ source))))))

module CaseR {Γ τ₁ τ₂ τ} {γ : Env Γ} {ts : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
             {v : Val τ₂} {u : Val τ}
             {R : Nat.suc (width-env γ) ⇒ Nat.suc (width v)}
             {S : Nat.suc (width-env (γ · v)) ⇒ width u}
             {D₁ : γ , ts ⇓ inr v [ R ]} {D₂ : γ · v , t₂ ⇓ u [ S ]} where

  private
    E = ⇓-case-r {t₁ = t₁} D₁ D₂

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

  Rt : (q : Path D₂) → M.Matrix (width-at q) (Nat.suc (width v))
  Rt q = ((B q ∘ iᵣ) ∘ p2) M.+ₘ (Bₛ q ∘ p1)

  Wsub : (i i' : Input) → M.Matrix (input-width (γ · v) i') (input-width γ i)
  Wsub environment environment = iₗ M.+ₘ ((iᵣ ∘ p2) ∘ collapse D₁)
  Wsub environment source      = p1 ∘ collapse D₁
  Wsub source      environment = (iᵣ ∘ p2) ∘ collapse-src D₁
  Wsub source      source      = ctrl-row {1} M.+ₘ (p1 ∘ collapse-src D₁)

  private
    Targets : Set ℓ
    Targets = Path D₂ ⊎ Root

    tgt : Targets → Path E
    tgt (inj₁ q) = case-r₂ q
    tgt (inj₂ _) = ε

    P₁ : (n : Targets) → M.Matrix (width-at (tgt n)) (Nat.suc (width v))
    P₁ (inj₁ q) = Rt q
    P₁ (inj₂ _) = M.εₘ

    K₁ : (n : Targets) (i : Input) → M.Matrix (width-at (tgt n)) (input-width γ i)
    K₁ (inj₁ q) environment = B q ∘ iₗ
    K₁ (inj₁ q) source      = Bₛ q ∘ ctrl-row {1}
    K₁ (inj₂ _) _           = M.εₘ

    P₂ : (n : Root) → M.Matrix (width u) (width-at (ε {D = D₂}))
    P₂ _ = M.I

    K₂ : (n : Root) (i : Input) → M.Matrix (width u) (input-width γ i)
    K₂ _ _ = M.εₘ

    module Sc = Single E (case-r₁ {t₁ = t₁} {D₁ = D₁} {D₂ = D₂}) is-ε ε tgt P₁ K₁
    module Br = Under E (γ · v) (case-r₂ {t₁ = t₁} {D₁ = D₁} {D₂ = D₂}) is-ε ε
                      (λ (_ : Root) → ε) Wsub P₂ K₂
    module Bh = Behind E (case-r₁ {t₁ = t₁} {D₁ = D₁} {D₂ = D₂})
                       (case-r₂ {t₁ = t₁} {D₁ = D₁} {D₂ = D₂})
                       (λ (_ : Root) → ε)
                       (λ p q → graph D₂ (at p) (at q))
                       (λ _ p → edge M.I p)

  open Sc.Premise
  open Br.Premise
  open Sc.Agrees
  open Br.Agrees
  open Sc.Entries
  open Br.Entries
  open Bh.Keeps

  private
    prem₁ : Graph D₁ → Sc.Premise
    prem₁ G .input-entry i q = G (inp i) (at q)
    prem₁ G .path-entry p q = G (at p) (at q)

    folds₁ : (ws : List (Path D₁)) (G : Graph D₁) →
             Sc.steps (prem₁ G) ws ≡ prem₁ (hide-all G (map at ws))
    folds₁ = Sc.folds prem₁ at hide (λ G w → ≡-refl)

    prem₂ : Graph D₂ → Br.Premise
    prem₂ G .input-entry i q = G (inp i) (at q)
    prem₂ G .path-entry p q = G (at p) (at q)

    folds₂ : (ws : List (Path D₂)) (G : Graph D₂) →
             Br.steps (prem₂ G) ws ≡ prem₂ (hide-all G (map at ws))
    folds₂ = Br.folds prem₂ at hide (λ G w → ≡-refl)

    G₁ : Graph E
    G₁ = hide-all (hide (hide (graph E) (at ε)) (at (case-r₁ ε)))
                  (map at (map case-r₁ (interior D₁)))

    entries₁ : Sc.Entries (graph E) (prem₁ (graph D₁))
    entries₁ .inputs environment q = ≈-refl
    entries₁ .inputs source q = ≈-refl
    entries₁ .block p q = ≈-refl
    entries₁ .offset (inj₁ q) environment = ≈-refl {f = K₁ (inj₁ q) environment}
    entries₁ .offset (inj₁ q) source = ≈-refl {f = K₁ (inj₁ q) source}
    entries₁ .offset (inj₂ _) environment = ≈-refl {f = M.εₘ}
    entries₁ .offset (inj₂ _) source = ≈-refl {f = M.εₘ}
    entries₁ .root-edge (inj₁ q) = ≈-refl {f = Rt q}
    entries₁ .root-edge (inj₂ _) = ≈-refl {f = M.εₘ}
    entries₁ .off-edge (inj₁ q) p np = edge-off (Rt q) p np
    entries₁ .off-edge (inj₂ _) p np = ≈-refl {f = M.εₘ}
    entries₁ .sink q = root-sink D₁ (at q)

    done₁ : Sc.Agrees G₁ (Sc.steps (prem₁ (hide (graph D₁) (at ε))) (interior D₁))
    done₁ = Sc.agrees-hide-all (interior D₁) (interior-not-root D₁) (Sc.agrees-base entries₁)

    behind₀ : Bh.Keeps (graph E)
    behind₀ .path-keeps p q = ≈-refl
    behind₀ .root-keeps _ p = ≈-refl {f = edge M.I p}
    behind₀ .two-one p q = ≈-refl {f = M.εₘ}

    behind₁ : Bh.Keeps G₁
    behind₁ = Bh.keeps-hide-all (λ w → w) (interior D₁)
                (Bh.keeps-hide ε (Bh.keeps-sink (at ε) (root-sink E) behind₀))

    collapsed₁ : ∀ i → Sc.steps (prem₁ (hide (graph D₁) (at ε))) (interior D₁) .input-entry i ε
                       ≈ collapse-at D₁ i
    collapsed₁ i = ≈-of-≡ (≡-cong (λ (H : Sc.Premise) → H .input-entry i ε)
                                  (folds₁ (interior D₁) (hide (graph D₁) (at ε))))

    route-env : ∀ (q : Path D₂) →
                ((B q ∘ iₗ) M.+ₘ (Rt q ∘ collapse D₁))
                ≈ ((B q ∘ Wsub environment environment) M.+ₘ (Bₛ q ∘ Wsub environment source))
    route-env q =
      ≈-trans (+ₘ-cong (≈-refl {f = B q ∘ iₗ})
                       (M.comp-bilinear₁ ((B q ∘ iᵣ) ∘ p2) (Bₛ q ∘ p1) (collapse D₁)))
      (≈-trans (≈-sym (+ₘ-assoc (B q ∘ iₗ) (((B q ∘ iᵣ) ∘ p2) ∘ collapse D₁)
                                ((Bₛ q ∘ p1) ∘ collapse D₁)))
               (+ₘ-cong (≈-trans (+ₘ-cong (≈-refl {f = B q ∘ iₗ})
                                   (≈-trans (∘-cong₁ {g = collapse D₁} (assoc (B q) iᵣ p2))
                                            (assoc (B q) (iᵣ ∘ p2) (collapse D₁))))
                                 (≈-sym (M.comp-bilinear₂ (B q) iₗ ((iᵣ ∘ p2) ∘ collapse D₁))))
                        (assoc (Bₛ q) p1 (collapse D₁))))

    route-src : ∀ (q : Path D₂) →
                ((Bₛ q ∘ ctrl-row {1}) M.+ₘ (Rt q ∘ collapse-src D₁))
                ≈ ((B q ∘ Wsub source environment) M.+ₘ (Bₛ q ∘ Wsub source source))
    route-src q =
      ≈-trans (+ₘ-cong (≈-refl {f = Bₛ q ∘ ctrl-row {1}})
                       (M.comp-bilinear₁ ((B q ∘ iᵣ) ∘ p2) (Bₛ q ∘ p1) (collapse-src D₁)))
      (≈-trans (+ₘ-swap-mid (Bₛ q ∘ ctrl-row {1}) (((B q ∘ iᵣ) ∘ p2) ∘ collapse-src D₁)
                            ((Bₛ q ∘ p1) ∘ collapse-src D₁))
               (+ₘ-cong (≈-trans (∘-cong₁ {g = collapse-src D₁} (assoc (B q) iᵣ p2))
                                 (assoc (B q) (iᵣ ∘ p2) (collapse-src D₁)))
                        (≈-trans (+ₘ-cong (≈-refl {f = Bₛ q ∘ ctrl-row {1}})
                                          (assoc (Bₛ q) p1 (collapse-src D₁)))
                                 (≈-sym (M.comp-bilinear₂ (Bₛ q) (ctrl-row {1})
                                                          (p1 ∘ collapse-src D₁))))))

    branch-rows : ∀ i q → G₁ (inp i) (at (case-r₂ q)) ≈ Br.input-sub (prem₂ (graph D₂)) i q
    branch-rows environment q =
      ≈-trans (done₁ .root-agrees (inj₁ q) environment)
      (≈-trans (Sc.root-cong (inj₁ q) environment (collapsed₁ environment)) (route-env q))
    branch-rows source q =
      ≈-trans (done₁ .root-agrees (inj₁ q) source)
      (≈-trans (Sc.root-cong (inj₁ q) source (collapsed₁ source)) (route-src q))

    scrut-col : ∀ i → M.Matrix (Nat.suc (width v)) (input-width γ i)
    scrut-col i = Sc.steps (prem₁ (hide (graph D₁) (at ε))) (interior D₁) .input-entry i ε

    branch-col : ∀ i → M.Matrix (width u) (input-width γ i)
    branch-col i = Br.input-sub (Br.steps (prem₂ (hide (graph D₂) (at ε))) (interior D₂)) i ε

    zero-root : ∀ i → G₁ (inp i) (at ε) ≈ M.εₘ
    zero-root i = ≈-trans (done₁ .root-agrees (inj₂ root) i) (absorb M.εₘ (scrut-col i))

    entries₂ : Br.Entries G₁ (prem₂ (graph D₂))
    entries₂ .inputs i q = branch-rows i q
    entries₂ .block p q = behind₁ .path-keeps p q
    entries₂ .offset _ i = zero-root i
    entries₂ .root-edge _ = behind₁ .root-keeps root ε
    entries₂ .off-edge _ p np = ≈-trans (behind₁ .root-keeps root p) (edge-off M.I p np)
    entries₂ .sink q = root-sink D₂ (at q)

    done₂ : Br.Agrees (hide-all (hide G₁ (at (case-r₂ ε))) (map at (map case-r₂ (interior D₂))))
                      (Br.steps (prem₂ (hide (graph D₂) (at ε))) (interior D₂))
    done₂ = Br.agrees-hide-all (interior D₂) (interior-not-root D₂) (Br.agrees-from entries₂)

    plumb : hide-all (graph E) (map at (paths E))
            ≡ hide-all (hide G₁ (at (case-r₂ ε))) (map at (map case-r₂ (interior D₂)))
    plumb =
      ≡-trans (≡-cong (hide-all (hide (graph E) (at ε)))
                      (map-++ at (map case-r₁ (paths D₁)) (map case-r₂ (paths D₂))))
              (hide-all-++ (hide (graph E) (at ε))
                           (map at (map case-r₁ (paths D₁)))
                           (map at (map case-r₂ (paths D₂))))

    collapsed₂ : ∀ i → Br.steps (prem₂ (hide (graph D₂) (at ε))) (interior D₂) .input-entry i ε
                       ≈ collapse-at D₂ i
    collapsed₂ i = ≈-of-≡ (≡-cong (λ (H : Br.Premise) → H .input-entry i ε)
                                  (folds₂ (interior D₂) (hide (graph D₂) (at ε))))

  agree : ∀ i → collapse-at E i
                ≈ ((collapse-at D₂ environment ∘ Wsub i environment)
                     M.+ₘ (collapse-at D₂ source ∘ Wsub i source))
  agree i =
    ≈-trans (≈-of-≡ (≡-cong (λ G → G (inp i) (at ε)) plumb))
    (≈-trans (done₂ .root-agrees root i)
    (≈-trans (+ₘ-lunit (M.I ∘ branch-col i))
    (≈-trans (id-left {f = branch-col i})
             (+ₘ-cong (∘-cong₁ {g = Wsub i environment} (collapsed₂ environment))
                      (∘-cong₁ {g = Wsub i source} (collapsed₂ source))))))

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
