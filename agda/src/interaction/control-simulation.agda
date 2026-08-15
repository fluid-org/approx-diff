{-# OPTIONS --prop --postfix-projections --safe #-}

open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- Agreement for a rule whose single premise is evaluated in the conclusion's environment. The
-- conclusion's graph carries the premise's graph on the image of the premise's paths, and its root
-- column is the premise's root column composed with a fixed matrix, offset at each input vertex.
-- That statement is closed under hiding an image path, so hiding the premise's paths one by one
-- carries it from the conclusion's graph to the conclusion's collapse.
module interaction.control-simulation {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig two.semiring 𝒫 two.I
  using (Val; Env; width; width-env)
open import language-operational.control Sig two.semiring 𝒫 two.I
open import interaction.control-path Sig 𝒫
open import interaction.control-graph Sig 𝒫
open import interaction.control-hide Sig 𝒫

private
  module M = matrix.Mat two.semiring

import Data.Bool as Bool
import Data.Nat as Nat
open import Data.List using (List; []; _∷_; map; foldl)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import categories using (Category)
open Category M.cat using (_⇒_; _∘_; _≈_; ∘-cong; ∘-cong₁; ∘-cong₂; ≈-refl; ≈-sym; ≈-trans)
open import interaction.control-agreement-algebra Sig 𝒫
  using (absorb; +ₘ-cong; +ₘ-lunit; root-step; offset-step; hide-root; keep-l; keep-r)

module Single
  {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v : Val τ} {R : Nat.suc (width-env γ) ⇒ width v}
  (E : γ , t ⇓ v [ R ])
  {Q : Set ℓ} (j : Q → Path E) (root? : Q → Bool.Bool) (q₀ : Q)
  (P : M.Matrix (width v) (width-at (j q₀)))
  (K : (i : Input) → M.Matrix (width v) (input-width γ i))
  where

  -- The premise's graph, read through the injection: its input rows and its path block. The two are
  -- kept apart because the injection maps input vertices to themselves and paths through j.
  record Premise : Set ℓ where
    field
      input-entry : (i : Input) (q : Q) → M.Matrix (width-at (j q)) (input-width γ i)
      path-entry  : (p q : Q) → M.Matrix (width-at (j q)) (width-at (j p))

  open Premise

  step : Premise → Q → Premise
  step H w .input-entry i q = H .input-entry i q M.+ₘ (H .path-entry w q ∘ H .input-entry i w)
  step H w .path-entry p q = H .path-entry p q M.+ₘ (H .path-entry w q ∘ H .path-entry p w)

  steps : Premise → List Q → Premise
  steps = foldl step

  record Agrees (G : Graph E) (H : Premise) : Set ℓ where
    field
      input-agrees : ∀ i q → G (inp i) (at (j q)) ≈ H .input-entry i q
      path-agrees  : ∀ p q → G (at (j p)) (at (j q)) ≈ H .path-entry p q
      root-agrees  : ∀ i → G (inp i) (at ε) ≈ (K i M.+ₘ (P ∘ H .input-entry i q₀))
      edge-agrees  : ∀ p → root? p ≡ Bool.false → G (at (j p)) (at ε) ≈ (P ∘ H .path-entry p q₀)

  open Agrees

  agrees-hide : ∀ {G H} (w : Q) → root? w ≡ Bool.false →
                Agrees G H → Agrees (hide G (at (j w))) (step H w)
  agrees-hide w nw s .input-agrees i q =
    +ₘ-cong (s .input-agrees i q) (∘-cong (s .path-agrees w q) (s .input-agrees i w))
  agrees-hide w nw s .path-agrees p q =
    +ₘ-cong (s .path-agrees p q) (∘-cong (s .path-agrees w q) (s .path-agrees p w))
  agrees-hide {H = H} w nw s .root-agrees i =
    offset-step {K = K i} {P = P} {X = H .input-entry i q₀} {Y = H .path-entry w q₀}
                {Z = H .input-entry i w}
      (s .root-agrees i) (s .edge-agrees w nw) (s .input-agrees i w)
  agrees-hide {H = H} w nw s .edge-agrees p np =
    root-step {P = P} {X = H .path-entry p q₀} {Y = H .path-entry w q₀} {Z = H .path-entry p w}
      (s .edge-agrees p np) (s .edge-agrees w nw) (s .path-agrees p w)

  -- Unification cannot invert _+ₘ_, so the two summands are supplied.
  root-cong : ∀ (i : Input) {C C' : M.Matrix (width-at (j q₀)) (input-width γ i)} → C ≈ C' →
              (K i M.+ₘ (P ∘ C)) ≈ (K i M.+ₘ (P ∘ C'))
  root-cong i {C} {C'} h =
    +ₘ-cong {R = K i} {R' = K i} {S = P ∘ C} {S' = P ∘ C'} ≈-refl (∘-cong₂ h)

  agrees-hide-all : ∀ {G H} (ws : List Q) → All (λ w → root? w ≡ Bool.false) ws →
                    Agrees G H → Agrees (hide-all G (map at (map j ws))) (steps H ws)
  agrees-hide-all []       []         s = s
  agrees-hide-all (w ∷ ws) (nw ∷ nws) s = agrees-hide-all ws nws (agrees-hide w nw s)

  -- The rule's defining entries for this premise, read off a graph. The last field says the
  -- premise's root is a sink.
  record Rule (G : Graph E) (H : Premise) : Set ℓ where
    field
      rule-input : ∀ i q → G (inp i) (at (j q)) ≈ H .input-entry i q
      rule-path  : ∀ p q → G (at (j p)) (at (j q)) ≈ H .path-entry p q
      rule-root  : ∀ i → G (inp i) (at ε) ≈ K i
      rule-edge  : G (at (j q₀)) (at ε) ≈ P
      rule-off   : ∀ p → root? p ≡ Bool.false → G (at (j p)) (at ε) ≈ M.εₘ
      rule-sink  : ∀ q → H .path-entry q₀ q ≈ M.εₘ

  open Rule

  agrees-from : ∀ {G H} → Rule G H → Agrees (hide G (at (j q₀))) (step H q₀)
  agrees-from r .input-agrees i q =
    +ₘ-cong (r .rule-input i q) (∘-cong (r .rule-path q₀ q) (r .rule-input i q₀))
  agrees-from r .path-agrees p q =
    +ₘ-cong (r .rule-path p q) (∘-cong (r .rule-path q₀ q) (r .rule-path p q₀))
  agrees-from {H = H} r .root-agrees i =
    ≈-trans (+ₘ-cong (r .rule-root i) (∘-cong (r .rule-edge) (r .rule-input i q₀)))
            (+ₘ-cong ≈-refl (∘-cong₂ (≈-sym (sink-input i))))
    where
    sink-input : ∀ i → step H q₀ .input-entry i q₀ ≈ H .input-entry i q₀
    sink-input i =
      ≈-trans (+ₘ-cong ≈-refl (∘-cong₁ (r .rule-sink q₀)))
              (absorb (H .input-entry i q₀) (H .input-entry i q₀))
  agrees-from {H = H} r .edge-agrees p np =
    ≈-trans (+ₘ-cong (r .rule-off p np) (∘-cong (r .rule-edge) (r .rule-path p q₀)))
    (≈-trans (+ₘ-lunit (P ∘ H .path-entry p q₀))
             (∘-cong₂ (≈-sym sink-path)))
    where
    sink-path : step H q₀ .path-entry p q₀ ≈ H .path-entry p q₀
    sink-path =
      ≈-trans (+ₘ-cong ≈-refl (∘-cong₁ (r .rule-sink q₀)))
              (absorb (H .path-entry p q₀) (H .path-entry p q₀))

  rule-hide-root : ∀ {H} → Rule (graph E) H → Rule (hide (graph E) (at ε)) H
  rule-hide-root r .rule-input i q = ≈-trans (hide-root E (inp i) (at (j q))) (r .rule-input i q)
  rule-hide-root r .rule-path p q = ≈-trans (hide-root E (at (j p)) (at (j q))) (r .rule-path p q)
  rule-hide-root r .rule-root i = ≈-trans (hide-root E (inp i) (at ε)) (r .rule-root i)
  rule-hide-root r .rule-edge = ≈-trans (hide-root E (at (j q₀)) (at ε)) (r .rule-edge)
  rule-hide-root r .rule-off p np = ≈-trans (hide-root E (at (j p)) (at ε)) (r .rule-off p np)
  rule-hide-root r .rule-sink q = r .rule-sink q

  agrees-base : ∀ {H} → Rule (graph E) H →
                Agrees (hide (hide (graph E) (at ε)) (at (j q₀))) (step H q₀)
  agrees-base r = agrees-from (rule-hide-root r)

-- A rule with two premises whose blocks are unlinked. While the first block's paths are hidden, the
-- second block's entries and the two zero blocks between them are undisturbed, so the second block
-- is in its rule position when its own phase begins.
module Apart
  {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v : Val τ} {R : Nat.suc (width-env γ) ⇒ width v}
  (E : γ , t ⇓ v [ R ])
  {Q₁ : Set ℓ} (j₁ : Q₁ → Path E)
  {Q₂ : Set ℓ} (j₂ : Q₂ → Path E)
  (B-input : (i : Input) (q : Q₂) → M.Matrix (width-at (j₂ q)) (input-width γ i))
  (B-path : (p q : Q₂) → M.Matrix (width-at (j₂ q)) (width-at (j₂ p)))
  (B-root : (p : Q₂) → M.Matrix (width v) (width-at (j₂ p)))
  where

  record Keeps (G : Graph E) : Set ℓ where
    field
      input-keeps : ∀ i q → G (inp i) (at (j₂ q)) ≈ B-input i q
      path-keeps  : ∀ p q → G (at (j₂ p)) (at (j₂ q)) ≈ B-path p q
      root-keeps  : ∀ p → G (at (j₂ p)) (at ε) ≈ B-root p
      one-two     : ∀ p q → G (at (j₁ p)) (at (j₂ q)) ≈ M.εₘ
      two-one     : ∀ p q → G (at (j₂ p)) (at (j₁ q)) ≈ M.εₘ

  open Keeps

  -- Hiding a sink disturbs nothing.
  keeps-sink : ∀ {G} (r : Vertex E) → (∀ y → G r y ≈ M.εₘ) → Keeps G → Keeps (hide G r)
  keeps-sink r z k .input-keeps i q = keep-l (k .input-keeps i q) (z (at (j₂ q)))
  keeps-sink r z k .path-keeps p q = keep-l (k .path-keeps p q) (z (at (j₂ q)))
  keeps-sink r z k .root-keeps p = keep-l (k .root-keeps p) (z (at ε))
  keeps-sink r z k .one-two p q = keep-l (k .one-two p q) (z (at (j₂ q)))
  keeps-sink r z k .two-one p q = keep-l (k .two-one p q) (z (at (j₁ q)))

  keeps-hide : ∀ {G} (w : Q₁) → Keeps G → Keeps (hide G (at (j₁ w)))
  keeps-hide w k .input-keeps i q = keep-l (k .input-keeps i q) (k .one-two w q)
  keeps-hide w k .path-keeps p q = keep-l (k .path-keeps p q) (k .one-two w q)
  keeps-hide w k .root-keeps p = keep-r (k .root-keeps p) (k .two-one p w)
  keeps-hide w k .one-two p q = keep-l (k .one-two p q) (k .one-two w q)
  keeps-hide w k .two-one p q = keep-r (k .two-one p q) (k .two-one p w)

  keeps-hide-all : ∀ {G} (ws : List Q₁) → Keeps G → Keeps (hide-all G (map at (map j₁ ws)))
  keeps-hide-all []       k = k
  keeps-hide-all (w ∷ ws) k = keeps-hide-all ws (keeps-hide w k)
