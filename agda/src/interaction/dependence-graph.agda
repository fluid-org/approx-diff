{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Bool as Bool
open Bool using (Bool)
open import Data.Fin using (zero)
open import Data.Nat using (ℕ; suc; _+_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (sym)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import every using (Every; []; _∷_)
open import prop-setoid using () renaming (_⇒_ to _⇒ₛ_)
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- The dependence graph of a control-source derivation. Each rule builds its graph from its
-- premises' graphs using the wiring that also defines the rule's relation, so collapsing the graph
-- recovers the relation rule by rule.
module interaction.dependence-graph {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open _⇒ₛ_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-operational.evaluation Sig two.semiring 𝒫 two.I
  using (Val; Env; width; width-env; width-subst; ctrl-row; proj-var; bool→val; brel-deps)
open Val
open Env
open import language-operational.control Sig two.semiring 𝒫 two.I
open import interaction.graph-algebra

private
  module M = matrix.Mat two.semiring

open import categories using (Category)
open Category M.cat using (_≈_; ≈-sym; ≈-trans)

-- The value at a vertex is first-order when the type of the subderivation's conclusion is.
fo-of : ∀ {Δ} (τ : type Δ) → Bool
fo-of τ = ⌊ first-order? τ ⌋

mutual
  graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} → γ , t ⇓ v [ R ] →
          Graph Input (input-width γ) (width v)
  graph {τ = τ} (⇓-var {γ = γ} x) = Rule₀.E (fo-of τ) (var-out x γ)
  graph {τ = τ} (⇓-unit {γ = γ}) = Rule₀.E (fo-of τ) (unit-out γ)
  graph {τ = τ} (⇓-lam {γ = γ} {t = t}) = Rule₀.E (fo-of τ) (lam-out γ t)
  graph {τ = τ} (⇓-inl {γ = γ} {v = v} D) =
    Rule₁.E (graph D) (M.id-linear (input-width γ)) (fo-of τ) (built-out γ (width v)) (M.in₂ {1})
  graph {τ = τ} (⇓-inr {γ = γ} {v = v} D) =
    Rule₁.E (graph D) (M.id-linear (input-width γ)) (fo-of τ) (built-out γ (width v)) (M.in₂ {1})
  graph {τ = τ} (⇓-case-l {γ = γ} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph D₂) (M.id-linear (input-width γ)) (branch-route γ v)
          (branch-link γ v) (fo-of τ) (λ _ → M.εₘ) M.εₘ M.I
  graph {τ = τ} (⇓-case-r {γ = γ} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph D₂) (M.id-linear (input-width γ)) (branch-route γ v)
          (branch-link γ v) (fo-of τ) (λ _ → M.εₘ) M.εₘ M.I
  graph {τ = τ} (⇓-pair {γ = γ} {v = v} {u = u} D₁ D₂) =
    Rule₂.E (graph D₁) (graph D₂) (M.id-linear (input-width γ)) (M.id-linear (input-width γ))
          (M.no-link (input-width γ) (width v)) (fo-of τ) (built-out γ (width v + width u))
          (M.in₂ {1} M.∘ M.in₁ {width v} {width u}) (M.in₂ {1} M.∘ M.in₂ {width v} {width u})
  graph {τ = τ} (⇓-fst {γ = γ} {v = v} {u = u} D) =
    Rule₁.E (graph D) (M.id-linear (input-width γ)) (fo-of τ) (elim-out γ (width v))
          (proj-up {width v} {width u} (M.p₁ {width v} {width u}))
  graph {τ = τ} (⇓-snd {γ = γ} {v = v} {u = u} D) =
    Rule₁.E (graph D) (M.id-linear (input-width γ)) (fo-of τ) (elim-out γ (width u))
          (proj-up {width v} {width u} (M.p₂ {width v} {width u}))
  graph {τ = τ} (⇓-app {γ = γ} {γ' = γ'} {v = v} D₁ D₂ D₃) =
    Rule₃.E (graph D₁) (graph D₂) (graph D₃) (M.id-linear (input-width γ))
           (M.id-linear (input-width γ)) (body-route γ γ' v) (body-link₁ γ' v) (body-link₂ γ' v)
           (fo-of τ) (λ _ → M.εₘ) M.εₘ M.εₘ M.I
  graph {τ = τ} (⇓-bop {γ = γ} {ω = ω} {vs = vs} D) =
    Rule₁.E (graph-s D) (M.id-linear (input-width γ)) (fo-of τ)
          (prim-out γ (width (const (op-fun ω .func vs)))) (op-deps ω .func vs)
  graph {τ = τ} (⇓-brel {γ = γ} {ω = ω} {vs = vs} D) =
    Rule₁.E (graph-s D) (M.id-linear (input-width γ)) (fo-of τ)
          (prim-out γ (width (bool→val (rel-pred ω .func vs))))
          (brel-deps ω vs (rel-pred ω .func vs))
  graph {τ = τ} (⇓-roll {γ = γ} D) =
    Rule₁.E (graph D) (M.id-linear (input-width γ)) (fo-of τ) (λ _ → M.εₘ) M.I
  graph {τ = τ} (⇓-fold {γ = γ} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph-m D₂) (M.id-linear (input-width γ)) (fold-route γ (width v))
          (fold-link γ (width v)) (fo-of τ) (λ _ → M.εₘ) M.εₘ M.I

  graph-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
            γ , Ms ⇓s vs [ R ] → Graph Input (input-width γ) (bases-width is)
  graph-s {γ = γ} [] = Rule₀.E Bool.true (λ _ → M.εₘ)
  graph-s {γ = γ} (_∷_ {is = is} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph-s D₂) (M.id-linear (input-width γ)) (M.id-linear (input-width γ))
          (M.no-link (input-width γ) (width (const v))) Bool.true (λ _ → M.εₘ)
          (M.in₁ {width (const v)} {bases-width is}) (M.in₂ {width (const v)} {bases-width is})

  graph-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {v' : Val (σ' [ σr ])} {F} →
            Map γ s σ' v v' F → Graph InputM (inputM-width γ (width v)) (width v')
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-rec {w = w} {w' = w'} D₁ D₂) =
    Rule₂.E (graph-m D₁) (graph D₂) (M.id-linear (inputM-width γ (width w))) (rec-route γ w')
          (rec-link γ w') (fo-of (σ' [ σr ])) (λ _ → M.εₘ) M.εₘ M.I
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-unit {v = v}) = Rule₀.E (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-base {v = v}) = Rule₀.E (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-arrow {v = v}) = Rule₀.E (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-inl {v = v} {v' = v'} D) =
    Rule₁.E (graph-m D) (input-route γ (M.p₂ {1} {width v})) (fo-of (σ' [ σr ]))
          (map-built-out γ (width v) (width v')) (M.in₂ {1})
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-inr {v = v} {v' = v'} D) =
    Rule₁.E (graph-m D) (input-route γ (M.p₂ {1} {width v})) (fo-of (σ' [ σr ]))
          (map-built-out γ (width v) (width v')) (M.in₂ {1})
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-pair {v = v} {v' = v'} {u = u} {u' = u'} D₁ D₂) =
    Rule₂.E (graph-m D₁) (graph-m D₂)
          (input-route γ (M.p₁ {width v} {width u} M.∘ M.p₂ {1} {width v + width u}))
          (input-route γ (M.p₂ {width v} {width u} M.∘ M.p₂ {1} {width v + width u}))
          (M.no-link (inputM-width γ (width u)) (width v')) (fo-of (σ' [ σr ]))
          (map-built-out γ (width v + width u) (width v' + width u'))
          (M.in₂ {1} M.∘ M.in₁ {width v'} {width u'})
          (M.in₂ {1} M.∘ M.in₂ {width v'} {width u'})
  graph-m {γ = γ} {τ₀ = τ₀} {σr = σr} {σ' = σ'} (m-mu {τ' = τ'} {w = w} {w' = w'} D) =
    Rule₁.E (graph-m D)
          (input-route γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) M.I))
          (fo-of (σ' [ σr ])) (λ _ → M.εₘ) (rcast (sym (width-subst (unfold₁-inst τ' σr) w')) M.I)


-- Chaining a combinator's collapse law with the induction hypotheses and the round trip through
-- the rule's relation.
private
  step-one : ∀ {Γ} {γ : Env Γ} {Inp' : Set} {iw' : Inp' → ℕ} {n n₀}
             (route : M.Linear iw' (input-width γ))
             (out : (i : Input) → M.Matrix n (input-width γ i)) (up : M.Matrix n n₀)
             {c c' : (i' : Inp') → M.Matrix n₀ (iw' i')} → (∀ i' → c i' ≈ c' i') →
             ∀ i → M.rule₁-result route out up c i ≈ cols (of-cols (M.rule₁-result route out up c')) i
  step-one route out up e i =
    ≈-trans (M.one-result-cong route {out = out} {up = up} e i)
            (≈-sym (cols-of-cols (M.rule₁-result route out up _) i))

  step-seq : ∀ {Γ} {γ : Env Γ} {Inp₁ Inp₂ : Set} {iw₁ : Inp₁ → ℕ} {iw₂ : Inp₂ → ℕ} {n n₁ n₂}
             (r₁ : M.Linear iw₁ (input-width γ)) (r₂ : M.Linear iw₂ (input-width γ))
             (l : M.Link iw₂ n₁) (out : (i : Input) → M.Matrix n (input-width γ i))
             (u₁ : M.Matrix n n₁) (u₂ : M.Matrix n n₂)
             {c₁ c₁' : (i' : Inp₁) → M.Matrix n₁ (iw₁ i')}
             {c₂ c₂' : (i' : Inp₂) → M.Matrix n₂ (iw₂ i')} →
             (∀ i' → c₁ i' ≈ c₁' i') → (∀ i' → c₂ i' ≈ c₂' i') →
             ∀ i → M.rule₂-result r₁ r₂ l out u₁ u₂ c₁ c₂ i
                   ≈ cols (of-cols (M.rule₂-result r₁ r₂ l out u₁ u₂ c₁' c₂')) i
  step-seq r₁ r₂ l out u₁ u₂ e₁ e₂ i =
    ≈-trans (M.seq-result-cong r₁ r₂ l {out = out} {u₁ = u₁} {u₂ = u₂} e₁ e₂ i)
            (≈-sym (cols-of-cols (M.rule₂-result r₁ r₂ l out u₁ u₂ _ _) i))

  step-seq3 : ∀ {Γ} {γ : Env Γ} {Inp₁ Inp₂ Inp₃ : Set}
              {iw₁ : Inp₁ → ℕ} {iw₂ : Inp₂ → ℕ} {iw₃ : Inp₃ → ℕ} {n n₁ n₂ n₃}
              (r₁ : M.Linear iw₁ (input-width γ)) (r₂ : M.Linear iw₂ (input-width γ))
              (r₃ : M.Linear iw₃ (input-width γ)) (l₁ : M.Link iw₃ n₁) (l₂ : M.Link iw₃ n₂)
              (out : (i : Input) → M.Matrix n (input-width γ i))
              (u₁ : M.Matrix n n₁) (u₂ : M.Matrix n n₂) (u₃ : M.Matrix n n₃)
              {c₁ c₁' : (i' : Inp₁) → M.Matrix n₁ (iw₁ i')}
              {c₂ c₂' : (i' : Inp₂) → M.Matrix n₂ (iw₂ i')}
              {c₃ c₃' : (i' : Inp₃) → M.Matrix n₃ (iw₃ i')} →
              (∀ i' → c₁ i' ≈ c₁' i') → (∀ i' → c₂ i' ≈ c₂' i') → (∀ i' → c₃ i' ≈ c₃' i') →
              ∀ i → M.rule₃-result r₁ r₂ r₃ l₁ l₂ out u₁ u₂ u₃ c₁ c₂ c₃ i
                    ≈ cols (of-cols (M.rule₃-result r₁ r₂ r₃ l₁ l₂ out u₁ u₂ u₃ c₁' c₂' c₃')) i
  step-seq3 r₁ r₂ r₃ l₁ l₂ out u₁ u₂ u₃ e₁ e₂ e₃ i =
    ≈-trans (M.seq3-result-cong r₁ r₂ r₃ l₁ l₂ {out = out} {u₁ = u₁} {u₂ = u₂} {u₃ = u₃}
                                e₁ e₂ e₃ i)
            (≈-sym (cols-of-cols (M.rule₃-result r₁ r₂ r₃ l₁ l₂ out u₁ u₂ u₃ _ _ _) i))

-- Collapsing a derivation's graph recovers the relation the rules build.
mutual
  agree : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) (i : Input) →
          collapse (graph D) i ≈ cols R i
  agree {τ = τ} (⇓-var {γ = γ} x) i =
    ≈-trans (Rule₀.agree (fo-of τ) (var-out x γ) i) (≈-sym (cols-of-cols (var-out x γ) i))
  agree {τ = τ} (⇓-unit {γ = γ}) i =
    ≈-trans (Rule₀.agree (fo-of τ) (unit-out γ) i) (≈-sym (cols-of-cols (unit-out γ) i))
  agree {τ = τ} (⇓-lam {γ = γ} {t = t}) i =
    ≈-trans (Rule₀.agree (fo-of τ) (lam-out γ t) i) (≈-sym (cols-of-cols (lam-out γ t) i))
  agree {τ = τ} (⇓-inl {γ = γ} {v = v} D) i =
    ≈-trans (Rule₁.agree (graph D) (M.id-linear (input-width γ)) (fo-of τ) (built-out γ (width v))
                       (M.in₂ {1}) i)
            (step-one (M.id-linear (input-width γ)) (built-out γ (width v)) (M.in₂ {1})
                      (agree D) i)
  agree {τ = τ} (⇓-inr {γ = γ} {v = v} D) i =
    ≈-trans (Rule₁.agree (graph D) (M.id-linear (input-width γ)) (fo-of τ) (built-out γ (width v))
                       (M.in₂ {1}) i)
            (step-one (M.id-linear (input-width γ)) (built-out γ (width v)) (M.in₂ {1})
                      (agree D) i)
  agree {τ = τ} (⇓-case-l {γ = γ} {v = v} D₁ D₂) i =
    ≈-trans (Rule₂.agree (graph D₁) (graph D₂) (M.id-linear (input-width γ)) (branch-route γ v)
                       (branch-link γ v) (fo-of τ) (λ _ → M.εₘ) M.εₘ M.I i)
            (step-seq (M.id-linear (input-width γ)) (branch-route γ v) (branch-link γ v)
                      (λ _ → M.εₘ) M.εₘ M.I (agree D₁) (agree D₂) i)
  agree {τ = τ} (⇓-case-r {γ = γ} {v = v} D₁ D₂) i =
    ≈-trans (Rule₂.agree (graph D₁) (graph D₂) (M.id-linear (input-width γ)) (branch-route γ v)
                       (branch-link γ v) (fo-of τ) (λ _ → M.εₘ) M.εₘ M.I i)
            (step-seq (M.id-linear (input-width γ)) (branch-route γ v) (branch-link γ v)
                      (λ _ → M.εₘ) M.εₘ M.I (agree D₁) (agree D₂) i)
  agree {τ = τ} (⇓-pair {γ = γ} {v = v} {u = u} D₁ D₂) i =
    ≈-trans (Rule₂.agree (graph D₁) (graph D₂) (M.id-linear (input-width γ))
                       (M.id-linear (input-width γ)) (M.no-link (input-width γ) (width v))
                       (fo-of τ) (built-out γ (width v + width u))
                       (M.in₂ {1} M.∘ M.in₁ {width v} {width u})
                       (M.in₂ {1} M.∘ M.in₂ {width v} {width u}) i)
            (step-seq (M.id-linear (input-width γ)) (M.id-linear (input-width γ))
                      (M.no-link (input-width γ) (width v)) (built-out γ (width v + width u))
                      (M.in₂ {1} M.∘ M.in₁ {width v} {width u})
                      (M.in₂ {1} M.∘ M.in₂ {width v} {width u}) (agree D₁) (agree D₂) i)
  agree {τ = τ} (⇓-fst {γ = γ} {v = v} {u = u} D) i =
    ≈-trans (Rule₁.agree (graph D) (M.id-linear (input-width γ)) (fo-of τ) (elim-out γ (width v))
                       (proj-up {width v} {width u} (M.p₁ {width v} {width u})) i)
            (step-one (M.id-linear (input-width γ)) (elim-out γ (width v))
                      (proj-up {width v} {width u} (M.p₁ {width v} {width u})) (agree D) i)
  agree {τ = τ} (⇓-snd {γ = γ} {v = v} {u = u} D) i =
    ≈-trans (Rule₁.agree (graph D) (M.id-linear (input-width γ)) (fo-of τ) (elim-out γ (width u))
                       (proj-up {width v} {width u} (M.p₂ {width v} {width u})) i)
            (step-one (M.id-linear (input-width γ)) (elim-out γ (width u))
                      (proj-up {width v} {width u} (M.p₂ {width v} {width u})) (agree D) i)
  agree {τ = τ} (⇓-app {γ = γ} {γ' = γ'} {v = v} D₁ D₂ D₃) i =
    ≈-trans (Rule₃.agree (graph D₁) (graph D₂) (graph D₃) (M.id-linear (input-width γ))
                        (M.id-linear (input-width γ)) (body-route γ γ' v) (body-link₁ γ' v)
                        (body-link₂ γ' v) (fo-of τ) (λ _ → M.εₘ) M.εₘ M.εₘ M.I i)
            (step-seq3 (M.id-linear (input-width γ)) (M.id-linear (input-width γ))
                       (body-route γ γ' v) (body-link₁ γ' v) (body-link₂ γ' v)
                       (λ _ → M.εₘ) M.εₘ M.εₘ M.I (agree D₁) (agree D₂) (agree D₃) i)
  agree {τ = τ} (⇓-bop {γ = γ} {ω = ω} {vs = vs} D) i =
    ≈-trans (Rule₁.agree (graph-s D) (M.id-linear (input-width γ))
                       (fo-of τ) (prim-out γ (width (const (op-fun ω .func vs)))) (op-deps ω .func vs) i)
            (step-one (M.id-linear (input-width γ))
                      (prim-out γ (width (const (op-fun ω .func vs)))) (op-deps ω .func vs)
                      (agree-s D) i)
  agree {τ = τ} (⇓-brel {γ = γ} {ω = ω} {vs = vs} D) i =
    ≈-trans (Rule₁.agree (graph-s D) (M.id-linear (input-width γ))
                       (fo-of τ) (prim-out γ (width (bool→val (rel-pred ω .func vs))))
                       (brel-deps ω vs (rel-pred ω .func vs)) i)
            (step-one (M.id-linear (input-width γ))
                      (prim-out γ (width (bool→val (rel-pred ω .func vs))))
                      (brel-deps ω vs (rel-pred ω .func vs)) (agree-s D) i)
  agree {τ = τ} (⇓-roll {γ = γ} D) i =
    ≈-trans (Rule₁.agree (graph D) (M.id-linear (input-width γ)) (fo-of τ) (λ _ → M.εₘ) M.I i)
            (step-one (M.id-linear (input-width γ)) (λ _ → M.εₘ) M.I (agree D) i)
  agree {τ = τ} (⇓-fold {γ = γ} {v = v} D₁ D₂) i =
    ≈-trans (Rule₂.agree (graph D₁) (graph-m D₂) (M.id-linear (input-width γ))
                       (fold-route γ (width v)) (fold-link γ (width v)) (fo-of τ) (λ _ → M.εₘ) M.εₘ M.I i)
            (step-seq (M.id-linear (input-width γ)) (fold-route γ (width v))
                      (fold-link γ (width v)) (λ _ → M.εₘ) M.εₘ M.I (agree D₁) (agree-m D₂) i)

  agree-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
            (D : γ , Ms ⇓s vs [ R ]) (i : Input) → collapse (graph-s D) i ≈ cols R i
  agree-s {γ = γ} [] i =
    ≈-trans (Rule₀.agree {iw = input-width γ} Bool.true (λ _ → M.εₘ) i)
            (≈-sym (cols-of-cols {γ = γ} (λ _ → M.εₘ) i))
  agree-s {γ = γ} (_∷_ {is = is} {v = v} D₁ D₂) i =
    ≈-trans (Rule₂.agree (graph D₁) (graph-s D₂) (M.id-linear (input-width γ))
                       (M.id-linear (input-width γ)) (M.no-link (input-width γ) (width (const v)))
                       Bool.true (λ _ → M.εₘ) (M.in₁ {width (const v)} {bases-width is})
                       (M.in₂ {width (const v)} {bases-width is}) i)
            (step-seq (M.id-linear (input-width γ)) (M.id-linear (input-width γ))
                      (M.no-link (input-width γ) (width (const v))) (λ _ → M.εₘ)
                      (M.in₁ {width (const v)} {bases-width is})
                      (M.in₂ {width (const v)} {bases-width is}) (agree D₁) (agree-s D₂) i)

  agree-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {v' : Val (σ' [ σr ])} {F}
            (D : Map γ s σ' v v' F) (i : InputM) → collapse (graph-m D) i ≈ F i
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-rec {w = w} {w' = w'} D₁ D₂) i =
    ≈-trans (Rule₂.agree (graph-m D₁) (graph D₂) (M.id-linear (inputM-width γ (width w)))
                       (rec-route γ w') (rec-link γ w') (fo-of (σ' [ σr ])) (λ _ → M.εₘ) M.εₘ M.I i)
            (M.seq-result-cong (M.id-linear (inputM-width γ (width w))) (rec-route γ w')
                               (rec-link γ w') (agree-m D₁) (agree D₂) i)
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-unit {v = v}) i = Rule₀.agree (fo-of (σ' [ σr ])) (map-leaf γ (width v)) i
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-base {v = v}) i = Rule₀.agree (fo-of (σ' [ σr ])) (map-leaf γ (width v)) i
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-arrow {v = v}) i = Rule₀.agree (fo-of (σ' [ σr ])) (map-leaf γ (width v)) i
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-inl {v = v} {v' = v'} D) i =
    ≈-trans (Rule₁.agree (graph-m D) (input-route γ (M.p₂ {1} {width v}))
                       (fo-of (σ' [ σr ])) (map-built-out γ (width v) (width v')) (M.in₂ {1}) i)
            (M.one-result-cong (input-route γ (M.p₂ {1} {width v}))
                               {out = map-built-out γ (width v) (width v')} {up = M.in₂ {1}}
                               (agree-m D) i)
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-inr {v = v} {v' = v'} D) i =
    ≈-trans (Rule₁.agree (graph-m D) (input-route γ (M.p₂ {1} {width v}))
                       (fo-of (σ' [ σr ])) (map-built-out γ (width v) (width v')) (M.in₂ {1}) i)
            (M.one-result-cong (input-route γ (M.p₂ {1} {width v}))
                               {out = map-built-out γ (width v) (width v')} {up = M.in₂ {1}}
                               (agree-m D) i)
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-pair {v = v} {v' = v'} {u = u} {u' = u'} D₁ D₂) i =
    ≈-trans (Rule₂.agree (graph-m D₁) (graph-m D₂)
                       (input-route γ (M.p₁ {width v} {width u} M.∘ M.p₂ {1} {width v + width u}))
                       (input-route γ (M.p₂ {width v} {width u} M.∘ M.p₂ {1} {width v + width u}))
                       (M.no-link (inputM-width γ (width u)) (width v'))
                       (fo-of (σ' [ σr ])) (map-built-out γ (width v + width u) (width v' + width u'))
                       (M.in₂ {1} M.∘ M.in₁ {width v'} {width u'})
                       (M.in₂ {1} M.∘ M.in₂ {width v'} {width u'}) i)
            (M.seq-result-cong
               (input-route γ (M.p₁ {width v} {width u} M.∘ M.p₂ {1} {width v + width u}))
               (input-route γ (M.p₂ {width v} {width u} M.∘ M.p₂ {1} {width v + width u}))
               (M.no-link (inputM-width γ (width u)) (width v'))
               {out = map-built-out γ (width v + width u) (width v' + width u')}
               {u₁ = M.in₂ {1} M.∘ M.in₁ {width v'} {width u'}}
               {u₂ = M.in₂ {1} M.∘ M.in₂ {width v'} {width u'}}
               (agree-m D₁) (agree-m D₂) i)
  agree-m {γ = γ} {τ₀ = τ₀} {σr = σr} {σ' = σ'} (m-mu {τ' = τ'} {w = w} {w' = w'} D) i =
    ≈-trans (Rule₁.agree (graph-m D)
                       (input-route γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) M.I))
                       (fo-of (σ' [ σr ])) (λ _ → M.εₘ)
                       (rcast (sym (width-subst (unfold₁-inst τ' σr) w')) M.I) i)
            (M.one-result-cong
               (input-route γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) M.I))
               {out = λ _ → M.εₘ} {up = rcast (sym (width-subst (unfold₁-inst τ' σr) w')) M.I}
               (agree-m D) i)
