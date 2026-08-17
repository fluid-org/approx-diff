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
open import signature.interpretation using (Interpretation)
import matrix
import two

-- The dependence graph of a derivation with a control input. Each rule builds its graph from its
-- premises' graphs using the wiring that also defines the rule's relation, so collapsing the graph
-- recovers the relation rule by rule.
module interaction.dependence-graph {ℓ} (Sig : Signature ℓ) (ℐ : Interpretation two.semiring Sig) where

open Signature Sig
open Interpretation ℐ
open _⇒ₛ_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-operational.evaluation Sig two.semiring ℐ two.I
open import interaction.graph

private
  module M = matrix.Mat two.semiring

open import categories using (Category; HasProducts)
open Category M.cat using (_∘_; _≈_; ≈-refl; ≈-sym; ≈-trans; ∘-cong₁; ∘-cong₂; ∘-cong; assoc; id-left; id-right)
open HasProducts M.products using (p₁; p₂)
open M using (⟨_,_⟩)

-- The value at a vertex is first-order when the type of the subderivation's conclusion is.
fo-of : ∀ {Δ} (τ : type Δ) → Bool
fo-of τ = ⌊ first-order? τ ⌋

mutual
  graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} → γ , t ⇓ v [ R ] → Graph (suc (width-env γ)) (width v)
  graph {τ = τ} (⇓-var {γ = γ} x) = Rule₀.E (fo-of τ) (var-out x γ)
  graph {τ = τ} (⇓-unit {γ = γ}) = Rule₀.E (fo-of τ) wctrl
  graph {τ = τ} (⇓-lam {γ = γ} {t = t}) = Rule₀.E (fo-of τ) (lam-out γ t)
  graph {τ = τ} (⇓-inl {γ = γ} {v = v} D) =
    Rule₁.E (graph D) M.I (fo-of τ) (built-out γ (width v)) (M.in₂ {1})
  graph {τ = τ} (⇓-inr {γ = γ} {v = v} D) =
    Rule₁.E (graph D) M.I (fo-of τ) (built-out γ (width v)) (M.in₂ {1})
  graph {τ = τ} (⇓-case-l {γ = γ} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph D₂) M.I (branch-inputs γ v) (fo-of τ) M.εₘ M.εₘ M.I
  graph {τ = τ} (⇓-case-r {γ = γ} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph D₂) M.I (branch-inputs γ v) (fo-of τ) M.εₘ M.εₘ M.I
  graph {τ = τ} (⇓-pair {γ = γ} {v = v} {u = u} D₁ D₂) =
    Rule₂.E (graph D₁) (graph D₂) M.I (p₁ {suc (width-env γ)} {width v}) (fo-of τ) (built-out γ (width v + width u))
          (M.in₂ {1} ∘ M.in₁ {width v} {width u}) (M.in₂ {1} ∘ M.in₂ {width v} {width u})
  graph {τ = τ} (⇓-fst {γ = γ} {v = v} {u = u} D) =
    Rule₁.E (graph D) M.I (fo-of τ) (elim-out γ v) (proj-up {width v} {width u} v (p₁ {width v} {width u}))
  graph {τ = τ} (⇓-snd {γ = γ} {v = v} {u = u} D) =
    Rule₁.E (graph D) M.I (fo-of τ) (elim-out γ u) (proj-up {width v} {width u} u (p₂ {width v} {width u}))
  graph {τ = τ} (⇓-app {γ = γ} {γ' = γ'} {v = v} D₁ D₂ D₃) =
    Rule₃.E (graph D₁) (graph D₂) (graph D₃) M.I M.I (body-inputs γ γ' v) (fo-of τ) M.εₘ M.εₘ M.εₘ M.I
  graph {τ = τ} (⇓-bop {γ = γ} {ω = ω} {vs = vs} D) =
    Rule₁.E (graph-s D) M.I (fo-of τ) wctrl (op-deps ω .func vs)
  graph {τ = τ} (⇓-brel {γ = γ} {ω = ω} {vs = vs} D) =
    Rule₁.E (graph-s D) M.I (fo-of τ) wctrl (brel-deps ω vs (rel-pred ω .func vs))
  graph {τ = τ} (⇓-roll {γ = γ} D) = Rule₁.E (graph D) M.I (fo-of τ) M.εₘ M.I
  graph {τ = τ} (⇓-fold {γ = γ} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph-m D₂) M.I M.I (fo-of τ) M.εₘ M.εₘ M.I

  graph-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
            γ , Ms ⇓s vs [ R ] → Graph (suc (width-env γ)) (bases-width is)
  graph-s {γ = γ} [] = Rule₀.E Bool.true M.εₘ
  graph-s {γ = γ} (_∷_ {is = is} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph-s D₂) M.I (p₁ {suc (width-env γ)} {width (const v)}) Bool.true M.εₘ
          (M.in₁ {width (const v)} {bases-width is}) (M.in₂ {width (const v)} {bases-width is})

  graph-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {v' : Val (σ' [ σr ])} {F} →
            Map γ s σ' v v' F → Graph (suc (width-env γ) + width v) (width v')
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-rec {w = w} {w' = w'} D₁ D₂) =
    Rule₂.E (graph-m D₁) (graph D₂) M.I (rec-inputs γ w') (fo-of (σ' [ σr ])) M.εₘ M.εₘ M.I
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-unit {v = v}) = Rule₀.E (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-base {v = v}) = Rule₀.E (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-arrow {v = v}) = Rule₀.E (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-inl {v = v} {v' = v'} D) =
    Rule₁.E (graph-m D) (sub-inputs γ (p₂ {1} {width v})) (fo-of (σ' [ σr ]))
          (map-built-out γ (width v) (width v')) (M.in₂ {1})
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-inr {v = v} {v' = v'} D) =
    Rule₁.E (graph-m D) (sub-inputs γ (p₂ {1} {width v})) (fo-of (σ' [ σr ]))
          (map-built-out γ (width v) (width v')) (M.in₂ {1})
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-pair {v = v} {v' = v'} {u = u} {u' = u'} D₁ D₂) =
    Rule₂.E (graph-m D₁) (graph-m D₂)
          (sub-inputs γ (p₁ {width v} {width u} ∘ p₂ {1} {width v + width u}))
          (sub-inputs γ (p₂ {width v} {width u} ∘ p₂ {1} {width v + width u}) ∘ p₁ {suc (width-env γ) + suc (width v + width u)} {width v'})
          (fo-of (σ' [ σr ])) (map-built-out γ (width v + width u) (width v' + width u'))
          (M.in₂ {1} ∘ M.in₁ {width v'} {width u'}) (M.in₂ {1} ∘ M.in₂ {width v'} {width u'})
  graph-m {γ = γ} {τ₀ = τ₀} {σr = σr} {σ' = σ'} (m-mu {τ' = τ'} {w = w} {w' = w'} D) =
    Rule₁.E (graph-m D) (sub-inputs γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) M.I))
          (fo-of (σ' [ σr ])) M.εₘ (rcast (sym (width-subst (unfold₁-inst τ' σr) w')) M.I)

-- A combinator's collapse law against the rule's relation, given the premises' collapses.
private
  one : ∀ {m n n₀} (out : M.Matrix n m) (up : M.Matrix n n₀) {c R' : M.Matrix n₀ m} → c ≈ R' →
        (out M.+ₘ (up ∘ (c ∘ M.I))) ≈ (out M.+ₘ (up ∘ R'))
  one out up {c = c} e = M.+ₘ-cong (≈-refl {f = out}) (∘-cong₂ (≈-trans {g = c} id-right e))

  one-inputs : ∀ {m m' n n₀} (out : M.Matrix n m) (up : M.Matrix n n₀) (ins : M.Matrix m' m)
               {c R' : M.Matrix n₀ m'} → c ≈ R' →
               (out M.+ₘ (up ∘ (c ∘ ins))) ≈ (out M.+ₘ (up ∘ (R' ∘ ins)))
  one-inputs out up ins e = M.+ₘ-cong (≈-refl {f = out}) (∘-cong₂ (∘-cong₁ e))

  pair-cong : ∀ {m n₁ n₂} {X₁ Y₁ : M.Matrix n₁ m} {X₂ Y₂ : M.Matrix n₂ m} → X₁ ≈ Y₁ → X₂ ≈ Y₂ →
              ⟨ X₁ , X₂ ⟩ ≈ ⟨ Y₁ , Y₂ ⟩
  pair-cong = HasProducts.pair-cong M.products

  seq : ∀ {m m₂ n₁ n₂} (ins : M.Matrix m₂ (m + n₁)) {c₁ R₁ : M.Matrix n₁ m} {c₂ T : M.Matrix n₂ m₂} →
        c₁ ≈ R₁ → c₂ ≈ T →
        ((M.εₘ M.+ₘ (M.εₘ ∘ (c₁ ∘ M.I))) M.+ₘ (M.I ∘ (c₂ ∘ (ins ∘ ⟨ M.I , c₁ ∘ M.I ⟩))))
        ≈ (T ∘ (ins ∘ ⟨ M.I , R₁ ⟩))
  seq ins {c₁ = c₁} {R₁ = R₁} {c₂ = c₂} {T = T} e₁ e₂ =
    ≈-trans {g = M.εₘ M.+ₘ (T ∘ (ins ∘ ⟨ M.I , R₁ ⟩))}
      (M.+ₘ-cong (M.absorb₁ M.εₘ (c₁ ∘ M.I))
                 (≈-trans {g = c₂ ∘ (ins ∘ ⟨ M.I , c₁ ∘ M.I ⟩)} id-left
                          (∘-cong e₂ (∘-cong₂ (pair-cong (≈-refl {f = M.I}) (≈-trans {g = c₁} id-right e₁))))))
      (M.+ₘ-lunit (T ∘ (ins ∘ ⟨ M.I , R₁ ⟩)))

  seq3 : ∀ {m m₃ n₁ n₂ n₃} (ins : M.Matrix m₃ ((m + n₁) + n₂))
         {c₁ R₁ : M.Matrix n₁ m} {c₂ R₂ : M.Matrix n₂ m} {c₃ U : M.Matrix n₃ m₃} →
         c₁ ≈ R₁ → c₂ ≈ R₂ → c₃ ≈ U →
         (((M.εₘ M.+ₘ (M.εₘ ∘ (c₁ ∘ M.I))) M.+ₘ (M.εₘ ∘ (c₂ ∘ M.I))) M.+ₘ
          (M.I ∘ (c₃ ∘ (ins ∘ ⟨ ⟨ M.I , c₁ ∘ M.I ⟩ , c₂ ∘ M.I ⟩))))
         ≈ (U ∘ (ins ∘ ⟨ ⟨ M.I , R₁ ⟩ , R₂ ⟩))
  seq3 ins {c₁ = c₁} {R₁ = R₁} {c₂ = c₂} {R₂ = R₂} {c₃ = c₃} {U = U} e₁ e₂ e₃ =
    ≈-trans {g = M.εₘ M.+ₘ (U ∘ (ins ∘ ⟨ ⟨ M.I , R₁ ⟩ , R₂ ⟩))}
      (M.+ₘ-cong (≈-trans {g = M.εₘ M.+ₘ (M.εₘ ∘ (c₁ ∘ M.I))} (M.absorb₁ _ (c₂ ∘ M.I)) (M.absorb₁ M.εₘ (c₁ ∘ M.I)))
                 (≈-trans {g = c₃ ∘ (ins ∘ ⟨ ⟨ M.I , c₁ ∘ M.I ⟩ , c₂ ∘ M.I ⟩)} id-left
                          (∘-cong e₃ (∘-cong₂ (pair-cong (pair-cong (≈-refl {f = M.I}) (≈-trans {g = c₁} id-right e₁))
                                                         (≈-trans {g = c₂} id-right e₂))))))
      (M.+ₘ-lunit (U ∘ (ins ∘ ⟨ ⟨ M.I , R₁ ⟩ , R₂ ⟩)))

  -- A premise whose inputs are the conclusion's alone, after the earlier premise has collapsed.
  ignore-root : ∀ {m m₂ n₁} (A : M.Matrix m₂ m) (X : M.Matrix n₁ m) → ((A ∘ p₁ {m} {n₁}) ∘ ⟨ M.I , X ⟩) ≈ A
  ignore-root {m} {n₁ = n₁} A X =
    ≈-trans {g = A ∘ (p₁ {m} {n₁} ∘ ⟨ M.I , X ⟩)} (assoc A (p₁ {m} {n₁}) ⟨ M.I , X ⟩)
            (≈-trans {g = A ∘ M.I} (∘-cong₂ (HasProducts.pair-p₁ M.products M.I X)) id-right)

  -- Two premises feeding a pair of roots.
  two-roots : ∀ {m m₁ m₂ n n₁ n₂} (out : M.Matrix n m) (r₁ : M.Matrix m₁ m) (ins₂ : M.Matrix m₂ (m + n₁))
              (u₁ : M.Matrix n n₁) (u₂ : M.Matrix n n₂)
              (c₁ : M.Matrix n₁ m₁) (c₂ : M.Matrix n₂ m₂) {X₁ : M.Matrix n₁ m} {X₂ : M.Matrix n₂ m} →
              (c₁ ∘ r₁) ≈ X₁ → (c₂ ∘ (ins₂ ∘ ⟨ M.I , c₁ ∘ r₁ ⟩)) ≈ X₂ →
              ((out M.+ₘ (u₁ ∘ (c₁ ∘ r₁))) M.+ₘ (u₂ ∘ (c₂ ∘ (ins₂ ∘ ⟨ M.I , c₁ ∘ r₁ ⟩))))
              ≈ (out M.+ₘ ((u₁ ∘ X₁) M.+ₘ (u₂ ∘ X₂)))
  two-roots out r₁ ins₂ u₁ u₂ c₁ c₂ {X₁ = X₁} {X₂ = X₂} e₁ e₂ =
    ≈-trans {g = (out M.+ₘ (u₁ ∘ X₁)) M.+ₘ (u₂ ∘ X₂)}
      (M.+ₘ-cong (M.+ₘ-cong (≈-refl {f = out}) (∘-cong₂ e₁)) (∘-cong₂ e₂))
      (M.+ₘ-assoc out (u₁ ∘ X₁) (u₂ ∘ X₂))

  inputs-only : ∀ {m n₁ n₂} (c₂ : M.Matrix n₂ m) (X : M.Matrix n₁ m) {R : M.Matrix n₂ m} → c₂ ≈ R →
                (c₂ ∘ (p₁ {m} {n₁} ∘ ⟨ M.I , X ⟩)) ≈ R
  inputs-only {m} {n₁} c₂ X e =
    ≈-trans {g = c₂ ∘ M.I} (∘-cong₂ (HasProducts.pair-p₁ M.products M.I X)) (≈-trans {g = c₂} id-right e)

  -- The pair of roots as the pairing.
  pairing : ∀ {m n₁ n₂} (X₁ : M.Matrix n₁ m) (X₂ : M.Matrix n₂ m) →
            (((M.in₂ {1} ∘ M.in₁ {n₁} {n₂}) ∘ X₁) M.+ₘ ((M.in₂ {1} ∘ M.in₂ {n₁} {n₂}) ∘ X₂))
            ≈ (M.in₂ {1} ∘ ⟨ X₁ , X₂ ⟩)
  pairing {n₁ = n₁} {n₂ = n₂} X₁ X₂ =
    ≈-trans {g = (M.in₂ {1} ∘ (M.in₁ {n₁} {n₂} ∘ X₁)) M.+ₘ (M.in₂ {1} ∘ (M.in₂ {n₁} {n₂} ∘ X₂))}
      (M.+ₘ-cong (assoc (M.in₂ {1}) (M.in₁ {n₁} {n₂}) X₁) (assoc (M.in₂ {1}) (M.in₂ {n₁} {n₂}) X₂))
      (≈-sym (M.comp-bilinear₂ (M.in₂ {1}) (M.in₁ {n₁} {n₂} ∘ X₁) (M.in₂ {n₁} {n₂} ∘ X₂)))

  mu : ∀ {m m' n n'} (rc : M.Matrix n' n) (ic : M.Matrix m' m) {c F : M.Matrix n m'} → c ≈ F →
       (M.εₘ M.+ₘ (rc ∘ (c ∘ ic))) ≈ (rc ∘ (F ∘ ic))
  mu rc ic {c = c} e = ≈-trans {g = rc ∘ (c ∘ ic)} (M.+ₘ-lunit (rc ∘ (c ∘ ic))) (∘-cong₂ (∘-cong₁ {g = ic} e))

-- Collapsing a derivation's graph recovers the relation the rules build.
mutual
  agree : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → collapse (graph D) ≈ R
  agree {τ = τ} (⇓-var {γ = γ} x) = Rule₀.agree (fo-of τ) (var-out x γ)
  agree {τ = τ} (⇓-unit {γ = γ}) = Rule₀.agree (fo-of τ) wctrl
  agree {τ = τ} (⇓-lam {γ = γ} {t = t}) = Rule₀.agree (fo-of τ) (lam-out γ t)
  agree {τ = τ} (⇓-inl {γ = γ} {v = v} D) =
    ≈-trans (Rule₁.agree (graph D) M.I (fo-of τ) (built-out γ (width v)) (M.in₂ {1}))
            (one (built-out γ (width v)) (M.in₂ {1}) (agree D))
  agree {τ = τ} (⇓-inr {γ = γ} {v = v} D) =
    ≈-trans (Rule₁.agree (graph D) M.I (fo-of τ) (built-out γ (width v)) (M.in₂ {1}))
            (one (built-out γ (width v)) (M.in₂ {1}) (agree D))
  agree {τ = τ} (⇓-case-l {γ = γ} {v = v} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph D₂) M.I (branch-inputs γ v) (fo-of τ) M.εₘ M.εₘ M.I)
            (seq (branch-inputs γ v) (agree D₁) (agree D₂))
  agree {τ = τ} (⇓-case-r {γ = γ} {v = v} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph D₂) M.I (branch-inputs γ v) (fo-of τ) M.εₘ M.εₘ M.I)
            (seq (branch-inputs γ v) (agree D₁) (agree D₂))
  agree {τ = τ} (⇓-pair {γ = γ} {v = v} {u = u} {R = R} {T = T} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph D₂) M.I (p₁ {suc (width-env γ)} {width v}) (fo-of τ)
                       (built-out γ (width v + width u))
                       (M.in₂ {1} ∘ M.in₁ {width v} {width u}) (M.in₂ {1} ∘ M.in₂ {width v} {width u}))
    (≈-trans (two-roots (built-out γ (width v + width u)) M.I (p₁ {suc (width-env γ)} {width v})
                        (M.in₂ {1} ∘ M.in₁ {width v} {width u}) (M.in₂ {1} ∘ M.in₂ {width v} {width u})
                        (collapse (graph D₁)) (collapse (graph D₂))
                        (≈-trans {g = collapse (graph D₁)} id-right (agree D₁))
                        (inputs-only (collapse (graph D₂)) (collapse (graph D₁) ∘ M.I) (agree D₂)))
             (M.+ₘ-cong (≈-refl {f = built-out γ (width v + width u)}) (pairing R T)))
  agree {τ = τ} (⇓-fst {γ = γ} {v = v} {u = u} D) =
    ≈-trans (Rule₁.agree (graph D) M.I (fo-of τ) (elim-out γ v) (proj-up {width v} {width u} v (p₁ {width v} {width u})))
            (one (elim-out γ v) (proj-up {width v} {width u} v (p₁ {width v} {width u})) (agree D))
  agree {τ = τ} (⇓-snd {γ = γ} {v = v} {u = u} D) =
    ≈-trans (Rule₁.agree (graph D) M.I (fo-of τ) (elim-out γ u) (proj-up {width v} {width u} u (p₂ {width v} {width u})))
            (one (elim-out γ u) (proj-up {width v} {width u} u (p₂ {width v} {width u})) (agree D))
  agree {τ = τ} (⇓-app {γ = γ} {γ' = γ'} {v = v} D₁ D₂ D₃) =
    ≈-trans (Rule₃.agree (graph D₁) (graph D₂) (graph D₃) M.I M.I (body-inputs γ γ' v) (fo-of τ) M.εₘ M.εₘ M.εₘ M.I)
            (seq3 (body-inputs γ γ' v) (agree D₁) (agree D₂) (agree D₃))
  agree {τ = τ} (⇓-bop {γ = γ} {ω = ω} {vs = vs} D) =
    ≈-trans (Rule₁.agree (graph-s D) M.I (fo-of τ) wctrl (op-deps ω .func vs))
            (one wctrl (op-deps ω .func vs) (agree-s D))
  agree {τ = τ} (⇓-brel {γ = γ} {ω = ω} {vs = vs} D) =
    ≈-trans (Rule₁.agree (graph-s D) M.I (fo-of τ) wctrl (brel-deps ω vs (rel-pred ω .func vs)))
            (one wctrl (brel-deps ω vs (rel-pred ω .func vs)) (agree-s D))
  agree {τ = τ} (⇓-roll {γ = γ} {R = R} D) =
    ≈-trans (Rule₁.agree (graph D) M.I (fo-of τ) M.εₘ M.I)
            (≈-trans {g = M.I ∘ (collapse (graph D) ∘ M.I)} (M.+ₘ-lunit (M.I ∘ (collapse (graph D) ∘ M.I)))
                     (≈-trans {g = collapse (graph D) ∘ M.I} id-left
                              (≈-trans {g = collapse (graph D)} id-right (agree D))))
  agree {τ = τ} (⇓-fold {γ = γ} {v = v} {R = R} {F = F} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph-m D₂) M.I M.I (fo-of τ) M.εₘ M.εₘ M.I)
            (≈-trans {g = F ∘ (M.I ∘ ⟨ M.I , R ⟩)} (seq M.I (agree D₁) (agree-m D₂))
                     (∘-cong₂ {f = F} (id-left {f = ⟨ M.I , R ⟩})))

  agree-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
            (D : γ , Ms ⇓s vs [ R ]) → collapse (graph-s D) ≈ R
  agree-s {γ = γ} [] = Rule₀.agree Bool.true M.εₘ
  agree-s {γ = γ} (_∷_ {is = is} {v = v} {R = R} {Rs = Rs} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph-s D₂) M.I (p₁ {suc (width-env γ)} {width (const v)}) Bool.true M.εₘ
                       (M.in₁ {width (const v)} {bases-width is}) (M.in₂ {width (const v)} {bases-width is}))
    (≈-trans (two-roots M.εₘ M.I (p₁ {suc (width-env γ)} {width (const v)})
                        (M.in₁ {width (const v)} {bases-width is}) (M.in₂ {width (const v)} {bases-width is})
                        (collapse (graph D₁)) (collapse (graph-s D₂))
                        (≈-trans {g = collapse (graph D₁)} id-right (agree D₁))
                        (inputs-only (collapse (graph-s D₂)) (collapse (graph D₁) ∘ M.I) (agree-s D₂)))
             (M.+ₘ-lunit ⟨ R , Rs ⟩))

  agree-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {v' : Val (σ' [ σr ])} {F}
            (D : Map γ s σ' v v' F) → collapse (graph-m D) ≈ F
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-rec {w = w} {w' = w'} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph-m D₁) (graph D₂) M.I (rec-inputs γ w') (fo-of (σ' [ σr ])) M.εₘ M.εₘ M.I)
            (seq (rec-inputs γ w') (agree-m D₁) (agree D₂))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-unit {v = v}) = Rule₀.agree (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-base {v = v}) = Rule₀.agree (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-arrow {v = v}) = Rule₀.agree (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-inl {v = v} {v' = v'} D) =
    ≈-trans (Rule₁.agree (graph-m D) (sub-inputs γ (p₂ {1} {width v})) (fo-of (σ' [ σr ]))
                       (map-built-out γ (width v) (width v')) (M.in₂ {1}))
            (one-inputs (map-built-out γ (width v) (width v')) (M.in₂ {1}) (sub-inputs γ (p₂ {1} {width v}))
                        (agree-m D))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-inr {v = v} {v' = v'} D) =
    ≈-trans (Rule₁.agree (graph-m D) (sub-inputs γ (p₂ {1} {width v})) (fo-of (σ' [ σr ]))
                       (map-built-out γ (width v) (width v')) (M.in₂ {1}))
            (one-inputs (map-built-out γ (width v) (width v')) (M.in₂ {1}) (sub-inputs γ (p₂ {1} {width v}))
                        (agree-m D))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-pair {v = v} {v' = v'} {u = u} {u' = u'} {F = F} {G = G} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph-m D₁) (graph-m D₂) ins₁ (ins₂ ∘ p₁ {suc (width-env γ) + suc (width v + width u)} {width v'})
                       (fo-of (σ' [ σr ])) (map-built-out γ (width v + width u) (width v' + width u'))
                       (M.in₂ {1} ∘ M.in₁ {width v'} {width u'}) (M.in₂ {1} ∘ M.in₂ {width v'} {width u'}))
    (≈-trans (two-roots (map-built-out γ (width v + width u) (width v' + width u')) ins₁
                        (ins₂ ∘ p₁ {suc (width-env γ) + suc (width v + width u)} {width v'})
                        (M.in₂ {1} ∘ M.in₁ {width v'} {width u'}) (M.in₂ {1} ∘ M.in₂ {width v'} {width u'})
                        (collapse (graph-m D₁)) (collapse (graph-m D₂))
                        (∘-cong₁ {g = ins₁} (agree-m D₁))
                        (≈-trans {g = collapse (graph-m D₂) ∘ ins₂}
                                 (∘-cong₂ {f = collapse (graph-m D₂)} (ignore-root ins₂ (collapse (graph-m D₁) ∘ ins₁)))
                                 (∘-cong₁ {g = ins₂} (agree-m D₂))))
             (M.+ₘ-cong (≈-refl {f = map-built-out γ (width v + width u) (width v' + width u')})
                        (pairing (F ∘ ins₁) (G ∘ ins₂))))
    where
    ins₁ = sub-inputs γ (p₁ {width v} {width u} ∘ p₂ {1} {width v + width u})
    ins₂ = sub-inputs γ (p₂ {width v} {width u} ∘ p₂ {1} {width v + width u})
  agree-m {γ = γ} {τ₀ = τ₀} {σr = σr} {σ' = σ'} (m-mu {τ' = τ'} {w = w} {w' = w'} D) =
    ≈-trans (Rule₁.agree (graph-m D) (sub-inputs γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) M.I))
                       (fo-of (σ' [ σr ])) M.εₘ (rcast (sym (width-subst (unfold₁-inst τ' σr) w')) M.I))
            (mu (rcast (sym (width-subst (unfold₁-inst τ' σr) w')) M.I)
                (sub-inputs γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) M.I)) (agree-m D))
