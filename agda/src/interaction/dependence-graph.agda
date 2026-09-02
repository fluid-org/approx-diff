{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Bool as Bool
open Bool using (Bool)
open import Data.Fin using (zero)
open import Data.Nat using (ℕ; suc; _+_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (sym)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List.Relation.Unary.All using ([]; _∷_) renaming (All to Every)
open import prop-setoid using (Setoid) renaming (_⇒_ to _⇒ₛ_)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)
import matrix

-- The dependence graph of a derivation with a control input. Each rule builds its graph from its
-- premises' graphs using the wiring that also defines the rule's relation, so collapsing the graph
-- recovers the relation rule by rule. Vertices carry free semimodules; the relation's matrices
-- enter as morphisms through the embedding.
module interaction.dependence-graph {ℓ} (Sig : Signature ℓ) {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (ℐ : Interpretation S Sig) (ctrl-weight : Setoid.Carrier A)
  (let module S = CommutativeSemiring S) (+-idem : ∀ x → (x S.+ x) S.≈ x) where

open Signature Sig
open Interpretation ℐ
open _⇒ₛ_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-operational.evaluation Sig S ℐ ctrl-weight hiding (_⇒_)
open import interaction.graph S +-idem
open import matrix-embedding S using (𝔽; mat; mat-cong; mat-comp; mat-I; mat-ε; mat-+)

private
  module M = matrix.Mat S

open import categories using (Category; HasProducts)
open Category SemiMod.cat
  using (_⇒_; _∘_; _≈_; ∘-cong; ∘-cong₁; ∘-cong₂; assoc; id-left; id-right; ≈-refl; ≈-sym; ≈-trans)
open HasProducts M.products using (p₁; p₂)
open M using () renaming (⟨_,_⟩ to ⟨_,_⟩ₘ)
open import cmon-enriched using (CMonEnriched; Biproduct)
private
  module CME = CMonEnriched SemiMod.cmon-enriched
  module BPP {X Y : SemiMod.Semimodule} = Biproduct (SemiMod.biproduct X Y)

fo-of : ∀ {Δ} (τ : type Δ) → Bool
fo-of τ = ⌊ first-order? τ ⌋

private
  join : ∀ m n → (𝔽 m ⊕ᵥ 𝔽 n) ⇒ 𝔽 (m + n)
  join m n = (mat (M.in₁ {m} {n}) ∘ pb₁) +ₘ (mat (M.in₂ {m} {n}) ∘ pb₂)

  join-inb₁ : ∀ m n → (join m n ∘ inb₁) ≈ mat (M.in₁ {m} {n})
  join-inb₁ m n =
    ≈-trans (CME.comp-bilinear₁ (mat (M.in₁ {m} {n}) ∘ pb₁) (mat (M.in₂ {m} {n}) ∘ pb₂) inb₁)
    (≈-trans (+ₘ-cong (≈-trans (assoc (mat (M.in₁ {m} {n})) pb₁ inb₁)
                               (≈-trans (∘-cong₂ {f = mat (M.in₁ {m} {n})} BPP.id-1) id-right))
                      (≈-trans (assoc (mat (M.in₂ {m} {n})) pb₂ inb₁)
                               (≈-trans (∘-cong₂ {f = mat (M.in₂ {m} {n})} BPP.zero-2)
                                        (CME.comp-bilinear-ε₂ (mat (M.in₂ {m} {n}))))))
             (+ₘ-runit (mat (M.in₁ {m} {n}))))

  join-inb₂ : ∀ m n → (join m n ∘ inb₂) ≈ mat (M.in₂ {m} {n})
  join-inb₂ m n =
    ≈-trans (CME.comp-bilinear₁ (mat (M.in₁ {m} {n}) ∘ pb₁) (mat (M.in₂ {m} {n}) ∘ pb₂) inb₂)
    (≈-trans (+ₘ-cong (≈-trans (assoc (mat (M.in₁ {m} {n})) pb₁ inb₂)
                               (≈-trans (∘-cong₂ {f = mat (M.in₁ {m} {n})} BPP.zero-1)
                                        (CME.comp-bilinear-ε₂ (mat (M.in₁ {m} {n})))))
                      (≈-trans (assoc (mat (M.in₂ {m} {n})) pb₂ inb₂)
                               (≈-trans (∘-cong₂ {f = mat (M.in₂ {m} {n})} BPP.id-2) id-right)))
             (+ₘ-lunit (mat (M.in₂ {m} {n}))))

  pair-congᴴ : ∀ {Z X Y : SemiMod.Semimodule} {f f' : Z ⇒ X} {g g' : Z ⇒ Y} →
               f ≈ f' → g ≈ g' → ⟨ f , g ⟩ ≈ ⟨ f' , g' ⟩
  pair-congᴴ ef eg = +ₘ-cong (∘-cong₂ {f = inb₁} ef) (∘-cong₂ {f = inb₂} eg)

  pair-pb₁ : ∀ {Z X Y : SemiMod.Semimodule} (f : Z ⇒ X) (g : Z ⇒ Y) → (pb₁ ∘ ⟨ f , g ⟩) ≈ f
  pair-pb₁ {Z} {X} {Y} f g =
    ≈-trans (CME.comp-bilinear₂ pb₁ (inb₁ ∘ f) (inb₂ ∘ g))
    (≈-trans (+ₘ-cong (≈-trans (≈-sym (assoc pb₁ inb₁ f)) (≈-trans (∘-cong₁ {g = f} BPP.id-1) id-left))
                      (≈-trans (≈-sym (assoc pb₁ inb₂ g)) (≈-trans (∘-cong₁ {g = g} BPP.zero-1)
                                                                   (CME.comp-bilinear-ε₁ g))))
             (+ₘ-runit f))

  mat-pair-flat : ∀ {m n k} (X : M.Matrix m k) (Y : M.Matrix n k) →
                  mat ⟨ X , Y ⟩ₘ ≈ ((mat (M.in₁ {m} {n}) ∘ mat X) +ₘ (mat (M.in₂ {m} {n}) ∘ mat Y))
  mat-pair-flat {m} {n} X Y =
    ≈-trans (mat-+ (M.in₁ {m} {n} M.∘ X) (M.in₂ {m} {n} M.∘ Y))
            (+ₘ-cong (mat-comp (M.in₁ {m} {n}) X) (mat-comp (M.in₂ {m} {n}) Y))

  mat-pair : ∀ {m n k} (X : M.Matrix m k) (Y : M.Matrix n k) →
             mat ⟨ X , Y ⟩ₘ ≈ (join m n ∘ ⟨ mat X , mat Y ⟩)
  mat-pair {m} {n} X Y =
    ≈-trans (mat-pair-flat X Y)
    (≈-sym (≈-trans (CME.comp-bilinear₂ (join m n) (inb₁ ∘ mat X) (inb₂ ∘ mat Y))
                    (+ₘ-cong (≈-trans (≈-sym (assoc (join m n) inb₁ (mat X))) (∘-cong₁ {g = mat X} (join-inb₁ m n)))
                             (≈-trans (≈-sym (assoc (join m n) inb₂ (mat Y))) (∘-cong₁ {g = mat Y} (join-inb₂ m n))))))

mutual
  graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} → γ , t ⇓ v [ R ] →
          Graph (𝔽 (suc (width-env γ))) (𝔽 (width v))
  graph {τ = τ} (⇓-var {γ = γ} x) = Rule₀.E (fo-of τ) (mat (var-out x γ))
  graph {τ = τ} (⇓-unit {γ = γ}) = Rule₀.E (fo-of τ) (mat wctrl)
  graph {τ = τ} (⇓-lam {γ = γ} {t = t}) = Rule₀.E (fo-of τ) (mat (lam-out γ t))
  graph {τ = τ} (⇓-inl {γ = γ} {v = v} D) =
    Rule₁.E (graph D) I (fo-of τ) (mat (built-out γ (width v))) (mat (M.in₂ {1}))
  graph {τ = τ} (⇓-inr {γ = γ} {v = v} D) =
    Rule₁.E (graph D) I (fo-of τ) (mat (built-out γ (width v))) (mat (M.in₂ {1}))
  graph {τ = τ} (⇓-case-l {γ = γ} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph D₂) I
          (mat (branch-inputs γ v) ∘ join (suc (width-env γ)) (suc (width v)))
          (fo-of τ) εₘ εₘ I
  graph {τ = τ} (⇓-case-r {γ = γ} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph D₂) I
          (mat (branch-inputs γ v) ∘ join (suc (width-env γ)) (suc (width v)))
          (fo-of τ) εₘ εₘ I
  graph {τ = τ} (⇓-pair {γ = γ} {v = v} {u = u} D₁ D₂) =
    Rule₂.E (graph D₁) (graph D₂) I
          (mat (p₁ {suc (width-env γ)} {width v}) ∘ join (suc (width-env γ)) (width v))
          (fo-of τ) (mat (built-out γ (width v + width u)))
          (mat (M.in₂ {1} M.∘ M.in₁ {width v} {width u})) (mat (M.in₂ {1} M.∘ M.in₂ {width v} {width u}))
  graph {τ = τ} (⇓-fst {γ = γ} {v = v} {u = u} D) =
    Rule₁.E (graph D) I (fo-of τ) (mat (elim-out γ v)) (mat (proj-up {width v} {width u} v (p₁ {width v} {width u})))
  graph {τ = τ} (⇓-snd {γ = γ} {v = v} {u = u} D) =
    Rule₁.E (graph D) I (fo-of τ) (mat (elim-out γ u)) (mat (proj-up {width v} {width u} u (p₂ {width v} {width u})))
  graph {τ = τ} (⇓-app {γ = γ} {γ' = γ'} {v = v} D₁ D₂ D₃) =
    Rule₃.E (graph D₁) (graph D₂) (graph D₃) I I
          (mat (body-inputs γ γ' v) ∘
            (join (suc (width-env γ) + suc (width-env γ')) (width v) ∘
              ⟨ join (suc (width-env γ)) (suc (width-env γ')) ∘ pb₁ , pb₂ ⟩))
          (fo-of τ) εₘ εₘ εₘ I
  graph {τ = τ} (⇓-bop {γ = γ} {ω = ω} {vs = vs} D) =
    Rule₁.E (graph-s D) I (fo-of τ) (mat wctrl) (mat (op-deps ω .func vs))
  graph {τ = τ} (⇓-brel {γ = γ} {ω = ω} {vs = vs} D) =
    Rule₁.E (graph-s D) I (fo-of τ) (mat wctrl) (mat (brel-deps ω vs (rel-pred ω .func vs)))
  graph {τ = τ} (⇓-roll {γ = γ} D) = Rule₁.E (graph D) I (fo-of τ) εₘ I
  graph {τ = τ} (⇓-fold {γ = γ} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph-m D₂) I (join (suc (width-env γ)) (width v)) (fo-of τ) εₘ εₘ I

  graph-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
            γ , Ms ⇓s vs [ R ] → Graph (𝔽 (suc (width-env γ))) (𝔽 (bases-width is))
  graph-s {γ = γ} [] = Rule₀.E Bool.true εₘ
  graph-s {γ = γ} (_∷_ {is = is} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph-s D₂) I
          (mat (p₁ {suc (width-env γ)} {width (const v)}) ∘ join (suc (width-env γ)) (width (const v)))
          Bool.true εₘ
          (mat (M.in₁ {width (const v)} {bases-width is})) (mat (M.in₂ {width (const v)} {bases-width is}))

  graph-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {v' : Val (σ' [ σr ])} {F} →
            Map γ s σ' v v' F → Graph (𝔽 (suc (width-env γ) + width v)) (𝔽 (width v'))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-rec {w = w} {w' = w'} D₁ D₂) =
    Rule₂.E (graph-m D₁) (graph D₂) I
          (mat (rec-inputs γ w') ∘ join (suc (width-env γ) + width w) (width w'))
          (fo-of (σ' [ σr ])) εₘ εₘ I
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-unit {v = v}) = Rule₀.E (fo-of (σ' [ σr ])) (mat (map-leaf γ (width v)))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-base {v = v}) = Rule₀.E (fo-of (σ' [ σr ])) (mat (map-leaf γ (width v)))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-arrow {v = v}) = Rule₀.E (fo-of (σ' [ σr ])) (mat (map-leaf γ (width v)))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-inl {v = v} {v' = v'} D) =
    Rule₁.E (graph-m D) (mat (sub-inputs γ (p₂ {1} {width v}))) (fo-of (σ' [ σr ]))
          (mat (map-built-out γ (width v) (width v'))) (mat (M.in₂ {1}))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-inr {v = v} {v' = v'} D) =
    Rule₁.E (graph-m D) (mat (sub-inputs γ (p₂ {1} {width v}))) (fo-of (σ' [ σr ]))
          (mat (map-built-out γ (width v) (width v'))) (mat (M.in₂ {1}))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-pair {v = v} {v' = v'} {u = u} {u' = u'} D₁ D₂) =
    Rule₂.E (graph-m D₁) (graph-m D₂)
          (mat (sub-inputs γ (p₁ {width v} {width u} M.∘ p₂ {1} {width v + width u})))
          (mat (sub-inputs γ (p₂ {width v} {width u} M.∘ p₂ {1} {width v + width u})) ∘
            (mat (p₁ {suc (width-env γ) + suc (width v + width u)} {width v'}) ∘
              join (suc (width-env γ) + suc (width v + width u)) (width v')))
          (fo-of (σ' [ σr ])) (mat (map-built-out γ (width v + width u) (width v' + width u')))
          (mat (M.in₂ {1} M.∘ M.in₁ {width v'} {width u'})) (mat (M.in₂ {1} M.∘ M.in₂ {width v'} {width u'}))
  graph-m {γ = γ} {τ₀ = τ₀} {σr = σr} {σ' = σ'} (m-mu {τ' = τ'} {w = w} {w' = w'} D) =
    Rule₁.E (graph-m D) (mat (sub-inputs γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) M.I)))
          (fo-of (σ' [ σr ])) εₘ (mat (rcast (sym (width-subst (unfold₁-inst τ' σr) w')) M.I))

private
  join-pair : ∀ {a b} {Z : SemiMod.Semimodule} (f : Z ⇒ 𝔽 a) (g : Z ⇒ 𝔽 b) →
              (join a b ∘ ⟨ f , g ⟩) ≈ ((mat (M.in₁ {a} {b}) ∘ f) +ₘ (mat (M.in₂ {a} {b}) ∘ g))
  join-pair {a} {b} f g =
    ≈-trans (CME.comp-bilinear₂ (join a b) (inb₁ ∘ f) (inb₂ ∘ g))
            (+ₘ-cong (≈-trans (≈-sym (assoc (join a b) inb₁ f)) (∘-cong₁ {g = f} (join-inb₁ a b)))
                     (≈-trans (≈-sym (assoc (join a b) inb₂ g)) (∘-cong₁ {g = g} (join-inb₂ a b))))

  one : ∀ {Xm N N₀ : SemiMod.Semimodule} (out : Xm ⇒ N) (up : N₀ ⇒ N) {c R' : Xm ⇒ N₀} → c ≈ R' →
        (out +ₘ (up ∘ (c ∘ I))) ≈ (out +ₘ (up ∘ R'))
  one out up e = +ₘ-cong (≈-refl {f = out}) (∘-cong₂ {f = up} (≈-trans id-right e))

  one-inputs : ∀ {Xm M' N N₀ : SemiMod.Semimodule} (out : Xm ⇒ N) (up : N₀ ⇒ N) (ins : Xm ⇒ M')
               {c R' : M' ⇒ N₀} → c ≈ R' →
               (out +ₘ (up ∘ (c ∘ ins))) ≈ (out +ₘ (up ∘ (R' ∘ ins)))
  one-inputs out up ins e = +ₘ-cong (≈-refl {f = out}) (∘-cong₂ {f = up} (∘-cong₁ {g = ins} e))

  seq : ∀ {Xm M₂ N₁ N₂ : SemiMod.Semimodule} (ins : (Xm ⊕ᵥ N₁) ⇒ M₂) {c₁ R₁ : Xm ⇒ N₁} {c₂ T : M₂ ⇒ N₂} →
        c₁ ≈ R₁ → c₂ ≈ T →
        ((εₘ +ₘ (εₘ ∘ (c₁ ∘ I))) +ₘ (I ∘ (c₂ ∘ (ins ∘ ⟨ I , c₁ ∘ I ⟩))))
        ≈ (T ∘ (ins ∘ ⟨ I , R₁ ⟩))
  seq ins {c₁ = c₁} {R₁ = R₁} {c₂ = c₂} {T = T} e₁ e₂ =
    ≈-trans
      (+ₘ-cong (absorb₁ εₘ (c₁ ∘ I))
               (≈-trans id-left
                        (∘-cong e₂ (∘-cong₂ {f = ins} (pair-congᴴ (≈-refl {f = I}) (≈-trans id-right e₁))))))
      (+ₘ-lunit (T ∘ (ins ∘ ⟨ I , R₁ ⟩)))

  seq3 : ∀ {Xm M₃ N₁ N₂ N₃ : SemiMod.Semimodule} (ins : ((Xm ⊕ᵥ N₁) ⊕ᵥ N₂) ⇒ M₃)
         {c₁ R₁ : Xm ⇒ N₁} {c₂ R₂ : Xm ⇒ N₂} {c₃ U : M₃ ⇒ N₃} →
         c₁ ≈ R₁ → c₂ ≈ R₂ → c₃ ≈ U →
         (((εₘ +ₘ (εₘ ∘ (c₁ ∘ I))) +ₘ (εₘ ∘ (c₂ ∘ I))) +ₘ
          (I ∘ (c₃ ∘ (ins ∘ ⟨ ⟨ I , c₁ ∘ I ⟩ , c₂ ∘ I ⟩))))
         ≈ (U ∘ (ins ∘ ⟨ ⟨ I , R₁ ⟩ , R₂ ⟩))
  seq3 ins {c₁ = c₁} {R₁ = R₁} {c₂ = c₂} {R₂ = R₂} {c₃ = c₃} {U = U} e₁ e₂ e₃ =
    ≈-trans
      (+ₘ-cong (≈-trans (absorb₁ _ (c₂ ∘ I)) (absorb₁ εₘ (c₁ ∘ I)))
               (≈-trans id-left
                        (∘-cong e₃ (∘-cong₂ {f = ins} (pair-congᴴ (pair-congᴴ (≈-refl {f = I}) (≈-trans id-right e₁))
                                                        (≈-trans id-right e₂))))))
      (+ₘ-lunit (U ∘ (ins ∘ ⟨ ⟨ I , R₁ ⟩ , R₂ ⟩)))

  ignore-root : ∀ {Xm M₂ N₁ : SemiMod.Semimodule} (A : Xm ⇒ M₂) (X : Xm ⇒ N₁) →
                ((A ∘ pb₁) ∘ ⟨ I , X ⟩) ≈ A
  ignore-root A X =
    ≈-trans (assoc A pb₁ ⟨ I , X ⟩)
            (≈-trans (∘-cong₂ {f = A} (pair-pb₁ I X)) id-right)

  two-roots : ∀ {Xm M₁ M₂ N N₁ N₂ : SemiMod.Semimodule} (out : Xm ⇒ N) (r₁ : Xm ⇒ M₁) (ins₂ : (Xm ⊕ᵥ N₁) ⇒ M₂)
              (u₁ : N₁ ⇒ N) (u₂ : N₂ ⇒ N)
              (c₁ : M₁ ⇒ N₁) (c₂ : M₂ ⇒ N₂) {X₁ : Xm ⇒ N₁} {X₂ : Xm ⇒ N₂} →
              (c₁ ∘ r₁) ≈ X₁ → (c₂ ∘ (ins₂ ∘ ⟨ I , c₁ ∘ r₁ ⟩)) ≈ X₂ →
              ((out +ₘ (u₁ ∘ (c₁ ∘ r₁))) +ₘ (u₂ ∘ (c₂ ∘ (ins₂ ∘ ⟨ I , c₁ ∘ r₁ ⟩))))
              ≈ (out +ₘ ((u₁ ∘ X₁) +ₘ (u₂ ∘ X₂)))
  two-roots out r₁ ins₂ u₁ u₂ c₁ c₂ {X₁ = X₁} {X₂ = X₂} e₁ e₂ =
    ≈-trans
      (+ₘ-cong (+ₘ-cong (≈-refl {f = out}) (∘-cong₂ {f = u₁} e₁)) (∘-cong₂ {f = u₂} e₂))
      (+ₘ-assoc {f = out} {g = u₁ ∘ X₁} {h = u₂ ∘ X₂})

  proj-join : ∀ a b (X : 𝔽 a ⇒ 𝔽 b) →
              ((mat (M.p₁ {a} {b}) ∘ join a b) ∘ ⟨ I , X ⟩) ≈ I
  proj-join a b X =
    ≈-trans (assoc (mat (M.p₁ {a} {b})) (join a b) ⟨ I , X ⟩)
    (≈-trans (∘-cong₂ {f = mat (M.p₁ {a} {b})}
               (≈-trans (join-pair I X) (+ₘ-cong id-right ≈-refl)))
    (≈-trans (CME.comp-bilinear₂ (mat (M.p₁ {a} {b})) (mat (M.in₁ {a} {b})) (mat (M.in₂ {a} {b}) ∘ X))
    (≈-trans (+ₘ-cong (≈-trans (≈-sym (mat-comp (M.p₁ {a} {b}) (M.in₁ {a} {b})))
                               (≈-trans (mat-cong (M.id-1 a b)) mat-I))
                      (≈-trans (≈-sym (assoc (mat (M.p₁ {a} {b})) (mat (M.in₂ {a} {b})) X))
                      (≈-trans (∘-cong₁ {g = X} (≈-trans (≈-sym (mat-comp (M.p₁ {a} {b}) (M.in₂ {a} {b})))
                                                          (≈-trans (mat-cong (M.zero-1 a b)) mat-ε)))
                               (CME.comp-bilinear-ε₁ X))))
             (+ₘ-runit I))))

  inputs-only : ∀ {a b N₂ : ℕ} (c₂ : 𝔽 a ⇒ 𝔽 N₂) (X : 𝔽 a ⇒ 𝔽 b)
                {R : 𝔽 a ⇒ 𝔽 N₂} → c₂ ≈ R →
                (c₂ ∘ ((mat (M.p₁ {a} {b}) ∘ join a b) ∘ ⟨ I , X ⟩)) ≈ R
  inputs-only {a} {b} c₂ X e =
    ≈-trans (∘-cong₂ {f = c₂} (proj-join a b X)) (≈-trans id-right e)

  mu : ∀ {Xm M' N N' : SemiMod.Semimodule} (rc : N ⇒ N') (ic : Xm ⇒ M') {c F : M' ⇒ N} → c ≈ F →
       (εₘ +ₘ (rc ∘ (c ∘ ic))) ≈ (rc ∘ (F ∘ ic))
  mu rc ic {c = c} e = ≈-trans (+ₘ-lunit (rc ∘ (c ∘ ic))) (∘-cong₂ {f = rc} (∘-cong₁ {g = ic} e))

  pair-pb₂ : ∀ {Z X Y : SemiMod.Semimodule} (f : Z ⇒ X) (g : Z ⇒ Y) → (pb₂ ∘ ⟨ f , g ⟩) ≈ g
  pair-pb₂ {Z} {X} {Y} f g =
    ≈-trans (CME.comp-bilinear₂ pb₂ (inb₁ ∘ f) (inb₂ ∘ g))
    (≈-trans (+ₘ-cong (≈-trans (≈-sym (assoc pb₂ inb₁ f)) (≈-trans (∘-cong₁ {g = f} BPP.zero-2)
                                                                   (CME.comp-bilinear-ε₁ f)))
                      (≈-trans (≈-sym (assoc pb₂ inb₂ g)) (≈-trans (∘-cong₁ {g = g} BPP.id-2) id-left)))
             (+ₘ-lunit g))

  pair-∘ : ∀ {Z W X Y : SemiMod.Semimodule} (f : Z ⇒ X) (g : Z ⇒ Y) (h : W ⇒ Z) →
           (⟨ f , g ⟩ ∘ h) ≈ ⟨ f ∘ h , g ∘ h ⟩
  pair-∘ f g h =
    ≈-trans (CME.comp-bilinear₁ (inb₁ ∘ f) (inb₂ ∘ g) h)
            (+ₘ-cong (assoc inb₁ f h) (assoc inb₂ g h))

  glue-out-up : ∀ {k m n} (out : M.Matrix n k) (up : M.Matrix n m) (R : M.Matrix m k) →
                mat (out M.+ₘ (up M.∘ R)) ≈ (mat out +ₘ (mat up ∘ mat R))
  glue-out-up out up R = ≈-trans (mat-+ out (up M.∘ R)) (+ₘ-cong ≈-refl (mat-comp up R))

  glue-seq : ∀ {a b k n} (Tm : M.Matrix n k) (bi : M.Matrix k (a + b)) (Rm : M.Matrix b a) →
             mat (Tm M.∘ (bi M.∘ ⟨ M.I , Rm ⟩ₘ)) ≈ (mat Tm ∘ ((mat bi ∘ join a b) ∘ ⟨ I , mat Rm ⟩))
  glue-seq {a} {b} Tm bi Rm =
    ≈-trans (mat-comp Tm (bi M.∘ ⟨ M.I , Rm ⟩ₘ))
    (∘-cong₂ {f = mat Tm}
      (≈-trans (mat-comp bi ⟨ M.I , Rm ⟩ₘ)
      (≈-trans (∘-cong₂ {f = mat bi}
                 (≈-trans (mat-pair M.I Rm)
                          (∘-cong₂ {f = join a b} (pair-congᴴ mat-I (≈-refl {f = mat Rm})))))
               (≈-sym (assoc (mat bi) (join a b) ⟨ I , mat Rm ⟩)))))

  glue-fold : ∀ {a b n} (Fm : M.Matrix n (a + b)) (Rm : M.Matrix b a) →
              mat (Fm M.∘ ⟨ M.I , Rm ⟩ₘ) ≈ (mat Fm ∘ (join a b ∘ ⟨ I , mat Rm ⟩))
  glue-fold {a} {b} Fm Rm =
    ≈-trans (mat-comp Fm ⟨ M.I , Rm ⟩ₘ)
      (∘-cong₂ {f = mat Fm}
        (≈-trans (mat-pair M.I Rm) (∘-cong₂ {f = join a b} (pair-congᴴ mat-I (≈-refl {f = mat Rm})))))

  glue-app : ∀ {a b c k n} (Um : M.Matrix n k) (bi : M.Matrix k ((a + b) + c))
             (Rm : M.Matrix b a) (Tm : M.Matrix c a) →
             mat (Um M.∘ (bi M.∘ ⟨ ⟨ M.I , Rm ⟩ₘ , Tm ⟩ₘ)) ≈
             (mat Um ∘ ((mat bi ∘ (join (a + b) c ∘ ⟨ join a b ∘ pb₁ , pb₂ ⟩)) ∘ ⟨ ⟨ I , mat Rm ⟩ , mat Tm ⟩))
  glue-app {a} {b} {c} Um bi Rm Tm =
    ≈-trans (mat-comp Um (bi M.∘ ⟨ ⟨ M.I , Rm ⟩ₘ , Tm ⟩ₘ))
    (∘-cong₂ {f = mat Um}
      (≈-trans (mat-comp bi ⟨ ⟨ M.I , Rm ⟩ₘ , Tm ⟩ₘ)
      (≈-trans (∘-cong₂ {f = mat bi}
                 (≈-trans (mat-pair ⟨ M.I , Rm ⟩ₘ Tm)
                 (≈-trans (∘-cong₂ {f = join (a + b) c}
                            (pair-congᴴ (≈-trans (mat-pair M.I Rm)
                                                 (∘-cong₂ {f = join a b} (pair-congᴴ mat-I (≈-refl {f = mat Rm}))))
                                        (≈-refl {f = mat Tm})))
                          (∘-cong₂ {f = join (a + b) c}
                            (≈-sym (≈-trans (pair-∘ (join a b ∘ pb₁) pb₂ ⟨ ⟨ I , mat Rm ⟩ , mat Tm ⟩)
                                   (pair-congᴴ (≈-trans (assoc (join a b) pb₁ ⟨ ⟨ I , mat Rm ⟩ , mat Tm ⟩)
                                                        (∘-cong₂ {f = join a b} (pair-pb₁ ⟨ I , mat Rm ⟩ (mat Tm))))
                                               (pair-pb₂ ⟨ I , mat Rm ⟩ (mat Tm)))))))))
               (≈-trans (∘-cong₂ {f = mat bi}
                          (≈-sym (assoc (join (a + b) c) ⟨ join a b ∘ pb₁ , pb₂ ⟩ ⟨ ⟨ I , mat Rm ⟩ , mat Tm ⟩)))
                        (≈-sym (assoc (mat bi) (join (a + b) c ∘ ⟨ join a b ∘ pb₁ , pb₂ ⟩) ⟨ ⟨ I , mat Rm ⟩ , mat Tm ⟩))))))

  glue-pair-out : ∀ {k a b w} (bo : M.Matrix w k) (Rm : M.Matrix a k) (Tm : M.Matrix b k)
                  (j : M.Matrix w (a + b)) →
                  mat (bo M.+ₘ (j M.∘ ⟨ Rm , Tm ⟩ₘ)) ≈
                  (mat bo +ₘ (((mat j ∘ mat (M.in₁ {a} {b})) ∘ mat Rm) +ₘ ((mat j ∘ mat (M.in₂ {a} {b})) ∘ mat Tm)))
  glue-pair-out {k} {a} {b} bo Rm Tm j =
    ≈-trans (mat-+ bo (j M.∘ ⟨ Rm , Tm ⟩ₘ))
    (+ₘ-cong ≈-refl
      (≈-trans (mat-comp j ⟨ Rm , Tm ⟩ₘ)
      (≈-trans (∘-cong₂ {f = mat j} (mat-pair-flat Rm Tm))
      (≈-trans (CME.comp-bilinear₂ (mat j) (mat (M.in₁ {a} {b}) ∘ mat Rm) (mat (M.in₂ {a} {b}) ∘ mat Tm))
               (+ₘ-cong (≈-sym (assoc (mat j) (mat (M.in₁ {a} {b})) (mat Rm)))
                        (≈-sym (assoc (mat j) (mat (M.in₂ {a} {b})) (mat Tm))))))))

  ignore-rootF : ∀ {a b} {M₂ : SemiMod.Semimodule} (A : 𝔽 a ⇒ M₂) (X : 𝔽 a ⇒ 𝔽 b) →
                 ((A ∘ (mat (M.p₁ {a} {b}) ∘ join a b)) ∘ ⟨ I , X ⟩) ≈ A
  ignore-rootF {a} {b} A X =
    ≈-trans (assoc A (mat (M.p₁ {a} {b}) ∘ join a b) ⟨ I , X ⟩)
            (≈-trans (∘-cong₂ {f = A} (proj-join a b X)) id-right)

mutual
  agree : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → collapse (graph D) ≈ mat R
  agree {τ = τ} (⇓-var {γ = γ} x) = Rule₀.agree (fo-of τ) (mat (var-out x γ))
  agree {τ = τ} (⇓-unit {γ = γ}) = Rule₀.agree (fo-of τ) (mat wctrl)
  agree {τ = τ} (⇓-lam {γ = γ} {t = t}) = Rule₀.agree (fo-of τ) (mat (lam-out γ t))
  agree {τ = τ} (⇓-inl {γ = γ} {v = v} {R = R} D) =
    ≈-trans (Rule₁.agree (graph D) I (fo-of τ) (mat (built-out γ (width v))) (mat (M.in₂ {1})))
    (≈-trans (one (mat (built-out γ (width v))) (mat (M.in₂ {1})) (agree D))
             (≈-sym (glue-out-up (built-out γ (width v)) (M.in₂ {1}) R)))
  agree {τ = τ} (⇓-inr {γ = γ} {v = v} {R = R} D) =
    ≈-trans (Rule₁.agree (graph D) I (fo-of τ) (mat (built-out γ (width v))) (mat (M.in₂ {1})))
    (≈-trans (one (mat (built-out γ (width v))) (mat (M.in₂ {1})) (agree D))
             (≈-sym (glue-out-up (built-out γ (width v)) (M.in₂ {1}) R)))
  agree {τ = τ} (⇓-case-l {γ = γ} {v = v} {R = R} {T = T} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph D₂) I
                       (mat (branch-inputs γ v) ∘ join (suc (width-env γ)) (suc (width v)))
                       (fo-of τ) εₘ εₘ I)
    (≈-trans (seq (mat (branch-inputs γ v) ∘ join (suc (width-env γ)) (suc (width v))) (agree D₁) (agree D₂))
             (≈-sym (glue-seq T (branch-inputs γ v) R)))
  agree {τ = τ} (⇓-case-r {γ = γ} {v = v} {R = R} {T = T} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph D₂) I
                       (mat (branch-inputs γ v) ∘ join (suc (width-env γ)) (suc (width v)))
                       (fo-of τ) εₘ εₘ I)
    (≈-trans (seq (mat (branch-inputs γ v) ∘ join (suc (width-env γ)) (suc (width v))) (agree D₁) (agree D₂))
             (≈-sym (glue-seq T (branch-inputs γ v) R)))
  agree {τ = τ} (⇓-pair {γ = γ} {v = v} {u = u} {R = R} {T = T} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph D₂) I insH (fo-of τ) (mat (built-out γ (width v + width u))) u₁ u₂)
    (≈-trans (two-roots (mat (built-out γ (width v + width u))) I insH u₁ u₂
                        (collapse (graph D₁)) (collapse (graph D₂))
                        (≈-trans id-right (agree D₁))
                        (inputs-only (collapse (graph D₂)) (collapse (graph D₁) ∘ I) (agree D₂)))
    (≈-trans (+ₘ-cong (≈-refl {f = mat (built-out γ (width v + width u))})
                      (+ₘ-cong (∘-cong₁ {g = mat R} (mat-comp (M.in₂ {1}) (M.in₁ {width v} {width u})))
                               (∘-cong₁ {g = mat T} (mat-comp (M.in₂ {1}) (M.in₂ {width v} {width u})))))
             (≈-sym (glue-pair-out (built-out γ (width v + width u)) R T (M.in₂ {1})))))
    where
    insH = mat (p₁ {suc (width-env γ)} {width v}) ∘ join (suc (width-env γ)) (width v)
    u₁ = mat (M.in₂ {1} M.∘ M.in₁ {width v} {width u})
    u₂ = mat (M.in₂ {1} M.∘ M.in₂ {width v} {width u})
  agree {τ = τ} (⇓-fst {γ = γ} {v = v} {u = u} {R = R} D) =
    ≈-trans (Rule₁.agree (graph D) I (fo-of τ) (mat (elim-out γ v)) (mat (proj-up {width v} {width u} v (p₁ {width v} {width u}))))
    (≈-trans (one (mat (elim-out γ v)) (mat (proj-up {width v} {width u} v (p₁ {width v} {width u}))) (agree D))
             (≈-sym (glue-out-up (elim-out γ v) (proj-up {width v} {width u} v (p₁ {width v} {width u})) R)))
  agree {τ = τ} (⇓-snd {γ = γ} {v = v} {u = u} {R = R} D) =
    ≈-trans (Rule₁.agree (graph D) I (fo-of τ) (mat (elim-out γ u)) (mat (proj-up {width v} {width u} u (p₂ {width v} {width u}))))
    (≈-trans (one (mat (elim-out γ u)) (mat (proj-up {width v} {width u} u (p₂ {width v} {width u}))) (agree D))
             (≈-sym (glue-out-up (elim-out γ u) (proj-up {width v} {width u} u (p₂ {width v} {width u})) R)))
  agree {τ = τ} (⇓-app {γ = γ} {γ' = γ'} {v = v} {R = R} {T = T} {U = U} D₁ D₂ D₃) =
    ≈-trans (Rule₃.agree (graph D₁) (graph D₂) (graph D₃) I I insH (fo-of τ) εₘ εₘ εₘ I)
    (≈-trans (seq3 insH (agree D₁) (agree D₂) (agree D₃))
             (≈-sym (glue-app U (body-inputs γ γ' v) R T)))
    where
    insH = mat (body-inputs γ γ' v) ∘
             (join (suc (width-env γ) + suc (width-env γ')) (width v) ∘
               ⟨ join (suc (width-env γ)) (suc (width-env γ')) ∘ pb₁ , pb₂ ⟩)
  agree {τ = τ} (⇓-bop {γ = γ} {ω = ω} {vs = vs} {R = R} D) =
    ≈-trans (Rule₁.agree (graph-s D) I (fo-of τ) (mat wctrl) (mat (op-deps ω .func vs)))
    (≈-trans (one (mat wctrl) (mat (op-deps ω .func vs)) (agree-s D))
             (≈-sym (glue-out-up wctrl (op-deps ω .func vs) R)))
  agree {τ = τ} (⇓-brel {γ = γ} {ω = ω} {vs = vs} {R = R} D) =
    ≈-trans (Rule₁.agree (graph-s D) I (fo-of τ) (mat wctrl) (mat (brel-deps ω vs (rel-pred ω .func vs))))
    (≈-trans (one (mat wctrl) (mat (brel-deps ω vs (rel-pred ω .func vs))) (agree-s D))
             (≈-sym (glue-out-up wctrl (brel-deps ω vs (rel-pred ω .func vs)) R)))
  agree {τ = τ} (⇓-roll {γ = γ} {R = R} D) =
    ≈-trans (Rule₁.agree (graph D) I (fo-of τ) εₘ I)
    (≈-trans (+ₘ-lunit (I ∘ (collapse (graph D) ∘ I)))
             (≈-trans id-left (≈-trans id-right (agree D))))
  agree {τ = τ} (⇓-fold {γ = γ} {v = v} {R = R} {F = F} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph-m D₂) I (join (suc (width-env γ)) (width v)) (fo-of τ) εₘ εₘ I)
    (≈-trans (seq (join (suc (width-env γ)) (width v)) (agree D₁) (agree-m D₂))
             (≈-sym (≈-trans (glue-fold F R) ≈-refl)))

  agree-s : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
            (D : γ , Ms ⇓s vs [ R ]) → collapse (graph-s D) ≈ mat R
  agree-s {γ = γ} [] = ≈-trans (Rule₀.agree Bool.true εₘ) (≈-sym mat-ε)
  agree-s {γ = γ} (_∷_ {is = is} {v = v} {R = R} {Rs = Rs} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph-s D₂) I insH Bool.true εₘ
                       (mat (M.in₁ {width (const v)} {bases-width is})) (mat (M.in₂ {width (const v)} {bases-width is})))
    (≈-trans (two-roots εₘ I insH
                        (mat (M.in₁ {width (const v)} {bases-width is})) (mat (M.in₂ {width (const v)} {bases-width is}))
                        (collapse (graph D₁)) (collapse (graph-s D₂))
                        (≈-trans id-right (agree D₁))
                        (inputs-only (collapse (graph-s D₂)) (collapse (graph D₁) ∘ I) (agree-s D₂)))
    (≈-trans (+ₘ-lunit ((mat (M.in₁ {width (const v)} {bases-width is}) ∘ mat R) +ₘ
                        (mat (M.in₂ {width (const v)} {bases-width is}) ∘ mat Rs)))
             (≈-sym (mat-pair-flat R Rs))))
    where
    insH = mat (p₁ {suc (width-env γ)} {width (const v)}) ∘ join (suc (width-env γ)) (width (const v))

  agree-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {v' : Val (σ' [ σr ])} {F}
            (D : Map γ s σ' v v' F) → collapse (graph-m D) ≈ mat F
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-rec {w = w} {w' = w'} {F = F} {T = T} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph-m D₁) (graph D₂) I insH (fo-of (σ' [ σr ])) εₘ εₘ I)
    (≈-trans (seq insH (agree-m D₁) (agree D₂))
             (≈-sym (glue-seq T (rec-inputs γ w') F)))
    where
    insH = mat (rec-inputs γ w') ∘ join (suc (width-env γ) + width w) (width w')
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-unit {v = v}) = Rule₀.agree (fo-of (σ' [ σr ])) (mat (map-leaf γ (width v)))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-base {v = v}) = Rule₀.agree (fo-of (σ' [ σr ])) (mat (map-leaf γ (width v)))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-arrow {v = v}) = Rule₀.agree (fo-of (σ' [ σr ])) (mat (map-leaf γ (width v)))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-inl {v = v} {v' = v'} {F = F} D) =
    ≈-trans (Rule₁.agree (graph-m D) (mat (sub-inputs γ (p₂ {1} {width v}))) (fo-of (σ' [ σr ]))
                       (mat (map-built-out γ (width v) (width v'))) (mat (M.in₂ {1})))
    (≈-trans (one-inputs (mat (map-built-out γ (width v) (width v'))) (mat (M.in₂ {1})) (mat (sub-inputs γ (p₂ {1} {width v})))
                         (agree-m D))
             (≈-sym (≈-trans (mat-+ (map-built-out γ (width v) (width v')) (M.in₂ {1} M.∘ (F M.∘ sub-inputs γ (p₂ {1} {width v}))))
                             (+ₘ-cong ≈-refl (≈-trans (mat-comp (M.in₂ {1}) (F M.∘ sub-inputs γ (p₂ {1} {width v})))
                                                      (∘-cong₂ {f = mat (M.in₂ {1})} (mat-comp F (sub-inputs γ (p₂ {1} {width v})))))))))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-inr {v = v} {v' = v'} {F = F} D) =
    ≈-trans (Rule₁.agree (graph-m D) (mat (sub-inputs γ (p₂ {1} {width v}))) (fo-of (σ' [ σr ]))
                       (mat (map-built-out γ (width v) (width v'))) (mat (M.in₂ {1})))
    (≈-trans (one-inputs (mat (map-built-out γ (width v) (width v'))) (mat (M.in₂ {1})) (mat (sub-inputs γ (p₂ {1} {width v})))
                         (agree-m D))
             (≈-sym (≈-trans (mat-+ (map-built-out γ (width v) (width v')) (M.in₂ {1} M.∘ (F M.∘ sub-inputs γ (p₂ {1} {width v}))))
                             (+ₘ-cong ≈-refl (≈-trans (mat-comp (M.in₂ {1}) (F M.∘ sub-inputs γ (p₂ {1} {width v})))
                                                      (∘-cong₂ {f = mat (M.in₂ {1})} (mat-comp F (sub-inputs γ (p₂ {1} {width v})))))))))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-pair {v = v} {v' = v'} {u = u} {u' = u'} {F = F} {G = G} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph-m D₁) (graph-m D₂) ins₁H ins₂H
                       (fo-of (σ' [ σr ])) (mat (map-built-out γ (width v + width u) (width v' + width u')))
                       u₁ u₂)
    (≈-trans (two-roots (mat (map-built-out γ (width v + width u) (width v' + width u'))) ins₁H ins₂H u₁ u₂
                        (collapse (graph-m D₁)) (collapse (graph-m D₂))
                        (∘-cong₁ {g = ins₁H} (agree-m D₁))
                        (≈-trans (∘-cong₂ {f = collapse (graph-m D₂)} (ignore-rootF ins₂core (collapse (graph-m D₁) ∘ ins₁H)))
                                 (∘-cong₁ {g = ins₂core} (agree-m D₂))))
    (≈-trans (+ₘ-cong (≈-refl {f = mat (map-built-out γ (width v + width u) (width v' + width u'))})
                      (+ₘ-cong (≈-trans (∘-cong₁ {g = mat F ∘ ins₁H} (mat-comp (M.in₂ {1}) (M.in₁ {width v'} {width u'})))
                                        (∘-cong₂ {f = mat (M.in₂ {1}) ∘ mat (M.in₁ {width v'} {width u'})} (≈-sym (mat-comp F (sub-inputs γ (p₁ {width v} {width u} M.∘ p₂ {1} {width v + width u}))))))
                               (≈-trans (∘-cong₁ {g = mat G ∘ ins₂core} (mat-comp (M.in₂ {1}) (M.in₂ {width v'} {width u'})))
                                        (∘-cong₂ {f = mat (M.in₂ {1}) ∘ mat (M.in₂ {width v'} {width u'})} (≈-sym (mat-comp G (sub-inputs γ (p₂ {width v} {width u} M.∘ p₂ {1} {width v + width u}))))))))
             (≈-sym (glue-pair-out (map-built-out γ (width v + width u) (width v' + width u'))
                                   (F M.∘ sub-inputs γ (p₁ {width v} {width u} M.∘ p₂ {1} {width v + width u}))
                                   (G M.∘ sub-inputs γ (p₂ {width v} {width u} M.∘ p₂ {1} {width v + width u}))
                                   (M.in₂ {1})))))
    where
    ins₁H = mat (sub-inputs γ (p₁ {width v} {width u} M.∘ p₂ {1} {width v + width u}))
    ins₂core = mat (sub-inputs γ (p₂ {width v} {width u} M.∘ p₂ {1} {width v + width u}))
    u₁ = mat (M.in₂ {1} M.∘ M.in₁ {width v'} {width u'})
    u₂ = mat (M.in₂ {1} M.∘ M.in₂ {width v'} {width u'})
    ins₂H = ins₂core ∘
              (mat (p₁ {suc (width-env γ) + suc (width v + width u)} {width v'}) ∘
                join (suc (width-env γ) + suc (width v + width u)) (width v'))
  agree-m {γ = γ} {τ₀ = τ₀} {σr = σr} {σ' = σ'} (m-mu {τ' = τ'} {w = w} {w' = w'} {F = F} D) =
    ≈-trans (Rule₁.agree (graph-m D) (mat (sub-inputs γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) M.I)))
                       (fo-of (σ' [ σr ])) εₘ (mat (rcast (sym (width-subst (unfold₁-inst τ' σr) w')) M.I)))
    (≈-trans (mu (mat (rcast (sym (width-subst (unfold₁-inst τ' σr) w')) M.I))
                 (mat (sub-inputs γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) M.I))) (agree-m D))
             (≈-sym (≈-trans (mat-comp (rcast (sym (width-subst (unfold₁-inst τ' σr) w')) M.I)
                                       (F M.∘ sub-inputs γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) M.I)))
                             (∘-cong₂ {f = mat (rcast (sym (width-subst (unfold₁-inst τ' σr) w')) M.I)}
                                      (mat-comp F (sub-inputs γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)) M.I)))))))
