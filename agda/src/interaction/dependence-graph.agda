{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _+_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (sym; cong)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List.Relation.Unary.All using ([]; _∷_) renaming (All to Every)
open import prop-setoid using (Setoid) renaming (_⇒_ to _⇒ₛ_)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)
import sd-semimodule-primitives

-- The dependence graph of a derivation with a control input. Each rule builds its graph from its
-- premises' graphs using the wiring that also defines the rule's relation, so collapsing the graph
-- recovers the relation rule by rule. Vertices carry free semimodules; the relation is a morphism
-- and enters the graph directly, with join comparing the vertex pairing with the width sum.
module interaction.dependence-graph {ℓ} (Sig : Signature ℓ) {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (ℐ : Interpretation S Sig) (ctrl-weight : Setoid.Carrier A)
  (let module S = CommutativeSemiring S) (+-idem : ∀ x → (x S.+ x) S.≈ x) where

open Signature Sig
open Interpretation ℐ
open _⇒ₛ_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-operational.evaluation Sig S ℐ ctrl-weight hiding (_⇒_; ⟨_,_⟩; I; εₘ)
open import interaction.graph S +-idem
open import matrix-embedding S using (𝔽; 𝔽-biproduct)

private
  module SDP = sd-semimodule-primitives S
open SDP.interp-deps Sig ℐ using (op-dep)

open import categories using (Category)
open Category SemiMod.cat
  using (_⇒_; _∘_; _≈_; ∘-cong; ∘-cong₁; ∘-cong₂; assoc; id-left; id-right; ≈-refl; ≈-sym; ≈-trans)
open import cmon-enriched using (CMonEnriched; Biproduct)
private
  module CME = CMonEnriched SemiMod.cmon-enriched
  module BPP {X Y : SemiMod.Semimodule} = Biproduct (SemiMod.biproduct X Y)
  module FB {m n : ℕ} = Biproduct (𝔽-biproduct m n)

fo-of : ∀ {Δ} (τ : type Δ) → Bool
fo-of τ = ⌊ first-order? τ ⌋

private
  join : ∀ m n → (𝔽 m ⊕ᵥ 𝔽 n) ⇒ 𝔽 (m + n)
  join m n = (in₁ {m} {n} ∘ pb₁) +ₘ (in₂ {m} {n} ∘ pb₂)

  join-inb₁ : ∀ m n → (join m n ∘ inb₁) ≈ in₁ {m} {n}
  join-inb₁ m n =
    ≈-trans (CME.comp-bilinear₁ (in₁ {m} {n} ∘ pb₁) (in₂ {m} {n} ∘ pb₂) inb₁)
    (≈-trans (+ₘ-cong (≈-trans (assoc (in₁ {m} {n}) pb₁ inb₁)
                               (≈-trans (∘-cong₂ {f = in₁ {m} {n}} BPP.id-1) id-right))
                      (≈-trans (assoc (in₂ {m} {n}) pb₂ inb₁)
                               (≈-trans (∘-cong₂ {f = in₂ {m} {n}} BPP.zero-2)
                                        (CME.comp-bilinear-ε₂ (in₂ {m} {n})))))
             (+ₘ-runit (in₁ {m} {n})))

  join-inb₂ : ∀ m n → (join m n ∘ inb₂) ≈ in₂ {m} {n}
  join-inb₂ m n =
    ≈-trans (CME.comp-bilinear₁ (in₁ {m} {n} ∘ pb₁) (in₂ {m} {n} ∘ pb₂) inb₂)
    (≈-trans (+ₘ-cong (≈-trans (assoc (in₁ {m} {n}) pb₁ inb₂)
                               (≈-trans (∘-cong₂ {f = in₁ {m} {n}} BPP.zero-1)
                                        (CME.comp-bilinear-ε₂ (in₁ {m} {n}))))
                      (≈-trans (assoc (in₂ {m} {n}) pb₂ inb₂)
                               (≈-trans (∘-cong₂ {f = in₂ {m} {n}} BPP.id-2) id-right)))
             (+ₘ-lunit (in₂ {m} {n})))

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

mutual
  graph : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} → γ , t ⇓ v [ R ] →
          Graph (suc (width-env γ)) (width v)
  graph {τ = τ} (⇓-var {γ = γ} x) = Rule₀.E (fo-of τ) (var-out x γ)
  graph {τ = τ} (⇓-unit {γ = γ}) = Rule₀.E (fo-of τ) wctrl
  graph {τ = τ} (⇓-lam {γ = γ} {t = t}) = Rule₀.E (fo-of τ) (lam-out γ t)
  graph {τ = τ} (⇓-inl {γ = γ} {v = v} D) =
    Rule₁.E (graph D) I (fo-of τ) (built-out γ (width v)) (in₂ {1})
  graph {τ = τ} (⇓-inr {γ = γ} {v = v} D) =
    Rule₁.E (graph D) I (fo-of τ) (built-out γ (width v)) (in₂ {1})
  graph {τ = τ} (⇓-case-l {γ = γ} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph D₂) I
          (branch-inputs γ v ∘ join (suc (width-env γ)) (suc (width v)))
          (fo-of τ) εₘ εₘ I
  graph {τ = τ} (⇓-case-r {γ = γ} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph D₂) I
          (branch-inputs γ v ∘ join (suc (width-env γ)) (suc (width v)))
          (fo-of τ) εₘ εₘ I
  graph {τ = τ} (⇓-pair {γ = γ} {v = v} {u = u} D₁ D₂) =
    Rule₂.E (graph D₁) (graph D₂) I
          (p₁ {suc (width-env γ)} {width v} ∘ join (suc (width-env γ)) (width v))
          (fo-of τ) (built-out γ (width v + width u))
          (in₂ {1} ∘ in₁ {width v} {width u}) (in₂ {1} ∘ in₂ {width v} {width u})
  graph {τ = τ} (⇓-fst {γ = γ} {v = v} {u = u} D) =
    Rule₁.E (graph D) I (fo-of τ) (elim-out γ v) (proj-up {width v} {width u} v (p₁ {width v} {width u}))
  graph {τ = τ} (⇓-snd {γ = γ} {v = v} {u = u} D) =
    Rule₁.E (graph D) I (fo-of τ) (elim-out γ u) (proj-up {width v} {width u} u (p₂ {width v} {width u}))
  graph {τ = τ} (⇓-app {γ = γ} {γ' = γ'} {v = v} D₁ D₂ D₃) =
    Rule₃.E (graph D₁) (graph D₂) (graph D₃) I I
          (body-inputs γ γ' v ∘
            (join (suc (width-env γ) + suc (width-env γ')) (width v) ∘
              ⟨ join (suc (width-env γ)) (suc (width-env γ')) ∘ pb₁ , pb₂ ⟩))
          (fo-of τ) εₘ εₘ εₘ I
  graph {τ = τ} (⇓-bop {γ = γ} {ω = ω} {vs = vs} D) =
    Ruleₛ.E (fo-of τ) wctrl (premises D (op-dep ω vs))
  graph {τ = τ} (⇓-brel {γ = γ} {ω = ω} {vs = vs} D) =
    Ruleₛ.E (fo-of τ) wctrl (premises D (brel-deps ω vs (rel-pred ω .func vs)))
  graph {τ = τ} (⇓-roll {γ = γ} D) = Rule₁.E (graph D) I (fo-of τ) εₘ I
  graph {τ = τ} (⇓-fold {γ = γ} {v = v} D₁ D₂) =
    Rule₂.E (graph D₁) (graph-m D₂) I (join (suc (width-env γ)) (width v)) (fo-of τ) εₘ εₘ I

  premises : ∀ {Γ is n} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
             γ , Ms ⇓s vs [ R ] → 𝔽 (bases-width is) ⇒ 𝔽 n → List (Premise (suc (width-env γ)) n)
  premises [] u = []
  premises (_∷_ {is = is} {v = v} D₁ D₂) u =
    premise (graph D₁) I (u ∘ in₁ {width (const v)} {bases-width is}) ∷
    premises D₂ (u ∘ in₂ {width (const v)} {bases-width is})

  graph-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {v' : Val (σ' [ σr ])} {F} →
            Map γ s σ' v v' F → Graph (suc (width-env γ) + width v) (width v')
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-rec {w = w} {w' = w'} D₁ D₂) =
    Rule₂.E (graph-m D₁) (graph D₂) I
          (rec-inputs γ w' ∘ join (suc (width-env γ) + width w) (width w'))
          (fo-of (σ' [ σr ])) εₘ εₘ I
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-unit {v = v}) = Rule₀.E (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-base {v = v}) = Rule₀.E (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-arrow {v = v}) = Rule₀.E (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-inl {v = v} {v' = v'} D) =
    Rule₁.E (graph-m D) (sub-inputs γ (p₂ {1} {width v})) (fo-of (σ' [ σr ]))
          (map-built-out γ (width v) (width v')) (in₂ {1})
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-inr {v = v} {v' = v'} D) =
    Rule₁.E (graph-m D) (sub-inputs γ (p₂ {1} {width v})) (fo-of (σ' [ σr ]))
          (map-built-out γ (width v) (width v')) (in₂ {1})
  graph-m {γ = γ} {σr = σr} {σ' = σ'} (m-pair {v = v} {v' = v'} {u = u} {u' = u'} D₁ D₂) =
    Rule₂.E (graph-m D₁) (graph-m D₂)
          (sub-inputs γ (p₁ {width v} {width u} ∘ p₂ {1} {width v + width u}))
          (sub-inputs γ (p₂ {width v} {width u} ∘ p₂ {1} {width v + width u}) ∘
            (p₁ {suc (width-env γ) + suc (width v + width u)} {width v'} ∘
              join (suc (width-env γ) + suc (width v + width u)) (width v')))
          (fo-of (σ' [ σr ])) (map-built-out γ (width v + width u) (width v' + width u'))
          (in₂ {1} ∘ in₁ {width v'} {width u'}) (in₂ {1} ∘ in₂ {width v'} {width u'})
  graph-m {γ = γ} {τ₀ = τ₀} {σr = σr} {σ' = σ'} (m-mu {τ' = τ'} {w = w} {w' = w'} D) =
    Rule₁.E (graph-m D) (sub-inputs γ (Category.≡-to-⇒ SemiMod.cat (cong 𝔽 (width-subst (unfold₁-inst τ' (μ τ₀)) w))))
          (fo-of (σ' [ σr ])) εₘ (Category.≡-to-⇒ SemiMod.cat (cong 𝔽 (sym (width-subst (unfold₁-inst τ' σr) w'))))

private
  join-pair : ∀ {a b} {Z : SemiMod.Semimodule} (f : Z ⇒ 𝔽 a) (g : Z ⇒ 𝔽 b) →
              (join a b ∘ ⟨ f , g ⟩) ≈ ((in₁ {a} {b} ∘ f) +ₘ (in₂ {a} {b} ∘ g))
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
              ((p₁ {a} {b} ∘ join a b) ∘ ⟨ I , X ⟩) ≈ I
  proj-join a b X =
    ≈-trans (assoc (p₁ {a} {b}) (join a b) ⟨ I , X ⟩)
    (≈-trans (∘-cong₂ {f = p₁ {a} {b}}
               (≈-trans (join-pair I X) (+ₘ-cong id-right ≈-refl)))
    (≈-trans (CME.comp-bilinear₂ (p₁ {a} {b}) (in₁ {a} {b}) (in₂ {a} {b} ∘ X))
    (≈-trans (+ₘ-cong (FB.id-1 {a} {b})
                      (≈-trans (≈-sym (assoc (p₁ {a} {b}) (in₂ {a} {b}) X))
                      (≈-trans (∘-cong₁ {g = X} (FB.zero-1 {a} {b}))
                               (CME.comp-bilinear-ε₁ X))))
             (+ₘ-runit I))))

  inputs-only : ∀ {a b N₂ : ℕ} (c₂ : 𝔽 a ⇒ 𝔽 N₂) (X : 𝔽 a ⇒ 𝔽 b)
                {R : 𝔽 a ⇒ 𝔽 N₂} → c₂ ≈ R →
                (c₂ ∘ ((p₁ {a} {b} ∘ join a b) ∘ ⟨ I , X ⟩)) ≈ R
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

  up-pair : ∀ {a b m} {Z : SemiMod.Semimodule} (u : 𝔽 (a + b) ⇒ 𝔽 m) (f : Z ⇒ 𝔽 a) (g : Z ⇒ 𝔽 b) →
            (((u ∘ in₁ {a} {b}) ∘ f) +ₘ ((u ∘ in₂ {a} {b}) ∘ g)) ≈
            (u ∘ ((in₁ {a} {b} ∘ f) +ₘ (in₂ {a} {b} ∘ g)))
  up-pair {a} {b} u f g =
    ≈-sym (≈-trans (CME.comp-bilinear₂ u (in₁ {a} {b} ∘ f) (in₂ {a} {b} ∘ g))
                   (+ₘ-cong (≈-sym (assoc u (in₁ {a} {b}) f)) (≈-sym (assoc u (in₂ {a} {b}) g))))

  seam : ∀ {a b} {M' : SemiMod.Semimodule} (bi : 𝔽 (a + b) ⇒ M') (X : 𝔽 a ⇒ 𝔽 b) →
         ((bi ∘ join a b) ∘ ⟨ I , X ⟩) ≈ (bi ∘ ((in₁ {a} {b} ∘ I) +ₘ (in₂ {a} {b} ∘ X)))
  seam {a} {b} bi X =
    ≈-trans (assoc bi (join a b) ⟨ I , X ⟩) (∘-cong₂ {f = bi} (join-pair I X))

  seam-app : ∀ {a b c} {M' : SemiMod.Semimodule} (bi : 𝔽 ((a + b) + c) ⇒ M')
             (X : 𝔽 a ⇒ 𝔽 b) (Y : 𝔽 a ⇒ 𝔽 c) →
             ((bi ∘ (join (a + b) c ∘ ⟨ join a b ∘ pb₁ , pb₂ ⟩)) ∘ ⟨ ⟨ I , X ⟩ , Y ⟩) ≈
             (bi ∘ ((in₁ {a + b} {c} ∘ ((in₁ {a} {b} ∘ I) +ₘ (in₂ {a} {b} ∘ X))) +ₘ (in₂ {a + b} {c} ∘ Y)))
  seam-app {a} {b} {c} bi X Y =
    ≈-trans (assoc bi (join (a + b) c ∘ ⟨ join a b ∘ pb₁ , pb₂ ⟩) ⟨ ⟨ I , X ⟩ , Y ⟩)
    (∘-cong₂ {f = bi}
      (≈-trans (assoc (join (a + b) c) ⟨ join a b ∘ pb₁ , pb₂ ⟩ ⟨ ⟨ I , X ⟩ , Y ⟩)
      (≈-trans (∘-cong₂ {f = join (a + b) c}
                 (≈-trans (pair-∘ (join a b ∘ pb₁) pb₂ ⟨ ⟨ I , X ⟩ , Y ⟩)
                          (pair-congᴴ (≈-trans (assoc (join a b) pb₁ ⟨ ⟨ I , X ⟩ , Y ⟩)
                                               (≈-trans (∘-cong₂ {f = join a b} (pair-pb₁ ⟨ I , X ⟩ Y))
                                                        (join-pair I X)))
                                      (pair-pb₂ ⟨ I , X ⟩ Y))))
               (join-pair ((in₁ {a} {b} ∘ I) +ₘ (in₂ {a} {b} ∘ X)) Y))))

  ignore-rootF : ∀ {a b} {M₂ : SemiMod.Semimodule} (A : 𝔽 a ⇒ M₂) (X : 𝔽 a ⇒ 𝔽 b) →
                 ((A ∘ (p₁ {a} {b} ∘ join a b)) ∘ ⟨ I , X ⟩) ≈ A
  ignore-rootF {a} {b} A X =
    ≈-trans (assoc A (p₁ {a} {b} ∘ join a b) ⟨ I , X ⟩)
            (≈-trans (∘-cong₂ {f = A} (proj-join a b X)) id-right)

mutual
  agree : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → collapse (graph D) ≈ R
  agree {τ = τ} (⇓-var {γ = γ} x) = Rule₀.agree (fo-of τ) (var-out x γ)
  agree {τ = τ} (⇓-unit {γ = γ}) = Rule₀.agree (fo-of τ) wctrl
  agree {τ = τ} (⇓-lam {γ = γ} {t = t}) = Rule₀.agree (fo-of τ) (lam-out γ t)
  agree {τ = τ} (⇓-inl {γ = γ} {v = v} {R = R} D) =
    ≈-trans (Rule₁.agree (graph D) I (fo-of τ) (built-out γ (width v)) (in₂ {1}))
            (one (built-out γ (width v)) (in₂ {1}) (agree D))
  agree {τ = τ} (⇓-inr {γ = γ} {v = v} {R = R} D) =
    ≈-trans (Rule₁.agree (graph D) I (fo-of τ) (built-out γ (width v)) (in₂ {1}))
            (one (built-out γ (width v)) (in₂ {1}) (agree D))
  agree {τ = τ} (⇓-case-l {γ = γ} {v = v} {R = R} {T = T} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph D₂) I
                       (branch-inputs γ v ∘ join (suc (width-env γ)) (suc (width v)))
                       (fo-of τ) εₘ εₘ I)
    (≈-trans (seq (branch-inputs γ v ∘ join (suc (width-env γ)) (suc (width v))) (agree D₁) (agree D₂))
             (∘-cong₂ {f = T} (seam (branch-inputs γ v) R)))
  agree {τ = τ} (⇓-case-r {γ = γ} {v = v} {R = R} {T = T} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph D₂) I
                       (branch-inputs γ v ∘ join (suc (width-env γ)) (suc (width v)))
                       (fo-of τ) εₘ εₘ I)
    (≈-trans (seq (branch-inputs γ v ∘ join (suc (width-env γ)) (suc (width v))) (agree D₁) (agree D₂))
             (∘-cong₂ {f = T} (seam (branch-inputs γ v) R)))
  agree {τ = τ} (⇓-pair {γ = γ} {v = v} {u = u} {R = R} {T = T} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph D₂) I insH (fo-of τ) (built-out γ (width v + width u)) u₁ u₂)
    (≈-trans (two-roots (built-out γ (width v + width u)) I insH u₁ u₂
                        (collapse (graph D₁)) (collapse (graph D₂))
                        (≈-trans id-right (agree D₁))
                        (inputs-only (collapse (graph D₂)) (collapse (graph D₁) ∘ I) (agree D₂)))
             (+ₘ-cong (≈-refl {f = built-out γ (width v + width u)}) (up-pair (in₂ {1}) R T)))
    where
    insH = p₁ {suc (width-env γ)} {width v} ∘ join (suc (width-env γ)) (width v)
    u₁ = in₂ {1} ∘ in₁ {width v} {width u}
    u₂ = in₂ {1} ∘ in₂ {width v} {width u}
  agree {τ = τ} (⇓-fst {γ = γ} {v = v} {u = u} {R = R} D) =
    ≈-trans (Rule₁.agree (graph D) I (fo-of τ) (elim-out γ v) (proj-up {width v} {width u} v (p₁ {width v} {width u})))
            (one (elim-out γ v) (proj-up {width v} {width u} v (p₁ {width v} {width u})) (agree D))
  agree {τ = τ} (⇓-snd {γ = γ} {v = v} {u = u} {R = R} D) =
    ≈-trans (Rule₁.agree (graph D) I (fo-of τ) (elim-out γ u) (proj-up {width v} {width u} u (p₂ {width v} {width u})))
            (one (elim-out γ u) (proj-up {width v} {width u} u (p₂ {width v} {width u})) (agree D))
  agree {τ = τ} (⇓-app {γ = γ} {γ' = γ'} {v = v} {R = R} {T = T} {U = U} D₁ D₂ D₃) =
    ≈-trans (Rule₃.agree (graph D₁) (graph D₂) (graph D₃) I I insH (fo-of τ) εₘ εₘ εₘ I)
    (≈-trans (seq3 insH (agree D₁) (agree D₂) (agree D₃))
             (∘-cong₂ {f = U} (seam-app (body-inputs γ γ' v) R T)))
    where
    insH = body-inputs γ γ' v ∘
             (join (suc (width-env γ) + suc (width-env γ')) (width v) ∘
               ⟨ join (suc (width-env γ)) (suc (width-env γ')) ∘ pb₁ , pb₂ ⟩)
  agree {τ = τ} (⇓-bop {γ = γ} {ω = ω} {vs = vs} {R = R} D) =
    ≈-trans (Ruleₛ.agree (fo-of τ) wctrl (premises D (op-dep ω vs)))
            (+ₘ-cong ≈-refl (agree-premises D (op-dep ω vs)))
  agree {τ = τ} (⇓-brel {γ = γ} {ω = ω} {vs = vs} {R = R} D) =
    ≈-trans (Ruleₛ.agree (fo-of τ) wctrl (premises D (brel-deps ω vs (rel-pred ω .func vs))))
            (+ₘ-cong ≈-refl (agree-premises D (brel-deps ω vs (rel-pred ω .func vs))))
  agree {τ = τ} (⇓-roll {γ = γ} {R = R} D) =
    ≈-trans (Rule₁.agree (graph D) I (fo-of τ) εₘ I)
    (≈-trans (+ₘ-lunit (I ∘ (collapse (graph D) ∘ I)))
             (≈-trans id-left (≈-trans id-right (agree D))))
  agree {τ = τ} (⇓-fold {γ = γ} {v = v} {R = R} {F = F} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph D₁) (graph-m D₂) I (join (suc (width-env γ)) (width v)) (fo-of τ) εₘ εₘ I)
    (≈-trans (seq (join (suc (width-env γ)) (width v)) (agree D₁) (agree-m D₂))
             (∘-cong₂ {f = F} (join-pair I R)))

  agree-premises : ∀ {Γ is n} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
                   (D : γ , Ms ⇓s vs [ R ]) (u : 𝔽 (bases-width is) ⇒ 𝔽 n) →
                   Ruleₛ.rel (premises D u) ≈ (u ∘ R)
  agree-premises [] u = ≈-sym (CME.comp-bilinear-ε₂ u)
  agree-premises (_∷_ {is = is} {v = v} {R = R} {Rs = Rs} D₁ D₂) u =
    ≈-trans (+ₘ-cong (∘-cong₂ {f = u ∘ in₁ {width (const v)} {bases-width is}}
                              (≈-trans id-right (agree D₁)))
                     (agree-premises D₂ (u ∘ in₂ {width (const v)} {bases-width is})))
            (up-pair u R Rs)

  agree-m : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {v' : Val (σ' [ σr ])} {F}
            (D : Map γ s σ' v v' F) → collapse (graph-m D) ≈ F
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-rec {w = w} {w' = w'} {F = F} {T = T} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph-m D₁) (graph D₂) I insH (fo-of (σ' [ σr ])) εₘ εₘ I)
    (≈-trans (seq insH (agree-m D₁) (agree D₂))
             (∘-cong₂ {f = T} (seam (rec-inputs γ w') F)))
    where
    insH = rec-inputs γ w' ∘ join (suc (width-env γ) + width w) (width w')
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-unit {v = v}) = Rule₀.agree (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-base {v = v}) = Rule₀.agree (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-arrow {v = v}) = Rule₀.agree (fo-of (σ' [ σr ])) (map-leaf γ (width v))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-inl {v = v} {v' = v'} {F = F} D) =
    ≈-trans (Rule₁.agree (graph-m D) (sub-inputs γ (p₂ {1} {width v})) (fo-of (σ' [ σr ]))
                       (map-built-out γ (width v) (width v')) (in₂ {1}))
            (one-inputs (map-built-out γ (width v) (width v')) (in₂ {1}) (sub-inputs γ (p₂ {1} {width v}))
                        (agree-m D))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-inr {v = v} {v' = v'} {F = F} D) =
    ≈-trans (Rule₁.agree (graph-m D) (sub-inputs γ (p₂ {1} {width v})) (fo-of (σ' [ σr ]))
                       (map-built-out γ (width v) (width v')) (in₂ {1}))
            (one-inputs (map-built-out γ (width v) (width v')) (in₂ {1}) (sub-inputs γ (p₂ {1} {width v}))
                        (agree-m D))
  agree-m {γ = γ} {σr = σr} {σ' = σ'} (m-pair {v = v} {v' = v'} {u = u} {u' = u'} {F = F} {G = G} D₁ D₂) =
    ≈-trans (Rule₂.agree (graph-m D₁) (graph-m D₂) ins₁H ins₂H
                       (fo-of (σ' [ σr ])) (map-built-out γ (width v + width u) (width v' + width u'))
                       u₁ u₂)
    (≈-trans (two-roots (map-built-out γ (width v + width u) (width v' + width u')) ins₁H ins₂H u₁ u₂
                        (collapse (graph-m D₁)) (collapse (graph-m D₂))
                        (∘-cong₁ {g = ins₁H} (agree-m D₁))
                        (≈-trans (∘-cong₂ {f = collapse (graph-m D₂)} (ignore-rootF ins₂core (collapse (graph-m D₁) ∘ ins₁H)))
                                 (∘-cong₁ {g = ins₂core} (agree-m D₂))))
             (+ₘ-cong (≈-refl {f = map-built-out γ (width v + width u) (width v' + width u')})
                      (up-pair (in₂ {1}) (F ∘ ins₁H) (G ∘ ins₂core))))
    where
    ins₁H = sub-inputs γ (p₁ {width v} {width u} ∘ p₂ {1} {width v + width u})
    ins₂core = sub-inputs γ (p₂ {width v} {width u} ∘ p₂ {1} {width v + width u})
    u₁ = in₂ {1} ∘ in₁ {width v'} {width u'}
    u₂ = in₂ {1} ∘ in₂ {width v'} {width u'}
    ins₂H = ins₂core ∘
              (p₁ {suc (width-env γ) + suc (width v + width u)} {width v'} ∘
                join (suc (width-env γ) + suc (width v + width u)) (width v'))
  agree-m {γ = γ} {τ₀ = τ₀} {σr = σr} {σ' = σ'} (m-mu {τ' = τ'} {w = w} {w' = w'} {F = F} D) =
    ≈-trans (Rule₁.agree (graph-m D) (sub-inputs γ (Category.≡-to-⇒ SemiMod.cat (cong 𝔽 (width-subst (unfold₁-inst τ' (μ τ₀)) w))))
                       (fo-of (σ' [ σr ])) εₘ (Category.≡-to-⇒ SemiMod.cat (cong 𝔽 (sym (width-subst (unfold₁-inst τ' σr) w')))))
            (mu (Category.≡-to-⇒ SemiMod.cat (cong 𝔽 (sym (width-subst (unfold₁-inst τ' σr) w'))))
                (sub-inputs γ (Category.≡-to-⇒ SemiMod.cat (cong 𝔽 (width-subst (unfold₁-inst τ' (μ τ₀)) w)))) (agree-m D))
