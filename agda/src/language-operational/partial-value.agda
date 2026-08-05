{-# OPTIONS --prop --postfix-projections --safe #-}

-- Partial values: the operational reading of a selection. A partial value keeps some of a value's
-- formers and cuts the rest to holes; keeping a position keeps the formers above it, so the
-- partial values of a value are the prefixes of its former tree, with an arbitrary subset of the
-- positions at each constant. The bridge to the model: the fixed vectors of a value's position
-- order are exactly its partial values, a hole where a former's root is unselected.
open import Level using (0ℓ)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; zero; suc; splitAt; _↑ˡ_; _↑ʳ_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl) renaming (sym to ≡-sym; trans to ≡-trans)
open import basics using (IsTop)
open import prop using (∃ₛ; proj₁; proj₂) renaming (_,_ to _,ₚ_; ⊥-elim to ⊥-elimₚ)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import primitives using (Primitives)
import two
import matrix
import order-idempotent
import order-idempotent-blocks

module language-operational.partial-value {ℓ} (Sig : Signature ℓ)
  (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
import language-syntax Sig as Syn
open import language-operational.evaluation Sig 𝒫 using (Val; Env)
open Val
open Env
open import language-operational.value-fibre Sig 𝒫 using (pos; pos-env)

private
  module T = CommutativeSemiring two.semiring
  module M = matrix.Mat two.semiring

open order-idempotent two.semiring
  (λ {x} → two.∨-idem {x}) (λ {x} → two.∧-idem {x}) (λ {x} → two.⊤-add-top {x})
open order-idempotent-blocks two.semiring
  (λ {x} → two.∨-idem {x}) (λ {x} → two.∧-idem {x}) (λ {x} → two.⊤-add-top {x})
  using (appendV; leftV; rightV; ⊕-fixed-left; ⊕-fixed-right; ⊕-fixed-append;
         appendV-↑ˡ; appendV-↑ʳ; split-eqˡ; split-eqʳ)

-- The formers that carry a root, so that a partial value can stop above them. Constants carry
-- their positions directly and rolling is transparent, so neither admits a hole of its own.
Rooted : ∀ {τ} → Val τ → Set
Rooted unit       = ⊤
Rooted (const _)  = ⊥
Rooted (inl _)    = ⊤
Rooted (inr _)    = ⊤
Rooted (pair _ _) = ⊤
Rooted (clo _ _)  = ⊤
Rooted (roll _)   = ⊥

mutual
  data PVal : ∀ {τ} → Val τ → Set ℓ where
    hole   : ∀ {τ} {v : Val τ} → Rooted v → PVal v
    unit*  : PVal unit
    const* : ∀ {s} {c : sort-val s} → M.Vec (sort-width s) → PVal (const c)
    inl*   : ∀ {τ₁ τ₂} {v : Val τ₁} → PVal v → PVal (inl {τ₁} {τ₂} v)
    inr*   : ∀ {τ₁ τ₂} {v : Val τ₂} → PVal v → PVal (inr {τ₁} {τ₂} v)
    pair*  : ∀ {τ₁ τ₂} {v : Val τ₁} {u : Val τ₂} → PVal v → PVal u → PVal (pair v u)
    clo*   : ∀ {Γ σ τ} {γ : Env Γ} {t : (Γ Syn., σ) Syn.⊢ τ} → PEnv γ → PVal (clo γ t)
    roll*  : ∀ {τ} {v : Val (τ Syn.[ Syn.μ τ ])} → PVal v → PVal (roll {τ = τ} v)

  data PEnv : ∀ {Γ} → Env Γ → Set ℓ where
    emp*  : PEnv emp
    _·*_  : ∀ {Γ τ} {γ : Env Γ} {v : Val τ} → PEnv γ → PVal v → PEnv (γ · v)

infixl 30 _·*_

-- A selection: a vector over the positions, fixed under the ancestor order.
Sel : Pos → Set
Sel P = ∃ₛ (M.Vec (P .dim)) (Fixed P)

private
  cons : ∀ {n} → two.Two → M.Vec n → M.Vec (ℕ.suc n)
  cons a u zero    = a
  cons a u (suc i) = u i

  -- Case analysis on a root bit that does not abstract it from the context, since the fixedness
  -- hypotheses mention the whole vector.
  two-case : ∀ {a} {A : Set a} (b : two.Two) → (b ≡ two.O → A) → (b ≡ two.I → A) → A
  two-case two.O o i = o refl
  two-case two.I o i = i refl

  -- The empty selection, and fixedness of a discrete selection.
  zero-sel : ∀ P → Sel P
  zero-sel P = (λ _ → T.ε) ,ₚ (λ i → app-ε (P .ord) i)

  disc-fixed : ∀ {n} (w : M.Vec n) → Fixed (disc n) w
  disc-fixed w i = M.Σ-unit i w

  -- A selection under a selected root: the payload's support is dominated because the root is top.
  under-root : ∀ P → Sel P → Sel (Lp P)
  under-root P (w ,ₚ fx) =
    cons T.ι w ,ₚ Lp-fixed P (cons T.ι w) fx (IsTop.≤-top L.⊤-isTop)

-- The selection a partial value denotes: holes select nothing, a kept former selects its root
-- above its payload's selection, a constant selects its subset. Recursion is driven by the value
-- so that the μ index never has to be recovered from a substituted type.
mutual
  sel : ∀ {τ} (v : Val τ) → PVal v → Sel (pos v)
  sel v (hole r)       = zero-sel (pos v)
  sel unit unit*       = under-root 𝟘p (zero-sel 𝟘p)
  sel (const c) (const* w) = w ,ₚ disc-fixed w
  sel (inl v) (inl* p) = under-root (pos v) (sel v p)
  sel (inr v) (inr* p) = under-root (pos v) (sel v p)
  sel (pair v u) (pair* p q) =
    under-root (pos v ⊕ pos u)
      (appendV (vec (pos v) (sel v p)) (vec (pos u) (sel u q)) ,ₚ
       ⊕-fixed-append (pos v) (pos u) (fxd (pos v) (sel v p)) (fxd (pos u) (sel u q)))
  sel (clo γ t) (clo* ρ) = under-root (pos-env γ) (sel-env γ ρ)
  sel (roll {τ = τ'} v) (roll* p) = sel v p

  sel-env : ∀ {Γ} (γ : Env Γ) → PEnv γ → Sel (pos-env γ)
  sel-env emp emp* = (λ ()) ,ₚ (λ ())
  sel-env (γ · v) (ρ ·* p) =
    appendV (vec (pos-env γ) (sel-env γ ρ)) (vec (pos v) (sel v p)) ,ₚ
    ⊕-fixed-append (pos-env γ) (pos v) (fxd (pos-env γ) (sel-env γ ρ)) (fxd (pos v) (sel v p))

-- The partial value a selection denotes: read the root; unselected cuts to a hole, selected
-- descends into the payload.
mutual
  pval : ∀ {τ} (v : Val τ) → Sel (pos v) → PVal v
  pval unit (w ,ₚ fx) =
    two-case (w zero) (λ _ → hole tt) (λ _ → unit*)
  pval (const c) (w ,ₚ fx) = const* w
  pval (inl v) (w ,ₚ fx) =
    two-case (w zero) (λ _ → hole tt)
      (λ _ → inl* (pval v (tail w ,ₚ Lp-fixed-tail (pos v) w fx)))
  pval (inr v) (w ,ₚ fx) =
    two-case (w zero) (λ _ → hole tt)
      (λ _ → inr* (pval v (tail w ,ₚ Lp-fixed-tail (pos v) w fx)))
  pval (pair v u) (w ,ₚ fx) =
    two-case (w zero) (λ _ → hole tt)
      (λ _ →
        pair* (pval v (leftV (tail w) ,ₚ
                       ⊕-fixed-left (pos v) (pos u) (Lp-fixed-tail (pos v ⊕ pos u) w fx)))
              (pval u (rightV (tail w) ,ₚ
                       ⊕-fixed-right (pos v) (pos u) (Lp-fixed-tail (pos v ⊕ pos u) w fx))))
  pval (clo γ t) (w ,ₚ fx) =
    two-case (w zero) (λ _ → hole tt)
      (λ _ → clo* (pval-env γ (tail w ,ₚ Lp-fixed-tail (pos-env γ) w fx)))
  pval (roll {τ = τ'} v) x = roll* {τ = τ'} (pval v x)

  pval-env : ∀ {Γ} (γ : Env Γ) → Sel (pos-env γ) → PEnv γ
  pval-env emp _ = emp*
  pval-env (γ · v) (w ,ₚ fx) =
    pval-env γ (leftV w ,ₚ ⊕-fixed-left (pos-env γ) (pos v) fx) ·*
    pval v (rightV w ,ₚ ⊕-fixed-right (pos-env γ) (pos v) fx)

-- Spine closure of a raw dependency vector: the least fixed selection above it, fixed by
-- idempotence of the order. The model reports raw selections; closing under the ancestor order
-- is the post-processing that turns a report into a partial value.
spine-close : ∀ P → M.Vec (P .dim) → Sel P
spine-close P w =
  app (P .ord) w ,ₚ
  (λ i → T.trans (T.sym (app-∘ (P .ord) (P .ord) w i)) (app-congₘ (ord-idem P) w i))

------------------------------------------------------------------------------
-- The bridge lemma: sel and pval are mutually inverse, up to structural equality of partial
-- values and pointwise equality of selection vectors.

private
  ⊥-elim-set : ∀ {a} {A : Set a} → prop.⊥ {0ℓ} → A
  ⊥-elim-set ()

  ≡→≈ : ∀ {x y : two.Two} → x ≡ y → x T.≈ y
  ≡→≈ refl = T.refl

  ≈→≡ : ∀ {x y : two.Two} → x T.≈ y → x ≡ y
  ≈→≡ {two.O} {two.O} _ = refl
  ≈→≡ {two.I} {two.I} _ = refl
  ≈→≡ {two.O} {two.I} h = ⊥-elim-set (h .proj₂)
  ≈→≡ {two.I} {two.O} h = ⊥-elim-set (h .proj₁)

  substP : ∀ {a p} {A : Set a} {x y : A} (P : A → Prop p) → x ≡ y → P x → P y
  substP P refl h = h

  -- Case analysis at the Prop level, and the equations reducing two-case at a known root bit.
  two-caseP : ∀ {p} {A : Prop p} (b : two.Two) → (b ≡ two.O → A) → (b ≡ two.I → A) → A
  two-caseP two.O o i = o refl
  two-caseP two.I o i = i refl

  two-case-O : ∀ {a} {A : Set a} {b} (e : b ≡ two.O) (f : b ≡ two.O → A) (g : b ≡ two.I → A) →
               two-case b f g ≡ f e
  two-case-O refl f g = refl

  two-case-I : ∀ {a} {A : Set a} {b} (e : b ≡ two.I) (f : b ≡ two.O → A) (g : b ≡ two.I → A) →
               two-case b f g ≡ g e
  two-case-I refl f g = refl

  ≤O : ∀ {x} → x L.≤ two.O → x T.≈ two.O
  ≤O {two.O} _ = T.refl {two.O}
  ≤O {two.I} h = h

  +-O₁ : ∀ x y → (x T.+ y) T.≈ two.O → x T.≈ two.O
  +-O₁ two.O y _ = T.refl {two.O}
  +-O₁ two.I y h = h

  +-O₂ : ∀ x y → (x T.+ y) T.≈ two.O → y T.≈ two.O
  +-O₂ two.O y h = h
  +-O₂ two.I y h = ⊥-elimₚ (h .proj₁)

  Σ-O : ∀ {n} (f : M.Vec n) → M.Σ {n} f T.≈ two.O → ∀ j → f j T.≈ two.O
  Σ-O {ℕ.suc n} f h zero    = +-O₁ (f zero) (M.Σ {n} (λ j → f (suc j))) h
  Σ-O {ℕ.suc n} f h (suc j) = Σ-O {n} (λ k → f (suc k)) (+-O₂ (f zero) _ h) j

  appendV-split : ∀ {m n} (u : M.Vec (m +ℕ n)) (i : Fin (m +ℕ n)) →
                  appendV {m} {n} (leftV {m} {n} u) (rightV {m} {n} u) i T.≈ u i
  appendV-split {m} u i with splitAt m i in eq
  ... | inj₁ j rewrite ≡-sym (split-eqˡ i eq) = T.refl
  ... | inj₂ k rewrite ≡-sym (split-eqʳ i eq) = T.refl

  appendV-cong : ∀ {m n} {u u' : M.Vec m} {w w' : M.Vec n} →
                 (∀ j → u j T.≈ u' j) → (∀ k → w k T.≈ w' k) →
                 ∀ i → appendV u w i T.≈ appendV u' w' i
  appendV-cong {m} eu ew i with splitAt m i
  ... | inj₁ j = eu j
  ... | inj₂ k = ew k

-- Structural equality of partial values: pointwise at the constants, componentwise elsewhere.
mutual
  data _≈pv_ : ∀ {τ} {v : Val τ} → PVal v → PVal v → Prop ℓ where
    ≈hole  : ∀ {τ} {v : Val τ} {r r' : Rooted v} → hole r ≈pv hole r'
    ≈unit  : unit* ≈pv unit*
    ≈const : ∀ {s} {c : sort-val s} {w w' : M.Vec (sort-width s)} →
             (∀ i → w i T.≈ w' i) → const* {c = c} w ≈pv const* w'
    ≈inl   : ∀ {τ₁ τ₂} {v : Val τ₁} {p q : PVal v} →
             p ≈pv q → inl* {τ₂ = τ₂} p ≈pv inl* q
    ≈inr   : ∀ {τ₁ τ₂} {v : Val τ₂} {p q : PVal v} →
             p ≈pv q → inr* {τ₁ = τ₁} p ≈pv inr* q
    ≈pair  : ∀ {τ₁ τ₂} {v : Val τ₁} {u : Val τ₂} {p p' : PVal v} {q q' : PVal u} →
             p ≈pv p' → q ≈pv q' → pair* p q ≈pv pair* p' q'
    ≈clo   : ∀ {Γ σ τ} {γ : Env Γ} {t : (Γ Syn., σ) Syn.⊢ τ} {ρ ρ' : PEnv γ} →
             ρ ≈pe ρ' → clo* {t = t} ρ ≈pv clo* ρ'
    ≈roll  : ∀ {τ} {v : Val (τ Syn.[ Syn.μ τ ])} {p q : PVal v} →
             p ≈pv q → roll* {τ = τ} p ≈pv roll* {τ = τ} q

  data _≈pe_ : ∀ {Γ} {γ : Env Γ} → PEnv γ → PEnv γ → Prop ℓ where
    ≈emp : emp* ≈pe emp*
    ≈ext : ∀ {Γ τ} {γ : Env Γ} {v : Val τ} {ρ ρ' : PEnv γ} {p q : PVal v} →
           ρ ≈pe ρ' → p ≈pv q → (ρ ·* p) ≈pe (ρ' ·* q)

mutual
  ≈pv-trans : ∀ {τ} {v : Val τ} {p q r : PVal v} → p ≈pv q → q ≈pv r → p ≈pv r
  ≈pv-trans ≈hole ≈hole = ≈hole
  ≈pv-trans ≈unit ≈unit = ≈unit
  ≈pv-trans (≈const e) (≈const e') = ≈const (λ i → T.trans (e i) (e' i))
  ≈pv-trans (≈inl h) (≈inl h') = ≈inl (≈pv-trans h h')
  ≈pv-trans (≈inr h) (≈inr h') = ≈inr (≈pv-trans h h')
  ≈pv-trans (≈pair h₁ h₂) (≈pair h₁' h₂') = ≈pair (≈pv-trans h₁ h₁') (≈pv-trans h₂ h₂')
  ≈pv-trans (≈clo h) (≈clo h') = ≈clo (≈pe-trans h h')
  ≈pv-trans (≈roll {τ = τ'} h) (≈roll h') = ≈roll {τ = τ'} (≈pv-trans h h')

  ≈pe-trans : ∀ {Γ} {γ : Env Γ} {ρ σ ω : PEnv γ} → ρ ≈pe σ → σ ≈pe ω → ρ ≈pe ω
  ≈pe-trans ≈emp ≈emp = ≈emp
  ≈pe-trans (≈ext h p) (≈ext h' p') = ≈ext (≈pe-trans h h') (≈pv-trans p p')

private
  ≈pv-resp : ∀ {τ} {v : Val τ} {p p' q q' : PVal v} → p ≡ p' → q ≡ q' → p' ≈pv q' → p ≈pv q
  ≈pv-resp refl refl h = h

  ≈pe-resp : ∀ {Γ} {γ : Env Γ} {ρ ρ' σ σ' : PEnv γ} → ρ ≡ ρ' → σ ≡ σ' → ρ' ≈pe σ' → ρ ≈pe σ
  ≈pe-resp refl refl h = h

-- Reading back respects pointwise equality of selections; the fixedness components are
-- proof-irrelevant.
mutual
  pval-cong : ∀ {τ} (v : Val τ) {w w' : M.Vec (pos v .dim)}
              {fx : Fixed (pos v) w} {fx' : Fixed (pos v) w'} →
              (∀ i → w i T.≈ w' i) → pval v (w ,ₚ fx) ≈pv pval v (w' ,ₚ fx')
  pval-cong unit {w} {w'} e =
    two-caseP (w zero)
      (λ eO → ≈pv-resp (two-case-O eO _ _)
                       (two-case-O (≡-trans (≡-sym (≈→≡ (e zero))) eO) _ _) ≈hole)
      (λ eI → ≈pv-resp (two-case-I eI _ _)
                       (two-case-I (≡-trans (≡-sym (≈→≡ (e zero))) eI) _ _) ≈unit)
  pval-cong (const c) e = ≈const e
  pval-cong (inl v) {w} {w'} e =
    two-caseP (w zero)
      (λ eO → ≈pv-resp (two-case-O eO _ _)
                       (two-case-O (≡-trans (≡-sym (≈→≡ (e zero))) eO) _ _) ≈hole)
      (λ eI → ≈pv-resp (two-case-I eI _ _)
                       (two-case-I (≡-trans (≡-sym (≈→≡ (e zero))) eI) _ _)
                       (≈inl (pval-cong v (λ i → e (suc i)))))
  pval-cong (inr v) {w} {w'} e =
    two-caseP (w zero)
      (λ eO → ≈pv-resp (two-case-O eO _ _)
                       (two-case-O (≡-trans (≡-sym (≈→≡ (e zero))) eO) _ _) ≈hole)
      (λ eI → ≈pv-resp (two-case-I eI _ _)
                       (two-case-I (≡-trans (≡-sym (≈→≡ (e zero))) eI) _ _)
                       (≈inr (pval-cong v (λ i → e (suc i)))))
  pval-cong (pair v u) {w} {w'} e =
    two-caseP (w zero)
      (λ eO → ≈pv-resp (two-case-O eO _ _)
                       (two-case-O (≡-trans (≡-sym (≈→≡ (e zero))) eO) _ _) ≈hole)
      (λ eI → ≈pv-resp (two-case-I eI _ _)
                       (two-case-I (≡-trans (≡-sym (≈→≡ (e zero))) eI) _ _)
                       (≈pair (pval-cong v (λ j → e (suc (j ↑ˡ pos u .dim))))
                              (pval-cong u (λ k → e (suc (pos v .dim ↑ʳ k))))))
  pval-cong (clo γ t) {w} {w'} e =
    two-caseP (w zero)
      (λ eO → ≈pv-resp (two-case-O eO _ _)
                       (two-case-O (≡-trans (≡-sym (≈→≡ (e zero))) eO) _ _) ≈hole)
      (λ eI → ≈pv-resp (two-case-I eI _ _)
                       (two-case-I (≡-trans (≡-sym (≈→≡ (e zero))) eI) _ _)
                       (≈clo (penv-cong γ (λ i → e (suc i)))))
  pval-cong (roll {τ = τ'} v) e = ≈roll {τ = τ'} (pval-cong v e)

  penv-cong : ∀ {Γ} (γ : Env Γ) {w w' : M.Vec (pos-env γ .dim)}
              {fx : Fixed (pos-env γ) w} {fx' : Fixed (pos-env γ) w'} →
              (∀ i → w i T.≈ w' i) → pval-env γ (w ,ₚ fx) ≈pe pval-env γ (w' ,ₚ fx')
  penv-cong emp e = ≈emp
  penv-cong (γ · v) e =
    ≈ext (penv-cong γ (λ j → e (j ↑ˡ pos v .dim)))
         (pval-cong v (λ k → e (pos-env γ .dim ↑ʳ k)))

mutual
  pval-sel : ∀ {τ} (v : Val τ) (p : PVal v) → pval v (sel v p) ≈pv p
  pval-sel unit (hole r)       = ≈hole
  pval-sel (inl v) (hole r)    = ≈hole
  pval-sel (inr v) (hole r)    = ≈hole
  pval-sel (pair v u) (hole r) = ≈hole
  pval-sel (clo γ t) (hole r)  = ≈hole
  pval-sel (const c) (hole ())
  pval-sel (roll v) (hole ())
  pval-sel unit unit*          = ≈unit
  pval-sel (const c) (const* w) = ≈const (λ i → T.refl)
  pval-sel (inl v) (inl* p)    = ≈inl (pval-sel v p)
  pval-sel (inr v) (inr* p)    = ≈inr (pval-sel v p)
  pval-sel (pair v u) (pair* p q) =
    ≈pair (≈pv-trans (pval-cong v (λ j → appendV-↑ˡ (pos v .dim) (pos u .dim)
                                           (vec (pos v) (sel v p)) (vec (pos u) (sel u q)) j))
                     (pval-sel v p))
          (≈pv-trans (pval-cong u (λ k → appendV-↑ʳ (pos v .dim) (pos u .dim)
                                           (vec (pos v) (sel v p)) (vec (pos u) (sel u q)) k))
                     (pval-sel u q))
  pval-sel (clo γ t) (clo* ρ)  = ≈clo (penv-sel γ ρ)
  pval-sel (roll {τ = τ'} v) (roll* p) = ≈roll {τ = τ'} (pval-sel v p)

  penv-sel : ∀ {Γ} (γ : Env Γ) (ρ : PEnv γ) → pval-env γ (sel-env γ ρ) ≈pe ρ
  penv-sel emp emp* = ≈emp
  penv-sel (γ · v) (ρ ·* p) =
    ≈ext (≈pe-trans (penv-cong γ (λ j → appendV-↑ˡ (pos-env γ .dim) (pos v .dim)
                                          (vec (pos-env γ) (sel-env γ ρ)) (vec (pos v) (sel v p)) j))
                    (penv-sel γ ρ))
         (≈pv-trans (pval-cong v (λ k → appendV-↑ʳ (pos-env γ .dim) (pos v .dim)
                                          (vec (pos-env γ) (sel-env γ ρ)) (vec (pos v) (sel v p)) k))
                    (pval-sel v p))

mutual
  sel-pval : ∀ {τ} (v : Val τ) (x : Sel (pos v)) (i : Fin (pos v .dim)) →
             vec (pos v) (sel v (pval v x)) i T.≈ vec (pos v) x i
  sel-pval unit (w ,ₚ fx) zero =
    two-caseP (w zero)
      (λ eO → substP (λ z → vec (Lp 𝟘p) (sel unit z) zero T.≈ w zero)
                     (≡-sym (two-case-O eO _ _)) (≡→≈ (≡-sym eO)))
      (λ eI → substP (λ z → vec (Lp 𝟘p) (sel unit z) zero T.≈ w zero)
                     (≡-sym (two-case-I eI _ _)) (≡→≈ (≡-sym eI)))
  sel-pval unit _ (suc ())
  sel-pval (const c) (w ,ₚ fx) i = T.refl
  sel-pval (inl {τ₂ = τ₂'} v) (w ,ₚ fx) i =
    two-caseP (w zero)
      (λ eO → substP (λ z → vec (Lp (pos v)) (sel (inl v) z) i T.≈ w i)
                     (≡-sym (two-case-O eO _ _)) (empty-under eO i))
      (λ eI → substP (λ z → vec (Lp (pos v)) (sel (inl v) z) i T.≈ w i)
                     (≡-sym (two-case-I eI _ _)) (kept eI i))
    where
    empty-under : w zero ≡ two.O → ∀ i → two.O T.≈ w i
    empty-under eO zero    = ≡→≈ (≡-sym eO)
    empty-under eO (suc j) =
      T.sym (Σ-O (tail w)
                 (≤O (substP (λ b → supp {pos v .dim} (tail w) L.≤ b) eO
                             (Lp-fixed-root (pos v) w fx))) j)
    kept : w zero ≡ two.I → ∀ i → vec (Lp (pos v)) (sel (inl v) (inl* {τ₂ = τ₂'} (pval v (tail w ,ₚ
             Lp-fixed-tail (pos v) w fx)))) i T.≈ w i
    kept eI zero    = ≡→≈ (≡-sym eI)
    kept eI (suc j) = sel-pval v (tail w ,ₚ Lp-fixed-tail (pos v) w fx) j
  sel-pval (inr {τ₁ = τ₁'} v) (w ,ₚ fx) i =
    two-caseP (w zero)
      (λ eO → substP (λ z → vec (Lp (pos v)) (sel (inr v) z) i T.≈ w i)
                     (≡-sym (two-case-O eO _ _)) (empty-under eO i))
      (λ eI → substP (λ z → vec (Lp (pos v)) (sel (inr v) z) i T.≈ w i)
                     (≡-sym (two-case-I eI _ _)) (kept eI i))
    where
    empty-under : w zero ≡ two.O → ∀ i → two.O T.≈ w i
    empty-under eO zero    = ≡→≈ (≡-sym eO)
    empty-under eO (suc j) =
      T.sym (Σ-O (tail w)
                 (≤O (substP (λ b → supp {pos v .dim} (tail w) L.≤ b) eO
                             (Lp-fixed-root (pos v) w fx))) j)
    kept : w zero ≡ two.I → ∀ i → vec (Lp (pos v)) (sel (inr v) (inr* {τ₁ = τ₁'} (pval v (tail w ,ₚ
             Lp-fixed-tail (pos v) w fx)))) i T.≈ w i
    kept eI zero    = ≡→≈ (≡-sym eI)
    kept eI (suc j) = sel-pval v (tail w ,ₚ Lp-fixed-tail (pos v) w fx) j
  sel-pval (pair v u) (w ,ₚ fx) i =
    two-caseP (w zero)
      (λ eO → substP (λ z → vec (Lp (pos v ⊕ pos u)) (sel (pair v u) z) i T.≈ w i)
                     (≡-sym (two-case-O eO _ _)) (empty-under eO i))
      (λ eI → substP (λ z → vec (Lp (pos v ⊕ pos u)) (sel (pair v u) z) i T.≈ w i)
                     (≡-sym (two-case-I eI _ _)) (kept eI i))
    where
    tfx = Lp-fixed-tail (pos v ⊕ pos u) w fx
    lfx = ⊕-fixed-left (pos v) (pos u) tfx
    rfx = ⊕-fixed-right (pos v) (pos u) tfx
    empty-under : w zero ≡ two.O → ∀ i → two.O T.≈ w i
    empty-under eO zero    = ≡→≈ (≡-sym eO)
    empty-under eO (suc j) =
      T.sym (Σ-O (tail w)
                 (≤O (substP (λ b → supp {pos v .dim +ℕ pos u .dim} (tail w) L.≤ b) eO
                             (Lp-fixed-root (pos v ⊕ pos u) w fx))) j)
    kept : w zero ≡ two.I → ∀ i → vec (Lp (pos v ⊕ pos u)) (sel (pair v u)
             (pair* (pval v (leftV (tail w) ,ₚ lfx)) (pval u (rightV (tail w) ,ₚ rfx)))) i
             T.≈ w i
    kept eI zero    = ≡→≈ (≡-sym eI)
    kept eI (suc j) =
      T.trans (appendV-cong {m = pos v .dim} {n = pos u .dim}
                            (λ j' → sel-pval v (leftV (tail w) ,ₚ lfx) j')
                            (λ k' → sel-pval u (rightV (tail w) ,ₚ rfx) k') j)
              (appendV-split {m = pos v .dim} {n = pos u .dim} (tail w) j)
  sel-pval (clo γ t) (w ,ₚ fx) i =
    two-caseP (w zero)
      (λ eO → substP (λ z → vec (Lp (pos-env γ)) (sel (clo γ t) z) i T.≈ w i)
                     (≡-sym (two-case-O eO _ _)) (empty-under eO i))
      (λ eI → substP (λ z → vec (Lp (pos-env γ)) (sel (clo γ t) z) i T.≈ w i)
                     (≡-sym (two-case-I eI _ _)) (kept eI i))
    where
    empty-under : w zero ≡ two.O → ∀ i → two.O T.≈ w i
    empty-under eO zero    = ≡→≈ (≡-sym eO)
    empty-under eO (suc j) =
      T.sym (Σ-O (tail w)
                 (≤O (substP (λ b → supp {pos-env γ .dim} (tail w) L.≤ b) eO
                             (Lp-fixed-root (pos-env γ) w fx))) j)
    kept : w zero ≡ two.I → ∀ i → vec (Lp (pos-env γ)) (sel (clo γ t) (clo* (pval-env γ
             (tail w ,ₚ Lp-fixed-tail (pos-env γ) w fx)))) i T.≈ w i
    kept eI zero    = ≡→≈ (≡-sym eI)
    kept eI (suc j) = selenv-pval γ (tail w ,ₚ Lp-fixed-tail (pos-env γ) w fx) j
  sel-pval (roll {τ = τ'} v) x i = sel-pval v x i

  selenv-pval : ∀ {Γ} (γ : Env Γ) (x : Sel (pos-env γ)) (i : Fin (pos-env γ .dim)) →
                vec (pos-env γ) (sel-env γ (pval-env γ x)) i T.≈ vec (pos-env γ) x i
  selenv-pval emp x ()
  selenv-pval (γ · v) (w ,ₚ fx) i =
    T.trans (appendV-cong {m = pos-env γ .dim} {n = pos v .dim}
              (λ j → selenv-pval γ (leftV w ,ₚ ⊕-fixed-left (pos-env γ) (pos v) fx) j)
              (λ k → sel-pval v (rightV w ,ₚ ⊕-fixed-right (pos-env γ) (pos v) fx) k) i)
            (appendV-split {m = pos-env γ .dim} {n = pos v .dim} w i)
