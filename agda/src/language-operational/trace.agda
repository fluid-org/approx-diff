{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (List; []; _∷_; map; concatMap; _++_; splitAt; applyUpTo; allFin)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Data.String using (String; intersperse) renaming (_++_ to _++ˢ_)
import Data.Nat.Show as ℕ-Show
open import prop-setoid using (Setoid)
open import every using (Every; []; _∷_)
open import signature using (Signature)
open import primitives using (Primitives)
import two
import matrix

-- Rendering of evaluation derivations as traces and dependence-graph edge lists.
module language-operational.trace
  {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives Sig)
  (show-op : ∀ {is o} → Signature.op Sig is o → String)
  where

open Signature Sig
open Primitives 𝒫
open prop-setoid._⇒_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig 𝒫

private
  module M = matrix.Mat two.semiring
open two using (Two; O; I)

var-to-ℕ : ∀ {Γ τ} → Γ ∋ τ → ℕ
var-to-ℕ zero     = zero
var-to-ℕ (succ x) = suc (var-to-ℕ x)

------------------------------------------------------------------------
-- Derivation pretty-printing (ignores the matrix indices).

show-eval  : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} → _,_⇓_[_] γ t v R → String
show-evals : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
             _,_⇓s_[_] γ Ms vs R → List String
show-map   : ∀ {Γ} {γ : Env Γ} {τ₀ σr} {s : Γ ▸ τ₀ [ σr ] ⊢ σr} {σ' v R v' R'} →
             Map γ {τ₀} {σr} s σ' v R v' R' → String

show-eval (⇓-var x)        = "(var " ++ˢ ℕ-Show.show (var-to-ℕ x) ++ˢ ")"
show-eval ⇓-unit           = "unit"
show-eval (⇓-inl t)        = "(inl " ++ˢ show-eval t ++ˢ ")"
show-eval (⇓-inr t)        = "(inr " ++ˢ show-eval t ++ˢ ")"
show-eval (⇓-case-l s b)   = "(case-l " ++ˢ show-eval s ++ˢ " " ++ˢ show-eval b ++ˢ ")"
show-eval (⇓-case-r s b)   = "(case-r " ++ˢ show-eval s ++ˢ " " ++ˢ show-eval b ++ˢ ")"
show-eval (⇓-pair a b)     = "(pair " ++ˢ show-eval a ++ˢ " " ++ˢ show-eval b ++ˢ ")"
show-eval (⇓-fst t)        = "(fst " ++ˢ show-eval t ++ˢ ")"
show-eval (⇓-snd t)        = "(snd " ++ˢ show-eval t ++ˢ ")"
show-eval ⇓-lam            = "lam"
show-eval (⇓-app f a b)    = "(app " ++ˢ show-eval f ++ˢ " " ++ˢ show-eval a ++ˢ " " ++ˢ show-eval b ++ˢ ")"
show-eval (⇓-bop {ω = ω} ts) = "(bop " ++ˢ show-op ω ++ˢ " (" ++ˢ intersperse " " (show-evals ts) ++ˢ "))"
show-eval (⇓-brel ts)      = "(brel (" ++ˢ intersperse " " (show-evals ts) ++ˢ "))"
show-eval (⇓-roll t)       = "(roll " ++ˢ show-eval t ++ˢ ")"
show-eval (⇓-fold t m)     = "(fold " ++ˢ show-eval t ++ˢ " " ++ˢ show-map m ++ˢ ")"

show-evals []       = []
show-evals (t ∷ ts) = show-eval t ∷ show-evals ts

show-map (m-rec m b)    = "(rec " ++ˢ show-map m ++ˢ " " ++ˢ show-eval b ++ˢ ")"
show-map m-unit         = "-"
show-map m-base         = "-"
show-map m-arrow        = "-"
show-map (m-inl m)      = "(inl " ++ˢ show-map m ++ˢ ")"
show-map (m-inr m)      = "(inr " ++ˢ show-map m ++ˢ ")"
show-map (m-pair m₁ m₂) = "(pair " ++ˢ show-map m₁ ++ˢ " " ++ˢ show-map m₂ ++ˢ ")"
show-map (m-mu m)       = "(mu " ++ˢ show-map m ++ˢ ")"

------------------------------------------------------------------------
-- Dependence graph extraction.

Edge : Set
Edge = String × ℕ × ℕ

matrix-entries : ∀ {m n} → M.Matrix m n → List (Fin m × Fin n)
matrix-entries {m} {n} M' =
  concatMap (λ i → concatMap (λ j → keep i j (M' i j)) (allFin n)) (allFin m)
  where
    keep : Fin m → Fin n → Two → List (Fin m × Fin n)
    keep i j I = (i , j) ∷ []
    keep i j O = []

private
  nth : List ℕ → ℕ → ℕ
  nth [] _              = 0
  nth (x ∷ _)  zero     = x
  nth (_ ∷ xs) (suc i)  = nth xs i

  -- A morphism m ⇒ n in Mat(𝟚) is an n×m matrix of Booleans.
  mat-edges : String → (m n : ℕ) → M.Matrix n m → List ℕ → List ℕ → List Edge
  mat-edges tag m n f ins outs =
    map (λ p → tag , nth ins (toℕ (proj₂ p)) , nth outs (toℕ (proj₁ p)))
        (matrix-entries {n} {m} f)

  -- State ℕ for fresh port ids + writer for emitted edges.
  GraphWriter : Set → Set
  GraphWriter A = ℕ → A × ℕ × List Edge

  pure : ∀ {A} → A → GraphWriter A
  pure a next = a , next , []

  _>>=_ : ∀ {A B} → GraphWriter A → (A → GraphWriter B) → GraphWriter B
  (m >>= k) next =
    let a , next₁ , es₁ = m next
        b , next₂ , es₂ = k a next₁
    in b , next₂ , es₁ ++ es₂

  _>>_ : ∀ {A B} → GraphWriter A → GraphWriter B → GraphWriter B
  m >> n = m >>= λ _ → n

  emit : String → (m n : ℕ) → M.Matrix n m → List ℕ → GraphWriter (List ℕ)
  emit tag m n r ins next =
    let outs = applyUpTo (next +_) n
    in outs , next + n , mat-edges tag m n r ins outs

edges  : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} → _,_⇓_[_] γ t v R →
         List ℕ → GraphWriter (List ℕ)
edgess : ∀ {Γ is} {γ : Env Γ} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R} →
         _,_⇓s_[_] γ Ms vs R → List ℕ → GraphWriter (List ℕ)
edgesm : ∀ {Γ} {γ : Env Γ} {τ₀ σr} {s : Γ ▸ τ₀ [ σr ] ⊢ σr} {σ' v R v' R'} →
         Map γ {τ₀} {σr} s σ' v R v' R' → List ℕ → List ℕ → GraphWriter (List ℕ)

edges {γ = γ} (⇓-var x) ctx =
  emit "var" (width-env γ) (width (lookup x γ)) (proj-var x γ) ctx
edges ⇓-unit _ = emit "unit" 0 0 (M.I) []
edges (⇓-inl {v = v} E) ctx = do
  Eₒ ← edges E ctx
  emit "inl" (width v) (width v) M.I Eₒ
edges (⇓-inr {v = v} E) ctx = do
  Eₒ ← edges E ctx
  emit "inr" (width v) (width v) M.I Eₒ
edges (⇓-case-l {v = v} {u = u} E F) ctx = do
  Eₒ ← edges E ctx
  Fₒ ← edges F (ctx ++ Eₒ)
  emit "case-l" (width u) (width u) M.I Fₒ
edges (⇓-case-r {v = v} {u = u} E F) ctx = do
  Eₒ ← edges E ctx
  Fₒ ← edges F (ctx ++ Eₒ)
  emit "case-r" (width u) (width u) M.I Fₒ
edges (⇓-pair {v = v} {u = u} E F) ctx = do
  Eₒ ← edges E ctx
  Fₒ ← edges F ctx
  emit "pair" (width v + width u) (width v + width u) M.I (Eₒ ++ Fₒ)
edges (⇓-fst {v = v} {u = u} E) ctx = do
  Eₒ ← edges E ctx
  emit "fst" (width v + width u) (width v) (M.p₁ {width v} {width u}) Eₒ
edges (⇓-snd {v = v} {u = u} E) ctx = do
  Eₒ ← edges E ctx
  emit "snd" (width v + width u) (width u) (M.p₂ {width v} {width u}) Eₒ
edges (⇓-lam {γ = γ}) ctx =
  emit "lam" (width-env γ) (width-env γ) M.I ctx
edges (⇓-app {u = u} E F B) ctx = do
  Eₒ ← edges E ctx
  Fₒ ← edges F ctx
  Bₒ ← edges B (Eₒ ++ Fₒ)
  emit "app" (width u) (width u) M.I Bₒ
edges (⇓-bop {is = is} {o' = o'} {ω = ω} {vs = vs} E) ctx = do
  Eₒ ← edgess E ctx
  emit (show-op ω) (bases-width is) (sort-width o') (op-rel ω .func vs) Eₒ
edges (⇓-brel {is = is} E) ctx = do
  Eₒ ← edgess E ctx
  emit "brel" (bases-width is) 0 (M.εₘ) Eₒ
edges (⇓-roll {v = v} E) ctx = do
  Eₒ ← edges E ctx
  emit "roll" (width v) (width v) M.I Eₒ
edges (⇓-fold E m) ctx = do
  Eₒ ← edges E ctx
  edgesm m ctx Eₒ

edgess [] _ = pure []
edgess (E ∷ Es) ctx = do
  Eₒ ← edges E ctx
  Esₒ ← edgess Es ctx
  pure (Eₒ ++ Esₒ)

-- ctx: environment ports; ins: ports of the traversed value; returns ports of the mapped value.
edgesm (m-rec {u = u} m B) ctx ins = do
  Wₒ ← edgesm m ctx ins
  Bₒ ← edges B (ctx ++ Wₒ)
  emit "rec" (width u) (width u) M.I Bₒ
edgesm m-unit  _ ins = pure ins
edgesm m-base  _ ins = pure ins
edgesm m-arrow _ ins = pure ins
edgesm (m-inl m) ctx ins = edgesm m ctx ins
edgesm (m-inr m) ctx ins = edgesm m ctx ins
edgesm (m-pair {v = v} m₁ m₂) ctx ins =
  let vs , us = splitAt (width v) ins in do
  Vₒ ← edgesm m₁ ctx vs
  Uₒ ← edgesm m₂ ctx us
  pure (Vₒ ++ Uₒ)
edgesm (m-mu m) ctx ins = edgesm m ctx ins

------------------------------------------------------------------------
-- Edge-list rendering.

showGraph : List Edge → String
showGraph es = intersperse ", " (map edge es)
  where
    edge : Edge → String
    edge (tag , i , j) =
      "(" ++ˢ tag ++ˢ ": " ++ˢ ℕ-Show.show i ++ˢ ", " ++ˢ ℕ-Show.show j ++ˢ ")"

showDot : List Edge → String
showDot es = "digraph G {\n" ++ˢ go es ++ˢ "}\n"
  where
    edge : Edge → String
    edge (tag , i , j) =
      "  " ++ˢ ℕ-Show.show i ++ˢ " -> " ++ˢ ℕ-Show.show j ++ˢ " [label=\"" ++ˢ tag ++ˢ "\"];\n"
    go : List Edge → String
    go []       = ""
    go (e ∷ es) = edge e ++ˢ go es
