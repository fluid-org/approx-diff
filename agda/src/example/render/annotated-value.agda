{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Vec as Vec using (Vec; fromList) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.String using (String)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)

module example.render.annotated-value {ℓ} (Sig : Signature ℓ)
  {A₀ : Setoid 0ℓ 0ℓ} (S₀ : CommutativeSemiring A₀)
  (ℐ : Interpretation S₀ Sig) (ctrl-weight : Setoid.Carrier A₀) where

open Signature Sig
open Interpretation ℐ
open import language-syntax Sig using (unit; base; μ; var; _[+]_; _[×]_; _[→]_)
open import language-operational.evaluation Sig S₀ ℐ ctrl-weight using (Val; Env)
open Val
open Env
open import Data.Fin using (zero)

data Tag : Set where
  unit inl inr pair cons nil : Tag
  clo   : ℕ → Tag
  const : String → Tag

arity : Tag → ℕ
arity unit      = 0
arity inl       = 1
arity inr       = 1
arity pair      = 2
arity cons      = 2
arity nil       = 0
arity (clo k)   = k
arity (const _) = 0

-- Positions are numbered by preorder traversal: a node's positions are consecutive and precede
-- its descendants'. A cons has two positions, the tag and the pair beneath it; nil the tag and
-- its unit; a scalar one; a label none.
data AVal (X : Set) : Set where
  node : (t : Tag) → X → ℕ → Vec (AVal X) (arity t) → AVal X

width : ∀ {X} → AVal X → ℕ
width-vec : ∀ {X : Set} {k} → Vec (AVal X) k → ℕ

width (node _ _ n cs) = n + width-vec cs
width-vec []ᵥ       = 0
width-vec (t ∷ᵥ ts) = width t + width-vec ts

module _ (show-const : ∀ {s} → sort-val s → String) where

  mutual
    shape-of : ∀ {τ} → Val τ → AVal ⊤
    shape-of {μ (unit [+] (_ [×] var zero))} v = cell-of v
    shape-of Val.unit          = node Tag.unit tt 1 []ᵥ
    shape-of (Val.const {s} c) = node (Tag.const (show-const c)) tt (sort-width s) []ᵥ
    shape-of (Val.inl v)       = node Tag.inl tt 1 (shape-of v ∷ᵥ []ᵥ)
    shape-of (Val.inr v)       = node Tag.inr tt 1 (shape-of v ∷ᵥ []ᵥ)
    shape-of (Val.pair v u)    = node Tag.pair tt 1 (shape-of v ∷ᵥ shape-of u ∷ᵥ []ᵥ)
    shape-of (Val.clo γ _)     = node (Tag.clo (length (shape-env-of γ))) tt 1 (fromList (shape-env-of γ))
    shape-of (Val.roll v)      = shape-of v

    cell-of : ∀ {σ} → Val (μ (unit [+] (σ [×] var zero))) → AVal ⊤
    cell-of (Val.roll (Val.inl Val.unit))         = node Tag.nil tt 2 []ᵥ
    cell-of (Val.roll (Val.inr (Val.pair hd tl))) = node Tag.cons tt 2 (shape-of hd ∷ᵥ shape-of tl ∷ᵥ []ᵥ)

    shape-env-of : ∀ {Γ} → Env Γ → List (AVal ⊤)
    shape-env-of emp     = []
    shape-env-of (γ · v) = shape-env-of γ ++ (shape-of v ∷ [])

label-of : Tag → String
label-of Tag.unit      = "()"
label-of Tag.inl       = "inl"
label-of Tag.inr       = "inr"
label-of Tag.pair      = "pr"
label-of (Tag.clo _)   = "clo"
label-of Tag.cons      = "∷"
label-of Tag.nil       = "[]"
label-of (Tag.const l) = l
