{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import primitives using (Primitives)
import two

module language-operational.annotated-value {ℓ} (Sig : Signature ℓ)
  (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig using (unit; μ; var; _[+]_; _[×]_)
open import language-operational.evaluation Sig 𝒫 using (Val; Env)
open Val
open Env
open import Data.Fin using (zero)

data Shape : Set where
  unit const inl inr pair clo cons nil : Shape

-- A node covers a run of positions at its own site, then its children in order. A cons covers the
-- tag and the pair beneath it, and nil the tag and its unit.
data AVal (X : Set) : Set where
  node : Shape → String → X → ℕ → List (AVal X) → AVal X

covers : ∀ {X} → AVal X → ℕ
covers-all : ∀ {X} → List (AVal X) → ℕ

covers (node _ _ _ n cs) = n + covers-all cs
covers-all []       = 0
covers-all (t ∷ ts) = covers t + covers-all ts

module _ (show-const : ∀ {s} → sort-val s → String) where

  mutual
    shape-of : ∀ {τ} → Val τ → AVal ⊤
    shape-of {μ (unit [+] (_ [×] var zero))} v = cell-of v
    shape-of Val.unit          = node Shape.unit "()" tt 1 []
    shape-of (Val.const {s} c) = node Shape.const (show-const c) tt (sort-width s) []
    shape-of (Val.inl v)       = node Shape.inl "inl" tt 1 (shape-of v ∷ [])
    shape-of (Val.inr v)       = node Shape.inr "inr" tt 1 (shape-of v ∷ [])
    shape-of (Val.pair v u)    = node Shape.pair "pr" tt 1 (shape-of v ∷ shape-of u ∷ [])
    shape-of (Val.clo γ _)     = node Shape.clo "clo" tt 1 (shape-env-of γ)
    shape-of (Val.roll v)      = shape-of v

    cell-of : ∀ {σ} → Val (μ (unit [+] (σ [×] var zero))) → AVal ⊤
    cell-of (Val.roll (Val.inl Val.unit))         = node Shape.nil "[]" tt 2 []
    cell-of (Val.roll (Val.inr (Val.pair hd tl))) =
      node Shape.cons "∷" tt 2 (shape-of hd ∷ shape-of tl ∷ [])

    shape-env-of : ∀ {Γ} → Env Γ → List (AVal ⊤)
    shape-env-of emp     = []
    shape-env-of (γ · v) = shape-env-of γ ++ (shape-of v ∷ [])

module annotate {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

  private
    module Sc = CommutativeSemiring S

  Scalar : Set
  Scalar = Setoid.Carrier A

  private
    join-run : (ℕ → Scalar) → ℕ → ℕ → Scalar
    join-run row off zero    = Sc.ε
    join-run row off (suc n) = row off Sc.+ join-run row (suc off) n

    at-run : Scalar → ℕ → ℕ → ℕ → Scalar
    at-run a zero    off      i        = Sc.ε
    at-run a (suc n) zero     zero     = a
    at-run a (suc n) zero     (suc i)  = at-run a n zero i
    at-run a (suc n) (suc o)  zero     = Sc.ε
    at-run a (suc n) (suc o)  (suc i)  = at-run a (suc n) o i

  mutual
    fill : (ℕ → Scalar) → ℕ → AVal ⊤ → AVal Scalar
    fill row off (node sh l _ n cs) = node sh l (join-run row off n) n (fill-all row (off + n) cs)

    fill-all : (ℕ → Scalar) → ℕ → List (AVal ⊤) → List (AVal Scalar)
    fill-all row off []       = []
    fill-all row off (t ∷ ts) = fill row off t ∷ fill-all row (off + covers t) ts

  mutual
    spread : AVal Scalar → ℕ → ℕ → Scalar
    spread (node _ _ a n cs) off i = at-run a n off i Sc.+ spread-all cs (off + n) i

    spread-all : List (AVal Scalar) → ℕ → ℕ → Scalar
    spread-all []       off i = Sc.ε
    spread-all (t ∷ ts) off i = spread t off i Sc.+ spread-all ts (off + covers t) i

  row→aval : ∀ {τ} (show-const : ∀ {s} → sort-val s → String) →
             (ℕ → Scalar) → Val τ → AVal Scalar
  row→aval sc row v = fill row 0 (shape-of sc v)

  aval→row : AVal Scalar → ℕ → Scalar
  aval→row t i = spread t 0 i
