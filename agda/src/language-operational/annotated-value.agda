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
open import Data.Nat.Properties using (+-identityʳ; +-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import language-syntax Sig using (unit; base; μ; var; _[+]_; _[×]_; _[→]_)
open import language-operational.evaluation Sig 𝒫 using (Val; Env; width; width-env)
open Val
open Env
open import Data.Fin using (zero)

data Tag : Set where
  unit inl inr pair clo cons nil : Tag
  const : String → Tag

-- A node covers a run of positions at its own site, then its children in order. A cons covers the
-- tag and the pair beneath it, and nil the tag and its unit.
data AVal (X : Set) : Set where
  node : Tag → X → ℕ → List (AVal X) → AVal X

covers : ∀ {X} → AVal X → ℕ
covers-all : ∀ {X} → List (AVal X) → ℕ

covers (node _ _ n cs) = n + covers-all cs
covers-all []       = 0
covers-all (t ∷ ts) = covers t + covers-all ts

fold : ∀ {X B : Set} → (Tag → X → ℕ → ℕ → List B → B) → ℕ → AVal X → B
fold-all : ∀ {X B : Set} → (Tag → X → ℕ → ℕ → List B → B) → ℕ → List (AVal X) → List B

fold f off (node sh x n cs) = f sh x n off (fold-all f (off + n) cs)
fold-all f off []       = []
fold-all f off (t ∷ ts) = fold f off t ∷ fold-all f (off + covers t) ts

covers-++ : ∀ {X} (ts us : List (AVal X)) →
            covers-all (ts ++ us) ≡ covers-all ts + covers-all us
covers-++ []       us = refl
covers-++ (t ∷ ts) us =
  trans (cong (covers t +_) (covers-++ ts us)) (sym (+-assoc (covers t) _ _))

module _ (show-const : ∀ {s} → sort-val s → String) where

  mutual
    shape-of : ∀ {τ} → Val τ → AVal ⊤
    shape-of {μ (unit [+] (_ [×] var zero))} v = cell-of v
    shape-of Val.unit          = node Tag.unit tt 1 []
    shape-of (Val.const {s} c) = node (Tag.const (show-const c)) tt (sort-width s) []
    shape-of (Val.inl v)       = node Tag.inl tt 1 (shape-of v ∷ [])
    shape-of (Val.inr v)       = node Tag.inr tt 1 (shape-of v ∷ [])
    shape-of (Val.pair v u)    = node Tag.pair tt 1 (shape-of v ∷ shape-of u ∷ [])
    shape-of (Val.clo γ _)     = node Tag.clo tt 1 (shape-env-of γ)
    shape-of (Val.roll v)      = shape-of v

    cell-of : ∀ {σ} → Val (μ (unit [+] (σ [×] var zero))) → AVal ⊤
    cell-of (Val.roll (Val.inl Val.unit))         = node Tag.nil tt 2 []
    cell-of (Val.roll (Val.inr (Val.pair hd tl))) =
      node Tag.cons tt 2 (shape-of hd ∷ shape-of tl ∷ [])

    shape-env-of : ∀ {Γ} → Env Γ → List (AVal ⊤)
    shape-env-of emp     = []
    shape-env-of (γ · v) = shape-env-of γ ++ (shape-of v ∷ [])

  mutual
    covers-width : ∀ {τ} (v : Val τ) → covers (shape-of v) ≡ width v
    covers-width {μ (unit [+] (_ [×] var zero))} v = covers-cell-width v
    covers-width Val.unit          = refl
    covers-width (Val.const {s} c) = +-identityʳ (sort-width s)
    covers-width (Val.inl v)       =
      cong suc (trans (+-identityʳ _) (covers-width v))
    covers-width (Val.inr v)       =
      cong suc (trans (+-identityʳ _) (covers-width v))
    covers-width (Val.pair v u)    =
      cong suc (trans (cong (covers (shape-of v) +_) (+-identityʳ _))
                      (cong₂ _+_ (covers-width v) (covers-width u)))
    covers-width (Val.clo γ _)     = cong suc (covers-env-width γ)
    covers-width (Val.roll {τ = var _} v) = covers-width v
    covers-width (Val.roll {τ = unit} v) = covers-width v
    covers-width (Val.roll {τ = base _} v) = covers-width v
    covers-width (Val.roll {τ = _ [×] _} v) = covers-width v
    covers-width (Val.roll {τ = _ [→] _} v) = covers-width v
    covers-width (Val.roll {τ = μ _} v) = covers-width v
    covers-width (Val.roll {τ = (var _) [+] _} v) = covers-width v
    covers-width (Val.roll {τ = (base _) [+] _} v) = covers-width v
    covers-width (Val.roll {τ = (_ [+] _) [+] _} v) = covers-width v
    covers-width (Val.roll {τ = (_ [×] _) [+] _} v) = covers-width v
    covers-width (Val.roll {τ = (_ [→] _) [+] _} v) = covers-width v
    covers-width (Val.roll {τ = (μ _) [+] _} v) = covers-width v
    covers-width (Val.roll {τ = unit [+] (var _)} v) = covers-width v
    covers-width (Val.roll {τ = unit [+] unit} v) = covers-width v
    covers-width (Val.roll {τ = unit [+] (base _)} v) = covers-width v
    covers-width (Val.roll {τ = unit [+] (_ [+] _)} v) = covers-width v
    covers-width (Val.roll {τ = unit [+] (_ [→] _)} v) = covers-width v
    covers-width (Val.roll {τ = unit [+] (μ _)} v) = covers-width v
    covers-width (Val.roll {τ = unit [+] (_ [×] (unit))} v) = covers-width v
    covers-width (Val.roll {τ = unit [+] (_ [×] (base _))} v) = covers-width v
    covers-width (Val.roll {τ = unit [+] (_ [×] (_ [+] _))} v) = covers-width v
    covers-width (Val.roll {τ = unit [+] (_ [×] (_ [×] _))} v) = covers-width v
    covers-width (Val.roll {τ = unit [+] (_ [×] (_ [→] _))} v) = covers-width v
    covers-width (Val.roll {τ = unit [+] (_ [×] (μ _))} v) = covers-width v

    covers-cell-width : ∀ {σ} (v : Val (μ (unit [+] (σ [×] var zero)))) →
                        covers (cell-of v) ≡ width v
    covers-cell-width (Val.roll (Val.inl Val.unit)) = refl
    covers-cell-width (Val.roll (Val.inr (Val.pair hd tl))) =
      cong (λ k → suc (suc k))
           (trans (cong (covers (shape-of hd) +_) (+-identityʳ _))
                  (cong₂ _+_ (covers-width hd) (covers-width tl)))

    covers-env-width : ∀ {Γ} (γ : Env Γ) → covers-all (shape-env-of γ) ≡ width-env γ
    covers-env-width emp     = refl
    covers-env-width (γ · v) =
      trans (covers-++ (shape-env-of γ) (shape-of v ∷ []))
            (cong₂ _+_ (covers-env-width γ) (trans (+-identityʳ _) (covers-width v)))

label-of : Tag → String
label-of Tag.unit      = "()"
label-of Tag.inl       = "inl"
label-of Tag.inr       = "inr"
label-of Tag.pair      = "pr"
label-of Tag.clo       = "clo"
label-of Tag.cons      = "∷"
label-of Tag.nil       = "[]"
label-of (Tag.const l) = l

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

  fill : (ℕ → Scalar) → ℕ → AVal ⊤ → AVal Scalar
  fill row = fold (λ sh _ n off cs → node sh (join-run row off n) n cs)

  private
    sum-at : List (ℕ → Scalar) → ℕ → Scalar
    sum-at []       i = Sc.ε
    sum-at (r ∷ rs) i = r i Sc.+ sum-at rs i

  spread : AVal Scalar → ℕ → ℕ → Scalar
  spread t off = fold (λ _ a n o rs i → at-run a n o i Sc.+ sum-at rs i) off t

  row→aval : ∀ {τ} (show-const : ∀ {s} → sort-val s → String) →
             (ℕ → Scalar) → Val τ → AVal Scalar
  row→aval sc row v = fill row 0 (shape-of sc v)

  aval→row : AVal Scalar → ℕ → Scalar
  aval→row t i = spread t 0 i
