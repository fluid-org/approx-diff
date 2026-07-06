{-# OPTIONS --prop --postfix-projections --safe #-}

module example-2 where

open import Level using (0ℓ; lift)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_)
open import every using (Every; []; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)
open import signature
import language-syntax-2
import label

open import example-signature

module L = language-syntax-2 Sig

module ex where
  open L
  open SynMonad

  Tag : ∀ {Δ} → type Δ → type Δ
  Tag τ = base approx [×] τ

  Tag-pure : ∀ {Γ τ} → Γ ⊢ τ [→] Tag τ
  Tag-pure = lam (pair (bop approx-unit []) (var zero))

  Tag-bind : ∀ {Γ σ τ} → Γ ⊢ Tag σ [→] (σ [→] Tag τ) [→] Tag τ
  Tag-bind =
    lam (lam (pair (bop approx-mult (fst (var (succ zero)) ∷ fst (app (var zero) (snd (var (succ zero)))) ∷ []))
                   (snd (app (var zero) (snd (var (succ zero)))))))

  Tag-monad : SynMonad
  Tag-monad .Mon         = Tag
  Tag-monad .Mon-ren _ _ = refl
  Tag-monad .Mon-sub _ _ = refl
  Tag-monad .pure        = Tag-pure
  Tag-monad .bind        = Tag-bind

  `_ : ∀ {Γ} → label.label → Γ ⊢ base label
  ` l = bop (lbl l) []

  _≟_ : ∀ {Γ} → Γ ⊢ base label → Γ ⊢ base label → Γ ⊢ bool
  M ≟ N = brel equal-label (M ∷ N ∷ [])

  sum : ∀ {Γ} → Γ ⊢ list (base number) [→] base number
  sum = lam (foldr (bop zero []) (bop add (var zero ∷ var (succ zero) ∷ [])) (var zero))

  some-eq : ∀ {Γ} → Γ ⊢ base label [→] list (base label) [→] bool
  some-eq = lam (lam
    (foldr false
      (if (brel equal-label (var (succ zero) ∷ var (succ (succ (succ zero))) ∷ []))
       then true else (var zero))
      (var zero)))

  query : label.label → emp , list (base label [×] base number) ⊢ base number
  query l =
    app sum
      (from var zero collect
      when fst (var zero) ≟ (` l) ；
      return (snd (var zero)))

  -- Rose trees of numbers: a nested recursive type (the children list is itself
  -- a μ-type mentioning the outer recursion variable).
  rose : type 0
  rose = μ (base number [×] μ (unit [+] (var (Fin.suc Fin.zero) [×] var Fin.zero)))

  node : ∀ {Γ} → Γ ⊢ base number → Γ ⊢ list rose → Γ ⊢ rose
  node n ts = roll (pair n ts)

  -- Sum of all numbers in a rose tree: the fold's recursion crosses the inner
  -- list μ, so the children arrive as a list of subtree sums.
  rose-sum : ∀ {Γ} → Γ ⊢ rose [→] base number
  rose-sum = lam (fold (bop add (fst (var zero) ∷ app sum (snd (var zero)) ∷ [])) (var zero))

  rose-query : emp , rose ⊢ base number
  rose-query = app rose-sum (var zero)
