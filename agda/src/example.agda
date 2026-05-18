{-# OPTIONS --prop --postfix-projections --safe #-}

module example where

open import Level using (0ℓ; lift)
open import Data.List using (List; []; _∷_)
open import every using (Every; []; _∷_)
open import signature
import language-syntax
import label

open import example-signature

module L = language-syntax Sig

-- example query. Given `List (label [×] nat)`, add up all the
-- elements labelled with a specific label:
--
--   sum [ snd e | e <- xs, equal-label 'a' (fst e) ]
--
--   sum (concatMap x (e. if equal-label 'a' (fst e) then return (snd e) else nil))
--
--   sum = fold zero (add (var zero) (var (succ zero)))

module ex where
  open L

  -- Writer monad over the approximation sort: pairs values with an
  -- accuracy tag. Tag-bind multiplies the two tags via approx-mult.
  Tag : type → type
  Tag τ = base approx [×] τ

  Tag-pure : ∀ {Γ τ} → Γ ⊢ τ [→] Tag τ
  Tag-pure = lam (pair (bop approx-unit []) (var zero))

  Tag-bind : ∀ {Γ σ τ} → Γ ⊢ Tag σ [→] (σ [→] Tag τ) [→] Tag τ
  Tag-bind = lam (lam (pair (bop approx-mult (fst (var (succ zero)) ∷ fst (app (var zero) (snd (var (succ zero)))) ∷ []))
                          (snd (app (var zero) (snd (var (succ zero)))))))

  Tag-monad : SynMonad
  Tag-monad .SynMonad.Mon = Tag
  Tag-monad .SynMonad.pure = Tag-pure
  Tag-monad .SynMonad.bind = Tag-bind

  -- Lifting monad: L τ = unit + τ. ⊥ is `inl unit`; values are `inr x`.
  -- L-bind propagates ⊥ on the left branch.
  L : type → type
  L τ = unit [+] τ

  L-pure : ∀ {Γ τ} → Γ ⊢ τ [→] L τ
  L-pure = lam (inr (var zero))

  L-bind : ∀ {Γ σ τ} → Γ ⊢ L σ [→] (σ [→] L τ) [→] L τ
  L-bind = lam (lam (case (var (succ zero)) (inl unit) (app (var (succ zero)) (var zero))))

  L-monad : SynMonad
  L-monad .SynMonad.Mon = L
  L-monad .SynMonad.pure = L-pure
  L-monad .SynMonad.bind = L-bind

  `_ : ∀ {Γ} → label.label → Γ ⊢ base label
  ` l = bop (lbl l) []

  _≟_ : ∀ {Γ} → Γ ⊢ base label → Γ ⊢ base label → Γ ⊢ bool
  M ≟ N = brel equal-label (M ∷ N ∷ [])

  -- Summation function, μ-types version (uses list).
  sum : ∀ {Γ} → Γ ⊢ list (base number) [→] base number
  sum = lam (fold (bop zero []) (bop add (var zero ∷ var (succ zero) ∷ [])) (var zero))

  query : label.label → emp , list (base label [×] base number) ⊢ base number
  query l = app sum
                 (from var zero collect
                  when fst (var zero) ≟ (` l) ；
                  return (snd (var zero)))

  -- Tag-decorated CBN translation: each component of every type former
  -- gets its own (approx-tag, value) pair.
  module cbn-Tag where
    open import cbn-translation Sig Tag-monad

    cbn-query : label.label → emp , Tag (list (Tag (Tag (base label) [×] Tag (base number)))) ⊢ Tag (base number)
    cbn-query l = ⟪ query l ⟫tm

  -- L-decorated CBN translation: each component gets its own (unit + τ) wrap.
  module cbn-L where
    open import cbn-translation Sig L-monad

    cbn-query : label.label → emp , L (list (L (L (base label) [×] L (base number)))) ⊢ L (base number)
    cbn-query l = ⟪ query l ⟫tm

  -- Tag-decorated approx translation: a single tag per type former
  -- root (rather than per-component).
  module approx-Tag where
    open import approx-translation Sig Tag-monad

    approx-query : label.label →
                   ⟪ emp , list (base label [×] base number) ⟫ctxt ⊢ ⟪ base number ⟫ty
    approx-query l = ⟪ query l ⟫tm

  -- L-decorated approx translation.
  module approx-L where
    open import approx-translation Sig L-monad

    approx-query : label.label →
                   ⟪ emp , list (base label [×] base number) ⟫ctxt ⊢ ⟪ base number ⟫ty
    approx-query l = ⟪ query l ⟫tm
