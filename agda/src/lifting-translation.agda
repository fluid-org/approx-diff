{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Lifting translation.
--
-- A monadic translation parameterised on an arbitrary syntactic monad
-- `Mon`, intended to insert "approximation points" at the natural sites
-- for Galois slicing. Unlike Moggi's CBN translation (cbn-translation),
-- which Mon-wraps every component of every type former, the lifting
-- translation wraps Mon at the root of every compound type former
-- (sum, product, function, μ) and at labels. Each type former gets one
-- approximation slot.
--
-- The design rationale comes from a Galois-slicing operational reading:
-- every value can be ⊥ at the top, and every eliminator has a
-- bind-like rule: `eliminator ⊥ = ⊥`. So the root Mon is the
-- "did this type former commit?" slot — including for `unroll` of a
-- μ-value, where `unroll ⊥ = ⊥` is the natural rule.
--
-- This avoids the redundant per-component wrapping of CBN: e.g. a pair
-- becomes Mon (σ × τ) (single approximation point at the pair) rather
-- than Mon σ × Mon τ (separate per-component slots as in CBN).
--
-- The intended target monad in practice is the lifting monad L (hence
-- the module name), but the translation is parameterised on an
-- arbitrary SynMonad as before.
------------------------------------------------------------------------------

open import Data.List using (List; []; _∷_)
open import signature using (Signature)
open import every
import language-syntax

module lifting-translation {ℓ} (Sig : Signature ℓ) (M : language-syntax.SynMonad Sig) where

open Signature Sig using (sort)
open language-syntax Sig
open SynMonad M

------------------------------------------------------------------------------
-- Type translation.

mutual
  ⟪_⟫ty : type → type
  ⟪ unit ⟫ty       = Mon unit
  ⟪ bool ⟫ty       = Mon bool
  ⟪ base s ⟫ty     = Mon (base s)
  ⟪ τ₁ [×] τ₂ ⟫ty  = Mon (⟪ τ₁ ⟫ty [×] ⟪ τ₂ ⟫ty)
  ⟪ τ₁ [+] τ₂ ⟫ty  = Mon (⟪ τ₁ ⟫ty [+] ⟪ τ₂ ⟫ty)
  ⟪ τ₁ [→] τ₂ ⟫ty  = Mon (⟪ τ₁ ⟫ty [→] ⟪ τ₂ ⟫ty)
  ⟪ μ P ⟫ty        = Mon (μ ⟪ P ⟫poly)

  -- Polynomial body translation. The body's structure is preserved
  -- syntactically; only the parameter slot's type gets translated.
  -- The Mon wraps at sum/product roots come from the unrolling at the
  -- type level (via ⟪_⟫ty applied to `apply P τ`), not from the
  -- polynomial body itself.
  ⟪_⟫poly : polynomial → polynomial
  ⟪ one ⟫poly       = one
  ⟪ const σ ⟫poly   = const ⟪ σ ⟫ty
  ⟪ var ⟫poly       = var
  ⟪ P₁ + P₂ ⟫poly  = ⟪ P₁ ⟫poly + ⟪ P₂ ⟫poly
  ⟪ P₁ × P₂ ⟫poly  = ⟪ P₁ ⟫poly × ⟪ P₂ ⟫poly

⟪_⟫ctxt : ctxt → ctxt
⟪ emp ⟫ctxt = emp
⟪ Γ , τ ⟫ctxt = ⟪ Γ ⟫ctxt , ⟪ τ ⟫ty

⟪_⟫var : ∀ {Γ τ} → Γ ∋ τ → ⟪ Γ ⟫ctxt ∋ ⟪ τ ⟫ty
⟪ zero ⟫var = zero
⟪ succ x ⟫var = succ ⟪ x ⟫var

-- TODO: ⟪_⟫tm
