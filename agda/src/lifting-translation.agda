{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Lifting translation.
--
-- A monadic translation parameterised on an arbitrary syntactic monad
-- `Mon`, intended to insert "approximation points" at the natural sites
-- for Galois slicing. Unlike Moggi's CBN translation (cbn-translation),
-- which Mon-wraps every component of every type former, the lifting
-- translation wraps Mon only at:
--
--   • labels (base types) — every label-valued value can be approximated
--     by ⊥/⊤ (or the chosen approximation lattice);
--   • the "root" of sum, product, and function types — a single
--     approximation slot per type former, capturing "did the value's
--     top-level shape get pinned down?".
--
-- This avoids the redundant per-component wrapping of CBN: e.g. a pair
-- becomes Mon (σ × τ) (single approximation point at the pair) rather
-- than Mon σ × Mon τ (separate approximation points at each component,
-- as in CBN).
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
  ⟪ unit ⟫ty       = unit                            -- no Mon: nothing to approximate
  ⟪ bool ⟫ty       = Mon bool                        -- primitive in syntax; treat like a label
  ⟪ base s ⟫ty     = Mon (base s)                    -- label: approximation at the leaf
  ⟪ τ₁ [×] τ₂ ⟫ty  = Mon (⟪ τ₁ ⟫ty [×] ⟪ τ₂ ⟫ty)    -- root Mon: one approximation slot for the pair
  ⟪ τ₁ [+] τ₂ ⟫ty  = Mon (⟪ τ₁ ⟫ty [+] ⟪ τ₂ ⟫ty)    -- root Mon: one approximation slot for the sum-tag choice
  ⟪ τ₁ [→] τ₂ ⟫ty  = Mon (⟪ τ₁ ⟫ty [→] ⟪ τ₂ ⟫ty)    -- root Mon: one approximation slot for the function value
  ⟪ μ P ⟫ty        = μ ⟪ P ⟫poly                     -- no outer Mon around μ (see "Recursive types" below)

  -- Polynomial body translation. The body's structure is preserved
  -- syntactically; only the parameter slot's type gets translated.
  -- The Mon wraps at sum/product roots come from the unrolling at the
  -- type level (via ⟪_⟫ty applied to `apply P τ`), not from the
  -- polynomial body itself.
  ⟪_⟫poly : polynomial → polynomial
  ⟪ one ⟫poly       = one
  ⟪ const σ ⟫poly   = const ⟪ σ ⟫ty
  ⟪ var ⟫poly       = var
  ⟪ P₁ +ᵖ P₂ ⟫poly  = ⟪ P₁ ⟫poly +ᵖ ⟪ P₂ ⟫poly
  ⟪ P₁ ×ᵖ P₂ ⟫poly  = ⟪ P₁ ⟫poly ×ᵖ ⟪ P₂ ⟫poly

------------------------------------------------------------------------------
-- Recursive types: discussion.
--
-- Source: μ P.
-- Translation: μ ⟪P⟫poly.
--
-- There is NO outer Mon around the μ. The approximation points the user
-- wants — e.g. "is this a nil or a cons?" for lists — arise from the
-- unrolling, via the sum and product structure of P:
--
--   List τ = μ (one +ᵖ (const τ ×ᵖ var))
--   ⟪List τ⟫ty = μ (one +ᵖ (const ⟪τ⟫ty ×ᵖ var))
--
-- Unrolling one level (apply P (μ P)):
--   apply (one +ᵖ (const τ ×ᵖ var)) (μ P)
--     = unit [+] (τ [×] μ P)
--
-- Translating this *as a type*:
--   ⟪apply (one +ᵖ (const τ ×ᵖ var)) (μ P)⟫ty
--     = Mon (unit [+] Mon (⟪τ⟫ty [×] μ ⟪P⟫poly))
--
-- The OUTER Mon (around the sum) is the "is this nil or cons?"
-- approximation point. The INNER Mon (around the cons-payload pair) is
-- the "did the cons get committed to?" approximation. The tail itself
-- is plain `μ ⟪P⟫poly` — no extra Mon, because we already get
-- approximation at each unroll via the Mon-wrapped sum.
--
-- This is exactly the user's intuition: an approximation point at the
-- tail arises naturally from the sum's root-Mon, without needing an L
-- wrapper around the recursive type itself.

------------------------------------------------------------------------------
-- Path-mismatch issue (same as cbn-translation).
--
-- The type-level translation ⟪_⟫ty inserts Mon at sum/product/function
-- roots. The polynomial body translation ⟪_⟫poly is structural (no Mon).
-- So in general:
--   ⟪apply P τ⟫ty   ≠   apply ⟪P⟫poly ⟪τ⟫ty
-- The first has Mon at sum/product roots; the second doesn't.
--
-- This affects ⟪roll⟫tm and ⟪fold-μ⟫tm: roll's source argument has
-- type ⟪apply P (μ P)⟫ty (Mon-wrapped at sum/product), but the target
-- `roll` expects apply ⟪P⟫poly ⟪μ P⟫ty (un-wrapped). Need a coerce
-- helper analogous to cbn-coerce, but adapted to the new wrap pattern
-- (Mon at root rather than per-component).
--
-- Sketch of coerce signature:
--   lift-coerce : (P : polynomial) → ∀ {Γ τ} →
--                 Γ ⊢ ⟪apply P τ⟫ty →
--                 Γ ⊢ Mon (apply ⟪P⟫poly ⟪τ⟫ty)
--
-- Structurally:
--   one:        pure unit
--   const σ:    pure $ M       (input is ⟪σ⟫ty; output is Mon ⟪σ⟫ty)
--   var:        pure M         (input is ⟪τ⟫ty; output is Mon ⟪τ⟫ty)
--   P₁ +ᵖ P₂:   input is Mon (⟪apply P₁ τ⟫ + ⟪apply P₂ τ⟫); bind it,
--               case-split, recurse, rewrap.
--   P₁ ×ᵖ P₂:   input is Mon (⟪apply P₁ τ⟫ × ⟪apply P₂ τ⟫); bind it,
--               project, recurse on each, pair, pure.
--
-- The +ᵖ and ×ᵖ cases for lift-coerce are SIMPLER than cbn-coerce's
-- (only ONE bind per layer, not per-component), because the input has
-- a single Mon at the root rather than Mons at each component.

------------------------------------------------------------------------------
-- Context translation. Variables hold bare translated types (no extra
-- Mon-wrap), in contrast to CBN's thunked-variable convention.

⟪_⟫ctxt : ctxt → ctxt
⟪ emp ⟫ctxt = emp
⟪ Γ , τ ⟫ctxt = ⟪ Γ ⟫ctxt , ⟪ τ ⟫ty

⟪_⟫var : ∀ {Γ τ} → Γ ∋ τ → ⟪ Γ ⟫ctxt ∋ ⟪ τ ⟫ty
⟪ zero ⟫var = zero
⟪ succ x ⟫var = succ ⟪ x ⟫var

------------------------------------------------------------------------------
-- Term translation: sketch.
--
-- Not yet filled in. The shape is similar to cbn-translation:
--   ⟪_⟫tm : ∀ {Γ τ} → Γ ⊢ τ → ⟪Γ⟫ctxt ⊢ Mon ⟪τ⟫ty
--
-- For each constructor, pure-wrap if the type translation puts Mon at
-- the root (which is true for product/sum/function/label/μ — all but
-- unit and bool), bind out operands where needed to access values.
--
-- TODO: implement ⟪_⟫tm, ⟪_⟫poly equivalents for terms.
