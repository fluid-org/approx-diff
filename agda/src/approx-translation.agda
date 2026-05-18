{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Approx (per-root) translation.
--
-- Parameterised on a SynMonad. Inserts Mon at the root of every type
-- former (one slot per type former), distinct from cbn-translation's
-- per-component design (one slot per component).
--
-- ⟪_⟫ty is defined via an inner decomposition: ⟪τ⟫ty = Mon ⟪τ⟫ty-inner.
-- This lets Agda see the outer Mon wrapper definitionally, so bind's
-- Mon-shaped body typechecks against ⟪τ⟫ty results without per-call
-- subst. The decomposition includes μ — μ-types are uniformly Mon-wrapped
-- at the root, like every other type former.
--
-- The polynomial body translation ⟪_⟫poly is structural. Mon-at-root
-- comes from ⟪_⟫ty on the unrolled type, not from the polynomial body.
-- This creates path-1/path-2 mismatch at sum/product roots — bridged by
-- approx-coerce/approx-coerce' (analogous to cbn-coerce/cbn-coerce').
------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.List using (List; []; _∷_)
open import signature using (Signature)
open import every
import language-syntax

module approx-translation {ℓ} (Sig : Signature ℓ) (M : language-syntax.SynMonad Sig) where

open Signature Sig using (sort)
open language-syntax Sig
open SynMonad M

mutual
  ⟪_⟫ty : type → type
  ⟪ τ ⟫ty = Mon ⟪ τ ⟫ty-inner

  ⟪_⟫ty-inner : type → type
  ⟪ unit ⟫ty-inner       = unit
  ⟪ bool ⟫ty-inner       = bool
  ⟪ base s ⟫ty-inner     = base s
  ⟪ τ₁ [×] τ₂ ⟫ty-inner  = ⟪ τ₁ ⟫ty [×] ⟪ τ₂ ⟫ty
  ⟪ τ₁ [+] τ₂ ⟫ty-inner  = ⟪ τ₁ ⟫ty [+] ⟪ τ₂ ⟫ty
  ⟪ τ₁ [→] τ₂ ⟫ty-inner  = ⟪ τ₁ ⟫ty [→] ⟪ τ₂ ⟫ty
  ⟪ μ P ⟫ty-inner        = μ ⟪ P ⟫poly

  ⟪_⟫poly : polynomial → polynomial
  ⟪ one ⟫poly      = one
  ⟪ const σ ⟫poly  = const ⟪ σ ⟫ty
  ⟪ var ⟫poly      = var
  ⟪ P [+] Q ⟫poly  = ⟪ P ⟫poly [+] ⟪ Q ⟫poly
  ⟪ P [×] Q ⟫poly  = ⟪ P ⟫poly [×] ⟪ Q ⟫poly

⟪_⟫ctxt : ctxt → ctxt
⟪ emp ⟫ctxt = emp
⟪ Γ , τ ⟫ctxt = ⟪ Γ ⟫ctxt , ⟪ τ ⟫ty

⟪_⟫var : ∀ {Γ τ} → Γ ∋ τ → ⟪ Γ ⟫ctxt ∋ ⟪ τ ⟫ty
⟪ zero ⟫var = zero
⟪ succ x ⟫var = succ ⟪ x ⟫var

_$_ : ∀ {Γ σ τ} → Γ ⊢ σ [→] τ → Γ ⊢ σ → Γ ⊢ τ
_$_ = app
infixl 10 _$_

-- Coerce for ⟪roll⟫tm. ⟪apply P τ⟫ty has Mon at every sum/product root
-- (per-root design); apply ⟪P⟫poly ⟪τ⟫ty has bare sum/product. Walk the
-- polynomial: extract from outer Mons, recurse, rebuild bare, repackage.
approx-coerce : (P : polynomial) → ∀ {Γ τ} →
                Γ ⊢ ⟪ apply P τ ⟫ty →
                Γ ⊢ Mon (apply ⟪ P ⟫poly ⟪ τ ⟫ty)
approx-coerce one        N = N
approx-coerce (const σ)  N = pure $ N
approx-coerce var        N = pure $ N
approx-coerce (P [+] Q)  N =
  bind $ N $ lam (case (var zero)
    (bind $ approx-coerce P (var zero) $ lam (pure $ inl (var zero)))
    (bind $ approx-coerce Q (var zero) $ lam (pure $ inr (var zero))))
approx-coerce (P [×] Q)  N =
  bind $ N $ lam (
    bind $ approx-coerce P (fst (var zero)) $ lam (
      bind $ approx-coerce Q (snd (var (succ zero))) $ lam (
        pure $ pair (var (succ zero)) (var zero))))

-- Strip Mon wrappers at var positions of the polynomial. Needed for
-- ⟪roll⟫tm: after approx-coerce strips sum/product-root Mons, var
-- positions still hold Mon-wrapped carriers (because ⟪μ P⟫ty has outer
-- Mon). Target roll wants bare carriers at var positions.
strip-var-Mon : (P : polynomial) → ∀ {Γ τ} →
                Γ ⊢ apply ⟪ P ⟫poly (Mon τ) →
                Γ ⊢ Mon (apply ⟪ P ⟫poly τ)
strip-var-Mon one        N = pure $ N
strip-var-Mon (const σ)  N = pure $ N
strip-var-Mon var        N = N
strip-var-Mon (P [+] Q)  N =
  case N
    (bind $ strip-var-Mon P (var zero) $ lam (pure $ inl (var zero)))
    (bind $ strip-var-Mon Q (var zero) $ lam (pure $ inr (var zero)))
strip-var-Mon (P [×] Q)  N =
  bind $ strip-var-Mon P (fst N) $ lam (
    bind $ strip-var-Mon Q (snd (weaken * N)) $ lam (
      pure $ pair (var (succ zero)) (var zero)))

-- The other direction (used by fold-μ for the algebra argument).
approx-coerce' : (P : polynomial) → ∀ {Γ τ} →
                 Γ ⊢ apply ⟪ P ⟫poly ⟪ τ ⟫ty →
                 Γ ⊢ ⟪ apply P τ ⟫ty
approx-coerce' one        N = pure $ N
approx-coerce' (const σ)  N = N
approx-coerce' var        N = N
approx-coerce' (P [+] Q)  N =
  pure $ case N
    (inl (approx-coerce' P (var zero)))
    (inr (approx-coerce' Q (var zero)))
approx-coerce' (P [×] Q)  N =
  pure $ pair (approx-coerce' P (fst N)) (approx-coerce' Q (snd N))

mutual
  ⟪_⟫tm : ∀ {Γ τ} → Γ ⊢ τ → ⟪ Γ ⟫ctxt ⊢ ⟪ τ ⟫ty
  ⟪ var x ⟫tm = var ⟪ x ⟫var
  ⟪ unit ⟫tm = pure $ unit
  ⟪ true ⟫tm = pure $ true
  ⟪ false ⟫tm = pure $ false
  ⟪ if M then M₁ else M₂ ⟫tm =
    bind $ ⟪ M ⟫tm $ lam (if (var zero) then (weaken * ⟪ M₁ ⟫tm) else (weaken * ⟪ M₂ ⟫tm))
  ⟪ inl M ⟫tm = pure $ inl ⟪ M ⟫tm
  ⟪ inr M ⟫tm = pure $ inr ⟪ M ⟫tm
  ⟪ case M N₁ N₂ ⟫tm =
    bind $ ⟪ M ⟫tm $ lam (case (var zero) (ext weaken * ⟪ N₁ ⟫tm) (ext weaken * ⟪ N₂ ⟫tm))
  ⟪ pair M N ⟫tm = pure $ pair ⟪ M ⟫tm ⟪ N ⟫tm
  ⟪ fst M ⟫tm = bind $ ⟪ M ⟫tm $ lam (fst (var zero))
  ⟪ snd M ⟫tm = bind $ ⟪ M ⟫tm $ lam (snd (var zero))
  ⟪ lam M ⟫tm = pure $ lam ⟪ M ⟫tm
  ⟪ app M N ⟫tm = bind $ ⟪ M ⟫tm $ lam ((var zero) $ (weaken * ⟪ N ⟫tm))
  ⟪ bop ω Ms ⟫tm = bindAll Ms (id-ren _) (λ ρ Ms' → pure $ bop ω Ms')
  ⟪ brel ω Ms ⟫tm = bindAll Ms (id-ren _) (λ ρ Ms' → pure $ brel ω Ms')
  ⟪ roll {P = P} M ⟫tm =
    bind $ approx-coerce P ⟪ M ⟫tm $ lam (
      bind $ strip-var-Mon P (var zero) $ lam (
        pure $ roll (var zero)))
  ⟪ fold-μ {P = Q} {τ = τ} alg M ⟫tm =
    bind $ ⟪ alg ⟫tm $ lam (
      bind $ (weaken * ⟪ M ⟫tm) $ lam (
        fold-μ
          (lam (app (var (succ (succ zero))) (approx-coerce' Q (var zero))))
          (var zero)))

  bindAll : ∀ {Γ Γ' σs τ} → Every (λ σ → Γ ⊢ base σ) σs → Ren ⟪ Γ ⟫ctxt Γ' →
            (∀ {Γ''} → Ren Γ' Γ'' → Every (λ σ → Γ'' ⊢ base σ) σs → Γ'' ⊢ Mon τ) → Γ' ⊢ Mon τ
  bindAll [] ρ κ = κ (id-ren _) []
  bindAll (M ∷ Ms) ρ κ =
    bind $ (ρ * ⟪ M ⟫tm) $ lam (
      bindAll Ms (weaken ∘ren ρ) (λ ρ' Ms' → κ (λ x → ρ' (succ x)) (var (ρ' zero) ∷ Ms')))
