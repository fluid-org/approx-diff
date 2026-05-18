{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Insert Mon at the root of every type former (per-root); cf. cbn-translation (per-component).
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

  -- Helps Agda see outer Mon wrapper definitionally
  ⟪_⟫ty-inner : type → type
  ⟪ unit ⟫ty-inner       = unit
  ⟪ bool ⟫ty-inner       = bool
  ⟪ base s ⟫ty-inner     = base s
  ⟪ τ₁ [×] τ₂ ⟫ty-inner  = ⟪ τ₁ ⟫ty [×] ⟪ τ₂ ⟫ty
  ⟪ τ₁ [+] τ₂ ⟫ty-inner  = ⟪ τ₁ ⟫ty [+] ⟪ τ₂ ⟫ty
  ⟪ τ₁ [→] τ₂ ⟫ty-inner  = ⟪ τ₁ ⟫ty [→] ⟪ τ₂ ⟫ty
  ⟪ μ P ⟫ty-inner        = μ ⟪ P ⟫poly
  ⟪ approx τ ⟫ty-inner   = approx ⟪ τ ⟫ty

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

-- Collapse Mon at every internal node of ⟪apply P τ⟫ty (and at the carrier) into a single outer Mon, via bind.
-- Used by ⟪roll⟫tm.
approx-coerce : (P : polynomial) → ∀ {Γ τ} →  Γ ⊢ ⟪ apply P τ ⟫ty → Γ ⊢ Mon (apply ⟪ P ⟫poly ⟪ τ ⟫ty-inner)
approx-coerce one        N = N
approx-coerce (const σ)  N = pure $ N
approx-coerce var        N = N
approx-coerce (P [+] Q)  N =
  bind $ N $ lam (case (var zero)
    (bind $ approx-coerce P (var zero) $ lam (pure $ inl (var zero)))
    (bind $ approx-coerce Q (var zero) $ lam (pure $ inr (var zero))))
approx-coerce (P [×] Q)  N =
  bind $ N $ lam (
    bind $ approx-coerce P (fst (var zero)) $ lam (
      bind $ approx-coerce Q (snd (var (succ zero))) $ lam (
        pure $ pair (var (succ zero)) (var zero))))

-- Insert Mon at every internal node, via pure. Used by ⟪fold-μ⟫tm.
approx-coerce' : (P : polynomial) → ∀ {Γ τ} → Γ ⊢ apply ⟪ P ⟫poly ⟪ τ ⟫ty → Γ ⊢ ⟪ apply P τ ⟫ty
approx-coerce' one        N = pure $ N
approx-coerce' (const σ)  N = N
approx-coerce' var        N = N
approx-coerce' (P [+] Q)  N = pure $ case N (inl (approx-coerce' P (var zero))) (inr (approx-coerce' Q (var zero)))
approx-coerce' (P [×] Q)  N = pure $ pair (approx-coerce' P (fst N)) (approx-coerce' Q (snd N))

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
    bind $ approx-coerce P ⟪ M ⟫tm $ lam (pure $ roll (var zero))
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
