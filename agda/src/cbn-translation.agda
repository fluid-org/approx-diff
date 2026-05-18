{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Moggi-style CBN translation, using the language's built-in approx
-- modality (formerly parameterised on an external SynMonad). This puts
-- approximation slots on every component of every compound type former
-- (per-component approxes) — distinct from approx-translation's
-- per-root design.
------------------------------------------------------------------------------

open import Data.List using (List; []; _∷_)
open import signature using (Signature)
open import every
import language-syntax

module cbn-translation {ℓ} (Sig : Signature ℓ) where

open Signature Sig using (sort)
open language-syntax Sig

mutual
  ⟪_⟫ty : type → type
  ⟪ unit ⟫ty = unit
  ⟪ bool ⟫ty = bool
  ⟪ base s ⟫ty = base s
  ⟪ τ₁ [×] τ₂ ⟫ty = approx ⟪ τ₁ ⟫ty [×] approx ⟪ τ₂ ⟫ty
  ⟪ τ₁ [+] τ₂ ⟫ty = approx ⟪ τ₁ ⟫ty [+] approx ⟪ τ₂ ⟫ty
  ⟪ τ₁ [→] τ₂ ⟫ty = (approx ⟪ τ₁ ⟫ty) [→] (approx ⟪ τ₂ ⟫ty)
  ⟪ μ P ⟫ty = μ ⟪ P ⟫poly
  ⟪ approx τ ⟫ty = approx ⟪ τ ⟫ty

  ⟪_⟫poly : polynomial → polynomial
  ⟪ one ⟫poly       = one
  ⟪ const σ ⟫poly   = const (approx ⟪ σ ⟫ty)
  ⟪ var ⟫poly       = var
  ⟪ P [+] Q ⟫poly        = ⟪ P ⟫poly [+] ⟪ Q ⟫poly
  ⟪ P [×] Q ⟫poly        = ⟪ P ⟫poly [×] ⟪ Q ⟫poly
  ⟪ approx P ⟫poly  = approx ⟪ P ⟫poly

⟪_⟫ctxt : ctxt → ctxt
⟪ emp ⟫ctxt = emp
⟪ Γ , τ ⟫ctxt = ⟪ Γ ⟫ctxt , approx ⟪ τ ⟫ty

⟪_⟫var : ∀ {Γ τ} → Γ ∋ τ → ⟪ Γ ⟫ctxt ∋ approx ⟪ τ ⟫ty
⟪ zero ⟫var = zero
⟪ succ x ⟫var = succ ⟪ x ⟫var

-- The type translation puts approx at every sum/product component, but
-- apply (a meta-level operation on syntactic types) doesn't see those
-- wraps when applied at the polynomial level. So ⟪apply P τ⟫ has extra
-- approx wraps compared to apply ⟪P⟫poly ⟪τ⟫. cbn-coerce builds a
-- target-language term that unwraps the approx at each sum/product
-- layer and rewraps once around the result.
cbn-coerce : (P : polynomial) → ∀ {Γ τ} →
             Γ ⊢ ⟪ apply P τ ⟫ty →
             Γ ⊢ approx (apply ⟪ P ⟫poly ⟪ τ ⟫ty)
cbn-coerce one         M = pure unit
cbn-coerce (const σ)   M = pure (pure M)
cbn-coerce var         M = pure M
cbn-coerce (P [+] Q) M =
  case M
    (bind (var zero) (bind (cbn-coerce P (var zero)) (pure (inl (var zero)))))
    (bind (var zero) (bind (cbn-coerce Q (var zero)) (pure (inr (var zero)))))
cbn-coerce (P [×] Q) M =
  bind (fst M) (
    bind (cbn-coerce P (var zero)) (
      bind (snd (weaken * (weaken * M))) (
        bind (cbn-coerce Q (var zero)) (
          pure (pair (var (succ (succ zero))) (var zero))))))
cbn-coerce (approx P) M = pure (bind M (cbn-coerce P (var zero)))

-- The other direction (used by fold-μ): from apply ⟪P⟫poly (approx ⟪τ⟫ty)
-- (target-side, with approx at var positions but no approx at sum/product
-- nodes) to approx ⟪apply P τ⟫ty (source-translation-side, with approx
-- at sum/product nodes). Aligns the algebra-argument type for fold-μ.
cbn-coerce' : (P : polynomial) → ∀ {Γ τ} →
              Γ ⊢ apply ⟪ P ⟫poly (approx ⟪ τ ⟫ty) →
              Γ ⊢ approx ⟪ apply P τ ⟫ty
cbn-coerce' one       M = pure M
cbn-coerce' (const σ) M = M
cbn-coerce' var       M = M
cbn-coerce' (P [+] Q) M =
  case M
    (pure (inl (cbn-coerce' P (var zero))))
    (pure (inr (cbn-coerce' Q (var zero))))
cbn-coerce' (P [×] Q) M =
  pure (pair (cbn-coerce' P (fst M)) (cbn-coerce' Q (snd M)))
cbn-coerce' (approx P) M = pure (bind M (cbn-coerce' P (var zero)))

mutual
  ⟪_⟫tm : ∀ {Γ τ} → Γ ⊢ τ → ⟪ Γ ⟫ctxt ⊢ approx ⟪ τ ⟫ty
  ⟪ var x ⟫tm = var ⟪ x ⟫var
  ⟪ unit ⟫tm = pure unit
  ⟪ true ⟫tm = pure true
  ⟪ false ⟫tm = pure false
  ⟪ if M then M₁ else M₂ ⟫tm =
    bind ⟪ M ⟫tm (if (var zero) then (weaken * ⟪ M₁ ⟫tm) else (weaken * ⟪ M₂ ⟫tm))
  ⟪ inl M ⟫tm = pure (inl ⟪ M ⟫tm)
  ⟪ inr M ⟫tm = pure (inr ⟪ M ⟫tm)
  ⟪ case M N₁ N₂ ⟫tm = bind ⟪ M ⟫tm (case (var zero) (ext weaken * ⟪ N₁ ⟫tm) (ext weaken * ⟪ N₂ ⟫tm))
  ⟪ pair M₁ M₂ ⟫tm = pure (pair ⟪ M₁ ⟫tm ⟪ M₂ ⟫tm)
  ⟪ fst M ⟫tm = bind ⟪ M ⟫tm (fst (var zero))
  ⟪ snd M ⟫tm = bind ⟪ M ⟫tm (snd (var zero))
  ⟪ lam M ⟫tm = pure (lam ⟪ M ⟫tm)
  ⟪ app M₁ M₂ ⟫tm = bind ⟪ M₁ ⟫tm (app (var zero) (weaken * ⟪ M₂ ⟫tm))
  ⟪ bop ω Ms ⟫tm = bindAll Ms (id-ren _) λ ρ Ms' → pure (bop ω Ms')
  ⟪ brel r Ms ⟫tm = bindAll Ms (id-ren _) λ ρ Ms' → pure (brel r Ms')
  ⟪ roll {P = P} M ⟫tm =
    bind ⟪ M ⟫tm (bind (cbn-coerce P (var zero)) (pure (roll (var zero))))
  ⟪ fold-μ {P = Q} {τ = τ} alg M ⟫tm =
    bind ⟪ alg ⟫tm (
      bind (weaken * ⟪ M ⟫tm) (
        fold-μ
          (lam (app (var (succ (succ zero))) (cbn-coerce' Q (var zero))))
          (var zero)))
  ⟪ pure M ⟫tm = pure ⟪ M ⟫tm
  ⟪ bind M N ⟫tm = bind ⟪ M ⟫tm ⟪ N ⟫tm

  bindAll : ∀ {Γ Γ' σs τ} →
            Every (λ σ → Γ ⊢ base σ) σs →
            Ren ⟪ Γ ⟫ctxt Γ' →
            (∀ {Γ''} → Ren Γ' Γ'' → Every (λ σ → Γ'' ⊢ base σ) σs → Γ'' ⊢ approx τ) →
            Γ' ⊢ approx τ
  bindAll [] ρ κ = κ (id-ren _) []
  bindAll (M ∷ Ms) ρ κ =
    bind (ρ * ⟪ M ⟫tm) (bindAll Ms (weaken ∘ren ρ) λ ρ' Ms' → κ (λ x → ρ' (succ x)) (var (ρ' zero) ∷ Ms'))
