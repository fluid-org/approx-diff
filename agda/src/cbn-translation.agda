{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.List using (List; []; _∷_)
open import signature using (Signature)
open import every
import language-syntax

module cbn-translation {ℓ} (Sig : Signature ℓ) (M : language-syntax.SynMonad Sig) where

open Signature Sig using (sort)
open language-syntax Sig
open SynMonad M

mutual
  ⟪_⟫ty : type → type
  ⟪ unit ⟫ty = unit
  ⟪ bool ⟫ty = bool
  ⟪ base s ⟫ty = base s
  ⟪ τ₁ [×] τ₂ ⟫ty = Mon ⟪ τ₁ ⟫ty [×] Mon ⟪ τ₂ ⟫ty
  ⟪ τ₁ [+] τ₂ ⟫ty = Mon ⟪ τ₁ ⟫ty [+] Mon ⟪ τ₂ ⟫ty
  ⟪ τ₁ [→] τ₂ ⟫ty = (Mon ⟪ τ₁ ⟫ty) [→] (Mon ⟪ τ₂ ⟫ty)
  ⟪ μ P ⟫ty = μ ⟪ P ⟫poly

  ⟪_⟫poly : polynomial → polynomial
  ⟪ one ⟫poly       = one
  ⟪ const σ ⟫poly   = const (Mon ⟪ σ ⟫ty)
  ⟪ var ⟫poly       = var
  ⟪ P₁ +ᵖ P₂ ⟫poly      = ⟪ P₁ ⟫poly +ᵖ ⟪ P₂ ⟫poly
  ⟪ P₁ ×ᵖ P₂ ⟫poly      = ⟪ P₁ ⟫poly ×ᵖ ⟪ P₂ ⟫poly

⟪_⟫ctxt : ctxt → ctxt
⟪ emp ⟫ctxt = emp
⟪ Γ , τ ⟫ctxt = ⟪ Γ ⟫ctxt , Mon ⟪ τ ⟫ty

⟪_⟫var : ∀ {Γ τ} → Γ ∋ τ → ⟪ Γ ⟫ctxt ∋ Mon ⟪ τ ⟫ty
⟪ zero ⟫var = zero
⟪ succ x ⟫var = succ ⟪ x ⟫var

_$_ : ∀ {Γ σ τ} → Γ ⊢ σ [→] τ → Γ ⊢ σ → Γ ⊢ τ
_$_ = app

infixl 10 _$_

-- The type translation Mon-wraps at every sum/product, but apply (a
-- meta-level operation on syntactic types) doesn't see the wraps when
-- applied at the polynomial level. So ⟪apply P τ⟫ has extra Mon-wraps
-- compared to apply ⟪P⟫poly ⟪τ⟫. cbn-coerce builds a target-language
-- term that unwraps the Mon at each sum/product layer and rewraps once
-- around the result.
cbn-coerce : (P : polynomial) → ∀ {Γ τ} →
             Γ ⊢ ⟪ apply P τ ⟫ty →
             Γ ⊢ Mon (apply ⟪ P ⟫poly ⟪ τ ⟫ty)
cbn-coerce one         M = pure $ unit
cbn-coerce (const σ)   M = pure $ (pure $ M)
cbn-coerce var         M = pure $ M
cbn-coerce (P₁ +ᵖ P₂) M =
  case M
    (bind $ var zero $ lam (bind $ cbn-coerce P₁ (var zero) $ lam (pure $ inl (var zero))))
    (bind $ var zero $ lam (bind $ cbn-coerce P₂ (var zero) $ lam (pure $ inr (var zero))))
cbn-coerce (P₁ ×ᵖ P₂) M =
  bind $ fst M $ lam (
    bind $ cbn-coerce P₁ (var zero) $ lam (
      bind $ snd (weaken * (weaken * M)) $ lam (
        bind $ cbn-coerce P₂ (var zero) $ lam (
          pure $ pair (var (succ (succ zero))) (var zero)))))

-- The other direction (used by fold-μ): from apply ⟪P⟫poly (Mon ⟪τ⟫ty)
-- (target-side, with Mon at var positions but no Mon at sum/product
-- nodes) to Mon ⟪apply P τ⟫ty (source-translation-side, with Mon at
-- sum/product nodes). Aligns the algebra-argument type for fold-μ.
cbn-coerce' : (P : polynomial) → ∀ {Γ τ} →
              Γ ⊢ apply ⟪ P ⟫poly (Mon ⟪ τ ⟫ty) →
              Γ ⊢ Mon ⟪ apply P τ ⟫ty
cbn-coerce' one       M = pure $ M
cbn-coerce' (const σ) M = M
cbn-coerce' var       M = M
cbn-coerce' (P₁ +ᵖ P₂) M =
  case M
    (pure $ inl (cbn-coerce' P₁ (var zero)))
    (pure $ inr (cbn-coerce' P₂ (var zero)))
cbn-coerce' (P₁ ×ᵖ P₂) M =
  pure $ pair (cbn-coerce' P₁ (fst M)) (cbn-coerce' P₂ (snd M))

mutual
  ⟪_⟫tm : ∀ {Γ τ} → Γ ⊢ τ → ⟪ Γ ⟫ctxt ⊢ Mon ⟪ τ ⟫ty
  ⟪ var x ⟫tm = var ⟪ x ⟫var
  ⟪ unit ⟫tm = pure $ unit
  ⟪ true ⟫tm = pure $ true
  ⟪ false ⟫tm = pure $ false
  ⟪ if M then M₁ else M₂ ⟫tm =
    bind $ ⟪ M ⟫tm $ lam (if (var zero) then (weaken * ⟪ M₁ ⟫tm) else (weaken * ⟪ M₂ ⟫tm))
  ⟪ inl M ⟫tm = pure $ inl ⟪ M ⟫tm
  ⟪ inr M ⟫tm = pure $ inr ⟪ M ⟫tm
  ⟪ case M N₁ N₂ ⟫tm = bind $ ⟪ M ⟫tm $ lam (case (var zero) (ext weaken * ⟪ N₁ ⟫tm) (ext weaken * ⟪ N₂ ⟫tm))
  ⟪ pair M₁ M₂ ⟫tm = pure $ pair ⟪ M₁ ⟫tm ⟪ M₂ ⟫tm
  ⟪ fst M ⟫tm = bind $ ⟪ M ⟫tm $ lam (fst (var zero))
  ⟪ snd M ⟫tm = bind $ ⟪ M ⟫tm $ lam (snd (var zero))
  ⟪ lam M ⟫tm = pure $ lam ⟪ M ⟫tm
  ⟪ app M₁ M₂ ⟫tm = bind $ ⟪ M₁ ⟫tm $ lam ((var zero) $ (weaken * ⟪ M₂ ⟫tm))
  ⟪ bop ω Ms ⟫tm = bindAll Ms (id-ren _) λ ρ Ms' → pure $ bop ω Ms'
  ⟪ brel r Ms ⟫tm = bindAll Ms (id-ren _) λ ρ Ms' → pure $ brel r Ms'
  ⟪ roll {P = P} M ⟫tm =
    bind $ ⟪ M ⟫tm $ lam (bind $ cbn-coerce P (var zero) $ lam (pure $ roll (var zero)))
  ⟪ fold-μ {P = Q} {τ = τ} alg M ⟫tm =
    bind $ ⟪ alg ⟫tm $ lam (
      bind $ (weaken * ⟪ M ⟫tm) $ lam (
        fold-μ
          (lam (app (var (succ (succ zero))) (cbn-coerce' Q (var zero))))
          (var zero)))

  bindAll : ∀ {Γ Γ' σs τ} →
            Every (λ σ → Γ ⊢ base σ) σs →
            Ren ⟪ Γ ⟫ctxt Γ' →
            (∀ {Γ''} → Ren Γ' Γ'' → Every (λ σ → Γ'' ⊢ base σ) σs → Γ'' ⊢ Mon τ) →
            Γ' ⊢ Mon τ
  bindAll [] ρ κ = κ (id-ren _) []
  bindAll (M ∷ Ms) ρ κ =
    bind $ (ρ * ⟪ M ⟫tm) $ lam (bindAll Ms (weaken ∘ren ρ) λ ρ' Ms' → κ (λ x → ρ' (succ x)) (var (ρ' zero) ∷ Ms'))
