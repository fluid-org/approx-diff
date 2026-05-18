{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Approx translation.
--
-- A translation that inserts the syntactic `approx` modality at the root
-- of every compound type former (sum, product, function, μ) and at labels.
-- Each type former gets one approximation slot at its root.
--
-- The design rationale comes from a Galois-slicing operational reading:
-- every value can be ⊥ at the top, and every eliminator has a bind-like
-- rule "eliminator ⊥ = ⊥". So the root `approx` is the "did this type
-- former commit?" slot — including for μ, where `unroll ⊥ = ⊥`.
--
-- Unlike Moggi's CBN translation (cbn-translation), which wraps every
-- component of every type former, this wraps once at the root: a pair
-- becomes approx (σ × τ) (one slot) rather than approx σ × approx τ
-- (per-component slots).
--
-- The polynomial body translation ⟪P⟫poly mirrors the type translation:
-- approx at sum/product/one roots, transparent at var/const. With this,
-- the equation
--     ⟪apply P τ⟫ty ≡ apply ⟪P⟫poly ⟪τ⟫ty
-- holds by structural induction (apply-coincides below).
--
-- For ⟪fold-μ⟫tm no bridge is needed: the algebra's argument type already
-- matches what target `fold-μ` expects (carrier substituted is the bare
-- result-type interpretation, which is what ⟪τ⟫ty already is).
------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; subst)
open import Data.List using (List; []; _∷_)
open import signature using (Signature)
open import every
import language-syntax

module approx-translation {ℓ} (Sig : Signature ℓ) where

open Signature Sig using (sort)
open language-syntax Sig

------------------------------------------------------------------------------
-- Type translation.

-- ⟪_⟫ty is the outer (approx-wrapped) form; ⟪_⟫ty-inner is what's under
-- the approx. The two-stage definition is *definitional* — Agda unfolds
-- ⟪τ⟫ty to approx ⟪τ⟫ty-inner unconditionally — which lets bind's
-- approx-shaped body typecheck against ⟪τ⟫ty results without needing
-- a per-call subst.
mutual
  ⟪_⟫ty : type → type
  ⟪ τ ⟫ty = approx ⟪ τ ⟫ty-inner

  ⟪_⟫ty-inner : type → type
  ⟪ unit ⟫ty-inner       = unit
  ⟪ bool ⟫ty-inner       = bool
  ⟪ base s ⟫ty-inner     = base s
  ⟪ τ₁ [×] τ₂ ⟫ty-inner  = ⟪ τ₁ ⟫ty [×] ⟪ τ₂ ⟫ty
  ⟪ τ₁ [+] τ₂ ⟫ty-inner  = ⟪ τ₁ ⟫ty [+] ⟪ τ₂ ⟫ty
  ⟪ τ₁ [→] τ₂ ⟫ty-inner  = ⟪ τ₁ ⟫ty [→] ⟪ τ₂ ⟫ty
  ⟪ μ P ⟫ty-inner        = μ ⟪ P ⟫poly
  ⟪ approx τ ⟫ty-inner   = ⟪ τ ⟫ty

  ⟪_⟫poly : polynomial → polynomial
  ⟪ one ⟫poly      = approx one
  ⟪ const σ ⟫poly  = const ⟪ σ ⟫ty
  ⟪ var ⟫poly      = var
  ⟪ P [+] Q ⟫poly    = approx (⟪ P ⟫poly [+] ⟪ Q ⟫poly)
  ⟪ P [×] Q ⟫poly    = approx (⟪ P ⟫poly [×] ⟪ Q ⟫poly)
  ⟪ approx P ⟫poly = approx ⟪ P ⟫poly

⟪_⟫ctxt : ctxt → ctxt
⟪ emp ⟫ctxt = emp
⟪ Γ , τ ⟫ctxt = ⟪ Γ ⟫ctxt , ⟪ τ ⟫ty

⟪_⟫var : ∀ {Γ τ} → Γ ∋ τ → ⟪ Γ ⟫ctxt ∋ ⟪ τ ⟫ty
⟪ zero ⟫var = zero
⟪ succ x ⟫var = succ ⟪ x ⟫var

-- Syntactic application of a translated polynomial agrees with the
-- type translation of the source-level application.
apply-coincides : ∀ Q τ → ⟪ apply Q τ ⟫ty ≡ apply ⟪ Q ⟫poly ⟪ τ ⟫ty
apply-coincides one       τ = refl
apply-coincides (const σ) τ = refl
apply-coincides var       τ = refl
apply-coincides (P [+] Q)   τ = cong approx (cong₂ _[+]_ (apply-coincides P τ) (apply-coincides Q τ))
apply-coincides (P [×] Q)   τ = cong approx (cong₂ _[×]_ (apply-coincides P τ) (apply-coincides Q τ))
apply-coincides (approx Q) τ = cong approx (apply-coincides Q τ)

------------------------------------------------------------------------------
-- Term translation.

-- Distributive law to lift inner approx to the outer level.
sequence-poly : (P : polynomial) → ∀ {Γ τ} → Γ ⊢ apply ⟪ P ⟫poly (approx τ) → Γ ⊢ approx (apply ⟪ P ⟫poly τ)
sequence-poly one         M = pure M
sequence-poly (const σ)   M = pure M
sequence-poly var         M = M
sequence-poly (P [+] Q)     M =
  pure (bind M (case (var zero)
    (bind (sequence-poly P (var zero)) (pure (inl (var zero))))
    (bind (sequence-poly Q (var zero)) (pure (inr (var zero))))))
sequence-poly (P [×] Q)     M =
  pure (bind M
    (bind (sequence-poly P (fst (var zero)))
      (bind (sequence-poly Q (snd (var (succ zero))))
        (pure (pair (var (succ zero)) (var zero))))))
sequence-poly (approx P)  M = pure (bind M (sequence-poly P (var zero)))

mutual
  ⟪_⟫tm : ∀ {Γ τ} → Γ ⊢ τ → ⟪ Γ ⟫ctxt ⊢ ⟪ τ ⟫ty
  ⟪ var x ⟫tm = var ⟪ x ⟫var
  ⟪ unit ⟫tm = pure unit
  ⟪ true ⟫tm = pure true
  ⟪ false ⟫tm = pure false
  ⟪ if M then M₁ else M₂ ⟫tm =
    bind ⟪ M ⟫tm (if (var zero) then (weaken * ⟪ M₁ ⟫tm) else (weaken * ⟪ M₂ ⟫tm))
  ⟪ inl M ⟫tm = pure (inl ⟪ M ⟫tm)
  ⟪ inr M ⟫tm = pure (inr ⟪ M ⟫tm)
  ⟪ case M N₁ N₂ ⟫tm =
    bind ⟪ M ⟫tm (case (var zero) (ext weaken * ⟪ N₁ ⟫tm) (ext weaken * ⟪ N₂ ⟫tm))
  ⟪ pair M N ⟫tm = pure (pair ⟪ M ⟫tm ⟪ N ⟫tm)
  ⟪ fst M ⟫tm = bind ⟪ M ⟫tm (fst (var zero))
  ⟪ snd M ⟫tm = bind ⟪ M ⟫tm (snd (var zero))
  ⟪ lam M ⟫tm = pure (lam ⟪ M ⟫tm)
  ⟪ app M N ⟫tm = bind ⟪ M ⟫tm (app (var zero) (weaken * ⟪ N ⟫tm))
  ⟪ bop ω Ms ⟫tm = bindAll Ms (id-ren _) (λ ρ Ms' → pure (bop ω Ms'))
  ⟪ brel ω Ms ⟫tm = bindAll Ms (id-ren _) (λ ρ Ms' → pure (brel ω Ms'))
  ⟪ roll {Γ = Γ} {P = P} M ⟫tm =
    bind (sequence-poly P (subst (λ A → ⟪ Γ ⟫ctxt ⊢ A) (apply-coincides P (μ P)) ⟪ M ⟫tm))
         (pure (roll (var zero)))
  ⟪ fold-μ {P = Q} {τ = τ} alg M ⟫tm =
    bind ⟪ alg ⟫tm
         (bind (weaken * ⟪ M ⟫tm) (fold-μ {P = ⟪ Q ⟫poly} (cast-alg Q τ (var (succ zero))) (var zero)))
    where
      cast-alg : ∀ Q τ {Γ'} → Γ' ⊢ ⟪ apply Q τ ⟫ty [→] ⟪ τ ⟫ty → Γ' ⊢ apply ⟪ Q ⟫poly ⟪ τ ⟫ty [→] ⟪ τ ⟫ty
      cast-alg Q τ {Γ'} f = subst (λ A → Γ' ⊢ A [→] ⟪ τ ⟫ty) (apply-coincides Q τ) f
  ⟪ pure M ⟫tm = pure ⟪ M ⟫tm
  ⟪ bind M N ⟫tm = bind ⟪ M ⟫tm ⟪ N ⟫tm

  bindAll : ∀ {Γ Γ' σs τ} → Every (λ σ → Γ ⊢ base σ) σs → Ren ⟪ Γ ⟫ctxt Γ' →
            (∀ {Γ''} → Ren Γ' Γ'' → Every (λ σ → Γ'' ⊢ base σ) σs → Γ'' ⊢ approx τ) → Γ' ⊢ approx τ
  bindAll [] ρ κ = κ (id-ren _) []
  bindAll (M ∷ Ms) ρ κ =
    bind (ρ * ⟪ M ⟫tm)
         (bindAll Ms (weaken ∘ren ρ) (λ ρ' Ms' → κ (λ x → ρ' (succ x)) (var (ρ' zero) ∷ Ms')))
