{-# OPTIONS --prop --postfix-projections --safe #-}

module example where

open import Level using (0ℓ; lift; _⊔_)
open import Data.List using (List; []; _∷_)
open import every using (Every; []; _∷_)
open import signature
open import categories using (Category; HasTerminal; HasProducts)
open import functor using (Functor; StrongPointedFunctor)
import language-syntax
import label

open import example-signature

module L = language-syntax Sig

------------------------------------------------------------------------------
-- Writer-style F X = A × X, but with unit (no bind) and a retraction.

module Tag
  {o m e} (𝒞 : Category o m e)
  (T : HasTerminal 𝒞) (P : HasProducts 𝒞)
  (A : Category.obj 𝒞)
  (⊤ : Category._⇒_ 𝒞 (HasTerminal.witness T) A)
  where

  open Category 𝒞
  open HasTerminal T
  open HasProducts P
  open Functor
  open import prop-setoid using (module ≈-Reasoning; IsEquivalence)
  open IsEquivalence

  Tag-F : Functor 𝒞 𝒞
  Tag-F .fobj x = prod A x
  Tag-F .fmor f = prod-m (id _) f
  Tag-F .fmor-cong eq = prod-m-cong ≈-refl eq
  Tag-F .fmor-id = prod-m-id
  Tag-F .fmor-comp f g =
    ≈-trans (prod-m-cong (≈-sym id-left) ≈-refl) (pair-functorial _ _ _ _)

  Tag-StrongPointedFunctor : StrongPointedFunctor P
  Tag-StrongPointedFunctor .StrongPointedFunctor.F              = Tag-F
  Tag-StrongPointedFunctor .StrongPointedFunctor.unit {x}       = pair (⊤ ∘ to-terminal) (id _)
  -- Right-strength: x × (A × y) ⇒ A × (x × y). Tag (in second slot) moves to outside.
  Tag-StrongPointedFunctor .StrongPointedFunctor.right-strength = pair (p₁ ∘ p₂) (pair p₁ (p₂ ∘ p₂))
  -- Naturality: both sides reduce to pair (p₁ ∘ p₂) (pair (f ∘ p₁) (g ∘ (p₂ ∘ p₂))).
  -- LHS direction filled; RHS-to-mid direction left as a hole (would mirror LHS
  -- via pair-natural + pair-cong unfolding the inner composites).
  Tag-StrongPointedFunctor .StrongPointedFunctor.right-strength-natural f g =
    begin
      prod-m (id A) (prod-m f g) ∘ pair (p₁ ∘ p₂) (pair p₁ (p₂ ∘ p₂))
    ≈⟨ pair-compose _ _ _ _ ⟩
      pair (id A ∘ (p₁ ∘ p₂)) (prod-m f g ∘ pair p₁ (p₂ ∘ p₂))
    ≈⟨ pair-cong id-left (pair-compose _ _ _ _) ⟩
      pair (p₁ ∘ p₂) (pair (f ∘ p₁) (g ∘ (p₂ ∘ p₂)))
    ≈⟨ {!!} ⟩
      pair (p₁ ∘ p₂) (pair p₁ (p₂ ∘ p₂)) ∘ prod-m f (prod-m (id A) g)
    ∎
    where open ≈-Reasoning isEquiv

------------------------------------------------------------------------------
-- Tag StrongPointedFunctor on galois.cat, using galois.TWO as the approximation object.

module _ where
  import galois
  Tag-galois : StrongPointedFunctor galois.products
  Tag-galois = Tag.Tag-StrongPointedFunctor galois.cat galois.terminal galois.products galois.TWO galois.unit

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
  open SynMonad

  -- Writer monad over the approximation sort: pairs values with an
  -- approximation tag. Tag-bind multiplies the two tags via approx-mult.
  Tag : type → type
  Tag τ = base approx [×] τ

  Tag-pure : ∀ {Γ τ} → Γ ⊢ τ [→] Tag τ
  Tag-pure = lam (pair (bop approx-unit []) (var zero))

  Tag-bind : ∀ {Γ σ τ} → Γ ⊢ Tag σ [→] (σ [→] Tag τ) [→] Tag τ
  Tag-bind =
    lam (lam (pair (bop approx-mult (fst (var (succ zero)) ∷ fst (app (var zero) (snd (var (succ zero)))) ∷ []))
                   (snd (app (var zero) (snd (var (succ zero)))))))

  Tag-monad : SynMonad
  Tag-monad .Mon = Tag
  Tag-monad .pure = Tag-pure
  Tag-monad .bind = Tag-bind

  `_ : ∀ {Γ} → label.label → Γ ⊢ base label
  ` l = bop (lbl l) []

  _≟_ : ∀ {Γ} → Γ ⊢ base label → Γ ⊢ base label → Γ ⊢ bool
  M ≟ N = brel equal-label (M ∷ N ∷ [])

  -- Summation function, μ-types version (uses list).
  sum : ∀ {Γ} → Γ ⊢ list (base number) [→] base number
  sum = lam (fold (bop zero []) (bop add (var zero ∷ var (succ zero) ∷ [])) (var zero))

  -- Whther some element of the list equals the given label. CBV semantics evaluates the predicate at every
  -- element, but backward demand "short- circuits": at the first matching element, the remaining list becomes
  -- ⊥-demanded.
  some-eq : ∀ {Γ} → Γ ⊢ base label [→] list (base label) [→] bool
  some-eq = lam (lam
    (fold false
      (if (brel equal-label (var (succ zero) ∷ var (succ (succ (succ zero))) ∷ []))
       then true else (var zero))
      (var zero)))

  query : label.label → emp , list (base label [×] base number) ⊢ base number
  query l =
    app sum
      (from var zero collect
      when fst (var zero) ≟ (` l) ；
      return (snd (var zero)))

  -- Instantiate our two translations with our two example approximation monads.
  module cbn-Tag where
    open import cbn-translation Sig Tag-monad

    cbn-query : label.label → emp , Tag (list (Tag (Tag (base label) [×] Tag (base number)))) ⊢ Tag (base number)
    cbn-query l = ⟪ query l ⟫tm

  module approx-Tag where
    open import approx-translation Sig Tag-monad

    approx-query : label.label → ⟪ emp , list (base label [×] base number) ⟫ctxt ⊢ ⟪ base number ⟫ty
    approx-query l = ⟪ query l ⟫tm
