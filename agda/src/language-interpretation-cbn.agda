{-# OPTIONS --prop --postfix-projections --safe #-}

-- Per-leaf CBN interpretation: every component of a compound type former
-- carries an explicit Mon-wrap; the outer type is not Mon-wrapped. Each
-- term produces an M-wrapped value (since values in CBN are suspended).
-- Contrast with language-interpretation-approx's per-root scheme.

open import Level using (_⊔_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; subst; trans)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasExponentials;
         HasBooleans; coproducts+exp→booleans)
open import functor using (Functor; PointedFunctor)
open import polynomial-functor using (μPoly; module Sem)
import language-syntax
open import signature using (Signature; Model; PFPC[_,_,_,_]; PointedFPCat)
open import every using (Every; []; _∷_)

module language-interpretation-cbn
  {ℓ} (Sig : Signature ℓ)
  {o m e}
  (𝒞 : Category o m e)
  (T  : HasTerminal 𝒞)
  (P  : HasProducts 𝒞)
  (C  : HasCoproducts 𝒞)
  (E  : HasExponentials 𝒞 P)
  (let open Sem T P C)
  (let open HasBooleans (coproducts+exp→booleans T C E))
  (PM : PointedFunctor)
  (let open μPoly-Sem (PointedFunctor.F PM))
  -- Strength: lets us pass a side context under the F-wrap without losing
  -- F-structure (whereas `force` would discard it). Required for fmor-style
  -- traversal in map-eval at Mon nodes.
  (strength : ∀ {x y} → Category._⇒_ 𝒞 (HasProducts.prod P (PointedFunctor.F PM .Functor.fobj x) y)
                                       (PointedFunctor.F PM .Functor.fobj (HasProducts.prod P x y)))
  (Mu : HasMu-μPoly)
  (Int : Model PFPC[ 𝒞 , T , P , Bool ] Sig)
  where

open HasExponentials E renaming (exp to _⟦→⟧_)
open PointedFPCat PFPC[ 𝒞 , T , P , Bool ] renaming (_×_ to _⊗_)
open HasCoproducts C renaming (coprod to _⊕_)
open language-syntax Sig
open Model Int
open PointedFunctor PM renaming (unit to η)

M : obj → obj
M X = fobj X

mutual
  -- Per-leaf: components are Mon-wrapped, the compound type-former itself is not.
  ⟦_⟧ty : type → obj
  ⟦ unit ⟧ty       = 𝟙
  ⟦ bool ⟧ty       = Bool
  ⟦ base σ ⟧ty     = ⟦sort⟧ σ
  ⟦ τ₁ [×] τ₂ ⟧ty  = M ⟦ τ₁ ⟧ty ⊗ M ⟦ τ₂ ⟧ty
  ⟦ τ₁ [+] τ₂ ⟧ty  = M ⟦ τ₁ ⟧ty ⊕ M ⟦ τ₂ ⟧ty
  ⟦ τ₁ [→] τ₂ ⟧ty  = M ⟦ τ₁ ⟧ty ⟦→⟧ M ⟦ τ₂ ⟧ty
  ⟦ μ P ⟧ty        = HasMu-μPoly.μ Mu ⟦ P ⟧poly

  -- Mon inside each side of sum/product; const/var unwrapped. Matches per-leaf
  -- type translation so apply-coincides holds at ⟦τ⟧ty without coercion.
  ⟦_⟧poly : polynomial → μPoly 𝒞
  ⟦ one ⟧poly       = μPoly.one
  ⟦ const σ ⟧poly   = μPoly.const ⟦ σ ⟧ty
  ⟦ var ⟧poly       = μPoly.var
  ⟦ P [+] Q ⟧poly   = (μPoly.Mon ⟦ P ⟧poly) μPoly.+ (μPoly.Mon ⟦ Q ⟧poly)
  ⟦ P [×] Q ⟧poly   = (μPoly.Mon ⟦ P ⟧poly) μPoly.× (μPoly.Mon ⟦ Q ⟧poly)

-- Every binding in the context stores an M-wrapped value.
⟦_⟧ctxt : ctxt → obj
⟦ emp ⟧ctxt   = 𝟙
⟦ Γ , τ ⟧ctxt = ⟦ Γ ⟧ctxt ⊗ M ⟦ τ ⟧ty

apply-coincides : ∀ Q τ → ⟦ apply Q τ ⟧ty ≡ μPoly-obj ⟦ Q ⟧poly ⟦ τ ⟧ty
apply-coincides one          τ = refl
apply-coincides (const σ)    τ = refl
apply-coincides var          τ = refl
apply-coincides (P [+] Q)    τ = cong₂ _⊕_ (cong M (apply-coincides P τ)) (cong M (apply-coincides Q τ))
apply-coincides (P [×] Q)    τ = cong₂ _⊗_ (cong M (apply-coincides P τ)) (cong M (apply-coincides Q τ))

-- map-eval evaluates a polynomial-of-closures over an input context to produce
-- a polynomial of values. Defined per μPoly constructor.
map-eval : (Q : μPoly 𝒞) {ctx t : obj} → (μPoly-obj Q (ctx ⟦→⟧ t) ⊗ ctx) ⇒ μPoly-obj Q t
map-eval μPoly.one         = to-terminal
map-eval (μPoly.const _)   = p₁
map-eval μPoly.var         = eval
map-eval (P μPoly.+ Q)     = eval ∘ ⟨ copair (lambda (in₁ ∘ map-eval P)) (lambda (in₂ ∘ map-eval Q)) ∘ p₁ , p₂ ⟩
map-eval (P μPoly.× Q)     = ⟨ map-eval P ∘ ⟨ p₁ ∘ p₁ , p₂ ⟩ , map-eval Q ∘ ⟨ p₂ ∘ p₁ , p₂ ⟩ ⟩
map-eval (μPoly.Mon P)     = fmor (map-eval P) ∘ strength

-- Variable lookup gives back an M-wrapped value (stored that way in the context).
⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ M ⟦ τ ⟧ty
⟦ zero ⟧var = p₂
⟦ succ x ⟧var = ⟦ x ⟧var ∘ p₁

mutual
  -- All terms produce an M-wrapped value.
  ⟦_⟧tm : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ctxt ⇒ M ⟦ τ ⟧ty
  ⟦ var x ⟧tm = ⟦ x ⟧var
  ⟦ unit ⟧tm = η ∘ to-terminal
  ⟦ true ⟧tm = η ∘ True ∘ to-terminal
  ⟦ false ⟧tm = η ∘ False ∘ to-terminal
  ⟦ if M then M₁ else M₂ ⟧tm = cond ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm ∘ ⟨ id _ , force ∘ ⟦ M ⟧tm ⟩
  ⟦ inl M ⟧tm = η ∘ in₁ ∘ ⟦ M ⟧tm
  ⟦ inr M ⟧tm = η ∘ in₂ ∘ ⟦ M ⟧tm
  ⟦ case M M₁ M₂ ⟧tm =
    eval ∘ ⟨ copair (lambda (⟦ M₁ ⟧tm ∘ ⟨ p₂ , p₁ ⟩)) (lambda (⟦ M₂ ⟧tm ∘ ⟨ p₂ , p₁ ⟩)) ∘ force ∘ ⟦ M ⟧tm , id _ ⟩
  ⟦ pair M N ⟧tm = η ∘ ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ fst M ⟧tm = p₁ ∘ force ∘ ⟦ M ⟧tm
  ⟦ snd M ⟧tm = p₂ ∘ force ∘ ⟦ M ⟧tm
  ⟦ lam M ⟧tm = η ∘ lambda ⟦ M ⟧tm
  ⟦ app M N ⟧tm = eval ∘ ⟨ force ∘ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ bop ω Ms ⟧tm = η ∘ ⟦op⟧ ω ∘ ⟦ Ms ⟧tms
  ⟦ brel ω Ms ⟧tm = η ∘ ⟦rel⟧ ω ∘ ⟦ Ms ⟧tms
  ⟦ roll {Γ = Γ} {P = P} t ⟧tm =
    η ∘ HasMu-μPoly.inμ Mu ⟦ P ⟧poly ∘ force ∘
      subst (⟦ Γ ⟧ctxt ⇒_) (cong M (apply-coincides P (μ P))) ⟦ t ⟧tm
  ⟦ fold-μ {Γ = Γ} {P = Q} {τ = τ} alg M ⟧tm =
    η ∘ eval ∘ ⟨ HasMu-μPoly.⦅_⦆ Mu closure-converted ∘ force ∘ ⟦ M ⟧tm , id _ ⟩
    where
      -- y = ⟦Γ⟧ ⟦→⟧ ⟦τ⟧ty (no outer Mon). The closure's body forces the alg's
      -- M-wrapped result, matching the way cbn-translation binds it out.
      closure-converted : μPoly-obj ⟦ Q ⟧poly (⟦ Γ ⟧ctxt ⟦→⟧ ⟦ τ ⟧ty) ⇒ (⟦ Γ ⟧ctxt ⟦→⟧ ⟦ τ ⟧ty)
      closure-converted = lambda (force ∘ eval ∘ ⟨
        force ∘ ⟦ alg ⟧tm ∘ p₂ ,
          η ∘ subst (λ X → (μPoly-obj ⟦ Q ⟧poly (⟦ Γ ⟧ctxt ⟦→⟧ ⟦ τ ⟧ty) ⊗ ⟦ Γ ⟧ctxt) ⇒ X)
                    (sym (apply-coincides Q τ)) (map-eval ⟦ Q ⟧poly)
        ⟩)

  -- Base-typed args need to be unwrapped before being passed to the operation;
  -- ⟦op⟧ / ⟦rel⟧ live at the underlying sort level.
  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ force ∘ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
