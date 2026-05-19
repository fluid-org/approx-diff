{-# OPTIONS --prop --postfix-projections --safe #-}

-- Moggi-style monadic interpretation, parameterised on a strong monad SM.
-- Term interpretation lands in Γ ⇒ M ⟦τ⟧ty; type interpretation puts M at
-- function results. With SM = id-strong-monad, M reduces to the identity
-- functor so the interpretation should agree (extensionally) with the
-- direct interpretation in language-interpretation.agda.

open import Level using (_⊔_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; subst)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasExponentials;
         HasBooleans; coproducts+exp→booleans; StrongMonad)
open import polynomial-functor using (Poly; module Sem)
import language-syntax
open import signature using (Signature; Model; PFPC[_,_,_,_]; PointedFPCat)
open import every using (Every; []; _∷_)

module language-interpretation-moggi
  {ℓ} (Sig : Signature ℓ)
  {o m e}
  (𝒞 : Category o m e)
  (T  : HasTerminal 𝒞)
  (P  : HasProducts 𝒞)
  (C  : HasCoproducts 𝒞)
  (E  : HasExponentials 𝒞 P)
  (Mu : Sem.HasMu T P C)
  (SM : StrongMonad 𝒞 P)
  (Int : Model PFPC[ 𝒞 , T , P , HasBooleans.Bool (coproducts+exp→booleans T C E) ] Sig)
  where

B : HasBooleans 𝒞 T P
B = coproducts+exp→booleans T C E

open HasExponentials E renaming (exp to _⟦→⟧_)
open PointedFPCat PFPC[ 𝒞 , T , P , HasBooleans.Bool B ] renaming (_×_ to _⊗_)
open HasCoproducts C renaming (coprod to _⊕_)
open HasBooleans B
open language-syntax Sig
open Model Int
open Sem T P C
open StrongMonad SM renaming (unit to η; M to Mon)

mutual
  ⟦_⟧ty : type → obj
  ⟦ unit ⟧ty = 𝟙
  ⟦ bool ⟧ty = Bool
  ⟦ base σ ⟧ty = ⟦sort⟧ σ
  ⟦ τ₁ [×] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⊗ ⟦ τ₂ ⟧ty
  ⟦ τ₁ [→] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⟦→⟧ Mon ⟦ τ₂ ⟧ty
  ⟦ τ₁ [+] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⊕ ⟦ τ₂ ⟧ty
  ⟦ μ P ⟧ty = HasMu.μ Mu ⟦ P ⟧poly
  ⟦ approx τ ⟧ty = Mon ⟦ τ ⟧ty

  ⟦_⟧poly : polynomial → Poly 𝒞
  ⟦ one ⟧poly       = Poly.one
  ⟦ const σ ⟧poly   = Poly.const ⟦ σ ⟧ty
  ⟦ var ⟧poly       = Poly.var
  ⟦ P [+] Q ⟧poly   = ⟦ P ⟧poly Poly.+ ⟦ Q ⟧poly
  ⟦ P [×] Q ⟧poly   = ⟦ P ⟧poly Poly.× ⟦ Q ⟧poly

⟦_⟧ctxt : ctxt → obj
⟦ emp ⟧ctxt = 𝟙
⟦ Γ , τ ⟧ctxt = ⟦ Γ ⟧ctxt ⊗ ⟦ τ ⟧ty

apply-coincides : ∀ Q τ → ⟦ apply Q τ ⟧ty ≡ poly-obj ⟦ Q ⟧poly ⟦ τ ⟧ty
apply-coincides one          τ = refl
apply-coincides (const σ)    τ = refl
apply-coincides var          τ = refl
apply-coincides (P [+] Q)    τ = cong₂ _⊕_ (apply-coincides P τ) (apply-coincides Q τ)
apply-coincides (P [×] Q)    τ = cong₂ _⊗_ (apply-coincides P τ) (apply-coincides Q τ)

map-eval : (Q : Poly 𝒞) {ctx t : obj} → (poly-obj Q (ctx ⟦→⟧ t) ⊗ ctx) ⇒ poly-obj Q t
map-eval Poly.one       = to-terminal
map-eval (Poly.const _) = p₁
map-eval Poly.var       = eval
map-eval (P Poly.+ Q) = eval ∘ ⟨ copair (lambda (in₁ ∘ map-eval P)) (lambda (in₂ ∘ map-eval Q)) ∘ p₁ , p₂ ⟩
map-eval (P Poly.× Q) = ⟨ map-eval P ∘ ⟨ p₁ ∘ p₁ , p₂ ⟩ , map-eval Q ∘ ⟨ p₂ ∘ p₁ , p₂ ⟩ ⟩

⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
⟦ zero ⟧var = p₂
⟦ succ x ⟧var = ⟦ x ⟧var ∘ p₁

swap : ∀ {x y} → (x ⊗ y) ⇒ (y ⊗ x)
swap = ⟨ p₂ , p₁ ⟩

-- Kleisli bind in Γ × X context: bind a Γ ⇒ Mon X with a Γ × X ⇒ Mon Y body.
bind : ∀ {Γ x y} → Γ ⇒ Mon x → (Γ ⊗ x) ⇒ Mon y → Γ ⇒ Mon y
bind f k = extend k ∘ ⟨ id _ , f ⟩

mutual
  ⟦_⟧tm : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ctxt ⇒ Mon ⟦ τ ⟧ty
  ⟦ var x ⟧tm = η ∘ ⟦ x ⟧var
  ⟦ unit ⟧tm = η ∘ to-terminal
  ⟦ true ⟧tm = η ∘ True ∘ to-terminal
  ⟦ false ⟧tm = η ∘ False ∘ to-terminal
  ⟦ if M then M₁ else M₂ ⟧tm = bind ⟦ M ⟧tm (cond ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm)
  ⟦ inl M ⟧tm = bind ⟦ M ⟧tm (η ∘ in₁ ∘ p₂)
  ⟦ inr M ⟧tm = bind ⟦ M ⟧tm (η ∘ in₂ ∘ p₂)
  ⟦ case M M₁ M₂ ⟧tm =
    bind ⟦ M ⟧tm (eval ∘ ⟨ copair (lambda (⟦ M₁ ⟧tm ∘ swap)) (lambda (⟦ M₂ ⟧tm ∘ swap)) ∘ p₂ , p₁ ⟩)
  ⟦ pair M N ⟧tm =
    bind ⟦ M ⟧tm (bind (⟦ N ⟧tm ∘ p₁) (η ∘ ⟨ p₂ ∘ p₁ , p₂ ⟩))
  ⟦ fst M ⟧tm = bind ⟦ M ⟧tm (η ∘ p₁ ∘ p₂)
  ⟦ snd M ⟧tm = bind ⟦ M ⟧tm (η ∘ p₂ ∘ p₂)
  ⟦ lam M ⟧tm = η ∘ lambda ⟦ M ⟧tm
  ⟦ app M N ⟧tm =
    bind ⟦ M ⟧tm (bind (⟦ N ⟧tm ∘ p₁) (eval ∘ ⟨ p₂ ∘ p₁ , p₂ ⟩))
  ⟦ bop ω Ms ⟧tm = bind ⟦ Ms ⟧tms (η ∘ ⟦op⟧ ω ∘ p₂)
  ⟦ brel ω Ms ⟧tm = bind ⟦ Ms ⟧tms (η ∘ ⟦rel⟧ ω ∘ p₂)
  ⟦ roll {Γ = Γ} {P = P} M ⟧tm =
    bind ⟦ M ⟧tm
         (η ∘ HasMu.inF Mu ⟦ P ⟧poly
            ∘ subst (λ X → (⟦ Γ ⟧ctxt ⊗ ⟦ apply P (μ P) ⟧ty) ⇒ X)
                    (apply-coincides P (μ P)) p₂)
  -- TODO: fold-μ requires Mon-aware initial algebras (HasMu-Mon, step 3).
  -- The var-carrier mismatch in the algebra body (poly applied at Mon ⟦τ⟧ty
  -- vs. ⟦apply Q τ⟧ty with bare τ at vars) can't be bridged without either
  -- (a) Howard's pointed retraction, or (b) initial algebras of Mon ∘ F.
  ⟦ fold-μ alg M ⟧tm = ?

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ Mon (list→product ⟦sort⟧ σs)
  ⟦ [] ⟧tms = η ∘ to-terminal
  ⟦ M ∷ Ms ⟧tms =
    bind ⟦ M ⟧tm (bind (⟦ Ms ⟧tms ∘ p₁) (η ∘ ⟨ p₂ ∘ p₁ , p₂ ⟩))
