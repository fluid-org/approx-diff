{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; subst)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasExponentials;
         HasBooleans; coproducts+exp→booleans)
open import polynomial-functor using (Poly; module Sem)
import language-syntax
open import signature using (Signature; Model; PFPC[_,_,_,_]; PointedFPCat)
open import every using (Every; []; _∷_)

module language-interpretation
  {ℓ} (Sig : Signature ℓ)
  {o m e}
  (𝒞 : Category o m e)
  (T  : HasTerminal 𝒞)
  (P  : HasProducts 𝒞)
  (C  : HasCoproducts 𝒞)
  (E  : HasExponentials 𝒞 P)
  (let open Sem T P C)
  (let open HasBooleans (coproducts+exp→booleans T C E))
  (Mu : HasMu)
  (Int : Model PFPC[ 𝒞 , T , P , Bool ] Sig)
  where

open HasExponentials E renaming (exp to _⟦→⟧_)
open PointedFPCat PFPC[ 𝒞 , T , P , Bool ] renaming (_×_ to _⊗_)
open HasCoproducts C renaming (coprod to _⊕_)
open language-syntax Sig
open Model Int

mutual
  ⟦_⟧ty : type → obj
  ⟦ unit ⟧ty = 𝟙
  ⟦ bool ⟧ty = Bool
  ⟦ base σ ⟧ty = ⟦sort⟧ σ
  ⟦ τ₁ [×] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⊗ ⟦ τ₂ ⟧ty
  ⟦ τ₁ [→] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⟦→⟧ ⟦ τ₂ ⟧ty
  ⟦ τ₁ [+] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⊕ ⟦ τ₂ ⟧ty
  ⟦ μ P ⟧ty = HasMu.μ Mu ⟦ P ⟧poly

  ⟦_⟧poly : polynomial → Poly 𝒞
  ⟦ one ⟧poly       = Poly.one
  ⟦ const σ ⟧poly   = Poly.const ⟦ σ ⟧ty
  ⟦ var ⟧poly       = Poly.var
  ⟦ P [+] Q ⟧poly   = ⟦ P ⟧poly Poly.+ ⟦ Q ⟧poly
  ⟦ P [×] Q ⟧poly   = ⟦ P ⟧poly Poly.× ⟦ Q ⟧poly

⟦_⟧ctxt : ctxt → obj
⟦ emp ⟧ctxt = 𝟙
⟦ Γ , τ ⟧ctxt = ⟦ Γ ⟧ctxt ⊗ ⟦ τ ⟧ty

-- Syntactic application of a polynomial agrees with action of corresponding functor on objects.
apply-coincides : ∀ Q τ → ⟦ apply Q τ ⟧ty ≡ poly-obj ⟦ Q ⟧poly ⟦ τ ⟧ty
apply-coincides one          τ = refl
apply-coincides (const σ)    τ = refl
apply-coincides var          τ = refl
apply-coincides (P [+] Q)    τ = cong₂ _⊕_ (apply-coincides P τ) (apply-coincides Q τ)
apply-coincides (P [×] Q)    τ = cong₂ _⊗_ (apply-coincides P τ) (apply-coincides Q τ)

-- Take a polynomial container of (ctx ⇒ t) morphisms and a ctx, and reduce using eval.
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

mutual
  ⟦_⟧tm : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
  ⟦ var x ⟧tm = ⟦ x ⟧var
  ⟦ unit ⟧tm = to-terminal
  ⟦ true ⟧tm = True ∘ to-terminal
  ⟦ false ⟧tm = False ∘ to-terminal
  ⟦ if M then M₁ else M₂ ⟧tm = cond ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ inl M ⟧tm = in₁ ∘ ⟦ M ⟧tm
  ⟦ inr M ⟧tm = in₂ ∘ ⟦ M ⟧tm
  ⟦ case M M₁ M₂ ⟧tm = eval ∘ ⟨ copair (lambda (⟦ M₁ ⟧tm ∘ swap)) (lambda (⟦ M₂ ⟧tm ∘ swap)) ∘ ⟦ M ⟧tm , id _ ⟩
  ⟦ pair M N ⟧tm = ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ fst M ⟧tm = p₁ ∘ ⟦ M ⟧tm
  ⟦ snd M ⟧tm = p₂ ∘ ⟦ M ⟧tm
  ⟦ lam M ⟧tm = lambda ⟦ M ⟧tm
  ⟦ app M  N ⟧tm = eval ∘ ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ bop ω Ms ⟧tm = ⟦op⟧ ω ∘ ⟦ Ms ⟧tms
  ⟦ brel ω Ms ⟧tm = ⟦rel⟧ ω ∘ ⟦ Ms ⟧tms
  ⟦ roll {Γ = Γ} {P = P} M ⟧tm =
    HasMu.inF Mu ⟦ P ⟧poly ∘ subst (⟦ Γ ⟧ctxt ⇒_) (apply-coincides P (μ P)) ⟦ M ⟧tm
  ⟦ fold-μ {Γ = Γ} {P = Q} {τ = τ} alg M ⟧tm =
    eval ∘ ⟨ HasMu.⦅_⦆ Mu closure-converted ∘ ⟦ M ⟧tm , id _ ⟩
    where
      closure-converted : poly-obj ⟦ Q ⟧poly (⟦ Γ ⟧ctxt ⟦→⟧ ⟦ τ ⟧ty) ⇒ (⟦ Γ ⟧ctxt ⟦→⟧ ⟦ τ ⟧ty)
      closure-converted = lambda (eval ∘ ⟨
        ⟦ alg ⟧tm ∘ p₂ ,
          subst (λ X → (poly-obj ⟦ Q ⟧poly (⟦ Γ ⟧ctxt ⟦→⟧ ⟦ τ ⟧ty) ⊗ ⟦ Γ ⟧ctxt) ⇒ X)
                (sym (apply-coincides Q τ)) (map-eval ⟦ Q ⟧poly)
        ⟩)

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
