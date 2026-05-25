{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; subst)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; HasExponentials;
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
  (SC : HasStrongCoproducts 𝒞 P)
  (E  : HasExponentials 𝒞 P)
  (let C = strong-coproducts→coproducts T SC)
  (let open Sem T P SC renaming (fobj to poly-obj))
  (let open HasBooleans (coproducts+exp→booleans T C E))
  (Mu : HasMu)
  (Int : Model PFPC[ 𝒞 , T , P , Bool ] Sig)
  where

open HasExponentials E renaming (exp to _⟦→⟧_)
open PointedFPCat PFPC[ 𝒞 , T , P , Bool ] renaming (_×_ to _⊗_)
open HasCoproducts C renaming (coprod to _⊕_)
open language-syntax Sig
open Model Int
open HasMu Mu using (inF; ⦅_⦆) renaming (μ to μ-obj)

mutual
  ⟦_⟧ty : type → obj
  ⟦ unit ⟧ty = 𝟙
  ⟦ bool ⟧ty = Bool
  ⟦ base σ ⟧ty = ⟦sort⟧ σ
  ⟦ τ₁ [×] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⊗ ⟦ τ₂ ⟧ty
  ⟦ τ₁ [→] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⟦→⟧ ⟦ τ₂ ⟧ty
  ⟦ τ₁ [+] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⊕ ⟦ τ₂ ⟧ty
  ⟦ μ P ⟧ty = μ-obj ⟦ P ⟧poly

  ⟦_⟧poly : polynomial → Poly 𝒞
  ⟦ const σ ⟧poly   = Poly.const ⟦ σ ⟧ty
  ⟦ var ⟧poly       = Poly.var
  ⟦ P [+] Q ⟧poly   = ⟦ P ⟧poly Poly.+ ⟦ Q ⟧poly
  ⟦ P [×] Q ⟧poly   = ⟦ P ⟧poly Poly.× ⟦ Q ⟧poly

⟦_⟧ctxt : ctxt → obj
⟦ emp ⟧ctxt = 𝟙
⟦ Γ , τ ⟧ctxt = ⟦ Γ ⟧ctxt ⊗ ⟦ τ ⟧ty

-- Syntactic application of a polynomial agrees with action of corresponding functor on objects.
apply-eq : ∀ Q τ → ⟦ apply Q τ ⟧ty ≡ poly-obj ⟦ Q ⟧poly ⟦ τ ⟧ty
apply-eq (const σ)    τ = refl
apply-eq var          τ = refl
apply-eq (P [+] Q)    τ = cong₂ _⊕_ (apply-eq P τ) (apply-eq Q τ)
apply-eq (P [×] Q)    τ = cong₂ _⊗_ (apply-eq P τ) (apply-eq Q τ)

⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
⟦ zero ⟧var = p₂
⟦ succ x ⟧var = ⟦ x ⟧var ∘ p₁

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
  ⟦ roll {Γ = Γ} {P = P} M ⟧tm = inF ⟦ P ⟧poly ∘ subst (⟦ Γ ⟧ctxt ⇒_) (apply-eq P (μ P)) ⟦ M ⟧tm
  ⟦ fold-μ {Γ = Γ} {P = Q} {τ = τ} alg M ⟧tm =
    ⦅ subst (λ X → (⟦ Γ ⟧ctxt ⊗ X) ⇒ ⟦ τ ⟧ty) (apply-eq Q τ) ⟦ alg ⟧tm ⦆ ∘ ⟨ id _ , ⟦ M ⟧tm ⟩

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
