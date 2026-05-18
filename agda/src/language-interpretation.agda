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
  (HM : ∀ Q → Sem.HasMu T P C Q)
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

-- Interpret as lifting L X = 𝟙 + X. Future refactor could parameterise on a "polynomial monad" record,
-- replacing the literal 𝟙 ⊕ _ here and `const 𝟙 +` in ⟦approx⟧poly below.
mutual
  ⟦_⟧ty : type → obj
  ⟦ unit ⟧ty = 𝟙
  ⟦ bool ⟧ty = Bool
  ⟦ base σ ⟧ty = ⟦sort⟧ σ
  ⟦ τ₁ [×] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⊗ ⟦ τ₂ ⟧ty
  ⟦ τ₁ [→] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⟦→⟧ ⟦ τ₂ ⟧ty
  ⟦ τ₁ [+] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⊕ ⟦ τ₂ ⟧ty
  ⟦ μ P ⟧ty = HasMu.μ (HM (⟦ P ⟧poly))
  ⟦ approx τ ⟧ty  = 𝟙 ⊕ ⟦ τ ⟧ty

  ⟦_⟧poly : polynomial → Poly 𝒞
  ⟦ one ⟧poly       = Poly.one
  ⟦ const σ ⟧poly   = Poly.const ⟦ σ ⟧ty
  ⟦ var ⟧poly       = Poly.var
  ⟦ P₁ + P₂ ⟧poly      = ⟦ P₁ ⟧poly Poly.+ ⟦ P₂ ⟧poly
  ⟦ P₁ × P₂ ⟧poly      = ⟦ P₁ ⟧poly Poly.× ⟦ P₂ ⟧poly
  ⟦ approx P ⟧poly  = Poly.const 𝟙 Poly.+ ⟦ P ⟧poly

⟦_⟧ctxt : ctxt → obj
⟦ emp ⟧ctxt = 𝟙
⟦ Γ , τ ⟧ctxt = ⟦ Γ ⟧ctxt ⊗ ⟦ τ ⟧ty

-- Syntactic application of a polynomial agrees with action of corresponding functor on objects.
apply-coincides : ∀ Q τ → ⟦ apply Q τ ⟧ty ≡ poly-obj ⟦ Q ⟧poly ⟦ τ ⟧ty
apply-coincides one          τ = refl
apply-coincides (const σ)    τ = refl
apply-coincides var          τ = refl
apply-coincides (Q₁ + Q₂)    τ = cong₂ _⊕_ (apply-coincides Q₁ τ) (apply-coincides Q₂ τ)
apply-coincides (Q₁ × Q₂)    τ = cong₂ _⊗_ (apply-coincides Q₁ τ) (apply-coincides Q₂ τ)
apply-coincides (approx Q)   τ = cong (𝟙 ⊕_) (apply-coincides Q τ)

-- F-apply: for a polynomial Q and result types ctx, t, take a polynomial
-- value whose recursive positions hold (ctx ⇒ t)-shaped function values
-- together with a ctx argument, and apply each function. Used by fold-μ
-- to thread the typing context Γ through the polynomial's algebra slots.
F-apply : (Q : Poly 𝒞) {ctx t : obj} → (poly-obj Q (ctx ⟦→⟧ t) ⊗ ctx) ⇒ poly-obj Q t
F-apply Poly.one       = to-terminal
F-apply (Poly.const _) = p₁
F-apply Poly.var       = eval
F-apply (Q₁ Poly.+ Q₂) = eval ∘ ⟨ copair (lambda (in₁ ∘ F-apply Q₁)) (lambda (in₂ ∘ F-apply Q₂)) ∘ p₁ , p₂ ⟩
F-apply (Q₁ Poly.× Q₂) = ⟨ F-apply Q₁ ∘ ⟨ p₁ ∘ p₁ , p₂ ⟩ , F-apply Q₂ ∘ ⟨ p₂ ∘ p₁ , p₂ ⟩ ⟩

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
    HasMu.inF (HM ⟦ P ⟧poly) ∘ subst (⟦ Γ ⟧ctxt ⇒_) (apply-coincides P (μ P)) ⟦ M ⟧tm
  ⟦ pure M ⟧tm   = in₂ ∘ ⟦ M ⟧tm
  ⟦ bind {σ = σ} M N ⟧tm =
    eval ∘ ⟨ copair (lambda (in₁ ∘ to-terminal)) (lambda (⟦ N ⟧tm ∘ swap)) ∘ ⟦ M ⟧tm , id _ ⟩
  ⟦ fold-μ {Γ = Γ} {P = Q} {τ = τ} alg M ⟧tm =
    eval ∘ ⟨ HasMu.⦅_⦆ (HM ⟦ Q ⟧poly) closed-alg ∘ ⟦ M ⟧tm , id _ ⟩
    where
      closed-alg : poly-obj ⟦ Q ⟧poly (⟦ Γ ⟧ctxt ⟦→⟧ ⟦ τ ⟧ty) ⇒ (⟦ Γ ⟧ctxt ⟦→⟧ ⟦ τ ⟧ty)
      closed-alg = lambda (eval ∘ ⟨
        ⟦ alg ⟧tm ∘ p₂ ,
          subst (λ X → (poly-obj ⟦ Q ⟧poly (⟦ Γ ⟧ctxt ⟦→⟧ ⟦ τ ⟧ty) ⊗ ⟦ Γ ⟧ctxt) ⇒ X)
                (sym (apply-coincides Q τ)) (F-apply ⟦ Q ⟧poly)
        ⟩)

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
