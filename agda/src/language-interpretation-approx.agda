{-# OPTIONS --prop --postfix-projections --safe #-}

-- Per-root approx interpretation: every type former carries an outer Mon, except
-- base types (whose primitive interpretation already includes approximation).

open import Level using (_⊔_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; subst; trans)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; HasExponentials;
         HasBooleans; coproducts+exp→booleans)
open import functor using (Functor; StrongPointedFunctor)
open import polynomial-functor using (μPoly; module Sem)
import language-syntax
open import signature using (Signature; Model; PFPC[_,_,_,_]; PointedFPCat)
open import every using (Every; []; _∷_)

module language-interpretation-approx
  {ℓ} (Sig : Signature ℓ)
  {o m e}
  (𝒞 : Category o m e)
  (T  : HasTerminal 𝒞)
  (P  : HasProducts 𝒞)
  (SC : HasStrongCoproducts 𝒞 P)
  (E  : HasExponentials 𝒞 P)
  (let C = strong-coproducts→coproducts T SC)
  (let open Sem T P SC)
  (let open HasBooleans (coproducts+exp→booleans T C E))
  (PM : StrongPointedFunctor P)
  (let open μPoly-Sem (StrongPointedFunctor.F PM))
  (Mu : HasMu-μPoly)
  (Int : Model PFPC[ 𝒞 , T , P , Bool ] Sig)
  where

open HasExponentials E renaming (exp to _⟦→⟧_)
open PointedFPCat PFPC[ 𝒞 , T , P , Bool ] renaming (_×_ to _⊗_)
open HasCoproducts C renaming (coprod to _⊕_)
open language-syntax Sig
open Model Int
open StrongPointedFunctor PM renaming (unit to η)

M : obj → obj
M X = fobj X

mutual
  ⟦_⟧ty : type → obj
  ⟦ unit ⟧ty       = M 𝟙
  ⟦ bool ⟧ty       = M Bool
  ⟦ base σ ⟧ty     = ⟦sort⟧ σ  -- comes with its own approximation structure
  ⟦ τ₁ [×] τ₂ ⟧ty  = M (⟦ τ₁ ⟧ty ⊗ ⟦ τ₂ ⟧ty)
  ⟦ τ₁ [+] τ₂ ⟧ty  = M (⟦ τ₁ ⟧ty ⊕ ⟦ τ₂ ⟧ty)
  ⟦ τ₁ [→] τ₂ ⟧ty  = M (⟦ τ₁ ⟧ty ⟦→⟧ ⟦ τ₂ ⟧ty)
  ⟦ μ P ⟧ty        = HasMu-μPoly.μ Mu ⟦ P ⟧poly

  ⟦_⟧poly : polynomial → μPoly 𝒞
  ⟦ one ⟧poly       = μPoly.Mon μPoly.one
  ⟦ const σ ⟧poly   = μPoly.const ⟦ σ ⟧ty
  ⟦ var ⟧poly       = μPoly.var
  ⟦ P [+] Q ⟧poly   = μPoly.Mon (⟦ P ⟧poly μPoly.+ ⟦ Q ⟧poly)
  ⟦ P [×] Q ⟧poly   = μPoly.Mon (⟦ P ⟧poly μPoly.× ⟦ Q ⟧poly)

⟦_⟧ctxt : ctxt → obj
⟦ emp ⟧ctxt = 𝟙
⟦ Γ , τ ⟧ctxt = ⟦ Γ ⟧ctxt ⊗ ⟦ τ ⟧ty

apply-eq : ∀ Q τ → ⟦ apply Q τ ⟧ty ≡ μPoly-obj ⟦ Q ⟧poly ⟦ τ ⟧ty
apply-eq one          τ = refl
apply-eq (const σ)    τ = refl
apply-eq var          τ = refl
apply-eq (P [+] Q)    τ = cong M (cong₂ _⊕_ (apply-eq P τ) (apply-eq Q τ))
apply-eq (P [×] Q)    τ = cong M (cong₂ _⊗_ (apply-eq P τ) (apply-eq Q τ))

map-eval : (Q : μPoly 𝒞) {ctx t : obj} → (μPoly-obj Q (ctx ⟦→⟧ t) ⊗ ctx) ⇒ μPoly-obj Q t
map-eval μPoly.one         = to-terminal
map-eval (μPoly.const _)   = p₁
map-eval μPoly.var         = eval
map-eval (P μPoly.+ Q)     = eval ∘ ⟨ copair (lambda (in₁ ∘ map-eval P)) (lambda (in₂ ∘ map-eval Q)) ∘ p₁ , p₂ ⟩
map-eval (P μPoly.× Q)     = ⟨ map-eval P ∘ ⟨ p₁ ∘ p₁ , p₂ ⟩ , map-eval Q ∘ ⟨ p₂ ∘ p₁ , p₂ ⟩ ⟩
map-eval (μPoly.Mon P)     = η ∘ map-eval P ∘ ⟨ force ∘ p₁ , p₂ ⟩

⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
⟦ zero ⟧var = p₂
⟦ succ x ⟧var = ⟦ x ⟧var ∘ p₁

mutual
  ⟦_⟧tm : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
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
  ⟦ bop ω Ms ⟧tm = ⟦op⟧ ω ∘ ⟦ Ms ⟧tms
  ⟦ brel ω Ms ⟧tm = η ∘ ⟦rel⟧ ω ∘ ⟦ Ms ⟧tms
  ⟦ roll {Γ = Γ} {P = P} M ⟧tm =
    HasMu-μPoly.inμ Mu ⟦ P ⟧poly ∘ subst (⟦ Γ ⟧ctxt ⇒_) (apply-eq P (μ P)) ⟦ M ⟧tm
  ⟦ fold-μ {Γ = Γ} {P = Q} {τ = τ} alg M ⟧tm =
    eval ∘ ⟨ HasMu-μPoly.⦅_⦆ Mu closure-converted ∘ ⟦ M ⟧tm , id _ ⟩
    where
      closure-converted : μPoly-obj ⟦ Q ⟧poly (⟦ Γ ⟧ctxt ⟦→⟧ ⟦ τ ⟧ty) ⇒ (⟦ Γ ⟧ctxt ⟦→⟧ ⟦ τ ⟧ty)
      closure-converted = lambda (eval ∘ ⟨
        force ∘ ⟦ alg ⟧tm ∘ p₂ ,
          subst (λ X → (μPoly-obj ⟦ Q ⟧poly (⟦ Γ ⟧ctxt ⟦→⟧ ⟦ τ ⟧ty) ⊗ ⟦ Γ ⟧ctxt) ⇒ X)
                (sym (apply-eq Q τ)) (map-eval ⟦ Q ⟧poly)
        ⟩)

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
