{-# OPTIONS --prop --postfix-projections --safe #-}

-- Per-root approx interpretation: every type former carries an outer Mon, except
-- base types (whose primitive interpretation already includes approximation).

open import Level using (_⊔_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; subst; trans)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasExponentials;
         HasBooleans; coproducts+exp→booleans)
open import polynomial-functor using (Poly; _∘ₚ_; module Sem)
import language-syntax
open import signature using (Signature; Model; PFPC[_,_,_,_]; PointedFPCat)
open import every using (Every; []; _∷_)

module language-interpretation-approx
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
  (PM : PolyMonad)
  (Int : Model PFPC[ 𝒞 , T , P , Bool ] Sig)
  where

open HasExponentials E renaming (exp to _⟦→⟧_)
open PointedFPCat PFPC[ 𝒞 , T , P , Bool ] renaming (_×_ to _⊗_)
open HasCoproducts C renaming (coprod to _⊕_)
open language-syntax Sig
open Model Int
open PolyMonad PM renaming (unit to η)

Mon : obj → obj
Mon X = poly-obj P-Mon X

mutual
  ⟦_⟧ty : type → obj
  ⟦ unit ⟧ty = 𝟙
  ⟦ bool ⟧ty = Bool
  ⟦ base σ ⟧ty = ⟦sort⟧ σ
  ⟦ τ₁ [×] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⊗ ⟦ τ₂ ⟧ty
  ⟦ τ₁ [→] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⟦→⟧ Mon ⟦ τ₂ ⟧ty
  ⟦ τ₁ [+] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⊕ ⟦ τ₂ ⟧ty
  ⟦ μ P ⟧ty = HasMu.μ Mu (P-Mon ∘ₚ ⟦ P ⟧poly)

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
map-eval (P Poly.+ Q)   = eval ∘ ⟨ copair (lambda (in₁ ∘ map-eval P)) (lambda (in₂ ∘ map-eval Q)) ∘ p₁ , p₂ ⟩
map-eval (P Poly.× Q)   = ⟨ map-eval P ∘ ⟨ p₁ ∘ p₁ , p₂ ⟩ , map-eval Q ∘ ⟨ p₂ ∘ p₁ , p₂ ⟩ ⟩

⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
⟦ zero ⟧var = p₂
⟦ succ x ⟧var = ⟦ x ⟧var ∘ p₁

-- Kleisli bind in Γ × X context: bind a Γ ⇒ Mon X with a Γ × X ⇒ Mon Y body.
bind : ∀ {Γ x y} → Γ ⇒ Mon x → (Γ ⊗ x) ⇒ Mon y → Γ ⇒ Mon y
bind f k = extend k ∘ ⟨ id _ , f ⟩

-- Functorial action of Mon on morphisms, derived from extend + unit.
Mon-map : ∀ {x y} → (x ⇒ y) → Mon x ⇒ Mon y
Mon-map f = extend (η ∘ f ∘ p₂) ∘ ⟨ to-terminal , id _ ⟩

-- Monadic traversal (sequence) for polynomials: poly-obj Q (Mon X) ⇒ Mon (poly-obj Q X).
-- For Q built from sums/products/var, this threads Mon outward through the structure.
seq-poly : (Q : Poly 𝒞) → ∀ {X} → poly-obj Q (Mon X) ⇒ Mon (poly-obj Q X)
seq-poly Poly.one       = η
seq-poly (Poly.const _) = η
seq-poly Poly.var       = id _
seq-poly (P Poly.+ Q)   = copair (Mon-map in₁ ∘ seq-poly P) (Mon-map in₂ ∘ seq-poly Q)
seq-poly (P Poly.× Q)   =
  bind (seq-poly P ∘ p₁) (bind (seq-poly Q ∘ p₂ ∘ p₁) (η ∘ ⟨ p₂ ∘ p₁ , p₂ ⟩))

eval-and-seq : (Q : Poly 𝒞) {ctx t : obj} → (poly-obj Q (ctx ⟦→⟧ Mon t) ⊗ ctx) ⇒ Mon (poly-obj Q t)
eval-and-seq Q = seq-poly Q ∘ map-eval Q

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
    bind ⟦ M ⟧tm (eval ∘ ⟨ copair (lambda (⟦ M₁ ⟧tm ∘ ⟨ p₂ , p₁ ⟩)) (lambda (⟦ M₂ ⟧tm ∘ ⟨ p₂ , p₁ ⟩)) ∘ p₂ , p₁ ⟩)
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
    η ∘ HasMu.inF Mu (P-Mon ∘ₚ ⟦ P ⟧poly) ∘ subst (⟦ Γ ⟧ctxt ⇒_) eq ⟦ M ⟧tm
    where
      eq : poly-obj P-Mon ⟦ apply P (μ P) ⟧ty ≡ poly-obj (P-Mon ∘ₚ ⟦ P ⟧poly) (HasMu.μ Mu (P-Mon ∘ₚ ⟦ P ⟧poly))
      eq = trans (cong (poly-obj P-Mon) (apply-coincides P (μ P))) (sym (poly-obj-comp P-Mon ⟦ P ⟧poly _))
  ⟦ fold-μ alg M ⟧tm = {!!}

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ Mon (list→product ⟦sort⟧ σs)
  ⟦ [] ⟧tms = η ∘ to-terminal
  ⟦ M ∷ Ms ⟧tms =
    bind ⟦ M ⟧tm (bind (⟦ Ms ⟧tms ∘ p₁) (η ∘ ⟨ p₂ ∘ p₁ , p₂ ⟩))
