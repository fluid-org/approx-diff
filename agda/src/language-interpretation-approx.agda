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
  (PM : PointedMonad) -- if force is lossy then so is this semantics
  (Int : Model PFPC[ 𝒞 , T , P , Bool ] Sig)
  where

open HasExponentials E renaming (exp to _⟦→⟧_)
open PointedFPCat PFPC[ 𝒞 , T , P , Bool ] renaming (_×_ to _⊗_)
open HasCoproducts C renaming (coprod to _⊕_)
open language-syntax Sig
open Model Int
open PointedMonad PM renaming (unit to η)

Mon : obj → obj
Mon X = poly-obj P-Mon X

mutual
  ⟦_⟧ty : type → obj
  ⟦ unit ⟧ty       = Mon 𝟙
  ⟦ bool ⟧ty       = Mon Bool
  ⟦ base σ ⟧ty     = ⟦sort⟧ σ  -- comes with its own approximation structure
  ⟦ τ₁ [×] τ₂ ⟧ty  = Mon (⟦ τ₁ ⟧ty ⊗ ⟦ τ₂ ⟧ty)
  ⟦ τ₁ [+] τ₂ ⟧ty  = Mon (⟦ τ₁ ⟧ty ⊕ ⟦ τ₂ ⟧ty)
  ⟦ τ₁ [→] τ₂ ⟧ty  = Mon (⟦ τ₁ ⟧ty ⟦→⟧ ⟦ τ₂ ⟧ty)
  ⟦ μ P ⟧ty        = Mu .HasMu.μ ⟦ P ⟧poly

  ⟦_⟧poly : polynomial → Poly 𝒞
  ⟦ one ⟧poly       = P-Mon ∘ₚ Poly.one
  ⟦ const σ ⟧poly   = Poly.const ⟦ σ ⟧ty
  ⟦ var ⟧poly       = Poly.var
  ⟦ P [+] Q ⟧poly   = P-Mon ∘ₚ (⟦ P ⟧poly Poly.+ ⟦ Q ⟧poly)
  ⟦ P [×] Q ⟧poly   = P-Mon ∘ₚ (⟦ P ⟧poly Poly.× ⟦ Q ⟧poly)

⟦_⟧ctxt : ctxt → obj
⟦ emp ⟧ctxt = 𝟙
⟦ Γ , τ ⟧ctxt = ⟦ Γ ⟧ctxt ⊗ ⟦ τ ⟧ty

apply-coincides : ∀ Q τ → ⟦ apply Q τ ⟧ty ≡ poly-obj ⟦ Q ⟧poly ⟦ τ ⟧ty
apply-coincides one          τ = sym (poly-obj-comp P-Mon Poly.one ⟦ τ ⟧ty)
apply-coincides (const σ)    τ = refl
apply-coincides var          τ = refl
apply-coincides (P [+] Q)    τ =
  trans (cong Mon (cong₂ _⊕_ (apply-coincides P τ) (apply-coincides Q τ)))
        (sym (poly-obj-comp P-Mon (⟦ P ⟧poly Poly.+ ⟦ Q ⟧poly) ⟦ τ ⟧ty))
apply-coincides (P [×] Q)    τ =
  trans (cong Mon (cong₂ _⊗_ (apply-coincides P τ) (apply-coincides Q τ)))
        (sym (poly-obj-comp P-Mon (⟦ P ⟧poly Poly.× ⟦ Q ⟧poly) ⟦ τ ⟧ty))

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
    Mu .HasMu.inF ⟦ P ⟧poly ∘ subst (⟦ Γ ⟧ctxt ⇒_) (apply-coincides P (μ P)) ⟦ M ⟧tm
  ⟦ fold-μ alg M ⟧tm = {!!}

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
