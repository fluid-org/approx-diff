{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; sym; subst)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasExponentials;
         HasBooleans; coproducts+exp→booleans; HasLists; Poly; HasMu; poly-obj)
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
  (L  : HasLists 𝒞 T P)
  (HM : ∀ Q → HasMu 𝒞 T P C Q)
  (Int : Model PFPC[ 𝒞 , T , P , HasBooleans.Bool (coproducts+exp→booleans T C E) ] Sig)
  where

B : HasBooleans 𝒞 T P
B = coproducts+exp→booleans T C E

open HasExponentials E renaming (exp to _⟦→⟧_)
open PointedFPCat PFPC[ 𝒞 , T , P , HasBooleans.Bool B ]
open HasCoproducts C renaming (coprod to _+_)
open HasBooleans B
open HasLists L renaming (list to ⟦list⟧; nil to ⟦nil⟧; cons to ⟦cons⟧; fold to ⟦fold⟧)

open language-syntax Sig
open Model Int

mutual
  ⟦_⟧ty : type → obj
  ⟦ unit ⟧ty = 𝟙
  ⟦ bool ⟧ty = Bool
  ⟦ base σ ⟧ty = ⟦sort⟧ σ
  ⟦ τ₁ [×] τ₂ ⟧ty = ⟦ τ₁ ⟧ty × ⟦ τ₂ ⟧ty
  ⟦ τ₁ [→] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⟦→⟧ ⟦ τ₂ ⟧ty
  ⟦ τ₁ [+] τ₂ ⟧ty = ⟦ τ₁ ⟧ty + ⟦ τ₂ ⟧ty
  ⟦ list τ ⟧ty = ⟦list⟧ ⟦ τ ⟧ty
  ⟦ μ P ⟧ty = HasMu.μ (HM (⟦ P ⟧poly))

  ⟦_⟧poly : polytype → Poly 𝒞
  ⟦ poly-one ⟧poly       = Poly.one
  ⟦ poly-param σ ⟧poly   = Poly.param ⟦ σ ⟧ty
  ⟦ poly-var ⟧poly       = Poly.var
  ⟦ P₁ [⊞] P₂ ⟧poly      = ⟦ P₁ ⟧poly Poly.⊞ ⟦ P₂ ⟧poly
  ⟦ P₁ [⊠] P₂ ⟧poly      = ⟦ P₁ ⟧poly Poly.⊠ ⟦ P₂ ⟧poly

⟦_⟧ctxt : ctxt → obj
⟦ emp ⟧ctxt = 𝟙
⟦ Γ , τ ⟧ctxt = ⟦ Γ ⟧ctxt × ⟦ τ ⟧ty

-- Equation showing that the meta-level polyApply on types agrees with the
-- categorical poly-obj on objects, modulo the polytype interpretation.
-- Needed because polyApply unfolds at the syntax level while poly-obj
-- unfolds at the categorical level — both reduce identically by structure,
-- but Agda doesn't see this without an explicit lemma.
polyApply-coincides : ∀ Q τ → ⟦ polyApply Q τ ⟧ty ≡ poly-obj T P C ⟦ Q ⟧poly ⟦ τ ⟧ty
polyApply-coincides poly-one       τ = refl
polyApply-coincides (poly-param σ) τ = refl
polyApply-coincides poly-var       τ = refl
polyApply-coincides (Q₁ [⊞] Q₂)    τ = cong₂ _+_ (polyApply-coincides Q₁ τ) (polyApply-coincides Q₂ τ)
polyApply-coincides (Q₁ [⊠] Q₂)    τ = cong₂ _×_ (polyApply-coincides Q₁ τ) (polyApply-coincides Q₂ τ)

⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
⟦ zero ⟧var = p₂
⟦ succ x ⟧var = ⟦ x ⟧var ∘ p₁

swap : ∀ {x y} → (x × y) ⇒ (y × x)
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
  ⟦ nil ⟧tm = ⟦nil⟧ ∘ to-terminal
  ⟦ cons M N ⟧tm = ⟦cons⟧ ∘ ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ fold M₁ M₂ M ⟧tm = ⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ roll {Γ = Γ} {P = P} M ⟧tm =
    HasMu.sup (HM ⟦ P ⟧poly) ∘ subst (⟦ Γ ⟧ctxt ⇒_) (polyApply-coincides P (μ P)) ⟦ M ⟧tm

  ⟦_⟧tms : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ list→product ⟦sort⟧ σs
  ⟦ [] ⟧tms = to-terminal
  ⟦ M ∷ Ms ⟧tms = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧tms ⟩
